/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block017

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part054`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0031 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_343 A))
          (Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_343 A))
            (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_344 h))
          (Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_344 h))
            (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_338 A) from (by
                      unfold nb090_alpha_dummy_338;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
                  (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_340 h) from (by
                      unfold nb090_alpha_dummy_340;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_337 A) from (by
                        unfold nb090_alpha_dummy_337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
                    (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_339 h) from (by
                        unfold nb090_alpha_dummy_339;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0340 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_343 A) from (by
                          unfold nb090_alpha_dummy_343;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0342 A) 0))))
                      (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_344 h) from (by
                          unfold nb090_alpha_dummy_344;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0343 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_341 A) from (by
                            unfold nb090_alpha_dummy_341;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                        (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_342 h) from (by
                            unfold nb090_alpha_dummy_342;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0341 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_335 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                              unfold nb090_alpha_dummy_345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                              unfold nb090_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from (by
                                unfold nb090_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from (by
                                unfold nb090_alpha_dummy_348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A),
        (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A),
        (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A),
        (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A),
        (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352
        A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                    (by
                                      unfold nb090_alpha_dummy_349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from
                                    (by
                                      unfold nb090_alpha_dummy_350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_338 A) from (by
                        unfold nb090_alpha_dummy_338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
                    (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_340 h) from (by
                        unfold nb090_alpha_dummy_340;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0340 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_337 A) from (by
                          unfold nb090_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
                      (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_339 h) from (by
                          unfold nb090_alpha_dummy_339;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_343 A) from (by
                            unfold nb090_alpha_dummy_343;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0342 A) 0))))
                        (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_344 h) from (by
                            unfold nb090_alpha_dummy_344;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0343 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_341 A) from (by
                              unfold nb090_alpha_dummy_341;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                          (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_342 h) from (by
                              unfold nb090_alpha_dummy_342;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0341 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_335 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                                unfold nb090_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                            (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                                unfold nb090_alpha_dummy_347;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from
                                (by
                                  unfold nb090_alpha_dummy_346;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                              (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from
                                (by
                                  unfold nb090_alpha_dummy_348;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_338 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_340 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A),
        (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A),
        (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A),
        (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A),
        (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352
        A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A)
                                        from (by
                                          unfold nb090_alpha_dummy_349;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0346 A) 0)))) (show
                                        (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h)
                                        from (by
                                          unfold nb090_alpha_dummy_350;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0347 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                      ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                      ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                      ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                      ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                      ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
                                      ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                      ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                      ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                      ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                      ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A)
                                        from (by
                                          unfold nb090_alpha_dummy_349;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0346 A) 0)))) (show
                                        (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h)
                                        from (by
                                          unfold nb090_alpha_dummy_350;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0347 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                      ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                      ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                      ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                      ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                      ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)),
                                      ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                      ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                      ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                      ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                      ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part055`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0032 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
        ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_369 A))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_369 A)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_370 h))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_370 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                              unfold nb090_alpha_dummy_345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                              unfold nb090_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from (by
                                unfold nb090_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from (by
                                unfold nb090_alpha_dummy_348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_371 A) from
                                (by
                                  unfold nb090_alpha_dummy_371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0374 A) 0))))
                              (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_372 h) from
                                (by
                                  unfold nb090_alpha_dummy_372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0375 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_369 A) from (by
                                    unfold nb090_alpha_dummy_369;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0372 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_370 h) from (by
                                    unfold nb090_alpha_dummy_370;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0373 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A),
        (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A),
        (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A),
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352
        A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A),
        (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A),
        (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A),
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
                                    ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                    (by
                                      unfold nb090_alpha_dummy_349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from
                                    (by
                                      unfold nb090_alpha_dummy_350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
                                    ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                              unfold nb090_alpha_dummy_345;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0344 A) 0))))
                          (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                              unfold nb090_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0345 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from (by
                                unfold nb090_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0344 A) 1))))
                            (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from (by
                                unfold nb090_alpha_dummy_348;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0345 h) 1))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_371 A) from
                                (by
                                  unfold nb090_alpha_dummy_371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0374 A) 0))))
                              (show (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_372 h) from
                                (by
                                  unfold nb090_alpha_dummy_372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0375 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_369 A) from (by
                                    unfold nb090_alpha_dummy_369;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0372 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_370 h) from (by
                                    unfold nb090_alpha_dummy_370;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0373 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 1)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A),
        (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A),
        (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A),
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352
        A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0352
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0353
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0350
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0351
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_359 A) from (by
          unfold
            nb090_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0356
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_360 h) from (by
          unfold
            nb090_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0357
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_357 A) from (by
          unfold
            nb090_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0354
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_358 h) from (by
          unfold
            nb090_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0355
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A),
        (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)),
        ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A),
        (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
        ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A),
        (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A),
        (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A),
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
        ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_363 A) from (by
          unfold
            nb090_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0360
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_364 h) from (by
          unfold
            nb090_alpha_dummy_364;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0361
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0358
                    A)
                  0)))) (show (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0359
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_365 A) from (by
          unfold
            nb090_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0364
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_366 h) from (by
          unfold
            nb090_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0365
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_361 A) from (by
          unfold
            nb090_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0362
                    A)
                  0)))) (show (nb090_alpha_dummy_356 h) ≠ (nb090_alpha_dummy_362 h) from (by
          unfold
            nb090_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0363
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
                                    ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                    (by
                                      unfold nb090_alpha_dummy_349;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0346 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from
                                    (by
                                      unfold nb090_alpha_dummy_350;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0347 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from
                                      (by
                                        unfold nb090_alpha_dummy_349;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0346 A)
                                                0)))) (show (nb090_alpha_dummy_347 h) ≠
                                        (nb090_alpha_dummy_350 h) from (by
                                        unfold nb090_alpha_dummy_350;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0347 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
                                    ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
                                    ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)),
                                    ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
                                    ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
                                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                                    ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
                                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                    ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                    ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
            ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
            ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
            ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
            ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
            ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
            ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
            ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
            ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
            ((nb090_alpha_dummy_001 A), u),
            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb090_compact_fv_empty_0300 (A : Class) :
    (nb090_alpha_dummy_373 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0301 (v : Var) :
    (nb090_alpha_dummy_374 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0302 (A : Class) :
    (nb090_alpha_dummy_375 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0303 (v : Var) :
    (nb090_alpha_dummy_376 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0304 (A : Class) :
    (nb090_alpha_dummy_378 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0305 (v : Var) :
    (nb090_alpha_dummy_380 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0306 (A : Class) :
    (nb090_alpha_dummy_377 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0307 (v : Var) :
    (nb090_alpha_dummy_379 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
