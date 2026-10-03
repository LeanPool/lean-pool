/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block019

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part058`. -/


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
noncomputable def nb090_split_alpha_0035 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_341 A)) (syn_ccompl
          (Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_342 h)) (syn_ccompl
          (Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                                  (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
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
                              (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_341 A) from
                                (by
                                  unfold nb090_alpha_dummy_341;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                              (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_342 h) from
                                (by
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
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                                    unfold nb090_alpha_dummy_345;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0344 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                                    unfold nb090_alpha_dummy_347;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0345 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from
                                    (by
                                      unfold nb090_alpha_dummy_346;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0344 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from
                                    (by
                                      unfold nb090_alpha_dummy_348;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0345 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
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
                  (nb090_support_mem_0348 A)
                  1)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_351 A) from (by
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
                  (nb090_support_mem_0346
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347
                    h)
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
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_359 A) from (by
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A
        h))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_363 A) from (by
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_365 A) from (by
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
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A),
        (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
        ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A),
        (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
        ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
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
                                  (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
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
                              (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_341 A) from
                                (by
                                  unfold nb090_alpha_dummy_341;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0339 A) 0))))
                              (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_342 h) from
                                (by
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
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from (by
                                    unfold nb090_alpha_dummy_345;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0344 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_347 h) from (by
                                    unfold nb090_alpha_dummy_347;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0345 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A) from
                                    (by
                                      unfold nb090_alpha_dummy_346;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0344 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h) from
                                    (by
                                      unfold nb090_alpha_dummy_348;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0345 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
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
                  (nb090_support_mem_0348 A)
                  1)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_351 A) from (by
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
                  (nb090_support_mem_0346
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347
                    h)
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
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_359 A) from (by
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A
        h))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_352 A) ≠
        (nb090_alpha_dummy_363 A) from (by
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
        (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠
        (nb090_alpha_dummy_365 A) from (by
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
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A),
        (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
        ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A),
        (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)),
        ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part059`. -/


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
noncomputable def nb090_split_alpha_0036 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
        ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
        ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
        ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_338 A))
          (Class.cv (nb090_alpha_dummy_333 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_340 h))
          (Class.cv (nb090_alpha_dummy_335 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
              unfold nb090_alpha_dummy_338;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))))
          (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
              unfold nb090_alpha_dummy_340;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))))
          (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_337 A) from (by
                unfold nb090_alpha_dummy_337;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))))
            (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
                unfold nb090_alpha_dummy_339;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))))
            (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_367 A) from
                (by
                  unfold nb090_alpha_dummy_367;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0370 A) 0))))
              (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_368 h) from (by
                  unfold nb090_alpha_dummy_368;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0371 h) 0))))
              (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_341 A) from
                  (by
                    unfold nb090_alpha_dummy_341;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0367 A) 0))))
                (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_342 h) from (by
                    unfold nb090_alpha_dummy_342;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0369 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
                ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
                ((Class.cv (nb090_alpha_dummy_335 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from
                                      (by
                                        unfold nb090_alpha_dummy_345;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0344 A)
                                                0)))) (show (nb090_alpha_dummy_340 h) ≠
                                        (nb090_alpha_dummy_347 h) from (by
                                        unfold nb090_alpha_dummy_347;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0345 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A)
                                        from (by
                                          unfold nb090_alpha_dummy_346;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0344 A) 1)))) (show
                                        (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h)
                                        from (by
                                          unfold nb090_alpha_dummy_348;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0345 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_338 A) ≠
        (nb090_alpha_dummy_371 A) from (by
          unfold nb090_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0374 A) 0)))) (show (nb090_alpha_dummy_340 h) ≠
        (nb090_alpha_dummy_372 h) from (by
          unfold nb090_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0375 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_369 A) from (by
          unfold nb090_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0372 A) 0)))) (show (nb090_alpha_dummy_340 h) ≠
        (nb090_alpha_dummy_370 h) from (by
          unfold nb090_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0373 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_338 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_340 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348
                    A)
                  1)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold
            nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold
            nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347
                    h)
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
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_359 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_359 A) from (by
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
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_365 A) from (by
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
        ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A),
        (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
        ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
        ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A),
        (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
        ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_345 A) from
                                      (by
                                        unfold nb090_alpha_dummy_345;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0344 A)
                                                0)))) (show (nb090_alpha_dummy_340 h) ≠
                                        (nb090_alpha_dummy_347 h) from (by
                                        unfold nb090_alpha_dummy_347;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0345 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_346 A)
                                        from (by
                                          unfold nb090_alpha_dummy_346;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0344 A) 1)))) (show
                                        (nb090_alpha_dummy_340 h) ≠ (nb090_alpha_dummy_348 h)
                                        from (by
                                          unfold nb090_alpha_dummy_348;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0345 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_338 A) ≠
        (nb090_alpha_dummy_371 A) from (by
          unfold nb090_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0374 A) 0)))) (show (nb090_alpha_dummy_340 h) ≠
        (nb090_alpha_dummy_372 h) from (by
          unfold nb090_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0375 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_338 A) ≠ (nb090_alpha_dummy_369 A) from (by
          unfold nb090_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0372 A) 0)))) (show (nb090_alpha_dummy_340 h) ≠
        (nb090_alpha_dummy_370 h) from (by
          unfold nb090_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0373 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_338 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_340 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_352 A) from (by
          unfold nb090_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348
                    A)
                  1)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_355 h) from (by
          unfold nb090_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_351 A) from (by
          unfold nb090_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0348
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_354 h) from (by
          unfold nb090_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0349
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold
            nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346
                    A)
                  0)))) (show (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_350 h) from (by
          unfold
            nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347
                    h)
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
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_359 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_353
        A) ≠ (nb090_alpha_dummy_359 A) from (by
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
        (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_353 A) ≠ (nb090_alpha_dummy_365 A) from (by
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠
        (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
        ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A),
        (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
        ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_349 A) from (by
          unfold nb090_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0346 A) 0)))) (show (nb090_alpha_dummy_347 h) ≠
        (nb090_alpha_dummy_350 h) from (by
          unfold nb090_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0347 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)),
        ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A),
        (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)),
        ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A),
        (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
        ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A),
        (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
        ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)),
                    ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)),
                    ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)),
                    ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)),
                    ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)),
                    ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                    ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                    ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                    ((nb090_alpha_dummy_001 A), u),
                    ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb090_split_alpha_0037 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_v : h ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classEq (syn_cin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))
        (syn_crn (Class.cv (nb090_alpha_dummy_000 A))))
      (Wff.classEq (syn_cin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))
        (syn_crn (Class.cv h))) :=
  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                                ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                  (nb090_alpha_dummy_004 v u A h))]
                              (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0031 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
          unfold nb090_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  1)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
          unfold nb090_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_337 A) from (by
          unfold
            nb090_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold
            nb090_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_367 A) from (by
          unfold
            nb090_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0370
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_368 h) from (by
          unfold
            nb090_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0371
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_341 A) from (by
          unfold
            nb090_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0367
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_342 h) from (by
          unfold
            nb090_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0369
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_334
        A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0032 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
          unfold nb090_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  1)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
          unfold nb090_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_337 A) from (by
          unfold
            nb090_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold
            nb090_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_367 A) from (by
          unfold
            nb090_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0370
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_368 h) from (by
          unfold
            nb090_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0371
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_341 A) from (by
          unfold
            nb090_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0367
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_342 h) from (by
          unfold
            nb090_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0369
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_334
        A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0032 v u A h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_334 A) from (by
                                    unfold nb090_alpha_dummy_334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0380 A)
                                            1)))) (show h ≠ (nb090_alpha_dummy_336 h) from (by
                                    unfold nb090_alpha_dummy_336;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0381 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_333 A) from
                                    (by
                                      unfold nb090_alpha_dummy_333;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0380 A)
                                              0)))) (show h ≠ (nb090_alpha_dummy_335 h) from (by
                                      unfold nb090_alpha_dummy_335;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0381 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_331 A) from
                                      (by
                                        unfold nb090_alpha_dummy_331;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0378 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_332 v h) from
                                      (by
                                        unfold nb090_alpha_dummy_332;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0379 v h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_329 A) from (by
                                          unfold nb090_alpha_dummy_329;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0376 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_330 v h) from (by
                                          unfold nb090_alpha_dummy_330;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0377 v h) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                              (freshVar_injective (((Class.cab (nb090_alpha_dummy_375 A)
                                    (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
                                        (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
        (Class.cv (nb090_alpha_dummy_373 A)))) (syn_csn
                                        (Class.cv (nb090_alpha_dummy_375 A)))))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
                                      (Class.cab (nb090_alpha_dummy_374 v)
                                        (syn_wbr (Class.cv v) (syn_c2nd)
        (Class.cv (nb090_alpha_dummy_374 v)))) (syn_csn
                                        (Class.cv (nb090_alpha_dummy_376 v)))))).fv)
                                (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
                                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0033 v u A h dv_h_v))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_373
        A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold
            nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold
            nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold
            nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold
            nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0034 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A),
        (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A),
        (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A),
        (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_373
        A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold
            nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold
            nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold
            nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold
            nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0034 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A),
        (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A),
        (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A),
        (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                      [((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                        ((nb090_alpha_dummy_331 A),
        (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c2nd) (nb090_wpp_refl_0124 v u A h))))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_375 A) ≠
        (nb090_alpha_dummy_417 A) from (by
          unfold nb090_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0430 A) 0)))) (show (nb090_alpha_dummy_376 v) ≠
        (nb090_alpha_dummy_418 v) from (by
          unfold nb090_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0431 v) 0)))) (TAlphaVar.here _ _ _))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                                ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                                ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)),
                                ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                                ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                  (nb090_alpha_dummy_004 v u A h))]
                              (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0031 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
          unfold nb090_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  1)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
          unfold nb090_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_337 A) from (by
          unfold
            nb090_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold
            nb090_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_367 A) from (by
          unfold
            nb090_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0370
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_368 h) from (by
          unfold
            nb090_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0371
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_341 A) from (by
          unfold
            nb090_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0367
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_342 h) from (by
          unfold
            nb090_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0369
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_334
        A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0032 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
          unfold nb090_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  1)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
          unfold nb090_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_337 A) from (by
          unfold
            nb090_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0366
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold
            nb090_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0368
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_367 A) from (by
          unfold
            nb090_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0370
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_368 h) from (by
          unfold
            nb090_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0371
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_333 A) ≠
        (nb090_alpha_dummy_341 A) from (by
          unfold
            nb090_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0367
                    A)
                  0)))) (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_342 h) from (by
          unfold
            nb090_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0369
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_334
        A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0032 v u A h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_334 A) from (by
                                    unfold nb090_alpha_dummy_334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0380 A)
                                            1)))) (show h ≠ (nb090_alpha_dummy_336 h) from (by
                                    unfold nb090_alpha_dummy_336;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0381 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_333 A) from
                                    (by
                                      unfold nb090_alpha_dummy_333;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0380 A)
                                              0)))) (show h ≠ (nb090_alpha_dummy_335 h) from (by
                                      unfold nb090_alpha_dummy_335;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0381 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_331 A) from
                                      (by
                                        unfold nb090_alpha_dummy_331;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0378 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_332 v h) from
                                      (by
                                        unfold nb090_alpha_dummy_332;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0379 v h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_329 A) from (by
                                          unfold nb090_alpha_dummy_329;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0376 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_330 v h) from (by
                                          unfold nb090_alpha_dummy_330;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0377 v h) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                              (freshVar_injective (((Class.cab (nb090_alpha_dummy_375 A)
                                    (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
                                        (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
        (Class.cv (nb090_alpha_dummy_373 A)))) (syn_csn
                                        (Class.cv (nb090_alpha_dummy_375 A)))))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
                                      (Class.cab (nb090_alpha_dummy_374 v)
                                        (syn_wbr (Class.cv v) (syn_c2nd)
        (Class.cv (nb090_alpha_dummy_374 v)))) (syn_csn
                                        (Class.cv (nb090_alpha_dummy_376 v)))))).fv)
                                (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
                                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0033 v u A h dv_h_v))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_373
        A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold
            nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold
            nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold
            nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold
            nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0034 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A),
        (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A),
        (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A),
        (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_373
        A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold
            nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold
            nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold
            nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold
            nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0034 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_413 A), (nb090_alpha_dummy_414 v)), ((nb090_alpha_dummy_382 A),
        (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)),
        ((nb090_alpha_dummy_411 A), (nb090_alpha_dummy_412 v)), ((nb090_alpha_dummy_385 A),
        (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A),
        (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
        ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A),
        (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                      [((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                                        ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                                        ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                                        ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                                        ((nb090_alpha_dummy_331 A),
        (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c2nd) (nb090_wpp_refl_0124 v u A h))))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_375 A) ≠
        (nb090_alpha_dummy_417 A) from (by
          unfold nb090_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0430 A) 0)))) (show (nb090_alpha_dummy_376 v) ≠
        (nb090_alpha_dummy_418 v) from (by
          unfold nb090_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0431 v) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                ((nb090_alpha_dummy_001 A), u),
                ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
              (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj (nb090_split_alpha_0035 v u A h)
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.neg (nb090_split_alpha_0036 v u A h)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.neg (nb090_split_alpha_0036 v u A h))))))))))))
            (TAlphaClass.cv (TAlphaVar.there
                (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_334 A) from (by
                    unfold nb090_alpha_dummy_334;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0380 A) 1))))
                (show h ≠ (nb090_alpha_dummy_336 h) from (by
                    unfold nb090_alpha_dummy_336;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0381 h) 1))))
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_333 A) from (by
                      unfold nb090_alpha_dummy_333;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0380 A) 0))))
                  (show h ≠ (nb090_alpha_dummy_335 h) from (by
                      unfold nb090_alpha_dummy_335;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0381 h) 0))))
                  (TAlphaVar.here _ _ _)))))))))

theorem nb090_compact_fv_empty_0340 (A : Class) :
    (nb090_alpha_dummy_421 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
