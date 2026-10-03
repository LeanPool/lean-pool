/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block018

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part063`. -/


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
noncomputable def nb078_split_alpha_0033 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)),
        ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
        ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
        ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_363))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_364 g))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_339) from (by
                            unfold nb078_alpha_dummy_339;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                        (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_341 g) from (by
                            unfold nb078_alpha_dummy_341;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_340) from (by
                              unfold nb078_alpha_dummy_340;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                          (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_342 g) from (by
                              unfold nb078_alpha_dummy_342;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_365) from (by
                                unfold nb078_alpha_dummy_365;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0368) 0))))
                            (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_366 g) from (by
                                unfold nb078_alpha_dummy_366;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0369 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_363) from (by
                                  unfold nb078_alpha_dummy_363;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0366) 0))))
                              (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_364 g) from
                                (by
                                  unfold nb078_alpha_dummy_364;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0367 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_339) ≠
        (nb078_alpha_dummy_346) from (by
          unfold nb078_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_349 g) from (by
          unfold nb078_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_345) from (by
          unfold nb078_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_348 g) from (by
          unfold nb078_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
          unfold nb078_alpha_dummy_343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340) 0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_344 g) from (by
          unfold nb078_alpha_dummy_344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363),
        (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
        ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361),
        (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_353) from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_353)
        from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_353) from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_353)
        from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363),
        (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
        ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361),
        (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_357) from (by
          unfold
            nb078_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_358 g) from (by
          unfold
            nb078_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_357)
        from (by
          unfold
            nb078_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_358 g) from (by
          unfold
            nb078_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_359) from (by
          unfold
            nb078_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_360 g) from (by
          unfold
            nb078_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠
        (nb078_alpha_dummy_359) from (by
          unfold
            nb078_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_360 g) from (by
          unfold
            nb078_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                    (by
                                      unfold nb078_alpha_dummy_343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0340)
                                              0)))) (show
                                    (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from
                                    (by
                                      unfold nb078_alpha_dummy_344;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0341 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                  ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                  ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                  ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)),
                                  ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)),
                                  ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                  ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                  ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)),
                                  ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                  ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                  ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                  ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                  ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
                                    unfold nb078_alpha_dummy_343;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0340) 0)))) (show
                                  (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from (by
                                    unfold nb078_alpha_dummy_344;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0341 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                    (by
                                      unfold nb078_alpha_dummy_343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0340)
                                              0)))) (show
                                    (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from
                                    (by
                                      unfold nb078_alpha_dummy_344;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0341 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                  ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                  ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                  ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)),
                                  ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)),
                                  ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                  ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                  ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)),
                                  ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                  ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                  ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                  ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                  ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_339) from (by
                            unfold nb078_alpha_dummy_339;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                        (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_341 g) from (by
                            unfold nb078_alpha_dummy_341;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_340) from (by
                              unfold nb078_alpha_dummy_340;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                          (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_342 g) from (by
                              unfold nb078_alpha_dummy_342;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_365) from (by
                                unfold nb078_alpha_dummy_365;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0368) 0))))
                            (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_366 g) from (by
                                unfold nb078_alpha_dummy_366;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0369 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_332) ≠ (nb078_alpha_dummy_363) from (by
                                  unfold nb078_alpha_dummy_363;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0366) 0))))
                              (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_364 g) from
                                (by
                                  unfold nb078_alpha_dummy_364;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0367 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_339) ≠
        (nb078_alpha_dummy_346) from (by
          unfold nb078_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_349 g) from (by
          unfold nb078_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_345) from (by
          unfold nb078_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_348 g) from (by
          unfold nb078_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
          unfold nb078_alpha_dummy_343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340) 0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_344 g) from (by
          unfold nb078_alpha_dummy_344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363),
        (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
        ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361),
        (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_353) from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_353)
        from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_353) from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_353)
        from (by
          unfold
            nb078_alpha_dummy_353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_354 g) from (by
          unfold
            nb078_alpha_dummy_354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_351)
        from (by
          unfold
            nb078_alpha_dummy_351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_352 g) from (by
          unfold
            nb078_alpha_dummy_352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363),
        (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
        ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361),
        (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_357) from (by
          unfold
            nb078_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_358 g) from (by
          unfold
            nb078_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_357)
        from (by
          unfold
            nb078_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_358 g) from (by
          unfold
            nb078_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_359) from (by
          unfold
            nb078_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_360 g) from (by
          unfold
            nb078_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠
        (nb078_alpha_dummy_359) from (by
          unfold
            nb078_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_360 g) from (by
          unfold
            nb078_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_347) ≠ (nb078_alpha_dummy_355)
        from (by
          unfold
            nb078_alpha_dummy_355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078_alpha_dummy_350 g) ≠ (nb078_alpha_dummy_356 g) from (by
          unfold
            nb078_alpha_dummy_356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                    (by
                                      unfold nb078_alpha_dummy_343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0340)
                                              0)))) (show
                                    (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from
                                    (by
                                      unfold nb078_alpha_dummy_344;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0341 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                  ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                  ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                  ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)),
                                  ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)),
                                  ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                  ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                  ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)),
                                  ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                  ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                  ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                  ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                  ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
                                    unfold nb078_alpha_dummy_343;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0340) 0)))) (show
                                  (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from (by
                                    unfold nb078_alpha_dummy_344;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0341 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                    (by
                                      unfold nb078_alpha_dummy_343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0340)
                                              0)))) (show
                                    (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from
                                    (by
                                      unfold nb078_alpha_dummy_344;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0341 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                  ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                  ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                  ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)),
                                  ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)),
                                  ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                  ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                  ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)),
                                  ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                  ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                  ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                  ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                  ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part064`. -/


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
noncomputable def nb078_split_alpha_0034 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_379))
          (Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_379)) (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
          (Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                    (by
                      unfold nb078_alpha_dummy_374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                      unfold nb078_alpha_dummy_376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from
                      (by
                        unfold nb078_alpha_dummy_373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                        unfold nb078_alpha_dummy_375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                          unfold nb078_alpha_dummy_379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                          unfold nb078_alpha_dummy_380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                            unfold nb078_alpha_dummy_377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                            unfold nb078_alpha_dummy_378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                              unfold nb078_alpha_dummy_381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                              unfold nb078_alpha_dummy_383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                unfold nb078_alpha_dummy_382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                                unfold nb078_alpha_dummy_384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                    ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                    (by
                                      unfold nb078_alpha_dummy_385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                    (by
                                      unfold nb078_alpha_dummy_386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                    ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                      (by
                        unfold nb078_alpha_dummy_374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                        unfold nb078_alpha_dummy_376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from (by
                          unfold nb078_alpha_dummy_373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                          unfold nb078_alpha_dummy_375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                            unfold nb078_alpha_dummy_379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                            unfold nb078_alpha_dummy_380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                              unfold nb078_alpha_dummy_377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                              unfold nb078_alpha_dummy_378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                                unfold nb078_alpha_dummy_381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                                unfold nb078_alpha_dummy_383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                  unfold nb078_alpha_dummy_382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from
                                (by
                                  unfold nb078_alpha_dummy_384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385)
        from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part065`. -/


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
noncomputable def nb078_split_alpha_0035 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_407))
          (syn_cphi (Class.cv (nb078_alpha_dummy_374)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_407))
            (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_408 g))
          (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_408 g))
            (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from
                    (by
                      unfold nb078_alpha_dummy_381;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                  (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                      unfold nb078_alpha_dummy_383;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from
                      (by
                        unfold nb078_alpha_dummy_382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                    (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                        unfold nb078_alpha_dummy_384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_407) from (by
                          unfold nb078_alpha_dummy_407;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                      (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_408 g) from (by
                          unfold nb078_alpha_dummy_408;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_405) from (by
                            unfold nb078_alpha_dummy_405;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                        (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_406 g) from (by
                            unfold nb078_alpha_dummy_406;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
                                        unfold nb078_alpha_dummy_388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0384)
                                                1)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_391 g) from (by
                                        unfold nb078_alpha_dummy_391;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0385 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from
                                        (by
                                          unfold nb078_alpha_dummy_387;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
                                          unfold nb078_alpha_dummy_390;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠
        (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_389),
        (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)),
                                        ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
                                        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                        ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                        ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                        ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                                        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                                        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                                        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                        ((nb078_alpha_dummy_001), g),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)),
        ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387),
        (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
        ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382),
        (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                            ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                            ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                            ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                            ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                            ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                            ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                            ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                            ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                            ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                            ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                            ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                            ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                            ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                            ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                            ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                            ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                            ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                              unfold nb078_alpha_dummy_385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                          (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                              unfold nb078_alpha_dummy_386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                            ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                            ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                            ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                            ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                            ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                            ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                            ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                            ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                            ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                            ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                            ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                            ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                            ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                            ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                            ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                            ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                            ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                        unfold nb078_alpha_dummy_381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                    (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                        unfold nb078_alpha_dummy_383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                          unfold nb078_alpha_dummy_382;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                      (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                          unfold nb078_alpha_dummy_384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_407) from (by
                            unfold nb078_alpha_dummy_407;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                        (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_408 g) from (by
                            unfold nb078_alpha_dummy_408;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_405) from (by
                              unfold nb078_alpha_dummy_405;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                          (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_406 g) from (by
                              unfold nb078_alpha_dummy_406;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from
                                        (by
                                          unfold nb078_alpha_dummy_388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
                                          unfold nb078_alpha_dummy_391;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠
        (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_389),
        (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)),
        ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385),
        (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
        ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_407),
        (nb078_alpha_dummy_408 g)), ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)), ((nb078_alpha_dummy_405),
        (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_403),
        (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367),
        (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                  unfold nb078_alpha_dummy_385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                (by
                                  unfold nb078_alpha_dummy_386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                              ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                              ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                              ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                              ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                              ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                              ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                              ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                              ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                              ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                              ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                              ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                              ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                              ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                              ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                              ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                              ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                              ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                  unfold nb078_alpha_dummy_385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                (by
                                  unfold nb078_alpha_dummy_386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                              ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                              ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                              ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                              ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                              ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                              ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                              ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                              ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                              ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                              ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                              ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                              ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                              ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                              ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                              ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                              ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                              ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
