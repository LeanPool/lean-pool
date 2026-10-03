/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block016

/-! NF weak partition development: NAR4C077C001Part048. -/


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
noncomputable def nb077_split_alpha_0034 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)),
        ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
        ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_345 F I))
          (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_345 F I))
            (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_346 x))
          (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_346 x))
            (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_319 F I) from (by
                      unfold nb077_alpha_dummy_319;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0314 F I) 0))))
                  (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_321 x) from (by
                      unfold nb077_alpha_dummy_321;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_320 F I) from (by
                        unfold nb077_alpha_dummy_320;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0314 F I) 1))))
                    (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_322 x) from (by
                        unfold nb077_alpha_dummy_322;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0315 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_345 F I) from (by
                          unfold nb077_alpha_dummy_345;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0344 F I) 0))))
                      (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_346 x) from (by
                          unfold nb077_alpha_dummy_346;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0345 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_343 F I) from (by
                            unfold nb077_alpha_dummy_343;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0342 F I) 0))))
                        (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_344 x) from (by
                            unfold nb077_alpha_dummy_344;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0343 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_312 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_314 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_326 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_326;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0318 F I) 1)))) (show
                                      (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_329 x) from
                                      (by
                                        unfold nb077_alpha_dummy_329;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0319 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_325 F I) from (by
                                          unfold nb077_alpha_dummy_325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0318 F I) 0)))) (show
                                        (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_328 x)
                                        from (by
                                          unfold nb077_alpha_dummy_328;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0319 x) 0))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_323 F I) from (by
          unfold nb077_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I) 0)))) (show (nb077_alpha_dummy_321 x) ≠
        (nb077_alpha_dummy_324 x) from (by
          unfold nb077_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_327 F I),
        (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I), (nb077_alpha_dummy_329 x)),
                                        ((nb077_alpha_dummy_325 F I),
        (nb077_alpha_dummy_328 x)), ((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                                        ((nb077_alpha_dummy_319 F I),
        (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                                        ((nb077_alpha_dummy_345 F I),
        (nb077_alpha_dummy_346 x)), ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
                                        ((nb077_alpha_dummy_312 F I),
        (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                                        ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                                        ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                        ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                        ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_333 F I) from (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_333 F I) from (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_333 F I) from
        (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_333 F I) from (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb077_alpha_dummy_327 F I),
        (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I), (nb077_alpha_dummy_329 x)),
        ((nb077_alpha_dummy_325 F I), (nb077_alpha_dummy_328 x)), ((nb077_alpha_dummy_323 F I),
        (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
        ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)), ((nb077_alpha_dummy_345 F I),
        (nb077_alpha_dummy_346 x)), ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_337 F I) from (by
          unfold
            nb077_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_338 x) from (by
          unfold
            nb077_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_337 F I) from (by
          unfold
            nb077_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_338 x) from (by
          unfold
            nb077_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_327 F I) ≠ (nb077_alpha_dummy_339 F I) from (by
          unfold
            nb077_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_340 x) from (by
          unfold
            nb077_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_327 F I) ≠ (nb077_alpha_dummy_339 F I) from (by
          unfold
            nb077_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_340 x) from (by
          unfold
            nb077_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from (by
                                unfold nb077_alpha_dummy_323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
                                unfold nb077_alpha_dummy_324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                            ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                            ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                            ((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)),
                            ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
                            ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                            ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                            ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
                            ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from
                            (by
                              unfold nb077_alpha_dummy_323;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                          (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
                              unfold nb077_alpha_dummy_324;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from (by
                                unfold nb077_alpha_dummy_323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
                                unfold nb077_alpha_dummy_324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                            ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                            ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                            ((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)),
                            ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
                            ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                            ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                            ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
                            ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_319 F I) from (by
                        unfold nb077_alpha_dummy_319;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0314 F I) 0))))
                    (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_321 x) from (by
                        unfold nb077_alpha_dummy_321;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0315 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_320 F I) from (by
                          unfold nb077_alpha_dummy_320;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0314 F I) 1))))
                      (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_322 x) from (by
                          unfold nb077_alpha_dummy_322;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0315 x) 1))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_345 F I) from (by
                            unfold nb077_alpha_dummy_345;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0344 F I) 0))))
                        (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_346 x) from (by
                            unfold nb077_alpha_dummy_346;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0345 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_343 F I) from
                            (by
                              unfold nb077_alpha_dummy_343;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0342 F I) 0))))
                          (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_344 x) from (by
                              unfold nb077_alpha_dummy_344;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0343 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_312 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_314 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_326 F I) from (by
                                          unfold nb077_alpha_dummy_326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0318 F I) 1)))) (show
                                        (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_329 x)
                                        from (by
                                          unfold nb077_alpha_dummy_329;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0319 x) 1))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_325 F I) from (by
          unfold nb077_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I) 0)))) (show (nb077_alpha_dummy_321 x) ≠
        (nb077_alpha_dummy_328 x) from (by
          unfold nb077_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from (by
          unfold nb077_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I) 0)))) (show (nb077_alpha_dummy_321 x) ≠
        (nb077_alpha_dummy_324 x) from (by
          unfold nb077_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_327 F I),
        (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I), (nb077_alpha_dummy_329 x)),
        ((nb077_alpha_dummy_325 F I), (nb077_alpha_dummy_328 x)), ((nb077_alpha_dummy_323 F I),
        (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
        ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)), ((nb077_alpha_dummy_345 F I),
        (nb077_alpha_dummy_346 x)), ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_326 F
        I) ≠ (nb077_alpha_dummy_333 F I) from (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠ (nb077_alpha_dummy_333 F I) from
        (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_333 F I) from
        (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0322
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0323
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0320
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0321
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠ (nb077_alpha_dummy_333 F I) from
        (by
          unfold
            nb077_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0326
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_334 x) from (by
          unfold
            nb077_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0327
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_331 F I) from (by
          unfold
            nb077_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0324
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_332 x) from (by
          unfold
            nb077_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0325
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_327 F I), (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I),
        (nb077_alpha_dummy_329 x)), ((nb077_alpha_dummy_325 F I), (nb077_alpha_dummy_328 x)),
        ((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I),
        (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
        ((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)), ((nb077_alpha_dummy_343 F I),
        (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_326 F
        I) ≠ (nb077_alpha_dummy_337 F I) from (by
          unfold
            nb077_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_338 x) from (by
          unfold
            nb077_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_337 F I) from
        (by
          unfold
            nb077_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0330
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_338 x) from (by
          unfold
            nb077_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0331
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_326 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0328
                    F I)
                  0)))) (show (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0329
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327 F
        I) ≠ (nb077_alpha_dummy_339 F I) from (by
          unfold
            nb077_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_340 x) from (by
          unfold
            nb077_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327 F
        I) ≠ (nb077_alpha_dummy_339 F I) from (by
          unfold
            nb077_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0334
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_340 x) from (by
          unfold
            nb077_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0335
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_327 F I) ≠
        (nb077_alpha_dummy_335 F I) from (by
          unfold
            nb077_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0332
                    F I)
                  0)))) (show (nb077_alpha_dummy_330 x) ≠ (nb077_alpha_dummy_336 x) from (by
          unfold
            nb077_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0333
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from
                                (by
                                  unfold nb077_alpha_dummy_323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                          0))))
                              (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                (by
                                  unfold nb077_alpha_dummy_324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                              ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                              ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                              ((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)),
                              ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
                              ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                              ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                              ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
                              ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from (by
                                unfold nb077_alpha_dummy_323;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0316 F I) 0))))
                            (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
                                unfold nb077_alpha_dummy_324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I) from
                                (by
                                  unfold nb077_alpha_dummy_323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                          0))))
                              (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                (by
                                  unfold nb077_alpha_dummy_324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0317 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                              ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                              ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                              ((nb077_alpha_dummy_345 F I), (nb077_alpha_dummy_346 x)),
                              ((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)),
                              ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                              ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                              ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)),
                              ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_compact_envfresh_0124 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccnv (syn_c1st))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x)
      (nb077_wpp_notmem_0912 F I) (nb077_wpp_notmem_0913 x)
      (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x)
        (nb077_wpp_notmem_0914 F I) (nb077_wpp_notmem_0915 x)
        (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x)
          (nb077_wpp_notmem_0916 F I) (nb077_wpp_notmem_0917 x)
          (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x)
            (nb077_wpp_notmem_0918 F I) (nb077_wpp_notmem_0919 x)
            (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F)
              (nb077_wpp_notmem_0920 F I) (nb077_wpp_notmem_0921 x F)
              (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F)
                (nb077_wpp_notmem_0922 F I) (nb077_wpp_notmem_0923 x F)
                (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I)
                  (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0924 F I)
                  (nb077_wpp_notmem_0925 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I)
                    (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0926 F I)
                    (nb077_wpp_notmem_0927 x F I)
                    (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I)
                      (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0932 F I)
                      (nb077_wpp_notmem_0933 x F I)
                      (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I)
                        (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0934 F I)
                        (nb077_wpp_notmem_0935 x F I)
                        (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I)
                          (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0936 F I)
                          (nb077_wpp_notmem_0937 x F I)
                          (TEnvFresh.nil ((syn_ccnv (syn_c1st))).fv))))))))))))

@[expose]
noncomputable def nb077_wpp_refl_0124 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccnv (syn_c1st))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0124 x F I)

theorem nb077_compact_envfresh_0125 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F)
      (nb077_wpp_notmem_0938 F I) (nb077_wpp_notmem_0939 x F)
      (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F)
        (nb077_wpp_notmem_0940 F I) (nb077_wpp_notmem_0941 x F)
        (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I)
          (nb077_wpp_notmem_0942 F I) (nb077_wpp_notmem_0943 x F I)
          (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I)
            (nb077_wpp_notmem_0944 F I) (nb077_wpp_notmem_0945 x F I)
            (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I)
              (nb077_wpp_notmem_0950 F I) (nb077_wpp_notmem_0951 x F I)
              (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I)
                (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0952 F I)
                (nb077_wpp_notmem_0953 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I)
                  (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0954 F I)
                  (nb077_wpp_notmem_0955 x F I) (TEnvFresh.nil
                    ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv))))))))

@[expose]
noncomputable def nb077_wpp_refl_0125 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0125 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
