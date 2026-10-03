/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part028`. -/


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
noncomputable def nb077_split_alpha_0015 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_317 F I))
          (Class.cab (nb077_alpha_dummy_311 F I)
            (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_317 F I))
            (Class.cab (nb077_alpha_dummy_311 F I)
              (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_318 x))
          (Class.cab (nb077_alpha_dummy_313 x)
            (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_318 x))
            (Class.cab (nb077_alpha_dummy_313 x)
              (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
                      unfold nb077_alpha_dummy_312;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
                  (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_314 x) from (by
                      unfold nb077_alpha_dummy_314;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_311 F I) from (by
                        unfold nb077_alpha_dummy_311;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
                    (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_313 x) from (by
                        unfold nb077_alpha_dummy_313;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0310 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_317 F I) from (by
                          unfold nb077_alpha_dummy_317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0312 F I) 0))))
                      (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_318 x) from (by
                          unfold nb077_alpha_dummy_318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0313 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_315 F I) from (by
                            unfold nb077_alpha_dummy_315;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0309 F I) 0))))
                        (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_316 x) from (by
                            unfold nb077_alpha_dummy_316;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0311 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_319 F I) from
                            (by
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
                                    (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_320 F I) from (by
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_312 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_314 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_326 F I) from
        (by
          unfold nb077_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I) 1)))) (show (nb077_alpha_dummy_321 x) ≠
        (nb077_alpha_dummy_329 x) from (by
          unfold nb077_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_325 F I) from (by
          unfold nb077_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  0)))) (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_328 x) from (by
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
                  (nb077_support_mem_0316 F I)
                  0)))) (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
          unfold nb077_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_327 F I), (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I),
        (nb077_alpha_dummy_329 x)), ((nb077_alpha_dummy_325 F I), (nb077_alpha_dummy_328 x)),
        ((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I),
        (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_326
        F I) ≠ (nb077_alpha_dummy_337 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327
        F I) ≠ (nb077_alpha_dummy_339 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327
        F I) ≠ (nb077_alpha_dummy_339 F I) from (by
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
                                      (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                      (by
                                        unfold nb077_alpha_dummy_324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_323 F I),
                                      (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I),
                                      (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I),
                                      (nb077_alpha_dummy_322 x)), ((nb077_alpha_dummy_312 F I),
                                      (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
                                      (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I),
                                      (nb077_alpha_dummy_318 x)), ((nb077_alpha_dummy_315 F I),
                                      (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_323;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0316 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                    (by
                                      unfold nb077_alpha_dummy_324;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0317 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                      (by
                                        unfold nb077_alpha_dummy_324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_323 F I),
                                      (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I),
                                      (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I),
                                      (nb077_alpha_dummy_322 x)), ((nb077_alpha_dummy_312 F I),
                                      (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
                                      (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I),
                                      (nb077_alpha_dummy_318 x)), ((nb077_alpha_dummy_315 F I),
                                      (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
                        unfold nb077_alpha_dummy_312;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))))
                    (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_314 x) from (by
                        unfold nb077_alpha_dummy_314;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0310 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_311 F I) from (by
                          unfold nb077_alpha_dummy_311;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))))
                      (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_313 x) from (by
                          unfold nb077_alpha_dummy_313;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0310 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_317 F I) from (by
                            unfold nb077_alpha_dummy_317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0312 F I) 0))))
                        (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_318 x) from (by
                            unfold nb077_alpha_dummy_318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0313 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_315 F I) from
                            (by
                              unfold nb077_alpha_dummy_315;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0309 F I) 0))))
                          (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_316 x) from (by
                              unfold nb077_alpha_dummy_316;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0311 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_319 F I) from (by
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
                                      (mem_lt_freshVar (nb077_support_mem_0315 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_312 F I) ≠ (nb077_alpha_dummy_320 F I) from
                                (by
                                  unfold nb077_alpha_dummy_320;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0314 F I)
                                          1))))
                              (show (nb077_alpha_dummy_314 x) ≠ (nb077_alpha_dummy_322 x) from
                                (by
                                  unfold nb077_alpha_dummy_322;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0315 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_312 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_314 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_326 F I) from (by
          unfold nb077_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  1)))) (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_329 x) from (by
          unfold nb077_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_325 F I) from (by
          unfold nb077_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0318 F I)
                  0)))) (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_328 x) from (by
          unfold nb077_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0319 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_323 F I) from (by
          unfold nb077_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0316 F I)
                  0)))) (show (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from (by
          unfold nb077_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0317 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_327 F I), (nb077_alpha_dummy_330 x)), ((nb077_alpha_dummy_326 F I),
        (nb077_alpha_dummy_329 x)), ((nb077_alpha_dummy_325 F I), (nb077_alpha_dummy_328 x)),
        ((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)), ((nb077_alpha_dummy_319 F I),
        (nb077_alpha_dummy_321 x)), ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I),
        (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
        ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_321
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_326
        F I) ≠ (nb077_alpha_dummy_337 F I) from (by
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
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327
        F I) ≠ (nb077_alpha_dummy_339 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_327
        F I) ≠ (nb077_alpha_dummy_339 F I) from (by
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
                                        (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_323 F I) from (by
                                          unfold nb077_alpha_dummy_323;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0316 F I) 0)))) (show
                                        (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x)
                                        from (by
                                          unfold nb077_alpha_dummy_324;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0317 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                                      ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                                      ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                                      ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                                      ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                                      ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
                                      ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_323 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_323;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0316 F I) 0)))) (show
                                      (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x) from
                                      (by
                                        unfold nb077_alpha_dummy_324;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0317 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_319 F I) ≠
        (nb077_alpha_dummy_323 F I) from (by
                                          unfold nb077_alpha_dummy_323;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0316 F I) 0)))) (show
                                        (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_324 x)
                                        from (by
                                          unfold nb077_alpha_dummy_324;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0317 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_323 F I), (nb077_alpha_dummy_324 x)),
                                      ((nb077_alpha_dummy_319 F I), (nb077_alpha_dummy_321 x)),
                                      ((nb077_alpha_dummy_320 F I), (nb077_alpha_dummy_322 x)),
                                      ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
                                      ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
                                      ((nb077_alpha_dummy_317 F I), (nb077_alpha_dummy_318 x)),
                                      ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part029`. -/


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
noncomputable def nb077_split_alpha_0016 (x : Var) (F : Class) (I : Class) :
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I),
        (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I),
        (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I),
        (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I),
        (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
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
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_wpp_notmem_0912 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0913 (x : Var) :
    (nb077_alpha_dummy_064 x) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0101 x)

theorem nb077_wpp_notmem_0914 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_060, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0064 F I)

theorem nb077_wpp_notmem_0915 (x : Var) :
    (nb077_alpha_dummy_063 x) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_063, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0065 x)

theorem nb077_wpp_notmem_0916 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_059, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0066 F I)

theorem nb077_wpp_notmem_0917 (x : Var) :
    (nb077_alpha_dummy_062 x) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_062, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0067 x)

theorem nb077_wpp_notmem_0918 (F : Class) (I : Class) :
    (nb077_alpha_dummy_065 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_065, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0068 F I)

theorem nb077_wpp_notmem_0919 (x : Var) :
    (nb077_alpha_dummy_066 x) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_066, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0069 x)

theorem nb077_wpp_notmem_0920 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_057, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0070 F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part030`. -/


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

theorem nb077_wpp_notmem_0921 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_058, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0071 x F)

theorem nb077_wpp_notmem_0922 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_055, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0072 F I)

theorem nb077_wpp_notmem_0923 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_056, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0073 x F)

theorem nb077_wpp_notmem_0924 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_016, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0030 F I)

theorem nb077_wpp_notmem_0925 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_018, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0031 x F I)

theorem nb077_wpp_notmem_0926 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_015, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0032 F I)

theorem nb077_wpp_notmem_0927 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_017, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0033 x F I)

theorem nb077_wpp_notmem_0928 (F : Class) (I : Class) :
    (nb077_alpha_dummy_013 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_013, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0034 F I)

theorem nb077_wpp_notmem_0929 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_014 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_014, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0035 x F I)

theorem nb077_wpp_notmem_0930 (F : Class) (I : Class) :
    (nb077_alpha_dummy_011 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_011, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0036 F I)

theorem nb077_wpp_notmem_0931 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_012 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_012, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0932 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0933 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0934 (F : Class) (I : Class) :
    (nb077_alpha_dummy_004 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0935 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_006 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0936 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0937 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ∉ ((syn_ccnv (syn_c1st))).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_ccnv, fv_syn_c1st] using
    (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0062 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
                    (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I)
                      (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0928 F I)
                      (nb077_wpp_notmem_0929 x F I)
                      (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I)
                        (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0930 F I)
                        (nb077_wpp_notmem_0931 x F I)
                        (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I)
                          (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0932 F I)
                          (nb077_wpp_notmem_0933 x F I)
                          (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I)
                            (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0934 F I)
                            (nb077_wpp_notmem_0935 x F I)
                            (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I)
                              (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0936 F I)
                              (nb077_wpp_notmem_0937 x F I)
                              (TEnvFresh.nil ((syn_ccnv (syn_c1st))).fv))))))))))))))

@[expose]
noncomputable def nb077_wpp_refl_0062 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccnv (syn_c1st))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0062 x F I)

theorem nb077_focused_notmem_0010 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                (syn_c1st)))).fv ∪
          ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (syn_c2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0938 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_057, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0070 F I)
      (And.intro (nb077_focused_notmem_0010 F I) (nb077_compact_fv_empty_0070 F I)))

theorem nb077_focused_notmem_0011 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                (syn_c1st)))).fv ∪
          ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (syn_c2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0939 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_058, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0071 x F)
      (And.intro (nb077_focused_notmem_0011 x F) (nb077_compact_fv_empty_0071 x F)))

theorem nb077_focused_notmem_0012 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
              (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (syn_c2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0940 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_055, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0072 F I)
      (And.intro (nb077_focused_notmem_0012 F I) (nb077_compact_fv_empty_0072 F I)))

theorem nb077_focused_notmem_0013 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin
              (syn_ccom (syn_ccnv (syn_c1st))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_ccom (syn_ccnv (syn_c1st))
        (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_ccom F (syn_c2nd)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb077_wpp_notmem_0941 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_056, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0073 x F)
      (And.intro (nb077_focused_notmem_0013 x F) (nb077_compact_fv_empty_0073 x F)))

theorem nb077_focused_notmem_0014 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
          ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0942 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_016, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0030 F I)
      (And.intro (nb077_focused_notmem_0014 F I) (nb077_compact_fv_empty_0030 F I)))

theorem nb077_focused_notmem_0015 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
          ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0943 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_018, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0031 x F I)
      (And.intro (nb077_focused_notmem_0015 x F I) (nb077_compact_fv_empty_0031 x F I)))

theorem nb077_focused_notmem_0016 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪
          ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0944 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_015, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0032 F I)
      (And.intro (nb077_focused_notmem_0016 F I) (nb077_compact_fv_empty_0032 F I)))

theorem nb077_focused_notmem_0017 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪
          ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0945 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_017, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0033 x F I)
      (And.intro (nb077_focused_notmem_0017 x F I) (nb077_compact_fv_empty_0033 x F I)))

theorem nb077_focused_notmem_0018 (F : Class) (I : Class) :
    (nb077_alpha_dummy_013 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪
          ((Class.cv (nb077_alpha_dummy_001 F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima
      (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
      (Class.cv (nb077_alpha_dummy_001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0946 (F : Class) (I : Class) :
    (nb077_alpha_dummy_013 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_013, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0034 F I)
      (And.intro (nb077_focused_notmem_0018 F I) (nb077_compact_fv_empty_0034 F I)))

theorem nb077_focused_notmem_0019 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_014 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
              (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪
          ((Class.cv (nb077_alpha_dummy_002 x F I))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
      (Class.cv (nb077_alpha_dummy_002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0947 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_014 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_014, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0035 x F I)
      (And.intro (nb077_focused_notmem_0019 x F I) (nb077_compact_fv_empty_0035 x F I)))

theorem nb077_focused_notmem_0020 (F : Class) (I : Class) :
    (nb077_alpha_dummy_011 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_001 F I)))
              (Class.cv (nb077_alpha_dummy_001 F I)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_001 F I)))
      (Class.cv (nb077_alpha_dummy_001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima
      (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
      (Class.cv (nb077_alpha_dummy_001 F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod
      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0948 (F : Class) (I : Class) :
    (nb077_alpha_dummy_011 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_011, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0036 F I)
      (And.intro (nb077_focused_notmem_0020 F I) (nb077_compact_fv_empty_0036 F I)))

theorem nb077_focused_notmem_0021 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_012 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                (Class.cv (nb077_alpha_dummy_002 x F I)))
              (Class.cv (nb077_alpha_dummy_002 x F I)))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_002 x F I)))
      (Class.cv (nb077_alpha_dummy_002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
      (Class.cv (nb077_alpha_dummy_002 x F I))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0949 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_012 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_012, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0037 x F I)
      (And.intro (nb077_focused_notmem_0021 x F I) (nb077_compact_fv_empty_0037 x F I)))

theorem nb077_focused_notmem_0022 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpprod
      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
      F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0950 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_001, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0004 F I)
      (And.intro (nb077_focused_notmem_0022 F I) (nb077_compact_fv_empty_0004 F I)))

theorem nb077_focused_notmem_0023 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((syn_csn (syn_cop (syn_c0c) I))).fv ∪
          ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb077_wpp_notmem_0951 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_002, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0005 x F I)
      (And.intro (nb077_focused_notmem_0023 x F I) (nb077_compact_fv_empty_0005 x F I)))

theorem nb077_focused_notmem_0024 (F : Class) (I : Class) :
    (nb077_alpha_dummy_004 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
              (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
              (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                  (Class.cv (nb077_alpha_dummy_001 F I)))
                (Class.cv (nb077_alpha_dummy_001 F I)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077_alpha_dummy_001 F I)
      (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
        (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0022 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
        (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_001 F I)))
        (Class.cv (nb077_alpha_dummy_001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod
        (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
        F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0952 (F : Class) (I : Class) :
    (nb077_alpha_dummy_004 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_004, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0006 F I)
      (And.intro (nb077_focused_notmem_0024 F I) (nb077_compact_fv_empty_0006 F I)))

theorem nb077_focused_notmem_0025 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_006 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
              (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
              (syn_wss (syn_cima
                  (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                  (Class.cv (nb077_alpha_dummy_002 x F I)))
                (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb077_alpha_dummy_002 x F I)
      (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
        (syn_wss (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))
          (Class.cv (nb077_alpha_dummy_002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0023 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
        (syn_wss (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_002 x F I)))
        (Class.cv (nb077_alpha_dummy_002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0953 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_006 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_006, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0007 x F I)
      (And.intro (nb077_focused_notmem_0025 x F I) (nb077_compact_fv_empty_0007 x F I)))

theorem nb077_focused_notmem_0026 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
              (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
              (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                  (Class.cv (nb077_alpha_dummy_001 F I)))
                (Class.cv (nb077_alpha_dummy_001 F I)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077_alpha_dummy_001 F I)
      (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
        (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0022 F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))
        (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
              (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_001 F I)))
        (Class.cv (nb077_alpha_dummy_001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
            (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_001 F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod
        (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
          (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
        F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0954 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_003, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0008 F I)
      (And.intro (nb077_focused_notmem_0026 F I) (nb077_compact_fv_empty_0008 F I)))

theorem nb077_focused_notmem_0027 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
              (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
              (syn_wss (syn_cima
                  (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                  (Class.cv (nb077_alpha_dummy_002 x F I)))
                (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb077_alpha_dummy_002 x F I)
      (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
        (syn_wss (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I)))
          (Class.cv (nb077_alpha_dummy_002 x F I))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb077_focused_notmem_0023 x F I)) (h_eq ▸ hu)
  · rw [fv_syn_wa
        (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))
        (syn_wss (syn_cima
            (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
            (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))]
    rw [Finset.mem_union]
    right
    rw [fv_syn_wss
        (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
          (Class.cv (nb077_alpha_dummy_002 x F I)))
        (Class.cv (nb077_alpha_dummy_002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cima
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
        (Class.cv (nb077_alpha_dummy_002 x F I))]
    rw [Finset.mem_union]
    left
    rw [fv_syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F]
    rw [Finset.mem_union]
    right
    exact hu

theorem nb077_wpp_notmem_0955 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ∉
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  by
  simpa only [nb077_alpha_dummy_005, fv_syn_ccom, Finset.mem_union, fv_syn_ccnv,
    fv_syn_c2nd, not_or] using
    (And.intro (nb077_compact_fv_empty_0009 x F I)
      (And.intro (nb077_focused_notmem_0027 x F I) (nb077_compact_fv_empty_0009 x F I)))

theorem nb077_compact_envfresh_0063 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
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
            (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I)
              (nb077_wpp_notmem_0946 F I) (nb077_wpp_notmem_0947 x F I)
              (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I)
                (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0948 F I)
                (nb077_wpp_notmem_0949 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I)
                  (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0950 F I)
                  (nb077_wpp_notmem_0951 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I)
                    (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0952 F I)
                    (nb077_wpp_notmem_0953 x F I)
                    (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I)
                      (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0954 F I)
                      (nb077_wpp_notmem_0955 x F I) (TEnvFresh.nil
                        ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv))))))))))

@[expose]
noncomputable def nb077_wpp_refl_0063 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0063 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
