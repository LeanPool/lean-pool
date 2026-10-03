/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part019Stage1


/-! NF weak partition development: NAR4H5C095M3Part019. -/


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
noncomputable def nb095_split_alpha_0030 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_305 D R S_cls E), (nb095_alpha_dummy_306 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_305 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_305 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_299 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_300 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_296 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_299 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_306 f))
          (Class.cab (nb095_alpha_dummy_301 f)
            (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_306 f))
            (Class.cab (nb095_alpha_dummy_301 f)
              (syn_wrex (nb095_alpha_dummy_302 f) (Class.cv (nb095_alpha_dummy_298 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_301 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_302 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                      (nb095_alpha_dummy_300 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_300;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_302 f) from (by
                      unfold nb095_alpha_dummy_302;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0298 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                        (nb095_alpha_dummy_299 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_301 f) from (by
                        unfold nb095_alpha_dummy_301;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0298 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                          (nb095_alpha_dummy_305 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_305;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0300 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_306 f) from (by
                          unfold nb095_alpha_dummy_306;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0301 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                            (nb095_alpha_dummy_303 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_303;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0297 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_304 f) from (by
                            unfold nb095_alpha_dummy_304;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0299 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_297 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                              (nb095_alpha_dummy_307 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_307;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0302 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_309 f) from (by
                              unfold nb095_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                (nb095_alpha_dummy_308 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_310 f) from (by
                                unfold nb095_alpha_dummy_310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_302 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_314 D R S_cls E) from (by
          unfold nb095_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_317 f) from (by
          unfold nb095_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_313 D R S_cls E) from (by
          unfold nb095_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_316 f) from (by
          unfold nb095_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_311 D R S_cls E) from (by
          unfold nb095_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from (by
          unfold nb095_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_305 D R S_cls E), (nb095_alpha_dummy_306 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_314
        D R S_cls E) ≠ (nb095_alpha_dummy_321 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_305 D R S_cls E), (nb095_alpha_dummy_306 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_307 D R S_cls E) ≠
                                        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                      (by
                                        unfold nb095_alpha_dummy_312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_311 D R S_cls E),
                                      (nb095_alpha_dummy_312 f)),
                                    ((nb095_alpha_dummy_307 D R S_cls E),
                                      (nb095_alpha_dummy_309 f)),
                                    ((nb095_alpha_dummy_308 D R S_cls E),
                                      (nb095_alpha_dummy_310 f)),
                                    ((nb095_alpha_dummy_300 D R S_cls E),
                                      (nb095_alpha_dummy_302 f)),
                                    ((nb095_alpha_dummy_299 D R S_cls E),
                                      (nb095_alpha_dummy_301 f)),
                                    ((nb095_alpha_dummy_305 D R S_cls E),
                                      (nb095_alpha_dummy_306 f)),
                                    ((nb095_alpha_dummy_303 D R S_cls E),
                                      (nb095_alpha_dummy_304 f)),
                                    ((nb095_alpha_dummy_296 D R S_cls E),
                                      (nb095_alpha_dummy_298 f)),
                                    ((nb095_alpha_dummy_295 D R S_cls E),
                                      (nb095_alpha_dummy_297 f)),
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
                                    (nb095_alpha_dummy_307 D R S_cls E) ≠
                                      (nb095_alpha_dummy_311 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_311;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                    (by
                                      unfold nb095_alpha_dummy_312;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0305 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_307 D R S_cls E) ≠
                                        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                      (by
                                        unfold nb095_alpha_dummy_312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_311 D R S_cls E),
                                      (nb095_alpha_dummy_312 f)),
                                    ((nb095_alpha_dummy_307 D R S_cls E),
                                      (nb095_alpha_dummy_309 f)),
                                    ((nb095_alpha_dummy_308 D R S_cls E),
                                      (nb095_alpha_dummy_310 f)),
                                    ((nb095_alpha_dummy_300 D R S_cls E),
                                      (nb095_alpha_dummy_302 f)),
                                    ((nb095_alpha_dummy_299 D R S_cls E),
                                      (nb095_alpha_dummy_301 f)),
                                    ((nb095_alpha_dummy_305 D R S_cls E),
                                      (nb095_alpha_dummy_306 f)),
                                    ((nb095_alpha_dummy_303 D R S_cls E),
                                      (nb095_alpha_dummy_304 f)),
                                    ((nb095_alpha_dummy_296 D R S_cls E),
                                      (nb095_alpha_dummy_298 f)),
                                    ((nb095_alpha_dummy_295 D R S_cls E),
                                      (nb095_alpha_dummy_297 f)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                        (nb095_alpha_dummy_300 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_302 f) from (by
                        unfold nb095_alpha_dummy_302;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0298 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                          (nb095_alpha_dummy_299 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0296 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_301 f) from (by
                          unfold nb095_alpha_dummy_301;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0298 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                            (nb095_alpha_dummy_305 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_305;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0300 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_306 f) from (by
                            unfold nb095_alpha_dummy_306;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0301 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_296 D R S_cls E) ≠
                              (nb095_alpha_dummy_303 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0297 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_298 f) ≠ (nb095_alpha_dummy_304 f) from (by
                              unfold nb095_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0299 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_296 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_295 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_298 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_297 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_300 D R S_cls E) ≠
                                (nb095_alpha_dummy_307 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_309 f) from (by
                                unfold nb095_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                  (nb095_alpha_dummy_308 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_310 f) from
                                (by
                                  unfold nb095_alpha_dummy_310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_314 D R S_cls E) from (by
          unfold nb095_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_317 f) from (by
          unfold nb095_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_313 D R S_cls E) from (by
          unfold nb095_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_316 f) from (by
          unfold nb095_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
          unfold nb095_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from (by
          unfold nb095_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_305 D R S_cls E), (nb095_alpha_dummy_306 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_314
        D R S_cls E) ≠ (nb095_alpha_dummy_321 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_305 D R S_cls E), (nb095_alpha_dummy_306 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_305 D R S_cls E),
                                        (nb095_alpha_dummy_306 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
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
                                      (nb095_alpha_dummy_307 D R S_cls E) ≠
                                        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                      (by
                                        unfold nb095_alpha_dummy_312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_305 D R S_cls E),
                                        (nb095_alpha_dummy_306 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
                                      ((nb095_alpha_dummy_293 D R S_cls E),
                                        (nb095_alpha_dummy_294 u S_cls f E)),
                                      ((nb095_alpha_dummy_291 D R S_cls E),
                                        (nb095_alpha_dummy_292 u S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0031 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_331 D R S_cls E))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_300 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_331 D R S_cls E))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_332 f))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_302 f)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_332 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_300 D R S_cls E) ≠
                                (nb095_alpha_dummy_307 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_309 f) from (by
                                unfold nb095_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                  (nb095_alpha_dummy_308 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_310 f) from
                                (by
                                  unfold nb095_alpha_dummy_310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                    (nb095_alpha_dummy_333 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_333;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0332 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_334 f) from (by
                                    unfold nb095_alpha_dummy_334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0333 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_300 D R S_cls E) ≠
                                      (nb095_alpha_dummy_331 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_331;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0330 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_332 f) from
                                    (by
                                      unfold nb095_alpha_dummy_332;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0331 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_314 D R S_cls E) from (by
          unfold nb095_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_317 f) from (by
          unfold nb095_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_313 D R S_cls E) from (by
          unfold nb095_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_316 f) from (by
          unfold nb095_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
          unfold nb095_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from (by
          unfold nb095_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_333 D R S_cls E), (nb095_alpha_dummy_334 f)),
        ((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_314
        D R S_cls E) ≠ (nb095_alpha_dummy_321 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_333 D R S_cls E), (nb095_alpha_dummy_334 f)),
        ((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_333 D R S_cls E),
                                        (nb095_alpha_dummy_334 f)),
                                      ((nb095_alpha_dummy_331 D R S_cls E),
                                        (nb095_alpha_dummy_332 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_329 D R S_cls E),
                                        (nb095_alpha_dummy_330 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
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
                                      (nb095_alpha_dummy_307 D R S_cls E) ≠
                                        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                      (by
                                        unfold nb095_alpha_dummy_312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_333 D R S_cls E),
                                        (nb095_alpha_dummy_334 f)),
                                      ((nb095_alpha_dummy_331 D R S_cls E),
                                        (nb095_alpha_dummy_332 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_329 D R S_cls E),
                                        (nb095_alpha_dummy_330 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
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
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_300 D R S_cls E) ≠
                                (nb095_alpha_dummy_307 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0302 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_309 f) from (by
                                unfold nb095_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0303 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                  (nb095_alpha_dummy_308 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_308;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0302 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_310 f) from
                                (by
                                  unfold nb095_alpha_dummy_310;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0303 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_300 D R S_cls E) ≠
                                    (nb095_alpha_dummy_333 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_333;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0332 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_334 f) from (by
                                    unfold nb095_alpha_dummy_334;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0333 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_300 D R S_cls E) ≠
                                      (nb095_alpha_dummy_331 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_331;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0330 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_302 f) ≠ (nb095_alpha_dummy_332 f) from
                                    (by
                                      unfold nb095_alpha_dummy_332;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0331 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_300 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_302 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_314 D R S_cls E) from (by
          unfold nb095_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_317 f) from (by
          unfold nb095_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_307 D R S_cls E) ≠ (nb095_alpha_dummy_313 D R S_cls E) from (by
          unfold nb095_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0306 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_316 f) from (by
          unfold nb095_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
          unfold nb095_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0304 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from (by
          unfold nb095_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_333 D R S_cls E), (nb095_alpha_dummy_334 f)),
        ((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_314
        D R S_cls E) ≠ (nb095_alpha_dummy_321 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0310
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0311
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0308
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0309
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠ (nb095_alpha_dummy_321
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0314
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_322 f) from (by
          unfold
            nb095_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0315
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_319 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0312
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_320 f) from (by
          unfold
            nb095_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0313
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_315 D R S_cls E), (nb095_alpha_dummy_318 f)),
        ((nb095_alpha_dummy_314 D R S_cls E), (nb095_alpha_dummy_317 f)),
        ((nb095_alpha_dummy_313 D R S_cls E), (nb095_alpha_dummy_316 f)),
        ((nb095_alpha_dummy_311 D R S_cls E), (nb095_alpha_dummy_312 f)),
        ((nb095_alpha_dummy_307 D R S_cls E), (nb095_alpha_dummy_309 f)),
        ((nb095_alpha_dummy_308 D R S_cls E), (nb095_alpha_dummy_310 f)),
        ((nb095_alpha_dummy_333 D R S_cls E), (nb095_alpha_dummy_334 f)),
        ((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
        ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
        ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
        ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
        ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
        ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
        ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_307 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠ (nb095_alpha_dummy_325
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0318
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_326 f) from (by
          unfold
            nb095_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0319
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_314 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0316
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_317 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0317
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_307
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_309 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_315
        D R S_cls E) ≠ (nb095_alpha_dummy_327 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0322
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_328 f) from (by
          unfold
            nb095_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0323
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_315 D R S_cls E) ≠
        (nb095_alpha_dummy_323 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0320
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_318 f) ≠ (nb095_alpha_dummy_324 f) from (by
          unfold
            nb095_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0321
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_333 D R S_cls E),
                                        (nb095_alpha_dummy_334 f)),
                                      ((nb095_alpha_dummy_331 D R S_cls E),
                                        (nb095_alpha_dummy_332 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_329 D R S_cls E),
                                        (nb095_alpha_dummy_330 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
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
                                      (nb095_alpha_dummy_307 D R S_cls E) ≠
                                        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_311;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0304 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_309 f) ≠ (nb095_alpha_dummy_312 f) from
                                      (by
                                        unfold nb095_alpha_dummy_312;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0305 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_307 D R S_cls E) ≠
        (nb095_alpha_dummy_311 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_311;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0304 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_309 f) ≠
        (nb095_alpha_dummy_312 f) from (by
                                          unfold nb095_alpha_dummy_312;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0305 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_311 D R S_cls E),
                                        (nb095_alpha_dummy_312 f)),
                                      ((nb095_alpha_dummy_307 D R S_cls E),
                                        (nb095_alpha_dummy_309 f)),
                                      ((nb095_alpha_dummy_308 D R S_cls E),
                                        (nb095_alpha_dummy_310 f)),
                                      ((nb095_alpha_dummy_333 D R S_cls E),
                                        (nb095_alpha_dummy_334 f)),
                                      ((nb095_alpha_dummy_331 D R S_cls E),
                                        (nb095_alpha_dummy_332 f)),
                                      ((nb095_alpha_dummy_300 D R S_cls E),
                                        (nb095_alpha_dummy_302 f)),
                                      ((nb095_alpha_dummy_299 D R S_cls E),
                                        (nb095_alpha_dummy_301 f)),
                                      ((nb095_alpha_dummy_329 D R S_cls E),
                                        (nb095_alpha_dummy_330 f)),
                                      ((nb095_alpha_dummy_303 D R S_cls E),
                                        (nb095_alpha_dummy_304 f)),
                                      ((nb095_alpha_dummy_296 D R S_cls E),
                                        (nb095_alpha_dummy_298 f)),
                                      ((nb095_alpha_dummy_295 D R S_cls E),
                                        (nb095_alpha_dummy_297 f)),
                                      ((nb095_alpha_dummy_293 D R S_cls E),
                                        (nb095_alpha_dummy_294 u S_cls f E)),
                                      ((nb095_alpha_dummy_291 D R S_cls E),
                                        (nb095_alpha_dummy_292 u S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb095_alpha_dummy_331 D R S_cls E), (nb095_alpha_dummy_332 f)),
            ((nb095_alpha_dummy_300 D R S_cls E), (nb095_alpha_dummy_302 f)),
            ((nb095_alpha_dummy_299 D R S_cls E), (nb095_alpha_dummy_301 f)),
            ((nb095_alpha_dummy_329 D R S_cls E), (nb095_alpha_dummy_330 f)),
            ((nb095_alpha_dummy_303 D R S_cls E), (nb095_alpha_dummy_304 f)),
            ((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
            ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
            ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
            ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
            ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
            ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb095_focused_notmem_0021 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_337 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv)
        0 ∉
      E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0022 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_338 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv)
        0 ∉
      E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0023 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_335 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0024 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_336 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cnin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0025 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_293 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0026 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_294 u S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0027 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_291 D R S_cls E) ∉ E.fv :=
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
      E.fv
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
  left
  exact hu

theorem nb095_focused_notmem_0028 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_292 u S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
          ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv)
        0 ∉
      E.fv
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
  left
  exact hu

theorem nb095_compact_envfresh_0112 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_337 D R S_cls E)
      (nb095_alpha_dummy_338 u S_cls E) (nb095_focused_notmem_0021 D R S_cls E)
      (nb095_focused_notmem_0022 u S_cls E)
      (TEnvFresh.consFresh (nb095_alpha_dummy_335 D R S_cls E)
        (nb095_alpha_dummy_336 u S_cls E) (nb095_focused_notmem_0023 D R S_cls E)
        (nb095_focused_notmem_0024 u S_cls E)
        (TEnvFresh.consFresh (nb095_alpha_dummy_293 D R S_cls E)
          (nb095_alpha_dummy_294 u S_cls f E) (nb095_focused_notmem_0025 D R S_cls E)
          (nb095_focused_notmem_0026 u S_cls f E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_291 D R S_cls E)
            (nb095_alpha_dummy_292 u S_cls f E) (nb095_focused_notmem_0027 D R S_cls E)
            (nb095_focused_notmem_0028 u S_cls f E)
            (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
              (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
              (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
                (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                  (nb095_focused_notmem_0004 D R S_cls E) dv_E_f (TEnvFresh.nil E.fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
