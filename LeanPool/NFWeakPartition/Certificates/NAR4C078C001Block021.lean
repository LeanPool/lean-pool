/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C078C001Part070Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part070`. -/


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
noncomputable def nb078_wpp_refl_0136 (x : Var) (y : Var) (g : Var) :
    TReflOn
      [((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0136 x y g)

@[expose]
noncomputable def nb078_split_alpha_0041 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_301))
          (Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_301)) (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_302 g))
          (Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_302 g))
            (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_296) from
                    (by
                      unfold nb078_alpha_dummy_296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
                  (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_298 g) from (by
                      unfold nb078_alpha_dummy_298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_295) from
                      (by
                        unfold nb078_alpha_dummy_295;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
                    (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_297 g) from (by
                        unfold nb078_alpha_dummy_297;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0296 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_301) from (by
                          unfold nb078_alpha_dummy_301;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0298) 0))))
                      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_302 g) from (by
                          unfold nb078_alpha_dummy_302;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0299 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_299) from (by
                            unfold nb078_alpha_dummy_299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0295) 0))))
                        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_300 g) from (by
                            unfold nb078_alpha_dummy_300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0297 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_303) from (by
                              unfold nb078_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                          (show (nb078_alpha_dummy_298 g) ≠ (nb078_alpha_dummy_305 g) from (by
                              unfold nb078_alpha_dummy_305;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_304) from (by
                                unfold nb078_alpha_dummy_304;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                            (show (nb078_alpha_dummy_298 g) ≠ (nb078_alpha_dummy_306 g) from (by
                                unfold nb078_alpha_dummy_306;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_298 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_310) from (by
          unfold nb078_alpha_dummy_310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_313 g) from (by
          unfold nb078_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_309) from (by
          unfold nb078_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_312 g) from (by
          unfold nb078_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295),
        (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_317)
        from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_317)
        from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295),
        (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠
        (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_321)
        from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
                                        unfold nb078_alpha_dummy_307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078_alpha_dummy_305 g) ≠
                                        (nb078_alpha_dummy_308 g) from (by
                                        unfold nb078_alpha_dummy_308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
                                    ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)),
                                    ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
                                    ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
                                    ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
                                    ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
                                    ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from
                                    (by
                                      unfold nb078_alpha_dummy_307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0302)
                                              0)))) (show
                                    (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_308 g) from
                                    (by
                                      unfold nb078_alpha_dummy_308;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0303 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
                                        unfold nb078_alpha_dummy_307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078_alpha_dummy_305 g) ≠
                                        (nb078_alpha_dummy_308 g) from (by
                                        unfold nb078_alpha_dummy_308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
                                    ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)),
                                    ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
                                    ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
                                    ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
                                    ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
                                    ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_296) from
                      (by
                        unfold nb078_alpha_dummy_296;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
                    (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_298 g) from (by
                        unfold nb078_alpha_dummy_298;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0296 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_295) from (by
                          unfold nb078_alpha_dummy_295;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0294) 0))))
                      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_297 g) from (by
                          unfold nb078_alpha_dummy_297;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_301) from (by
                            unfold nb078_alpha_dummy_301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0298) 0))))
                        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_302 g) from (by
                            unfold nb078_alpha_dummy_302;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0299 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_299) from (by
                              unfold nb078_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0295) 0))))
                          (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_300 g) from (by
                              unfold nb078_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0297 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_303) from (by
                                unfold nb078_alpha_dummy_303;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                            (show (nb078_alpha_dummy_298 g) ≠ (nb078_alpha_dummy_305 g) from (by
                                unfold nb078_alpha_dummy_305;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_304) from (by
                                  unfold nb078_alpha_dummy_304;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                              (show (nb078_alpha_dummy_298 g) ≠ (nb078_alpha_dummy_306 g) from
                                (by
                                  unfold nb078_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_298 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_310) from (by
          unfold nb078_alpha_dummy_310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_313 g) from (by
          unfold nb078_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_309) from (by
          unfold nb078_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_312 g) from (by
          unfold nb078_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307)
        from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302)
                  0)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295),
        (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_317)
        from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_317)
        from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295),
        (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠
        (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_321)
        from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from
                                        (by
                                          unfold nb078_alpha_dummy_307;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0302)
                                                  0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
                                          unfold nb078_alpha_dummy_308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0303 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
                                      ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)),
                                      ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
                                      ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
                                      ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
                                      ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
                                      ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
                                        unfold nb078_alpha_dummy_307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078_alpha_dummy_305 g) ≠
                                        (nb078_alpha_dummy_308 g) from (by
                                        unfold nb078_alpha_dummy_308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from
                                        (by
                                          unfold nb078_alpha_dummy_307;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0302)
                                                  0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
                                          unfold nb078_alpha_dummy_308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0303 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
                                      ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)),
                                      ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
                                      ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
                                      ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
                                      ((nb078_alpha_dummy_301), (nb078_alpha_dummy_302 g)),
                                      ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part071`. -/


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
noncomputable def nb078_split_alpha_0042 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
        ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
        ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)),
        ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_296))
          (Class.cv (nb078_alpha_dummy_288))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_298 g))
          (Class.cv (nb078_alpha_dummy_291 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_296) from (by
              unfold nb078_alpha_dummy_296;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))))
          (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_298 g) from (by
              unfold nb078_alpha_dummy_298;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_295) from (by
                unfold nb078_alpha_dummy_295;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))))
            (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_297 g) from (by
                unfold nb078_alpha_dummy_297;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_325) from (by
                  unfold nb078_alpha_dummy_325;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0326) 0))))
              (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_326 g) from (by
                  unfold nb078_alpha_dummy_326;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0327 g) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_299) from (by
                    unfold nb078_alpha_dummy_299;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0323) 0))))
                (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_300 g) from (by
                    unfold nb078_alpha_dummy_300;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0325 g) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_303) from (by
                                        unfold nb078_alpha_dummy_303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0300)
                                                0)))) (show (nb078_alpha_dummy_298 g) ≠
                                        (nb078_alpha_dummy_305 g) from (by
                                        unfold nb078_alpha_dummy_305;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0301 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_304) from
                                        (by
                                          unfold nb078_alpha_dummy_304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0300)
                                                  1)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_306 g) from (by
                                          unfold nb078_alpha_dummy_306;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0301 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_296) ≠
        (nb078_alpha_dummy_329) from (by
          unfold nb078_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0330) 0)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_330 g) from (by
          unfold nb078_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0331 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_327) from (by
          unfold nb078_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0328) 0)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_328 g) from (by
          unfold nb078_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0329 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_296))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_298 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_310) from (by
          unfold nb078_alpha_dummy_310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304)
                  1)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_313 g) from (by
          unfold nb078_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_309)
        from (by
          unfold nb078_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304)
                  0)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_312 g) from (by
          unfold nb078_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307)
        from (by
          unfold
            nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302)
                  0)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_308 g) from (by
          unfold
            nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327),
        (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
        ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325),
        (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327),
        (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
        ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325),
        (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠
        (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307)
        from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
        ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304),
        (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)),
        ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296),
        (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
        ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299),
        (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
        ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304),
        (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)),
        ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296),
        (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
        ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299),
        (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_303) from (by
                                        unfold nb078_alpha_dummy_303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0300)
                                                0)))) (show (nb078_alpha_dummy_298 g) ≠
                                        (nb078_alpha_dummy_305 g) from (by
                                        unfold nb078_alpha_dummy_305;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0301 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_304) from
                                        (by
                                          unfold nb078_alpha_dummy_304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0300)
                                                  1)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_306 g) from (by
                                          unfold nb078_alpha_dummy_306;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0301 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_296) ≠
        (nb078_alpha_dummy_329) from (by
          unfold nb078_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0330) 0)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_330 g) from (by
          unfold nb078_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0331 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_296) ≠ (nb078_alpha_dummy_327) from (by
          unfold nb078_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0328) 0)))) (show (nb078_alpha_dummy_298 g) ≠
        (nb078_alpha_dummy_328 g) from (by
          unfold nb078_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0329 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_296))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_298 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_310) from (by
          unfold nb078_alpha_dummy_310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304)
                  1)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_313 g) from (by
          unfold nb078_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_309)
        from (by
          unfold nb078_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304)
                  0)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_312 g) from (by
          unfold nb078_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307)
        from (by
          unfold
            nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302)
                  0)))) (show (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_308 g) from (by
          unfold
            nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327),
        (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
        ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325),
        (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_317) from (by
          unfold
            nb078_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_318 g) from (by
          unfold
            nb078_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_315)
        from (by
          unfold
            nb078_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_316 g) from (by
          unfold
            nb078_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310),
        (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)),
        ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303),
        (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)),
        ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327),
        (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
        ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325),
        (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠
        (nb078_alpha_dummy_321) from (by
          unfold
            nb078_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_322 g) from (by
          unfold
            nb078_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠
        (nb078_alpha_dummy_323) from (by
          unfold
            nb078_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_324 g) from (by
          unfold
            nb078_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_311) ≠ (nb078_alpha_dummy_319)
        from (by
          unfold
            nb078_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078_alpha_dummy_314 g) ≠ (nb078_alpha_dummy_320 g) from (by
          unfold
            nb078_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307)
        from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
        ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304),
        (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)),
        ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296),
        (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
        ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299),
        (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_307) from (by
          unfold nb078_alpha_dummy_307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078_alpha_dummy_305 g) ≠
        (nb078_alpha_dummy_308 g) from (by
          unfold nb078_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)),
        ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304),
        (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)),
        ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296),
        (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
        ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299),
        (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)),
                    ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)),
                    ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)),
                    ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)),
                    ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)),
                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part072`. -/


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
noncomputable def nb078_split_alpha_0043 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_337))
          (Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_337)) (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_338 g))
          (Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_338 g))
            (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_332) from
                    (by
                      unfold nb078_alpha_dummy_332;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
                  (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_334 g) from (by
                      unfold nb078_alpha_dummy_334;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_331) from
                      (by
                        unfold nb078_alpha_dummy_331;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
                    (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_333 g) from (by
                        unfold nb078_alpha_dummy_333;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0334 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_337) from (by
                          unfold nb078_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0336) 0))))
                      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_338 g) from (by
                          unfold nb078_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0337 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_335) from (by
                            unfold nb078_alpha_dummy_335;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0333) 0))))
                        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_336 g) from (by
                            unfold nb078_alpha_dummy_336;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0335 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_289))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_346) from (by
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
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331),
        (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331),
        (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
                                        unfold nb078_alpha_dummy_343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078_alpha_dummy_341 g) ≠
                                        (nb078_alpha_dummy_344 g) from (by
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
                                    ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                    ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                    ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
                                    ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                    ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
                                        unfold nb078_alpha_dummy_343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078_alpha_dummy_341 g) ≠
                                        (nb078_alpha_dummy_344 g) from (by
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
                                    ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                    ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                    ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
                                    ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                    ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_332) from
                      (by
                        unfold nb078_alpha_dummy_332;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
                    (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_334 g) from (by
                        unfold nb078_alpha_dummy_334;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0334 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_331) from (by
                          unfold nb078_alpha_dummy_331;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0332) 0))))
                      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_333 g) from (by
                          unfold nb078_alpha_dummy_333;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_337) from (by
                            unfold nb078_alpha_dummy_337;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0336) 0))))
                        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_338 g) from (by
                            unfold nb078_alpha_dummy_338;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0337 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_335) from (by
                              unfold nb078_alpha_dummy_335;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0333) 0))))
                          (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_336 g) from (by
                              unfold nb078_alpha_dummy_336;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0335 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078_alpha_dummy_001))).fv ∪
                                  ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_289))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_334 g) ≠ (nb078_alpha_dummy_342 g) from
                                (by
                                  unfold nb078_alpha_dummy_342;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_334 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_346) from (by
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
                  (nb078_support_mem_0343 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343)
        from (by
          unfold nb078_alpha_dummy_343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340)
                  0)))) (show (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_344 g) from (by
          unfold nb078_alpha_dummy_344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346),
        (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)),
        ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339),
        (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
        ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331),
        (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331),
        (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
        ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                        (by
                                          unfold nb078_alpha_dummy_343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_344 g) from (by
                                          unfold nb078_alpha_dummy_344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                      ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                      ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                      ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                      ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                      ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
                                      ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from (by
                                        unfold nb078_alpha_dummy_343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078_alpha_dummy_341 g) ≠
                                        (nb078_alpha_dummy_344 g) from (by
                                        unfold nb078_alpha_dummy_344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_343) from
                                        (by
                                          unfold nb078_alpha_dummy_343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078_alpha_dummy_341 g) ≠
        (nb078_alpha_dummy_344 g) from (by
                                          unfold nb078_alpha_dummy_344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)),
                                      ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)),
                                      ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)),
                                      ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)),
                                      ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
                                      ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)),
                                      ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
