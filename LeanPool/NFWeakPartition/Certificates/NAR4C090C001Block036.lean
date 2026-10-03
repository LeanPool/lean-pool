/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block035

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part102`. -/


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
noncomputable def nb090_split_alpha_0080 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_297 A))
          (Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_297 A))
            (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_298 u))
          (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_298 u))
            (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_292 A) from (by
                      unfold nb090_alpha_dummy_292;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
                  (show u ≠ (nb090_alpha_dummy_294 u) from (by
                      unfold nb090_alpha_dummy_294;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_291 A) from (by
                        unfold nb090_alpha_dummy_291;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
                    (show u ≠ (nb090_alpha_dummy_293 u) from (by
                        unfold nb090_alpha_dummy_293;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0300 u) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_297 A) from (by
                          unfold nb090_alpha_dummy_297;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0302 A) 0))))
                      (show u ≠ (nb090_alpha_dummy_298 u) from (by
                          unfold nb090_alpha_dummy_298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0303 u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_295 A) from (by
                            unfold nb090_alpha_dummy_295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0299 A) 0))))
                        (show u ≠ (nb090_alpha_dummy_296 u) from (by
                            unfold nb090_alpha_dummy_296;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0301 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_283 A) from (by
                              unfold nb090_alpha_dummy_283;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
                          (show u ≠ (nb090_alpha_dummy_284 u) from (by
                              unfold nb090_alpha_dummy_284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_285 A) from (by
                                unfold nb090_alpha_dummy_285;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
                            (show u ≠ (nb090_alpha_dummy_286 u) from (by
                                unfold nb090_alpha_dummy_286;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_288 A) from
                                (by
                                  unfold nb090_alpha_dummy_288;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0294 A) 1))))
                              (show u ≠ (nb090_alpha_dummy_290 u) from (by
                                  unfold nb090_alpha_dummy_290;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0297 u) 1))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_287 A) from (by
                                    unfold nb090_alpha_dummy_287;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0294 A)
                                            0)))) (show u ≠ (nb090_alpha_dummy_289 u) from (by
                                    unfold nb090_alpha_dummy_289;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0297 u)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_041 A) from
                                    (by
                                      unfold nb090_alpha_dummy_041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0642 A)
                                              0)))) (show u ≠ (nb090_alpha_dummy_043 v u h) from
                                    (by
                                      unfold nb090_alpha_dummy_043;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0643 v u h) 0))))
                                  (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                    (Ne.symm dv_h_u) (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                      (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_299 A) from (by
                              unfold nb090_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                          (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_301 u) from (by
                              unfold nb090_alpha_dummy_301;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_300 A) from (by
                                unfold nb090_alpha_dummy_300;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                            (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_302 u) from (by
                                unfold nb090_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_306 A) from (by
          unfold nb090_alpha_dummy_306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_309 u) from (by
          unfold nb090_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_305 A) from (by
          unfold nb090_alpha_dummy_305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_308 u) from (by
          unfold nb090_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from (by
          unfold nb090_alpha_dummy_303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A)
                  0)))) (show (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from (by
          unfold nb090_alpha_dummy_304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A),
        (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A),
        (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A),
        (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_306
        A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A),
        (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A),
        (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A),
        (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301
        u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                      (by
                                        unfold nb090_alpha_dummy_303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090_alpha_dummy_301 u) ≠
                                        (nb090_alpha_dummy_304 u) from (by
                                        unfold nb090_alpha_dummy_304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                    ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                    ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                    ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                    ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                    ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
                                    ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                    ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                    ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                    ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                    ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                    (by
                                      unfold nb090_alpha_dummy_303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from
                                    (by
                                      unfold nb090_alpha_dummy_304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                      (by
                                        unfold nb090_alpha_dummy_303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090_alpha_dummy_301 u) ≠
                                        (nb090_alpha_dummy_304 u) from (by
                                        unfold nb090_alpha_dummy_304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                    ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                    ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                    ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                    ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                    ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
                                    ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                    ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                    ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                    ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                    ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_292 A) from (by
                        unfold nb090_alpha_dummy_292;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
                    (show u ≠ (nb090_alpha_dummy_294 u) from (by
                        unfold nb090_alpha_dummy_294;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0300 u) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_291 A) from (by
                          unfold nb090_alpha_dummy_291;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
                      (show u ≠ (nb090_alpha_dummy_293 u) from (by
                          unfold nb090_alpha_dummy_293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_297 A) from (by
                            unfold nb090_alpha_dummy_297;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0302 A) 0))))
                        (show u ≠ (nb090_alpha_dummy_298 u) from (by
                            unfold nb090_alpha_dummy_298;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0303 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_295 A) from (by
                              unfold nb090_alpha_dummy_295;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0299 A) 0))))
                          (show u ≠ (nb090_alpha_dummy_296 u) from (by
                              unfold nb090_alpha_dummy_296;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0301 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_283 A) from (by
                                unfold nb090_alpha_dummy_283;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
                            (show u ≠ (nb090_alpha_dummy_284 u) from (by
                                unfold nb090_alpha_dummy_284;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_285 A) from
                                (by
                                  unfold nb090_alpha_dummy_285;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
                              (show u ≠ (nb090_alpha_dummy_286 u) from (by
                                  unfold nb090_alpha_dummy_286;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_288 A) from (by
                                    unfold nb090_alpha_dummy_288;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0294 A)
                                            1)))) (show u ≠ (nb090_alpha_dummy_290 u) from (by
                                    unfold nb090_alpha_dummy_290;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0297 u)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_287 A) from
                                    (by
                                      unfold nb090_alpha_dummy_287;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0294 A)
                                              0)))) (show u ≠ (nb090_alpha_dummy_289 u) from (by
                                      unfold nb090_alpha_dummy_289;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0297 u)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_041 A) from
                                      (by
                                        unfold nb090_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                0))))
                                    (show u ≠ (nb090_alpha_dummy_043 v u h) from (by
                                        unfold nb090_alpha_dummy_043;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0643 v u h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_u) (TAlphaVar.there
                                        (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                        (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_299 A) from (by
                                unfold nb090_alpha_dummy_299;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                            (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_301 u) from (by
                                unfold nb090_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_300 A) from
                                (by
                                  unfold nb090_alpha_dummy_300;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                              (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_302 u) from
                                (by
                                  unfold nb090_alpha_dummy_302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_292 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_294 u))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_306 A) from (by
          unfold nb090_alpha_dummy_306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_309 u) from (by
          unfold nb090_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_305 A) from (by
          unfold nb090_alpha_dummy_305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A)
                  0)))) (show (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_308 u) from (by
          unfold nb090_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_299 A) ≠
        (nb090_alpha_dummy_303 A) from (by
          unfold nb090_alpha_dummy_303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A)
                  0)))) (show (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from (by
          unfold nb090_alpha_dummy_304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A),
        (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A),
        (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A),
        (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_306
        A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A),
        (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A),
        (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A),
        (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301
        u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A)
                                        from (by
                                          unfold nb090_alpha_dummy_303;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0306 A) 0)))) (show
                                        (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u)
                                        from (by
                                          unfold nb090_alpha_dummy_304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0307 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                      ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                      ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                      ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                      ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                      ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
                                      ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                      ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                      ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                      ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                      ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                      (by
                                        unfold nb090_alpha_dummy_303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090_alpha_dummy_301 u) ≠
                                        (nb090_alpha_dummy_304 u) from (by
                                        unfold nb090_alpha_dummy_304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A)
                                        from (by
                                          unfold nb090_alpha_dummy_303;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0306 A) 0)))) (show
                                        (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u)
                                        from (by
                                          unfold nb090_alpha_dummy_304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0307 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                      ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                      ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                      ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                      ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                      ((nb090_alpha_dummy_297 A), (nb090_alpha_dummy_298 u)),
                                      ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                      ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                      ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                      ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                      ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part103`. -/


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
noncomputable def nb090_split_alpha_0081 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)),
        ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
        ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)),
        ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_323 A))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_324 u))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_299 A) from (by
                            unfold nb090_alpha_dummy_299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                        (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_301 u) from (by
                            unfold nb090_alpha_dummy_301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_300 A) from (by
                              unfold nb090_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                          (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_302 u) from (by
                              unfold nb090_alpha_dummy_302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_325 A) from (by
                                unfold nb090_alpha_dummy_325;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0334 A) 0))))
                            (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_326 u) from (by
                                unfold nb090_alpha_dummy_326;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0335 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_323 A) from
                                (by
                                  unfold nb090_alpha_dummy_323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0332 A) 0))))
                              (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_324 u) from
                                (by
                                  unfold nb090_alpha_dummy_324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0333 u) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_299 A) ≠
        (nb090_alpha_dummy_306 A) from (by
          unfold nb090_alpha_dummy_306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_309 u) from (by
          unfold nb090_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_305 A) from (by
          unfold nb090_alpha_dummy_305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_308 u) from (by
          unfold nb090_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from (by
          unfold nb090_alpha_dummy_303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A) 0)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_304 u) from (by
          unfold nb090_alpha_dummy_304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_306
        A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                    (by
                                      unfold nb090_alpha_dummy_303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from
                                    (by
                                      unfold nb090_alpha_dummy_304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                  ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                  ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                  ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)),
                                  ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)),
                                  ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                  ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                  ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)),
                                  ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                  ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                  ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                  ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                  ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                  ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from (by
                                    unfold nb090_alpha_dummy_303;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0306 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from (by
                                    unfold nb090_alpha_dummy_304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0307 u)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                    (by
                                      unfold nb090_alpha_dummy_303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from
                                    (by
                                      unfold nb090_alpha_dummy_304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                  ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                  ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                  ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)),
                                  ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)),
                                  ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                  ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                  ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)),
                                  ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                  ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                  ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                  ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                  ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                  ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_299 A) from (by
                            unfold nb090_alpha_dummy_299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                        (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_301 u) from (by
                            unfold nb090_alpha_dummy_301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_300 A) from (by
                              unfold nb090_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                          (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_302 u) from (by
                              unfold nb090_alpha_dummy_302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_325 A) from (by
                                unfold nb090_alpha_dummy_325;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0334 A) 0))))
                            (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_326 u) from (by
                                unfold nb090_alpha_dummy_326;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0335 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_292 A) ≠ (nb090_alpha_dummy_323 A) from
                                (by
                                  unfold nb090_alpha_dummy_323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0332 A) 0))))
                              (show (nb090_alpha_dummy_294 u) ≠ (nb090_alpha_dummy_324 u) from
                                (by
                                  unfold nb090_alpha_dummy_324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0333 u) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_299 A) ≠
        (nb090_alpha_dummy_306 A) from (by
          unfold nb090_alpha_dummy_306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_309 u) from (by
          unfold nb090_alpha_dummy_309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_305 A) from (by
          unfold nb090_alpha_dummy_305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_308 u) from (by
          unfold nb090_alpha_dummy_308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from (by
          unfold nb090_alpha_dummy_303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A) 0)))) (show (nb090_alpha_dummy_301 u) ≠
        (nb090_alpha_dummy_304 u) from (by
          unfold nb090_alpha_dummy_304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠ (nb090_alpha_dummy_313 A) from (by
          unfold
            nb090_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_314 u) from (by
          unfold
            nb090_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_311 A) from (by
          unfold
            nb090_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_312 u) from (by
          unfold
            nb090_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A),
        (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)),
        ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A),
        (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
        ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_306
        A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_317 A) from (by
          unfold
            nb090_alpha_dummy_317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_318 u) from (by
          unfold
            nb090_alpha_dummy_318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_306 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_307
        A) ≠ (nb090_alpha_dummy_319 A) from (by
          unfold
            nb090_alpha_dummy_319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_320 u) from (by
          unfold
            nb090_alpha_dummy_320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_307 A) ≠
        (nb090_alpha_dummy_315 A) from (by
          unfold
            nb090_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090_alpha_dummy_310 u) ≠ (nb090_alpha_dummy_316 u) from (by
          unfold
            nb090_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                    (by
                                      unfold nb090_alpha_dummy_303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from
                                    (by
                                      unfold nb090_alpha_dummy_304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                  ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                  ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                  ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)),
                                  ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)),
                                  ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                  ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                  ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)),
                                  ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                  ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                  ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                  ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                  ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                  ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from (by
                                    unfold nb090_alpha_dummy_303;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0306 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from (by
                                    unfold nb090_alpha_dummy_304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0307 u)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_303 A) from
                                    (by
                                      unfold nb090_alpha_dummy_303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_304 u) from
                                    (by
                                      unfold nb090_alpha_dummy_304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)),
                                  ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)),
                                  ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)),
                                  ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)),
                                  ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)),
                                  ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
                                  ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
                                  ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)),
                                  ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
                                  ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                  ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                  ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                  ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                  ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

theorem nb090_wpp_notmem_1596 (A : Class) : (nb090_alpha_dummy_041 A) ∉ ((syn_c2nd)).fv :=
  by simpa only [nb090_alpha_dummy_041, fv_syn_c2nd] using (nb090_compact_fv_empty_0462 A)

theorem nb090_wpp_notmem_1597 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_043, fv_syn_c2nd] using
    (nb090_compact_fv_empty_0463 v u h)

theorem nb090_compact_envfresh_0275 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c2nd)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u)
      (nb090_wpp_notmem_0838 A) (nb090_wpp_notmem_0839 u)
      (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u)
        (nb090_wpp_notmem_0840 A) (nb090_wpp_notmem_0841 u)
        (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u)
          (nb090_wpp_notmem_0842 A) (nb090_wpp_notmem_0843 u)
          (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u)
            (nb090_wpp_notmem_0844 A) (nb090_wpp_notmem_0845 u)
            (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h)
              (nb090_wpp_notmem_1596 A) (nb090_wpp_notmem_1597 v u h)
              (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0846 A)
                (nb090_wpp_notmem_0847 h)
                (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0848 A)
                  (nb090_wpp_notmem_0849 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u
                    (nb090_wpp_notmem_0850 A) (nb090_wpp_notmem_0851 u)
                    (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                      (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0852 A)
                      (nb090_wpp_notmem_0853 v u A h) (TEnvFresh.nil ((syn_c2nd)).fv))))))))))

@[expose]
noncomputable def nb090_wpp_refl_0275 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
        ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0275 v u A h)

theorem nb090_compact_fv_empty_0464 (A : Class) :
    (nb090_alpha_dummy_042 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0465 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
