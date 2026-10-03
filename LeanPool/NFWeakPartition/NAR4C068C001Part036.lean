/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block009

/-! NF weak partition development: NAR4C068C001Part036. -/


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
noncomputable def nb068_split_alpha_0085 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
        (syn_cphi (Class.cv (nb068_alpha_dummy_288))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_295) from (by
                    unfold nb068_alpha_dummy_295;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
                (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_297 f) from (by
                    unfold nb068_alpha_dummy_297;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_296) from
                    (by
                      unfold nb068_alpha_dummy_296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
                  (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_298 f) from (by
                      unfold nb068_alpha_dummy_298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_302) from
                                    (by
                                      unfold nb068_alpha_dummy_302;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0302)
                                              1)))) (show
                                    (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_305 f) from
                                    (by
                                      unfold nb068_alpha_dummy_305;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0303 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_301) from (by
                                        unfold nb068_alpha_dummy_301;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0302)
                                                0)))) (show (nb068_alpha_dummy_297 f) ≠
                                        (nb068_alpha_dummy_304 f) from (by
                                        unfold nb068_alpha_dummy_304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                                        (by
                                          unfold nb068_alpha_dummy_299;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0300)
                                                  0)))) (show (nb068_alpha_dummy_297 f) ≠
        (nb068_alpha_dummy_300 f) from (by
                                          unfold nb068_alpha_dummy_300;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0301 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
                                      ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
                                      ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
                                      ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                                      ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0084 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                              unfold nb068_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                              unfold nb068_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                            unfold nb068_alpha_dummy_299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                        (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                            unfold nb068_alpha_dummy_300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                              unfold nb068_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                              unfold nb068_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0086 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
        ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
        ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
        ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
        ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
        ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_301))
            (syn_cun (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_304 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_305 f))
              (Class.cv (nb068_alpha_dummy_306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
          ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
          ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
          ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
          ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
          ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
          ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0087 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
        ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_295))
          (Class.cv (nb068_alpha_dummy_288))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_296))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_295))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f))
          (Class.cv (nb068_alpha_dummy_290 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_298 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_297 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_295) from (by
              unfold nb068_alpha_dummy_295;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
          (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_297 f) from (by
              unfold nb068_alpha_dummy_297;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_296) from (by
                unfold nb068_alpha_dummy_296;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
            (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_298 f) from (by
                unfold nb068_alpha_dummy_298;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_321) from (by
                  unfold nb068_alpha_dummy_321;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0328) 0))))
              (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_322 f) from (by
                  unfold nb068_alpha_dummy_322;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0329 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_319) from (by
                    unfold nb068_alpha_dummy_319;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0326) 0))))
                (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_320 f) from (by
                    unfold nb068_alpha_dummy_320;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0327 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_302) from (by
                                  unfold nb068_alpha_dummy_302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0302) 1))))
                              (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_305 f) from
                                (by
                                  unfold nb068_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0303 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_301) from (by
                                    unfold nb068_alpha_dummy_301;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0302) 0)))) (show
                                  (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_304 f) from (by
                                    unfold nb068_alpha_dummy_304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0303 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                                    (by
                                      unfold nb068_alpha_dummy_299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0300)
                                              0)))) (show
                                    (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from
                                    (by
                                      unfold nb068_alpha_dummy_300;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0301 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
                                  ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
                                  ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
                                  ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                                  ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                                  ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                                  ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                                  ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                                  ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                                  ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                                  ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                                  ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                                  ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                                  ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0086 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                          unfold nb068_alpha_dummy_299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                          unfold nb068_alpha_dummy_300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                      ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                      ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                      ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                      (by
                        unfold nb068_alpha_dummy_299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                    (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                        unfold nb068_alpha_dummy_300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                          unfold nb068_alpha_dummy_299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                          unfold nb068_alpha_dummy_300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                      ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                      ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                      ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0088 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_317))
          (Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_317))
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f))
          (Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f))
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from
                    (by
                      unfold nb068_alpha_dummy_288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                  (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
                      unfold nb068_alpha_dummy_290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from
                      (by
                        unfold nb068_alpha_dummy_287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                    (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
                        unfold nb068_alpha_dummy_289;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_317) from (by
                          unfold nb068_alpha_dummy_317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_318 f) from (by
                          unfold nb068_alpha_dummy_318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_291) from (by
                            unfold nb068_alpha_dummy_291;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_292 f) from (by
                            unfold nb068_alpha_dummy_292;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0087 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0087 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from
                      (by
                        unfold nb068_alpha_dummy_288;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                    (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
                        unfold nb068_alpha_dummy_290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from (by
                          unfold nb068_alpha_dummy_287;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
                          unfold nb068_alpha_dummy_289;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_317) from (by
                            unfold nb068_alpha_dummy_317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_318 f) from (by
                            unfold nb068_alpha_dummy_318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_291) from (by
                              unfold nb068_alpha_dummy_291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                          (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_292 f) from (by
                              unfold nb068_alpha_dummy_292;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_284))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0087 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0087 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                            ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                            ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                            ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                            ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                            ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                            ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb068_compact_fv_empty_0272 : (nb068_alpha_dummy_325) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0273 (f : Var) :
    (nb068_alpha_dummy_326 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0274 : (nb068_alpha_dummy_323) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0275 (f : Var) :
    (nb068_alpha_dummy_324 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
