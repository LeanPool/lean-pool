/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part036

/-! NF weak partition development: NAR4H5C095M3Part037. -/


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
noncomputable def nb095_split_alpha_0082 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095_alpha_dummy_287 D R S_cls E))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_288 x R))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                            (nb095_alpha_dummy_263 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_263;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_265 x R) from (by
                            unfold nb095_alpha_dummy_265;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0265 x R) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                              (nb095_alpha_dummy_264 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_266 x R) from
                            (by
                              unfold nb095_alpha_dummy_266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0265 x R) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                                (nb095_alpha_dummy_289 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_289;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0294 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_290 x R) from (by
                                unfold nb095_alpha_dummy_290;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0295 x R) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                                  (nb095_alpha_dummy_287 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_287;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0292 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_288 x R) from
                                (by
                                  unfold nb095_alpha_dummy_288;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0293 x R)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_258 x R))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_270 D R S_cls E) from (by
          unfold nb095_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_273 x R) from (by
          unfold nb095_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_269 D R S_cls E) from (by
          unfold nb095_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_272 x R) from (by
          unfold nb095_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_267 D R S_cls E) from (by
          unfold nb095_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0266 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R) from (by
          unfold nb095_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0267 x R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_289 D R S_cls E), (nb095_alpha_dummy_290 x R)),
        ((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_289 D R S_cls E), (nb095_alpha_dummy_290 x R)),
        ((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270 D
        R S_cls E) ≠ (nb095_alpha_dummy_281 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_282 x R) from (by
          unfold
            nb095_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_281
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_282 x R) from (by
          unfold
            nb095_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271 D
        R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_284 x R) from (by
          unfold
            nb095_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271 D
        R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_284 x R) from (by
          unfold
            nb095_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_263 D R S_cls E) ≠
                                      (nb095_alpha_dummy_267 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_267;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                    from (by
                                      unfold nb095_alpha_dummy_268;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_267 D R S_cls E),
                                    (nb095_alpha_dummy_268 x R)),
                                  ((nb095_alpha_dummy_263 D R S_cls E),
                                    (nb095_alpha_dummy_265 x R)),
                                  ((nb095_alpha_dummy_264 D R S_cls E),
                                    (nb095_alpha_dummy_266 x R)),
                                  ((nb095_alpha_dummy_289 D R S_cls E),
                                    (nb095_alpha_dummy_290 x R)),
                                  ((nb095_alpha_dummy_287 D R S_cls E),
                                    (nb095_alpha_dummy_288 x R)),
                                  ((nb095_alpha_dummy_256 D R S_cls E),
                                    (nb095_alpha_dummy_258 x R)),
                                  ((nb095_alpha_dummy_255 D R S_cls E),
                                    (nb095_alpha_dummy_257 x R)),
                                  ((nb095_alpha_dummy_285 D R S_cls E),
                                    (nb095_alpha_dummy_286 x R)),
                                  ((nb095_alpha_dummy_259 D R S_cls E),
                                    (nb095_alpha_dummy_260 x R)),
                                  ((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
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
                                  (nb095_alpha_dummy_263 D R S_cls E) ≠
                                    (nb095_alpha_dummy_267 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_267;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R) from
                                  (by
                                    unfold nb095_alpha_dummy_268;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_263 D R S_cls E) ≠
                                      (nb095_alpha_dummy_267 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_267;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                    from (by
                                      unfold nb095_alpha_dummy_268;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_267 D R S_cls E),
                                    (nb095_alpha_dummy_268 x R)),
                                  ((nb095_alpha_dummy_263 D R S_cls E),
                                    (nb095_alpha_dummy_265 x R)),
                                  ((nb095_alpha_dummy_264 D R S_cls E),
                                    (nb095_alpha_dummy_266 x R)),
                                  ((nb095_alpha_dummy_289 D R S_cls E),
                                    (nb095_alpha_dummy_290 x R)),
                                  ((nb095_alpha_dummy_287 D R S_cls E),
                                    (nb095_alpha_dummy_288 x R)),
                                  ((nb095_alpha_dummy_256 D R S_cls E),
                                    (nb095_alpha_dummy_258 x R)),
                                  ((nb095_alpha_dummy_255 D R S_cls E),
                                    (nb095_alpha_dummy_257 x R)),
                                  ((nb095_alpha_dummy_285 D R S_cls E),
                                    (nb095_alpha_dummy_286 x R)),
                                  ((nb095_alpha_dummy_259 D R S_cls E),
                                    (nb095_alpha_dummy_260 x R)),
                                  ((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                            (nb095_alpha_dummy_263 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_263;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_265 x R) from (by
                            unfold nb095_alpha_dummy_265;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0265 x R) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                              (nb095_alpha_dummy_264 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_266 x R) from
                            (by
                              unfold nb095_alpha_dummy_266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0265 x R) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                                (nb095_alpha_dummy_289 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_289;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0294 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_290 x R) from (by
                                unfold nb095_alpha_dummy_290;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0295 x R) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                                  (nb095_alpha_dummy_287 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_287;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0292 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_288 x R) from
                                (by
                                  unfold nb095_alpha_dummy_288;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0293 x R)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_258 x R))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_270 D R S_cls E) from (by
          unfold nb095_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_273 x R) from (by
          unfold nb095_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_269 D R S_cls E) from (by
          unfold nb095_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_272 x R) from (by
          unfold nb095_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_267 D R S_cls E) from (by
          unfold nb095_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0266 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R) from (by
          unfold nb095_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0267 x R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_289 D R S_cls E), (nb095_alpha_dummy_290 x R)),
        ((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_278 x R) from (by
          unfold
            nb095_alpha_dummy_278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_275 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_276 x R) from (by
          unfold
            nb095_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_289 D R S_cls E), (nb095_alpha_dummy_290 x R)),
        ((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_263 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270 D
        R S_cls E) ≠ (nb095_alpha_dummy_281 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_282 x R) from (by
          unfold
            nb095_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_281
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_282 x R) from (by
          unfold
            nb095_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_273 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271 D
        R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_284 x R) from (by
          unfold
            nb095_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271 D
        R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_284 x R) from (by
          unfold
            nb095_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠
        (nb095_alpha_dummy_279 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_274 x R) ≠ (nb095_alpha_dummy_280 x R) from (by
          unfold
            nb095_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_263 D R S_cls E) ≠
                                      (nb095_alpha_dummy_267 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_267;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                    from (by
                                      unfold nb095_alpha_dummy_268;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_267 D R S_cls E),
                                    (nb095_alpha_dummy_268 x R)),
                                  ((nb095_alpha_dummy_263 D R S_cls E),
                                    (nb095_alpha_dummy_265 x R)),
                                  ((nb095_alpha_dummy_264 D R S_cls E),
                                    (nb095_alpha_dummy_266 x R)),
                                  ((nb095_alpha_dummy_289 D R S_cls E),
                                    (nb095_alpha_dummy_290 x R)),
                                  ((nb095_alpha_dummy_287 D R S_cls E),
                                    (nb095_alpha_dummy_288 x R)),
                                  ((nb095_alpha_dummy_256 D R S_cls E),
                                    (nb095_alpha_dummy_258 x R)),
                                  ((nb095_alpha_dummy_255 D R S_cls E),
                                    (nb095_alpha_dummy_257 x R)),
                                  ((nb095_alpha_dummy_285 D R S_cls E),
                                    (nb095_alpha_dummy_286 x R)),
                                  ((nb095_alpha_dummy_259 D R S_cls E),
                                    (nb095_alpha_dummy_260 x R)),
                                  ((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
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
                                  (nb095_alpha_dummy_263 D R S_cls E) ≠
                                    (nb095_alpha_dummy_267 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_267;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R) from
                                  (by
                                    unfold nb095_alpha_dummy_268;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_263 D R S_cls E) ≠
                                      (nb095_alpha_dummy_267 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_267;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                    from (by
                                      unfold nb095_alpha_dummy_268;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_267 D R S_cls E),
                                    (nb095_alpha_dummy_268 x R)),
                                  ((nb095_alpha_dummy_263 D R S_cls E),
                                    (nb095_alpha_dummy_265 x R)),
                                  ((nb095_alpha_dummy_264 D R S_cls E),
                                    (nb095_alpha_dummy_266 x R)),
                                  ((nb095_alpha_dummy_289 D R S_cls E),
                                    (nb095_alpha_dummy_290 x R)),
                                  ((nb095_alpha_dummy_287 D R S_cls E),
                                    (nb095_alpha_dummy_288 x R)),
                                  ((nb095_alpha_dummy_256 D R S_cls E),
                                    (nb095_alpha_dummy_258 x R)),
                                  ((nb095_alpha_dummy_255 D R S_cls E),
                                    (nb095_alpha_dummy_257 x R)),
                                  ((nb095_alpha_dummy_285 D R S_cls E),
                                    (nb095_alpha_dummy_286 x R)),
                                  ((nb095_alpha_dummy_259 D R S_cls E),
                                    (nb095_alpha_dummy_260 x R)),
                                  ((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

theorem nb095_focused_notmem_0050 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_1510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0050 D R S_cls E)
      (nb095_compact_fv_empty_0436 D R S_cls E))

theorem nb095_focused_notmem_0051 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_1511 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  by
  simpa only [nb095_alpha_dummy_006, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0051 x u D R S_cls f E)
      (nb095_compact_fv_empty_0437 x u D R S_cls f E))

theorem nb095_compact_envfresh_0282 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_250 D R S_cls E) (nb095_alpha_dummy_252 x R)
      (nb095_wpp_notmem_0738 D R S_cls E) (nb095_wpp_notmem_0739 x R)
      (TEnvFresh.consFresh (nb095_alpha_dummy_249 D R S_cls E) (nb095_alpha_dummy_251 x R)
        (nb095_wpp_notmem_0740 D R S_cls E) (nb095_wpp_notmem_0741 x R)
        (TEnvFresh.consFresh (nb095_alpha_dummy_247 D R S_cls E)
          (nb095_alpha_dummy_248 x D R) (nb095_wpp_notmem_0742 D R S_cls E)
          (nb095_wpp_notmem_0743 x D R) (TEnvFresh.consFresh (nb095_alpha_dummy_245 D R S_cls E)
            (nb095_alpha_dummy_246 x D R) (nb095_wpp_notmem_0744 D R S_cls E)
            (nb095_wpp_notmem_0745 x D R)
            (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
              (nb095_alpha_dummy_006 x u D R S_cls f E) (nb095_wpp_notmem_1510 D R S_cls E)
              (nb095_wpp_notmem_1511 x u D R S_cls f E)
              (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
                (nb095_alpha_dummy_005 x u D R S_cls f E) (nb095_wpp_notmem_1500 D R S_cls E)
                (nb095_wpp_notmem_1501 x u D R S_cls f E)
                (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
                  (nb095_wpp_notmem_0746 D R S_cls E) (nb095_wpp_notmem_0747 u R dv_R_u)
                  (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                    (nb095_wpp_notmem_0748 D R S_cls E) (nb095_wpp_notmem_0749 x R dv_R_x)
                    (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                      (nb095_wpp_notmem_0750 D R S_cls E) (nb095_wpp_notmem_0751 R f dv_R_f)
                      (TEnvFresh.nil ((syn_ccnv (syn_cdif R (syn_cid)))).fv))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
