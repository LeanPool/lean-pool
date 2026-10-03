/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part047`. -/


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
noncomputable def nb090_split_alpha_0024 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
        ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)),
        ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_248 A))
          (Class.cv (nb090_alpha_dummy_243 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_250 h))
          (Class.cv (nb090_alpha_dummy_245 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_248 A) from (by
              unfold nb090_alpha_dummy_248;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
          (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_250 h) from (by
              unfold nb090_alpha_dummy_250;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
          (TAlphaVar.there (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_247 A) from (by
                unfold nb090_alpha_dummy_247;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
            (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_249 h) from (by
                unfold nb090_alpha_dummy_249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
            (TAlphaVar.there (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_277 A) from
                (by
                  unfold nb090_alpha_dummy_277;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0284 A) 0))))
              (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_278 h) from (by
                  unfold nb090_alpha_dummy_278;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0285 h) 0))))
              (TAlphaVar.there (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_251 A) from
                  (by
                    unfold nb090_alpha_dummy_251;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0281 A) 0))))
                (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_252 h) from (by
                    unfold nb090_alpha_dummy_252;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0283 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv)
                    (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
                ((Class.cv (nb090_alpha_dummy_243 A))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
                ((Class.cv (nb090_alpha_dummy_245 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_255 A) from
                                      (by
                                        unfold nb090_alpha_dummy_255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0258 A)
                                                0)))) (show (nb090_alpha_dummy_250 h) ≠
                                        (nb090_alpha_dummy_257 h) from (by
                                        unfold nb090_alpha_dummy_257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0259 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_256 A)
                                        from (by
                                          unfold nb090_alpha_dummy_256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0258 A) 1)))) (show
                                        (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_258 h)
                                        from (by
                                          unfold nb090_alpha_dummy_258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0259 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_248 A) ≠
        (nb090_alpha_dummy_281 A) from (by
          unfold nb090_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0288 A) 0)))) (show (nb090_alpha_dummy_250 h) ≠
        (nb090_alpha_dummy_282 h) from (by
          unfold nb090_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0289 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_279 A) from (by
          unfold nb090_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0286 A) 0)))) (show (nb090_alpha_dummy_250 h) ≠
        (nb090_alpha_dummy_280 h) from (by
          unfold nb090_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0287 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_262 A) from (by
          unfold nb090_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  1)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_265 h) from (by
          unfold nb090_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_261 A) from (by
          unfold nb090_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_264 h) from (by
          unfold nb090_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold
            nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_260 h) from (by
          unfold
            nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A),
        (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)),
        ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A),
        (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)),
        ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A),
        (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
        ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A),
        (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A),
        (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)),
        ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A),
        (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)),
        ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A),
        (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
        ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A),
        (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_273 A) from (by
          unfold
            nb090_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_274 h) from (by
          unfold
            nb090_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262
        A) ≠ (nb090_alpha_dummy_273 A) from (by
          unfold
            nb090_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_274 h) from (by
          unfold
            nb090_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_275 A) from (by
          unfold
            nb090_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_276 h) from (by
          unfold
            nb090_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_275 A) from (by
          unfold
            nb090_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_276 h) from (by
          unfold
            nb090_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)),
        ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A),
        (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)),
        ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)),
        ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A),
        (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)),
        ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_255 A) from
                                      (by
                                        unfold nb090_alpha_dummy_255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0258 A)
                                                0)))) (show (nb090_alpha_dummy_250 h) ≠
                                        (nb090_alpha_dummy_257 h) from (by
                                        unfold nb090_alpha_dummy_257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0259 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_256 A)
                                        from (by
                                          unfold nb090_alpha_dummy_256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0258 A) 1)))) (show
                                        (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_258 h)
                                        from (by
                                          unfold nb090_alpha_dummy_258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0259 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_248 A) ≠
        (nb090_alpha_dummy_281 A) from (by
          unfold nb090_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0288 A) 0)))) (show (nb090_alpha_dummy_250 h) ≠
        (nb090_alpha_dummy_282 h) from (by
          unfold nb090_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0289 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_279 A) from (by
          unfold nb090_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0286 A) 0)))) (show (nb090_alpha_dummy_250 h) ≠
        (nb090_alpha_dummy_280 h) from (by
          unfold nb090_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0287 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_262 A) from (by
          unfold nb090_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  1)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_265 h) from (by
          unfold nb090_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_261 A) from (by
          unfold nb090_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_264 h) from (by
          unfold nb090_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold
            nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_260 h) from (by
          unfold
            nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A),
        (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)),
        ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A),
        (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)),
        ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A),
        (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
        ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A),
        (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0266
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0267
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0264
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0265
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_269 A) from (by
          unfold
            nb090_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0270
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_270 h) from (by
          unfold
            nb090_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0271
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_267 A) from (by
          unfold
            nb090_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0268
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_268 h) from (by
          unfold
            nb090_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0269
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A),
        (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)),
        ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A),
        (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)),
        ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A),
        (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
        ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A),
        (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_273 A) from (by
          unfold
            nb090_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_274 h) from (by
          unfold
            nb090_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262
        A) ≠ (nb090_alpha_dummy_273 A) from (by
          unfold
            nb090_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0274
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_274 h) from (by
          unfold
            nb090_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0275
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0272
                    A)
                  0)))) (show (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0273
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_275 A) from (by
          unfold
            nb090_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_276 h) from (by
          unfold
            nb090_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263
        A) ≠ (nb090_alpha_dummy_275 A) from (by
          unfold
            nb090_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0278
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_276 h) from (by
          unfold
            nb090_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0279
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_271 A) from (by
          unfold
            nb090_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0276
                    A)
                  0)))) (show (nb090_alpha_dummy_266 h) ≠ (nb090_alpha_dummy_272 h) from (by
          unfold
            nb090_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0277
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)),
        ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A),
        (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)),
        ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260 A) 0)))) (show (nb090_alpha_dummy_257 h) ≠
        (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)),
        ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A),
        (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)),
        ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)),
                    ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)),
                    ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
                    ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)),
                    ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
                    ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                    ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                    ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                    ((nb090_alpha_dummy_001 A), u),
                    ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part048`. -/


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
noncomputable def nb090_split_alpha_0025 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
          (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
          (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                      unfold nb090_alpha_dummy_136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                      unfold nb090_alpha_dummy_138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                        unfold nb090_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                        unfold nb090_alpha_dummy_137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                          unfold nb090_alpha_dummy_141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                          unfold nb090_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                            unfold nb090_alpha_dummy_139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                            unfold nb090_alpha_dummy_140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                              unfold nb090_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                              unfold nb090_alpha_dummy_145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                                unfold nb090_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                                unfold nb090_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                    ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                    ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                        unfold nb090_alpha_dummy_136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                        unfold nb090_alpha_dummy_138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                          unfold nb090_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                          unfold nb090_alpha_dummy_137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                            unfold nb090_alpha_dummy_141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                            unfold nb090_alpha_dummy_142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                              unfold nb090_alpha_dummy_139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                              unfold nb090_alpha_dummy_140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                                unfold nb090_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                                unfold nb090_alpha_dummy_145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from
                                (by
                                  unfold nb090_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from
                                (by
                                  unfold nb090_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                      ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                      ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part049`. -/


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
noncomputable def nb090_split_alpha_0026 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_167 A))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_168 h))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                            unfold nb090_alpha_dummy_143;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                            unfold nb090_alpha_dummy_145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                              unfold nb090_alpha_dummy_144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                              unfold nb090_alpha_dummy_146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                                unfold nb090_alpha_dummy_169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                                unfold nb090_alpha_dummy_170;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from
                                (by
                                  unfold nb090_alpha_dummy_167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from
                                (by
                                  unfold nb090_alpha_dummy_168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                  ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                  ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                  ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                  ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                  ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                  ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                  ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                  ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                  ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                  ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                  ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                  ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                  ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                    unfold nb090_alpha_dummy_147;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0134 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                    unfold nb090_alpha_dummy_148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0135 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                  ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                  ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                  ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                  ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                  ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                  ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                  ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                  ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                  ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                  ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                  ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                  ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                  ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                            unfold nb090_alpha_dummy_143;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                            unfold nb090_alpha_dummy_145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                              unfold nb090_alpha_dummy_144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                              unfold nb090_alpha_dummy_146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                                unfold nb090_alpha_dummy_169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                                unfold nb090_alpha_dummy_170;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from
                                (by
                                  unfold nb090_alpha_dummy_167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from
                                (by
                                  unfold nb090_alpha_dummy_168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                  ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                  ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                  ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                  ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                  ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                  ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                  ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                  ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                  ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                  ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                  ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                  ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                  ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                    unfold nb090_alpha_dummy_147;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0134 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                    unfold nb090_alpha_dummy_148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0135 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                  ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                  ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                  ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                  ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                  ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                  ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                  ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                  ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                  ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                  ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                  ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                  ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                                  ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
