/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C078C001Part057

/-! NF weak partition development: NAR4C078C001Part059. -/


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
noncomputable def nb078_split_alpha_0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
        ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)),
        ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_248))
          (Class.cv (nb078_alpha_dummy_243))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_250 f))
          (Class.cv (nb078_alpha_dummy_245 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_248) from (by
              unfold nb078_alpha_dummy_248;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
          (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_250 f) from (by
              unfold nb078_alpha_dummy_250;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_247) from (by
                unfold nb078_alpha_dummy_247;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
            (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_249 f) from (by
                unfold nb078_alpha_dummy_249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_277) from (by
                  unfold nb078_alpha_dummy_277;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0282) 0))))
              (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_278 f) from (by
                  unfold nb078_alpha_dummy_278;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0283 f) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_251) from (by
                    unfold nb078_alpha_dummy_251;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0279) 0))))
                (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_252 f) from (by
                    unfold nb078_alpha_dummy_252;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0281 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_244))).fv ∪
                ((Class.cv (nb078_alpha_dummy_243))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
                ((Class.cv (nb078_alpha_dummy_245 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_255) from (by
                                        unfold nb078_alpha_dummy_255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                0)))) (show (nb078_alpha_dummy_250 f) ≠
                                        (nb078_alpha_dummy_257 f) from (by
                                        unfold nb078_alpha_dummy_257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_256) from
                                        (by
                                          unfold nb078_alpha_dummy_256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0256)
                                                  1)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_258 f) from (by
                                          unfold nb078_alpha_dummy_258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0257 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_248) ≠
        (nb078_alpha_dummy_281) from (by
          unfold nb078_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0286) 0)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_282 f) from (by
          unfold nb078_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0287 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_279) from (by
          unfold nb078_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0284) 0)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_280 f) from (by
          unfold nb078_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0285 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_248))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_250 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_262) from (by
          unfold nb078_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_265 f) from (by
          unfold nb078_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_261)
        from (by
          unfold nb078_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_264 f) from (by
          unfold nb078_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold
            nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_260 f) from (by
          unfold
            nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279),
        (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
        ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277),
        (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243),
        (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279),
        (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
        ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277),
        (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243),
        (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠
        (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)),
        ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256),
        (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)),
        ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)),
        ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256),
        (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)),
        ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_255) from (by
                                        unfold nb078_alpha_dummy_255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                0)))) (show (nb078_alpha_dummy_250 f) ≠
                                        (nb078_alpha_dummy_257 f) from (by
                                        unfold nb078_alpha_dummy_257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_256) from
                                        (by
                                          unfold nb078_alpha_dummy_256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0256)
                                                  1)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_258 f) from (by
                                          unfold nb078_alpha_dummy_258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0257 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_248) ≠
        (nb078_alpha_dummy_281) from (by
          unfold nb078_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0286) 0)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_282 f) from (by
          unfold nb078_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0287 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_279) from (by
          unfold nb078_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0284) 0)))) (show (nb078_alpha_dummy_250 f) ≠
        (nb078_alpha_dummy_280 f) from (by
          unfold nb078_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0285 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_248))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_250 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_262) from (by
          unfold nb078_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_265 f) from (by
          unfold nb078_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_261)
        from (by
          unfold nb078_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_264 f) from (by
          unfold nb078_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold
            nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_260 f) from (by
          unfold
            nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279),
        (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
        ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277),
        (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243),
        (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279),
        (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
        ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277),
        (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243),
        (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠
        (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)),
        ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256),
        (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)),
        ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)),
        ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256),
        (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)),
        ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)),
                    ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)),
                    ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
                    ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)),
                    ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
                    ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
                    ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb078_split_alpha_0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)),
        ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_251)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_251)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_247)
                (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_252 f)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_252 f)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_249 f)
                (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_248) from (by
                              unfold nb078_alpha_dummy_248;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0250) 1))))
                          (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_250 f) from (by
                              unfold nb078_alpha_dummy_250;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_247) from (by
                                unfold nb078_alpha_dummy_247;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0250) 0))))
                            (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_249 f) from (by
                                unfold nb078_alpha_dummy_249;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_253) from (by
                                  unfold nb078_alpha_dummy_253;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0254) 0))))
                              (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_254 f) from
                                (by
                                  unfold nb078_alpha_dummy_254;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0255 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_251) from (by
                                    unfold nb078_alpha_dummy_251;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0251) 0)))) (show
                                  (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_252 f) from (by
                                    unfold nb078_alpha_dummy_252;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0253 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_244))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_243))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_245 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_255) from
                                    (by
                                      unfold nb078_alpha_dummy_255;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0256)
                                              0)))) (show
                                    (nb078_alpha_dummy_250 f) ≠ (nb078_alpha_dummy_257 f) from
                                    (by
                                      unfold nb078_alpha_dummy_257;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0257 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_256) from (by
                                        unfold nb078_alpha_dummy_256;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                1)))) (show (nb078_alpha_dummy_250 f) ≠
                                        (nb078_alpha_dummy_258 f) from (by
                                        unfold nb078_alpha_dummy_258;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_248))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_250 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_262) from (by
          unfold nb078_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_265 f) from (by
          unfold nb078_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_261)
        from (by
          unfold nb078_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_264 f) from (by
          unfold nb078_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247),
        (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)),
        ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244),
        (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247),
        (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)),
        ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244),
        (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠
        (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259),
        (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)),
        ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠
        (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259),
        (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)),
        ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_248) from (by
                              unfold nb078_alpha_dummy_248;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0250) 1))))
                          (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_250 f) from (by
                              unfold nb078_alpha_dummy_250;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_247) from (by
                                unfold nb078_alpha_dummy_247;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0250) 0))))
                            (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_249 f) from (by
                                unfold nb078_alpha_dummy_249;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_253) from (by
                                  unfold nb078_alpha_dummy_253;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0254) 0))))
                              (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_254 f) from
                                (by
                                  unfold nb078_alpha_dummy_254;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0255 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_251) from (by
                                    unfold nb078_alpha_dummy_251;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0251) 0)))) (show
                                  (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_252 f) from (by
                                    unfold nb078_alpha_dummy_252;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0253 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_244))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_243))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_245 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_255) from
                                    (by
                                      unfold nb078_alpha_dummy_255;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0256)
                                              0)))) (show
                                    (nb078_alpha_dummy_250 f) ≠ (nb078_alpha_dummy_257 f) from
                                    (by
                                      unfold nb078_alpha_dummy_257;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0257 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_248) ≠ (nb078_alpha_dummy_256) from (by
                                        unfold nb078_alpha_dummy_256;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                1)))) (show (nb078_alpha_dummy_250 f) ≠
                                        (nb078_alpha_dummy_258 f) from (by
                                        unfold nb078_alpha_dummy_258;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_248))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_250 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_262) from (by
          unfold nb078_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_265 f) from (by
          unfold nb078_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_261)
        from (by
          unfold nb078_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_264 f) from (by
          unfold nb078_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259)
        from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247),
        (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)),
        ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244),
        (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_269) from (by
          unfold
            nb078_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_270 f) from (by
          unfold
            nb078_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_267)
        from (by
          unfold
            nb078_alpha_dummy_267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_268 f) from (by
          unfold
            nb078_alpha_dummy_268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262),
        (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)),
        ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255),
        (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)),
        ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247),
        (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)),
        ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244),
        (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠
        (nb078_alpha_dummy_273) from (by
          unfold
            nb078_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_274 f) from (by
          unfold
            nb078_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠
        (nb078_alpha_dummy_275) from (by
          unfold
            nb078_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_276 f) from (by
          unfold
            nb078_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_263) ≠ (nb078_alpha_dummy_271)
        from (by
          unfold
            nb078_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078_alpha_dummy_266 f) ≠ (nb078_alpha_dummy_272 f) from (by
          unfold
            nb078_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259),
        (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)),
        ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_255) ≠
        (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_259) from (by
          unfold nb078_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078_alpha_dummy_257 f) ≠
        (nb078_alpha_dummy_260 f) from (by
          unfold nb078_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_259),
        (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)),
        ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248),
        (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)),
        ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251),
        (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
        ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0028 x y f)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0028 x y f)))))))))))

theorem nb078_compact_fv_empty_0240 : (nb078_alpha_dummy_285) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0241 (g : Var) :
    (nb078_alpha_dummy_286 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0242 : (nb078_alpha_dummy_283) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0243 (g : Var) :
    (nb078_alpha_dummy_284 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0244 : (nb078_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
