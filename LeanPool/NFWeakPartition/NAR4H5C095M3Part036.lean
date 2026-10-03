/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C095M3Part036Block001


/-! NF weak partition development: NAR4H5C095M3Part036. -/


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
noncomputable def nb095_split_alpha_0081 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_261 D R S_cls E), (nb095_alpha_dummy_262 x R)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_261 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_261 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_255 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_256 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_255 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_256 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_262 x R))
          (Class.cab (nb095_alpha_dummy_257 x R)
            (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_262 x R))
            (Class.cab (nb095_alpha_dummy_257 x R)
              (syn_wrex (nb095_alpha_dummy_258 x R) (Class.cv (nb095_alpha_dummy_252 x R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_257 x R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_258 x R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                      (nb095_alpha_dummy_256 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_256;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
                      unfold nb095_alpha_dummy_258;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0260 x R) 1)))) (TAlphaVar.there
                    (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                        (nb095_alpha_dummy_255 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_255;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
                        unfold nb095_alpha_dummy_257;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                          (nb095_alpha_dummy_261 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_261;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0262 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_262 x R) from (by
                          unfold nb095_alpha_dummy_262;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0263 x R) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                            (nb095_alpha_dummy_259 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_259;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0259 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
                            unfold nb095_alpha_dummy_260;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0261 x R) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_256 D R S_cls E) ≠
                              (nb095_alpha_dummy_263 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_265 x R) from
                            (by
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
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0264 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_266 x R) from (by
                                unfold nb095_alpha_dummy_266;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0265 x R) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_258 x R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_263 D R S_cls E) ≠
        (nb095_alpha_dummy_270 D R S_cls E) from (by
          unfold nb095_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls
                    E)
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
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_272 x R) from (by
          unfold nb095_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_263 D R S_cls E) ≠
        (nb095_alpha_dummy_267 D R S_cls E) from (by
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
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_261 D R S_cls E), (nb095_alpha_dummy_262 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270
        D R S_cls E) ≠ (nb095_alpha_dummy_277 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_261 D R S_cls E), (nb095_alpha_dummy_262 x R)),
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
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270
        D R S_cls E) ≠ (nb095_alpha_dummy_281 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271
        D R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271
        D R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls
                    E)
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
                    D R
                    S_cls E)
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
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_267 D R S_cls E),
                                      (nb095_alpha_dummy_268 x R)),
                                    ((nb095_alpha_dummy_263 D R S_cls E),
                                      (nb095_alpha_dummy_265 x R)),
                                    ((nb095_alpha_dummy_264 D R S_cls E),
                                      (nb095_alpha_dummy_266 x R)),
                                    ((nb095_alpha_dummy_256 D R S_cls E),
                                      (nb095_alpha_dummy_258 x R)),
                                    ((nb095_alpha_dummy_255 D R S_cls E),
                                      (nb095_alpha_dummy_257 x R)),
                                    ((nb095_alpha_dummy_261 D R S_cls E),
                                      (nb095_alpha_dummy_262 x R)),
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
                                    (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                    from (by
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
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_267 D R S_cls E),
                                      (nb095_alpha_dummy_268 x R)),
                                    ((nb095_alpha_dummy_263 D R S_cls E),
                                      (nb095_alpha_dummy_265 x R)),
                                    ((nb095_alpha_dummy_264 D R S_cls E),
                                      (nb095_alpha_dummy_266 x R)),
                                    ((nb095_alpha_dummy_256 D R S_cls E),
                                      (nb095_alpha_dummy_258 x R)),
                                    ((nb095_alpha_dummy_255 D R S_cls E),
                                      (nb095_alpha_dummy_257 x R)),
                                    ((nb095_alpha_dummy_261 D R S_cls E),
                                      (nb095_alpha_dummy_262 x R)),
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
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                        (nb095_alpha_dummy_256 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_256;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
                        unfold nb095_alpha_dummy_258;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0260 x R) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                          (nb095_alpha_dummy_255 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_255;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
                          unfold nb095_alpha_dummy_257;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                            (nb095_alpha_dummy_261 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_261;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0262 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_262 x R) from (by
                            unfold nb095_alpha_dummy_262;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0263 x R) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_250 D R S_cls E) ≠
                              (nb095_alpha_dummy_259 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_259;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0259 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_252 x R) ≠ (nb095_alpha_dummy_260 x R) from
                            (by
                              unfold nb095_alpha_dummy_260;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0261 x R) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_250 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_256 D R S_cls E) ≠
                                (nb095_alpha_dummy_263 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0264 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_265 x R) from (by
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
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0264 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_258 x R) ≠ (nb095_alpha_dummy_266 x R) from
                                (by
                                  unfold nb095_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0265 x R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_256 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_258 x R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_263 D R S_cls E) ≠ (nb095_alpha_dummy_270 D R S_cls E) from (by
          unfold nb095_alpha_dummy_270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_273 x R) from (by
          unfold nb095_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_263 D R S_cls E) ≠
        (nb095_alpha_dummy_269 D R S_cls E) from (by
          unfold nb095_alpha_dummy_269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_272 x R) from (by
          unfold nb095_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_263 D R S_cls E) ≠
        (nb095_alpha_dummy_267 D R S_cls E) from (by
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
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_271 D R S_cls E), (nb095_alpha_dummy_274 x R)),
        ((nb095_alpha_dummy_270 D R S_cls E), (nb095_alpha_dummy_273 x R)),
        ((nb095_alpha_dummy_269 D R S_cls E), (nb095_alpha_dummy_272 x R)),
        ((nb095_alpha_dummy_267 D R S_cls E), (nb095_alpha_dummy_268 x R)),
        ((nb095_alpha_dummy_263 D R S_cls E), (nb095_alpha_dummy_265 x R)),
        ((nb095_alpha_dummy_264 D R S_cls E), (nb095_alpha_dummy_266 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_261 D R S_cls E), (nb095_alpha_dummy_262 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270
        D R S_cls E) ≠ (nb095_alpha_dummy_277 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_271 D R S_cls E) ≠ (nb095_alpha_dummy_277
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_261 D R S_cls E), (nb095_alpha_dummy_262 x R)),
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
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_263 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_270
        D R S_cls E) ≠ (nb095_alpha_dummy_281 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_270 D R S_cls E) ≠ (nb095_alpha_dummy_281
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        (nb095_alpha_dummy_265 x R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271
        D R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_271
        D R S_cls E) ≠ (nb095_alpha_dummy_283 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R
                    S_cls E)
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
                    D R
                    S_cls
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
                                                  (nb095_support_mem_0266 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_265 x R) ≠
        (nb095_alpha_dummy_268 x R) from (by
                                          unfold nb095_alpha_dummy_268;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0267 x R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_267 D R S_cls E),
                                        (nb095_alpha_dummy_268 x R)),
                                      ((nb095_alpha_dummy_263 D R S_cls E),
                                        (nb095_alpha_dummy_265 x R)),
                                      ((nb095_alpha_dummy_264 D R S_cls E),
                                        (nb095_alpha_dummy_266 x R)),
                                      ((nb095_alpha_dummy_256 D R S_cls E),
                                        (nb095_alpha_dummy_258 x R)),
                                      ((nb095_alpha_dummy_255 D R S_cls E),
                                        (nb095_alpha_dummy_257 x R)),
                                      ((nb095_alpha_dummy_261 D R S_cls E),
                                        (nb095_alpha_dummy_262 x R)),
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
                                      (nb095_alpha_dummy_265 x R) ≠ (nb095_alpha_dummy_268 x R)
                                      from (by
                                        unfold nb095_alpha_dummy_268;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_263 D R S_cls E) ≠
        (nb095_alpha_dummy_267 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_267;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0266 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_265 x R) ≠
        (nb095_alpha_dummy_268 x R) from (by
                                          unfold nb095_alpha_dummy_268;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0267 x R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_267 D R S_cls E),
                                        (nb095_alpha_dummy_268 x R)),
                                      ((nb095_alpha_dummy_263 D R S_cls E),
                                        (nb095_alpha_dummy_265 x R)),
                                      ((nb095_alpha_dummy_264 D R S_cls E),
                                        (nb095_alpha_dummy_266 x R)),
                                      ((nb095_alpha_dummy_256 D R S_cls E),
                                        (nb095_alpha_dummy_258 x R)),
                                      ((nb095_alpha_dummy_255 D R S_cls E),
                                        (nb095_alpha_dummy_257 x R)),
                                      ((nb095_alpha_dummy_261 D R S_cls E),
                                        (nb095_alpha_dummy_262 x R)),
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
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
