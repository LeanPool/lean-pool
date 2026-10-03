/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part031`. -/


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
noncomputable def nb067_split_alpha_0077 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_213))
          (Class.cv (nb067_alpha_dummy_206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_214))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f))
          (Class.cv (nb067_alpha_dummy_208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_216 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_213) from (by
              unfold nb067_alpha_dummy_213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_215 f) from (by
              unfold nb067_alpha_dummy_215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
                unfold nb067_alpha_dummy_214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_216 f) from (by
                unfold nb067_alpha_dummy_216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_220) from (by
                                  unfold nb067_alpha_dummy_220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_223 f) from
                                (by
                                  unfold nb067_alpha_dummy_223;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_219) from (by
                                    unfold nb067_alpha_dummy_219;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_222 f) from (by
                                    unfold nb067_alpha_dummy_222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                                    (by
                                      unfold nb067_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from
                                    (by
                                      unfold nb067_alpha_dummy_218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
                                  ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
                                  ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
                                  ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                                  ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                                  ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                                  ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                                  ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                                  ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                                  ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                                  ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                                  ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0076 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                      (by
                        unfold nb067_alpha_dummy_217;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                    (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                        unfold nb067_alpha_dummy_218;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0078 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
        ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
        ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
        ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
        ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_219))
            (syn_cun (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_222 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_223 f))
              (Class.cv (nb067_alpha_dummy_224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
          ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
          ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0079 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
        ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_213))
          (Class.cv (nb067_alpha_dummy_206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_214))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f))
          (Class.cv (nb067_alpha_dummy_208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_216 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_213) from (by
              unfold nb067_alpha_dummy_213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_215 f) from (by
              unfold nb067_alpha_dummy_215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
                unfold nb067_alpha_dummy_214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_216 f) from (by
                unfold nb067_alpha_dummy_216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_239) from (by
                  unfold nb067_alpha_dummy_239;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0250) 0))))
              (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_240 f) from (by
                  unfold nb067_alpha_dummy_240;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0251 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_237) from (by
                    unfold nb067_alpha_dummy_237;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0248) 0))))
                (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_238 f) from (by
                    unfold nb067_alpha_dummy_238;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0249 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_220) from (by
                                  unfold nb067_alpha_dummy_220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_223 f) from
                                (by
                                  unfold nb067_alpha_dummy_223;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_219) from (by
                                    unfold nb067_alpha_dummy_219;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_222 f) from (by
                                    unfold nb067_alpha_dummy_222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                                    (by
                                      unfold nb067_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from
                                    (by
                                      unfold nb067_alpha_dummy_218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
                                  ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
                                  ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
                                  ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                                  ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                                  ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                                  ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
                                  ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                                  ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                                  ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                                  ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                                  ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                                  ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                                  ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0078 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
                      ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                      (by
                        unfold nb067_alpha_dummy_217;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                    (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                        unfold nb067_alpha_dummy_218;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
                      ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0080 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_235))
          (Class.cab (nb067_alpha_dummy_205)
            (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_235))
            (Class.cab (nb067_alpha_dummy_205)
              (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_236 f))
          (Class.cab (nb067_alpha_dummy_207 f)
            (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_236 f))
            (Class.cab (nb067_alpha_dummy_207 f)
              (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_206) from
                    (by
                      unfold nb067_alpha_dummy_206;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))))
                  (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_208 f) from (by
                      unfold nb067_alpha_dummy_208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_205) from
                      (by
                        unfold nb067_alpha_dummy_205;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))))
                    (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_207 f) from (by
                        unfold nb067_alpha_dummy_207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0244 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_235) from (by
                          unfold nb067_alpha_dummy_235;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0246) 0))))
                      (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_236 f) from (by
                          unfold nb067_alpha_dummy_236;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0247 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_209) from (by
                            unfold nb067_alpha_dummy_209;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0243) 0))))
                        (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_210 f) from (by
                            unfold nb067_alpha_dummy_210;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0245 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0079 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0079 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                          ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_206) from
                      (by
                        unfold nb067_alpha_dummy_206;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))))
                    (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_208 f) from (by
                        unfold nb067_alpha_dummy_208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0244 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_205) from (by
                          unfold nb067_alpha_dummy_205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0242) 0))))
                      (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_207 f) from (by
                          unfold nb067_alpha_dummy_207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0244 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_235) from (by
                            unfold nb067_alpha_dummy_235;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0246) 0))))
                        (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_236 f) from (by
                            unfold nb067_alpha_dummy_236;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0247 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_209) from (by
                              unfold nb067_alpha_dummy_209;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0243) 0))))
                          (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_210 f) from (by
                              unfold nb067_alpha_dummy_210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0245 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0079 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0079 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                            ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                            ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                            ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                            ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                            ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                            ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                            ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                            ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                            ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0081 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb067_alpha_dummy_167))
          (syn_cop (Class.cv (nb067_alpha_dummy_163)) (Class.cv (nb067_alpha_dummy_164))))
        (Wff.neg (syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_163)))))
      (Wff.imp (Wff.classEq (Class.cv (nb067_alpha_dummy_168 f))
          (syn_cop (Class.cv (nb067_alpha_dummy_165 f)) (Class.cv (nb067_alpha_dummy_166 f))))
        (Wff.neg (syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_165 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_167) from (by
                unfold nb067_alpha_dummy_167;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0174) 0))))) (Ne.symm
            (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_168 f) from (by
                unfold nb067_alpha_dummy_168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0175 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_167) from
                (by
                  unfold nb067_alpha_dummy_167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0172) 0)))))
            (Ne.symm (show (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_168 f) from (by
                  unfold nb067_alpha_dummy_168;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0173 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_170) from
                                    (by
                                      unfold nb067_alpha_dummy_170;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0176)
                                              1)))) (show
                                    (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_172 f) from
                                    (by
                                      unfold nb067_alpha_dummy_172;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0178 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_169) from (by
                                        unfold nb067_alpha_dummy_169;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0176)
                                                0)))) (show (nb067_alpha_dummy_165 f) ≠
                                        (nb067_alpha_dummy_171 f) from (by
                                        unfold nb067_alpha_dummy_171;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0178 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_175) from
                                        (by
                                          unfold nb067_alpha_dummy_175;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0180)
                                                  0)))) (show (nb067_alpha_dummy_165 f) ≠
        (nb067_alpha_dummy_176 f) from (by
                                          unfold nb067_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0181 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_163) ≠
        (nb067_alpha_dummy_173) from (by
          unfold nb067_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0177) 0)))) (show (nb067_alpha_dummy_165 f) ≠
        (nb067_alpha_dummy_174 f) from (by
          unfold nb067_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0179 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0072 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_170) from
                                    (by
                                      unfold nb067_alpha_dummy_170;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0176)
                                              1)))) (show
                                    (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_172 f) from
                                    (by
                                      unfold nb067_alpha_dummy_172;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0178 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_169) from (by
                                        unfold nb067_alpha_dummy_169;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0176)
                                                0)))) (show (nb067_alpha_dummy_165 f) ≠
                                        (nb067_alpha_dummy_171 f) from (by
                                        unfold nb067_alpha_dummy_171;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0178 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_175) from
                                        (by
                                          unfold nb067_alpha_dummy_175;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0180)
                                                  0)))) (show (nb067_alpha_dummy_165 f) ≠
        (nb067_alpha_dummy_176 f) from (by
                                          unfold nb067_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0181 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_163) ≠
        (nb067_alpha_dummy_173) from (by
          unfold nb067_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0177) 0)))) (show (nb067_alpha_dummy_165 f) ≠
        (nb067_alpha_dummy_174 f) from (by
          unfold nb067_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0179 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0072 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0075 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_206) from (by
                                        unfold nb067_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0214)
                                                1)))) (show (nb067_alpha_dummy_166 f) ≠
                                        (nb067_alpha_dummy_208 f) from (by
                                        unfold nb067_alpha_dummy_208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_205) from
                                        (by
                                          unfold nb067_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0214)
                                                  0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_207 f) from (by
                                          unfold nb067_alpha_dummy_207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠
        (nb067_alpha_dummy_211) from (by
          unfold nb067_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0218) 0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_212 f) from (by
          unfold nb067_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_209) from (by
          unfold nb067_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0215) 0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_210 f) from (by
          unfold nb067_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0077 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_206) from (by
                                        unfold nb067_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0214)
                                                1)))) (show (nb067_alpha_dummy_166 f) ≠
                                        (nb067_alpha_dummy_208 f) from (by
                                        unfold nb067_alpha_dummy_208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_205) from
                                        (by
                                          unfold nb067_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0214)
                                                  0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_207 f) from (by
                                          unfold nb067_alpha_dummy_207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠
        (nb067_alpha_dummy_211) from (by
          unfold nb067_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0218) 0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_212 f) from (by
          unfold nb067_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_209) from (by
          unfold nb067_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0215) 0)))) (show (nb067_alpha_dummy_166 f) ≠
        (nb067_alpha_dummy_210 f) from (by
          unfold nb067_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0077 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0080 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_164) from (by
                unfold nb067_alpha_dummy_164;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 1))))
            (show f ≠ (nb067_alpha_dummy_166 f) from (by
                unfold nb067_alpha_dummy_166;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_163) from (by
                  unfold nb067_alpha_dummy_163;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 0))))
              (show f ≠ (nb067_alpha_dummy_165 f) from (by
                  unfold nb067_alpha_dummy_165;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_167) from (by
                    unfold nb067_alpha_dummy_167;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0260) 0))))
                (show f ≠ (nb067_alpha_dummy_168 f) from (by
                    unfold nb067_alpha_dummy_168;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0261 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_278) from
                    (by
                      unfold nb067_alpha_dummy_278;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0340) 1))))
                  (show f ≠ (nb067_alpha_dummy_280 f) from (by
                      unfold nb067_alpha_dummy_280;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0341 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_277) from
                      (by
                        unfold nb067_alpha_dummy_277;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0340) 0))))
                    (show f ≠ (nb067_alpha_dummy_279 f) from (by
                        unfold nb067_alpha_dummy_279;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0341 f) 0))))
                    (TAlphaVar.here _ _ _))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part032`. -/


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
noncomputable def nb067_split_alpha_0082 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (syn_wfun (Class.cv (nb067_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_002)))))
      (Wff.imp (syn_wfun (Class.cv f))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067_split_alpha_0038 x y f))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067_split_alpha_0038 x y f))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_089) from (by
                          unfold nb067_alpha_dummy_089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0094) 0))))) (Ne.symm
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_090 f) from (by
                          unfold nb067_alpha_dummy_090;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0095 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_089) from (by
                            unfold nb067_alpha_dummy_089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0092) 0))))) (Ne.symm
                        (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_090 f) from (by
                            unfold nb067_alpha_dummy_090;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0093 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_092) from (by
          unfold nb067_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_094 f) from (by
          unfold nb067_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_091) from (by
          unfold nb067_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_093 f) from (by
          unfold nb067_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_097) from (by
          unfold nb067_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_098 f) from (by
          unfold nb067_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_095)
        from (by
          unfold nb067_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_096 f) from (by
          unfold nb067_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb067_split_alpha_0040 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_092) from (by
          unfold nb067_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_094 f) from (by
          unfold nb067_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_091) from (by
          unfold nb067_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_093 f) from (by
          unfold nb067_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_097) from (by
          unfold nb067_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_098 f) from (by
          unfold nb067_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_095)
        from (by
          unfold nb067_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_096 f) from (by
          unfold nb067_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb067_split_alpha_0040 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb067_split_alpha_0043 x y f)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0065 x y f)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                    ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                    ((nb067_alpha_dummy_000), f),
                    ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                    ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                    ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_282) from (by
          unfold nb067_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 1)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_284 f) from (by
          unfold nb067_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_281) from (by
          unfold nb067_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 0)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_283 f) from (by
          unfold nb067_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_287) from (by
          unfold nb067_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0306) 0)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_288 f) from (by
          unfold nb067_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_285)
        from (by
          unfold nb067_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0303)
                  0)))) (show (nb067_alpha_dummy_280 f) ≠ (nb067_alpha_dummy_286 f) from (by
          unfold nb067_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0067 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_282) from (by
          unfold nb067_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 1)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_284 f) from (by
          unfold nb067_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_281) from (by
          unfold nb067_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 0)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_283 f) from (by
          unfold nb067_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_287) from (by
          unfold nb067_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0306) 0)))) (show (nb067_alpha_dummy_280 f) ≠
        (nb067_alpha_dummy_288 f) from (by
          unfold nb067_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_278) ≠ (nb067_alpha_dummy_285)
        from (by
          unfold nb067_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0303)
                  0)))) (show (nb067_alpha_dummy_280 f) ≠ (nb067_alpha_dummy_286 f) from (by
          unfold nb067_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0067 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb067_split_alpha_0070 x y f))))))))
                (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0081 x y f)))))))))
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_y) (TAlphaVar.there
              (show (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_003) from (by
                  unfold nb067_alpha_dummy_003;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))))
              (show y ≠ (nb067_alpha_dummy_004 x y f) from (by
                  unfold nb067_alpha_dummy_004;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))))
              (TAlphaVar.here _ _ _)))))))

@[expose]
noncomputable def nb067_split_alpha_0083 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
        ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
        ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
        ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
        ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_339))
            (syn_cun (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_342 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_343 f))
              (Class.cv (nb067_alpha_dummy_344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
          ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
          ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
          ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
          ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
          ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
          ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0084 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_333))
            (Class.cv (nb067_alpha_dummy_326))) (Wff.classEq (Class.cv (nb067_alpha_dummy_334))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_333))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f))
            (Class.cv (nb067_alpha_dummy_328 f)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_336 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_335 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_333) from (by
                unfold nb067_alpha_dummy_333;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
            (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_335 f) from (by
                unfold nb067_alpha_dummy_335;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
            (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_334) from (by
                  unfold nb067_alpha_dummy_334;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
              (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_336 f) from (by
                  unfold nb067_alpha_dummy_336;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_340) from (by
                                  unfold nb067_alpha_dummy_340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_343 f) from
                                (by
                                  unfold nb067_alpha_dummy_343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_339) from (by
                                    unfold nb067_alpha_dummy_339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_342 f) from (by
                                    unfold nb067_alpha_dummy_342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                                    (by
                                      unfold nb067_alpha_dummy_337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from
                                    (by
                                      unfold nb067_alpha_dummy_338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
                                  ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
                                  ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
                                  ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                                  ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                                  ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                                  ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                                  ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                                  ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                                  ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                                  ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                                  ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                                  ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                                  ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0083 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                      ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                      (by
                        unfold nb067_alpha_dummy_337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                        unfold nb067_alpha_dummy_338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                      ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part033`. -/


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
noncomputable def nb067_split_alpha_0085 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
        ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
        ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
        ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
        ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
        ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_339))
            (syn_cun (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_342 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_343 f))
              (Class.cv (nb067_alpha_dummy_344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
          ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
          ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
          ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
          ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
          ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
          ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
          ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
          ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0086 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
        ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_333))
          (Class.cv (nb067_alpha_dummy_326))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_334))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_333))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f))
          (Class.cv (nb067_alpha_dummy_328 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_336 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_335 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_333) from (by
              unfold nb067_alpha_dummy_333;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
          (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_335 f) from (by
              unfold nb067_alpha_dummy_335;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_334) from (by
                unfold nb067_alpha_dummy_334;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
            (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_336 f) from (by
                unfold nb067_alpha_dummy_336;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_359) from (by
                  unfold nb067_alpha_dummy_359;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0378) 0))))
              (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_360 f) from (by
                  unfold nb067_alpha_dummy_360;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0379 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_357) from (by
                    unfold nb067_alpha_dummy_357;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0376) 0))))
                (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_358 f) from (by
                    unfold nb067_alpha_dummy_358;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0377 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_340) from (by
                                  unfold nb067_alpha_dummy_340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_343 f) from
                                (by
                                  unfold nb067_alpha_dummy_343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_339) from (by
                                    unfold nb067_alpha_dummy_339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_342 f) from (by
                                    unfold nb067_alpha_dummy_342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                                    (by
                                      unfold nb067_alpha_dummy_337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from
                                    (by
                                      unfold nb067_alpha_dummy_338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
                                  ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
                                  ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
                                  ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                                  ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                                  ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                                  ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                                  ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                                  ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                                  ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                                  ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                                  ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                                  ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                                  ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                                  ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                                  ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0085 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                      ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                      ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                      (by
                        unfold nb067_alpha_dummy_337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                        unfold nb067_alpha_dummy_338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                      ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                      ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0087 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_355))
          (Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_355))
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_356 f))
          (Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_356 f))
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_326) from
                    (by
                      unfold nb067_alpha_dummy_326;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                  (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_328 f) from (by
                      unfold nb067_alpha_dummy_328;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_325) from
                      (by
                        unfold nb067_alpha_dummy_325;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                    (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_327 f) from (by
                        unfold nb067_alpha_dummy_327;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_355) from (by
                          unfold nb067_alpha_dummy_355;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                      (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_356 f) from (by
                          unfold nb067_alpha_dummy_356;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_329) from (by
                            unfold nb067_alpha_dummy_329;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                        (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_330 f) from (by
                            unfold nb067_alpha_dummy_330;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_322))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_321))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0086 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0086 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                          ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                          ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                          ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_326) from
                      (by
                        unfold nb067_alpha_dummy_326;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                    (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_328 f) from (by
                        unfold nb067_alpha_dummy_328;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_325) from (by
                          unfold nb067_alpha_dummy_325;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                      (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_327 f) from (by
                          unfold nb067_alpha_dummy_327;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0372 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_355) from (by
                            unfold nb067_alpha_dummy_355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                        (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_356 f) from (by
                            unfold nb067_alpha_dummy_356;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_329) from (by
                              unfold nb067_alpha_dummy_329;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                          (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_330 f) from (by
                              unfold nb067_alpha_dummy_330;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_322))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_321))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0086 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0086 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                            ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                            ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                            ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                            ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                            ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                            ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                            ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                            ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0088 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
        ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_319))
          (syn_crn (Class.cv (nb067_alpha_dummy_000)))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_319)) (Class.cv (nb067_alpha_dummy_001)))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_320 x f)) (syn_crn (Class.cv f)))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_320 x f)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                  ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                  ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)),
                  ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠
        (nb067_alpha_dummy_326) from (by
          unfold nb067_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 1)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_328 f) from (by
          unfold nb067_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_325) from (by
          unfold nb067_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_327 f) from (by
          unfold nb067_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_331) from (by
          unfold nb067_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_332 f) from (by
          unfold nb067_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_329) from (by
          unfold nb067_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_330 f) from (by
          unfold nb067_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb067_split_alpha_0084 x y f)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠
        (nb067_alpha_dummy_326) from (by
          unfold nb067_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 1)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_328 f) from (by
          unfold nb067_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_325) from (by
          unfold nb067_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_327 f) from (by
          unfold nb067_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_331) from (by
          unfold nb067_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_332 f) from (by
          unfold nb067_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_329) from (by
          unfold nb067_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343) 0)))) (show (nb067_alpha_dummy_324 f) ≠
        (nb067_alpha_dummy_330 f) from (by
          unfold nb067_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb067_split_alpha_0084 x y f)))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0087 x y f))))))))
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_322) from (by
                      unfold nb067_alpha_dummy_322;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0384) 1))))
                  (show f ≠ (nb067_alpha_dummy_324 f) from (by
                      unfold nb067_alpha_dummy_324;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0385 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_321) from
                      (by
                        unfold nb067_alpha_dummy_321;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0384) 0))))
                    (show f ≠ (nb067_alpha_dummy_323 f) from (by
                        unfold nb067_alpha_dummy_323;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0385 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_319) from (by
                          unfold nb067_alpha_dummy_319;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0382) 0))))
                      (show f ≠ (nb067_alpha_dummy_320 x f) from (by
                          unfold nb067_alpha_dummy_320;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0383 x f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_317) from (by
                            unfold nb067_alpha_dummy_317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0380) 0))))
                        (show f ≠ (nb067_alpha_dummy_318 x f) from (by
                            unfold nb067_alpha_dummy_318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0381 x f) 0))))
                        (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_319) from (by
                unfold nb067_alpha_dummy_319;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0388) 0))))
            (show x ≠ (nb067_alpha_dummy_320 x f) from (by
                unfold nb067_alpha_dummy_320;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0389 x f) 0))))
            (TAlphaVar.there (show (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_317) from (by
                  unfold nb067_alpha_dummy_317;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0386) 0))))
              (show x ≠ (nb067_alpha_dummy_318 x f) from (by
                  unfold nb067_alpha_dummy_318;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0387 x f) 0))))
              (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                (Ne.symm dv_f_x) (TAlphaVar.there
                  (show (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_003) from (by
                      unfold nb067_alpha_dummy_003;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))))
                  (show x ≠ (nb067_alpha_dummy_004 x y f) from (by
                      unfold nb067_alpha_dummy_004;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))))
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part034`. -/


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
noncomputable def nb067_split_alpha_0089 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
        ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
        ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
        ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
        ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_339))
            (syn_cun (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_342 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_343 f))
              (Class.cv (nb067_alpha_dummy_344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
          ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
          ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
          ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
          ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0090 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
        (syn_cphi (Class.cv (nb067_alpha_dummy_326))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
        (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
            ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_333) from (by
                    unfold nb067_alpha_dummy_333;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
                (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_335 f) from (by
                    unfold nb067_alpha_dummy_335;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_334) from
                    (by
                      unfold nb067_alpha_dummy_334;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
                  (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_336 f) from (by
                      unfold nb067_alpha_dummy_336;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_340) from
                                    (by
                                      unfold nb067_alpha_dummy_340;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0352)
                                              1)))) (show
                                    (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_343 f) from
                                    (by
                                      unfold nb067_alpha_dummy_343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0353 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_339) from (by
                                        unfold nb067_alpha_dummy_339;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0352)
                                                0)))) (show (nb067_alpha_dummy_335 f) ≠
                                        (nb067_alpha_dummy_342 f) from (by
                                        unfold nb067_alpha_dummy_342;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0353 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                                        (by
                                          unfold nb067_alpha_dummy_337;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0350)
                                                  0)))) (show (nb067_alpha_dummy_335 f) ≠
        (nb067_alpha_dummy_338 f) from (by
                                          unfold nb067_alpha_dummy_338;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0351 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
                                      ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
                                      ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
                                      ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                                      ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                                      ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                        (nb067_alpha_dummy_004 x y f)),
                                      ((nb067_alpha_dummy_002), y),
                                      ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005),
                                        (nb067_alpha_dummy_006 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067_split_alpha_0089 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                              unfold nb067_alpha_dummy_337;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                          (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                              unfold nb067_alpha_dummy_338;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                          ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                            unfold nb067_alpha_dummy_337;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                        (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                            unfold nb067_alpha_dummy_338;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                              unfold nb067_alpha_dummy_337;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                          (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                              unfold nb067_alpha_dummy_338;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                          ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)),
                          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0091 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
        ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
        ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
        ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
        ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
        ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_339))
            (syn_cun (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_342 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_343 f))
              (Class.cv (nb067_alpha_dummy_344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_347) from (by
                              unfold nb067_alpha_dummy_347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_348 f) from (by
                              unfold nb067_alpha_dummy_348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_345) from (by
                                unfold nb067_alpha_dummy_345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_346 f) from (by
                                unfold nb067_alpha_dummy_346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
          ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
          ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
          ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
          ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
          ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
          ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
          ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
          ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_351) from (by
                                unfold nb067_alpha_dummy_351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_352 f) from (by
                                unfold nb067_alpha_dummy_352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_353) from (by
                                unfold nb067_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_354 f) from (by
                                unfold nb067_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_341) ≠ (nb067_alpha_dummy_349) from (by
                                  unfold nb067_alpha_dummy_349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067_alpha_dummy_344 f) ≠ (nb067_alpha_dummy_350 f) from
                                (by
                                  unfold nb067_alpha_dummy_350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0092 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
        ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
        ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
        ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
        ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
        ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
        ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_333))
          (Class.cv (nb067_alpha_dummy_326))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_334))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_333))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f))
          (Class.cv (nb067_alpha_dummy_328 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_336 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_335 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_333) from (by
              unfold nb067_alpha_dummy_333;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
          (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_335 f) from (by
              unfold nb067_alpha_dummy_335;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_334) from (by
                unfold nb067_alpha_dummy_334;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
            (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_336 f) from (by
                unfold nb067_alpha_dummy_336;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_359) from (by
                  unfold nb067_alpha_dummy_359;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0378) 0))))
              (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_360 f) from (by
                  unfold nb067_alpha_dummy_360;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0379 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_326) ≠ (nb067_alpha_dummy_357) from (by
                    unfold nb067_alpha_dummy_357;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0376) 0))))
                (show (nb067_alpha_dummy_328 f) ≠ (nb067_alpha_dummy_358 f) from (by
                    unfold nb067_alpha_dummy_358;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0377 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_340) from (by
                                  unfold nb067_alpha_dummy_340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_343 f) from
                                (by
                                  unfold nb067_alpha_dummy_343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_339) from (by
                                    unfold nb067_alpha_dummy_339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_342 f) from (by
                                    unfold nb067_alpha_dummy_342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                                    (by
                                      unfold nb067_alpha_dummy_337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from
                                    (by
                                      unfold nb067_alpha_dummy_338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)),
                                  ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)),
                                  ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)),
                                  ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                                  ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                                  ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                                  ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                                  ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                                  ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                                  ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                                  ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                                  ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                                  ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                                  ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0091 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                      ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from
                      (by
                        unfold nb067_alpha_dummy_337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                        unfold nb067_alpha_dummy_338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_337) from (by
                          unfold nb067_alpha_dummy_337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_338 f) from (by
                          unfold nb067_alpha_dummy_338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)),
                      ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)),
                      ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)),
                      ((nb067_alpha_dummy_359), (nb067_alpha_dummy_360 f)),
                      ((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                      ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                      ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                      ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                      ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                      ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                      ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0093 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
        ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
        ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
        ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_355))
          (Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_355))
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_356 f))
          (Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_356 f))
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_326) from
                    (by
                      unfold nb067_alpha_dummy_326;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                  (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_328 f) from (by
                      unfold nb067_alpha_dummy_328;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_325) from
                      (by
                        unfold nb067_alpha_dummy_325;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                    (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_327 f) from (by
                        unfold nb067_alpha_dummy_327;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_355) from (by
                          unfold nb067_alpha_dummy_355;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                      (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_356 f) from (by
                          unfold nb067_alpha_dummy_356;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_329) from (by
                            unfold nb067_alpha_dummy_329;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                        (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_330 f) from (by
                            unfold nb067_alpha_dummy_330;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_322))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_321))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0092 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0092 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                          ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                          ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                          ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                          ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                          ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                          ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_326) from
                      (by
                        unfold nb067_alpha_dummy_326;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                    (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_328 f) from (by
                        unfold nb067_alpha_dummy_328;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_325) from (by
                          unfold nb067_alpha_dummy_325;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                      (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_327 f) from (by
                          unfold nb067_alpha_dummy_327;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0372 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_355) from (by
                            unfold nb067_alpha_dummy_355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                        (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_356 f) from (by
                            unfold nb067_alpha_dummy_356;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_329) from (by
                              unfold nb067_alpha_dummy_329;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                          (show (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_330 f) from (by
                              unfold nb067_alpha_dummy_330;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_322))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_321))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_323 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0092 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0092 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_357), (nb067_alpha_dummy_358 f)),
                            ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)),
                            ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)),
                            ((nb067_alpha_dummy_355), (nb067_alpha_dummy_356 f)),
                            ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)),
                            ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                            ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part035`. -/


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
noncomputable def nb067_split_alpha_0094 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb067_alpha_dummy_005)) (syn_cop
            (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
            (Class.cv (nb067_alpha_dummy_003)))) (Wff.neg (syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv))
              (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000)
                (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002))
                  (Class.cv (nb067_alpha_dummy_001))))))))
      (Wff.imp (Wff.classEq (Class.cv (nb067_alpha_dummy_006 x y f))
          (syn_cop (syn_cop (Class.cv x) (Class.cv y))
            (Class.cv (nb067_alpha_dummy_004 x y f)))) (Wff.neg (syn_wa
            (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f))
              (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb067_alpha_dummy_003) ≠ (nb067_alpha_dummy_005) from (by
                unfold nb067_alpha_dummy_005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0004) 0))))) (Ne.symm
            (show (nb067_alpha_dummy_004 x y f) ≠ (nb067_alpha_dummy_006 x y f) from (by
                unfold nb067_alpha_dummy_006;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0005 x y f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_005) from
                (by
                  unfold nb067_alpha_dummy_005;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0002) 0)))))
            (Ne.symm (show y ≠ (nb067_alpha_dummy_006 x y f) from (by
                  unfold nb067_alpha_dummy_006;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0003 x y f) 0)))))
            (TAlphaVar.there (Ne.symm
                (show (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_005) from (by
                    unfold nb067_alpha_dummy_005;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0000) 0)))))
              (Ne.symm (show x ≠ (nb067_alpha_dummy_006 x y f) from (by
                    unfold nb067_alpha_dummy_006;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0001 x y f) 0)))))
              (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0009 x y f dv_x_y))))) (TAlphaWff.neg
      (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (show (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_003) from (by
                    unfold nb067_alpha_dummy_003;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))))
                (show x ≠ (nb067_alpha_dummy_004 x y f) from (by
                    unfold nb067_alpha_dummy_004;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_closed
              [((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
              (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_003) from (by
                    unfold nb067_alpha_dummy_003;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))))
                (show y ≠ (nb067_alpha_dummy_004 x y f) from (by
                    unfold nb067_alpha_dummy_004;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))))
                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
              [((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
              (syn_cvv) (by simp only [fv_syn_cvv]))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.conj (TAlphaWff.neg (nb067_split_alpha_0082 x y f dv_f_y))
              (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                              (nb067_split_alpha_0088 x y f dv_f_x dv_x_y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                              (nb067_split_alpha_0088 x y f dv_f_x dv_x_y))))))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)),
                            ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_326) from (by
          unfold nb067_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  1)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_328 f) from (by
          unfold nb067_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f)
                  1)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_325)
        from (by
          unfold nb067_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_327 f) from (by
          unfold nb067_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344
                    f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_331)
        from (by
          unfold nb067_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_332 f) from (by
          unfold nb067_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_329)
        from (by
          unfold
            nb067_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_330 f) from (by
          unfold
            nb067_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0090 x y f)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_326) from (by
          unfold nb067_alpha_dummy_326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  1)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_328 f) from (by
          unfold nb067_alpha_dummy_328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f)
                  1)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_325)
        from (by
          unfold nb067_alpha_dummy_325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_327 f) from (by
          unfold nb067_alpha_dummy_327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344
                    f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_331)
        from (by
          unfold nb067_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_332 f) from (by
          unfold nb067_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_322) ≠ (nb067_alpha_dummy_329)
        from (by
          unfold
            nb067_alpha_dummy_329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343)
                  0)))) (show (nb067_alpha_dummy_324 f) ≠ (nb067_alpha_dummy_330 f) from (by
          unfold
            nb067_alpha_dummy_330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0090 x y f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb067_split_alpha_0093 x y f))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_322) from (by
                                unfold nb067_alpha_dummy_322;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0384) 1))))
                            (show f ≠ (nb067_alpha_dummy_324 f) from (by
                                unfold nb067_alpha_dummy_324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0385 f) 1))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_321) from (by
                                  unfold nb067_alpha_dummy_321;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0384) 0))))
                              (show f ≠ (nb067_alpha_dummy_323 f) from (by
                                  unfold nb067_alpha_dummy_323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0385 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nominal_df_map (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cmap)
        (syn_cmpt2 x (syn_cvv) y (syn_cvv) (.cab f (syn_wf (.cv f) (.cv y) (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.neg (nb067_split_alpha_0094 x y f dv_f_x dv_f_y dv_x_y))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
