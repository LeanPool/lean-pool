/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part045`. -/


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
noncomputable def nb090_split_alpha_0021 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
        ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_239 A))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_239 A)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_240 h))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_240 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_215 A) from (by
                              unfold nb090_alpha_dummy_215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                          (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_217 h) from (by
                              unfold nb090_alpha_dummy_217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_216 A) from (by
                                unfold nb090_alpha_dummy_216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                            (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_218 h) from (by
                                unfold nb090_alpha_dummy_218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_241 A) from
                                (by
                                  unfold nb090_alpha_dummy_241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                              (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_242 h) from
                                (by
                                  unfold nb090_alpha_dummy_242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_239 A) from (by
                                    unfold nb090_alpha_dummy_239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0248 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_240 h) from (by
                                    unfold nb090_alpha_dummy_240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0249 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_222 A) from (by
          unfold nb090_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_225 h) from (by
          unfold nb090_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_221 A) from (by
          unfold nb090_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 0)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_224 h) from (by
          unfold nb090_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
          unfold nb090_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)), ((nb090_alpha_dummy_239 A),
        (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_237 A),
        (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)), ((nb090_alpha_dummy_239 A),
        (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_237 A),
        (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_222
        A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
                                    ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                    (by
                                      unfold nb090_alpha_dummy_219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0222 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from
                                    (by
                                      unfold nb090_alpha_dummy_220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0223 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
                                    ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_215 A) from (by
                              unfold nb090_alpha_dummy_215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                          (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_217 h) from (by
                              unfold nb090_alpha_dummy_217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_216 A) from (by
                                unfold nb090_alpha_dummy_216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                            (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_218 h) from (by
                                unfold nb090_alpha_dummy_218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_241 A) from
                                (by
                                  unfold nb090_alpha_dummy_241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                              (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_242 h) from
                                (by
                                  unfold nb090_alpha_dummy_242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_239 A) from (by
                                    unfold nb090_alpha_dummy_239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0248 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_240 h) from (by
                                    unfold nb090_alpha_dummy_240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0249 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_222 A) from (by
          unfold nb090_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_225 h) from (by
          unfold nb090_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_221 A) from (by
          unfold nb090_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 0)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_224 h) from (by
          unfold nb090_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
          unfold nb090_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)), ((nb090_alpha_dummy_239 A),
        (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_237 A),
        (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)), ((nb090_alpha_dummy_239 A),
        (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_237 A),
        (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_222
        A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
                                    ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                    (by
                                      unfold nb090_alpha_dummy_219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0222 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from
                                    (by
                                      unfold nb090_alpha_dummy_220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0223 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
                                    ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
            ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
            ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
            ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
            ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
            ((nb090_alpha_dummy_001 A), u),
            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb090_split_alpha_0022 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classEq (syn_cin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))
        (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
          (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))
      (Wff.classEq (syn_cin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))
        (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))) :=
  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0011 v u A h))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_reflOn
                      [((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                        ((nb090_alpha_dummy_001 A), u),
                        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                      (syn_cid) (nb090_wpp_refl_0043 v u A h)))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0011 v u A h))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_reflOn
                      [((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                        ((nb090_alpha_dummy_001 A), u),
                        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                      (syn_cid) (nb090_wpp_refl_0043 v u A h)))))))))) (TAlphaClass.cab
      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (Ne.symm
                    (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_055 A) from (by
                        unfold nb090_alpha_dummy_055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0044 A) 0))))) (Ne.symm
                    (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_056 h) from (by
                        unfold nb090_alpha_dummy_056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0045 h) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_055 A) from (by
                          unfold nb090_alpha_dummy_055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0042 A) 0))))) (Ne.symm
                      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_056 h) from (by
                          unfold nb090_alpha_dummy_056;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0043 h) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0012 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_058 A) from (by
          unfold nb090_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 1)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_060 h) from (by
          unfold nb090_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_087 A) from (by
          unfold nb090_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0078 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_088 h) from (by
          unfold nb090_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0079 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_061 A) from (by
          unfold nb090_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_062 h) from (by
          unfold nb090_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb090_split_alpha_0013 v u A h)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_058 A) from (by
          unfold nb090_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 1)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_060 h) from (by
          unfold nb090_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from (by
          unfold nb090_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0074 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_059 h) from (by
          unfold nb090_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0076 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_087 A) from (by
          unfold nb090_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0078 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_088 h) from (by
          unfold nb090_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0079 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_061 A) from (by
          unfold nb090_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_062 h) from (by
          unfold nb090_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab
                                        (nb090_split_alpha_0013 v u A h)))))))))))))))
            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090_split_alpha_0014 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_094 A) from (by
          unfold nb090_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 1)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_096 h) from (by
          unfold nb090_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_123 A) from (by
          unfold nb090_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_124 h) from (by
          unfold nb090_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_097 A) from (by
          unfold nb090_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_098 h) from (by
          unfold nb090_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_051 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0015 v u A h))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_094 A) from (by
          unfold nb090_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A) 1)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_096 h) from (by
          unfold nb090_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_093 A) from (by
          unfold nb090_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0112 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_123 A) from (by
          unfold nb090_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_124 h) from (by
          unfold nb090_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_097 A) from (by
          unfold nb090_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A)
                  0)))) (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_098 h) from (by
          unfold nb090_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_051 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0015 v u A h)))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (Ne.symm (show
                                    (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_133 A) from
                                    (by
                                      unfold nb090_alpha_dummy_133;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0124 A)
                                              0))))) (Ne.symm (show
                                    (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_134 h) from
                                    (by
                                      unfold nb090_alpha_dummy_134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0125 h)
                                              0))))) (TAlphaVar.there (Ne.symm (show
                                      (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_133 A) from
                                      (by
                                        unfold nb090_alpha_dummy_133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0122 A)
                                                0))))) (Ne.symm (show
                                      (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_134 h) from
                                      (by
                                        unfold nb090_alpha_dummy_134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0123 h)
                                                0))))) (TAlphaVar.here _ _ _))))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0016 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold
            nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold
            nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold
            nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold
            nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold
            nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold
            nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0017 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001
        A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold
            nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold
            nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold
            nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold
            nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold
            nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold
            nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0017 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001
        A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0018 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold
            nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold
            nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold
            nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold
            nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold
            nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold
            nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0019 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001
        A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold
            nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold
            nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold
            nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold
            nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold
            nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold
            nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0019 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001
        A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_130 A) from (by
                                    unfold nb090_alpha_dummy_130;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0212 A)
                                            1)))) (show h ≠ (nb090_alpha_dummy_132 h) from (by
                                    unfold nb090_alpha_dummy_132;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0213 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_129 A) from
                                    (by
                                      unfold nb090_alpha_dummy_129;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0212 A)
                                              0)))) (show h ≠ (nb090_alpha_dummy_131 h) from (by
                                      unfold nb090_alpha_dummy_131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0213 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_133 A) from
                                      (by
                                        unfold nb090_alpha_dummy_133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0210 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_134 h) from
                                      (by
                                        unfold nb090_alpha_dummy_134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0211 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_051 A)
                                        from (by
                                          unfold nb090_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0206 A) 2))))
                                      (show h ≠ (nb090_alpha_dummy_054 h) from (by
                                          unfold nb090_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0208 h) 2))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_050 A) from (by
          unfold nb090_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0206 A) 1)))) (show h ≠ (nb090_alpha_dummy_053 h) from (by
          unfold nb090_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0208 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_049 A) from (by
          unfold nb090_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0206 A) 0)))) (show h ≠ (nb090_alpha_dummy_052 h) from (by
          unfold nb090_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0208 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_055 A) from (by
          unfold nb090_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0207 A) 0)))) (show h ≠ (nb090_alpha_dummy_056 h) from (by
          unfold nb090_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0209 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb090_split_alpha_0020 v u A h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_208 A) from (by
          unfold nb090_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 1)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_210 h) from (by
          unfold nb090_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_237 A) from (by
          unfold nb090_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_238 h) from (by
          unfold nb090_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_211 A) from (by
          unfold nb090_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_212 h) from (by
          unfold nb090_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_050 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0021 v u A h))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_208 A) from (by
          unfold nb090_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A) 1)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_210 h) from (by
          unfold nb090_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0242 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_237 A) from (by
          unfold nb090_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_238 h) from (by
          unfold nb090_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_211 A) from (by
          unfold nb090_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A)
                  0)))) (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_212 h) from (by
          unfold nb090_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_050 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0021 v u A h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_051 A) from (by
                          unfold nb090_alpha_dummy_051;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
                      (show h ≠ (nb090_alpha_dummy_054 h) from (by
                          unfold nb090_alpha_dummy_054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_050 A) from (by
                            unfold nb090_alpha_dummy_050;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0206 A) 1))))
                        (show h ≠ (nb090_alpha_dummy_053 h) from (by
                            unfold nb090_alpha_dummy_053;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0208 h) 1))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_049 A) from (by
                              unfold nb090_alpha_dummy_049;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0206 A) 0))))
                          (show h ≠ (nb090_alpha_dummy_052 h) from (by
                              unfold nb090_alpha_dummy_052;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0208 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_055 A) from (by
                                unfold nb090_alpha_dummy_055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0207 A) 0))))
                            (show h ≠ (nb090_alpha_dummy_056 h) from (by
                                unfold nb090_alpha_dummy_056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0209 h) 0))))
                            (TAlphaVar.here _ _ _))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part046`. -/


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
noncomputable def nb090_split_alpha_0023 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_251 A)) (syn_ccompl
          (Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_252 h)) (syn_ccompl
          (Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_248 A) from (by
                            unfold nb090_alpha_dummy_248;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
                        (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_250 h) from (by
                            unfold nb090_alpha_dummy_250;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_247 A) from (by
                              unfold nb090_alpha_dummy_247;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
                          (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_249 h) from (by
                              unfold nb090_alpha_dummy_249;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_253 A) from (by
                                unfold nb090_alpha_dummy_253;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0256 A) 0))))
                            (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_254 h) from (by
                                unfold nb090_alpha_dummy_254;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0257 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_251 A) from
                                (by
                                  unfold nb090_alpha_dummy_251;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0253 A) 0))))
                              (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_252 h) from
                                (by
                                  unfold nb090_alpha_dummy_252;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0255 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
                            ((Class.cv (nb090_alpha_dummy_243 A))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
                            ((Class.cv (nb090_alpha_dummy_245 h))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_255 A) from (by
                                    unfold nb090_alpha_dummy_255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0258 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_257 h) from (by
                                    unfold nb090_alpha_dummy_257;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0259 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_256 A) from
                                    (by
                                      unfold nb090_alpha_dummy_256;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0258 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_258 h) from
                                    (by
                                      unfold nb090_alpha_dummy_258;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0259 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_262 A) from (by
          unfold nb090_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  1)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_265 h) from (by
          unfold nb090_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_261 A) from (by
          unfold nb090_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_264 h) from (by
          unfold nb090_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
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
        ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A),
        (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)),
        ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_269 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_269 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_269 A) from (by
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
        ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A),
        (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)),
        ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A
        h))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_273 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_275 A) from (by
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
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
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
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A),
        (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)),
        ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
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
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
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
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A),
        (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)),
        ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_248 A) from (by
                            unfold nb090_alpha_dummy_248;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
                        (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_250 h) from (by
                            unfold nb090_alpha_dummy_250;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_247 A) from (by
                              unfold nb090_alpha_dummy_247;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
                          (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_249 h) from (by
                              unfold nb090_alpha_dummy_249;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_253 A) from (by
                                unfold nb090_alpha_dummy_253;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0256 A) 0))))
                            (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_254 h) from (by
                                unfold nb090_alpha_dummy_254;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0257 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_251 A) from
                                (by
                                  unfold nb090_alpha_dummy_251;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0253 A) 0))))
                              (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_252 h) from
                                (by
                                  unfold nb090_alpha_dummy_252;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0255 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
                            ((Class.cv (nb090_alpha_dummy_243 A))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
                            ((Class.cv (nb090_alpha_dummy_245 h))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_255 A) from (by
                                    unfold nb090_alpha_dummy_255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0258 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_257 h) from (by
                                    unfold nb090_alpha_dummy_257;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0259 h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_248 A) ≠ (nb090_alpha_dummy_256 A) from
                                    (by
                                      unfold nb090_alpha_dummy_256;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0258 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_250 h) ≠ (nb090_alpha_dummy_258 h) from
                                    (by
                                      unfold nb090_alpha_dummy_258;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0259 h)
                                              1)))) (TAlphaVar.here _ _ _)))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_262 A) from (by
          unfold nb090_alpha_dummy_262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  1)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_265 h) from (by
          unfold nb090_alpha_dummy_265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_261 A) from (by
          unfold nb090_alpha_dummy_261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0262 A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_264 h) from (by
          unfold nb090_alpha_dummy_264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0263 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
        (nb090_alpha_dummy_259 A) from (by
          unfold nb090_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0260
                    A)
                  0)))) (show (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_260 h) from (by
          unfold nb090_alpha_dummy_260;
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
        ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A),
        (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)),
        ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_269 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_269 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠ (nb090_alpha_dummy_269 A) from (by
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
        ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A),
        (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)),
        ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A),
        (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A
        h))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_262 A) ≠
        (nb090_alpha_dummy_273 A) from (by
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_263 A) ≠
        (nb090_alpha_dummy_275 A) from (by
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
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
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
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A),
        (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)),
        ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_255 A) ≠
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
                  (nb090_support_mem_0261 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_259 A) from (by
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
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_259 A),
        (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)),
        ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A),
        (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)),
        ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A),
        (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
