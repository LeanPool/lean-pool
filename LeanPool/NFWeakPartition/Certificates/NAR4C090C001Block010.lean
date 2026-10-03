/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part034`. -/


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
noncomputable def nb090_split_alpha_0010 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
        ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
        ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
        ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_241 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_241 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_242 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_242 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_215 A) from (by
                      unfold nb090_alpha_dummy_215;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                  (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_217 h) from (by
                      unfold nb090_alpha_dummy_217;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
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
                              (mem_lt_freshVar (nb090_support_mem_0221 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_241 A) from (by
                          unfold nb090_alpha_dummy_241;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                      (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_242 h) from (by
                          unfold nb090_alpha_dummy_242;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_239 A) from (by
                            unfold nb090_alpha_dummy_239;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0248 A) 0))))
                        (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_240 h) from (by
                            unfold nb090_alpha_dummy_240;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0249 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_222 A) from
                                      (by
                                        unfold nb090_alpha_dummy_222;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0224 A)
                                                1)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_225 h) from (by
                                        unfold nb090_alpha_dummy_225;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0225 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_221 A)
                                        from (by
                                          unfold nb090_alpha_dummy_221;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0224 A) 0)))) (show
                                        (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_224 h)
                                        from (by
                                          unfold nb090_alpha_dummy_224;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0225 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠
        (nb090_alpha_dummy_219 A) from (by
          unfold nb090_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A) 0)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_223 A),
        (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A), (nb090_alpha_dummy_225 h)),
                                        ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
                                        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
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
                                        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_229 A) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_229 A) from (by
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
                                        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)),
        ((nb090_alpha_dummy_222 A), (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A),
        (nb090_alpha_dummy_224 h)), ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
        ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A),
        (nb090_alpha_dummy_218 h)), ((nb090_alpha_dummy_241 A), (nb090_alpha_dummy_242 h)),
        ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A),
        (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
        ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A),
        (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
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
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_233 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_235 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_235 A) from (by
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
                                unfold nb090_alpha_dummy_219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
                                unfold nb090_alpha_dummy_220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
                              unfold nb090_alpha_dummy_219;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                          (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
                              unfold nb090_alpha_dummy_220;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
                                unfold nb090_alpha_dummy_219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
                                unfold nb090_alpha_dummy_220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
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
                              (mem_lt_freshVar (nb090_support_mem_0221 h) 0)))) (TAlphaVar.there
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
                        (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_241 A) from (by
                            unfold nb090_alpha_dummy_241;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0250 A) 0))))
                        (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_242 h) from (by
                            unfold nb090_alpha_dummy_242;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0251 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_239 A) from (by
                              unfold nb090_alpha_dummy_239;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0248 A) 0))))
                          (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_240 h) from (by
                              unfold nb090_alpha_dummy_240;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0249 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠
        (nb090_alpha_dummy_222 A) from (by
                                          unfold nb090_alpha_dummy_222;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0224 A) 1)))) (show
                                        (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_225 h)
                                        from (by
                                          unfold nb090_alpha_dummy_225;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0225 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠
        (nb090_alpha_dummy_221 A) from (by
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
                  (nb090_support_mem_0222 A) 0)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_223 A),
        (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A), (nb090_alpha_dummy_225 h)),
        ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)), ((nb090_alpha_dummy_219 A),
        (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
        ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)), ((nb090_alpha_dummy_241 A),
        (nb090_alpha_dummy_242 h)), ((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A),
        (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_235 A) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_235 A) from (by
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                (by
                                  unfold nb090_alpha_dummy_219;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                              (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from
                                (by
                                  unfold nb090_alpha_dummy_220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
                                unfold nb090_alpha_dummy_219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                            (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
                                unfold nb090_alpha_dummy_220;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                (by
                                  unfold nb090_alpha_dummy_219;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0222 A) 0))))
                              (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from
                                (by
                                  unfold nb090_alpha_dummy_220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0223 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part035`. -/


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
noncomputable def nb090_split_alpha_0011 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_055 A))
          (syn_cop (Class.cv (nb090_alpha_dummy_049 A)) (Class.cv (nb090_alpha_dummy_050 A))))
        (Wff.neg (syn_wex (nb090_alpha_dummy_051 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_051 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_050 A)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_056 h))
          (syn_cop (Class.cv (nb090_alpha_dummy_052 h)) (Class.cv (nb090_alpha_dummy_053 h))))
        (Wff.neg (syn_wex (nb090_alpha_dummy_054 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_054 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_053 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_055 A) from (by
                unfold nb090_alpha_dummy_055;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0044 A) 0)))))
          (Ne.symm (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_056 h) from (by
                unfold nb090_alpha_dummy_056;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0045 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_055 A) from (by
                  unfold nb090_alpha_dummy_055;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0042 A) 0)))))
            (Ne.symm (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_056 h) from (by
                  unfold nb090_alpha_dummy_056;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0043 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0001 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_058 A) from
                                    (by
                                      unfold nb090_alpha_dummy_058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0074 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_060 h) from
                                    (by
                                      unfold nb090_alpha_dummy_060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0076 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from
                                      (by
                                        unfold nb090_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0074 A)
                                                0)))) (show (nb090_alpha_dummy_053 h) ≠
                                        (nb090_alpha_dummy_059 h) from (by
                                        unfold nb090_alpha_dummy_059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0076 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_087 A)
                                        from (by
                                          unfold nb090_alpha_dummy_087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0078 A) 0)))) (show
                                        (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_088 h)
                                        from (by
                                          unfold nb090_alpha_dummy_088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0079 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_061 A) from (by
          unfold nb090_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_062 h) from (by
          unfold nb090_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090_split_alpha_0002 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_058 A) from
                                    (by
                                      unfold nb090_alpha_dummy_058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0074 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_060 h) from
                                    (by
                                      unfold nb090_alpha_dummy_060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0076 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_057 A) from
                                      (by
                                        unfold nb090_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0074 A)
                                                0)))) (show (nb090_alpha_dummy_053 h) ≠
                                        (nb090_alpha_dummy_059 h) from (by
                                        unfold nb090_alpha_dummy_059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0076 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_087 A)
                                        from (by
                                          unfold nb090_alpha_dummy_087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0078 A) 0)))) (show
                                        (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_088 h)
                                        from (by
                                          unfold nb090_alpha_dummy_088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0079 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_061 A) from (by
          unfold nb090_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0075 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_062 h) from (by
          unfold nb090_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0077 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090_split_alpha_0002 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0003 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_094 A) from (by
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
                  (nb090_support_mem_0112 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_123 A) from (by
          unfold nb090_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_124 h) from (by
          unfold nb090_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_097 A) from (by
          unfold nb090_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_098 h) from (by
          unfold nb090_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0004 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A),
        (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
        ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A),
        (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_051 A) ≠
        (nb090_alpha_dummy_094 A) from (by
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
                  (nb090_support_mem_0112 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_095 h) from (by
          unfold nb090_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0114 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_123 A) from (by
          unfold nb090_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0116 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_124 h) from (by
          unfold nb090_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0117 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_097 A) from (by
          unfold nb090_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0113 A) 0)))) (show (nb090_alpha_dummy_054 h) ≠
        (nb090_alpha_dummy_098 h) from (by
          unfold nb090_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0115 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0004 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A),
        (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
        ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A),
        (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_133 A) from (by
                                unfold nb090_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0124 A) 0)))))
                          (Ne.symm (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_134 h)
                              from (by
                                unfold nb090_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0125 h) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_133 A) from
                                (by
                                  unfold nb090_alpha_dummy_133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0122 A) 0)))))
                            (Ne.symm (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_134 h)
                                from (by
                                  unfold nb090_alpha_dummy_134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0123 h) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090_split_alpha_0005 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0006 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0006 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090_split_alpha_0007 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0008 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0008 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_130 A) from (by
                              unfold nb090_alpha_dummy_130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0212 A) 1))))
                          (show h ≠ (nb090_alpha_dummy_132 h) from (by
                              unfold nb090_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0213 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_129 A) from (by
                                unfold nb090_alpha_dummy_129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0212 A) 0))))
                            (show h ≠ (nb090_alpha_dummy_131 h) from (by
                                unfold nb090_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0213 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_133 A) from
                                (by
                                  unfold nb090_alpha_dummy_133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0210 A) 0))))
                              (show h ≠ (nb090_alpha_dummy_134 h) from (by
                                  unfold nb090_alpha_dummy_134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0211 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_051 A) from (by
                                    unfold nb090_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0206 A)
                                            2)))) (show h ≠ (nb090_alpha_dummy_054 h) from (by
                                    unfold nb090_alpha_dummy_054;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0208 h)
                                            2)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_050 A) from
                                    (by
                                      unfold nb090_alpha_dummy_050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0206 A)
                                              1)))) (show h ≠ (nb090_alpha_dummy_053 h) from (by
                                      unfold nb090_alpha_dummy_053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0208 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_049 A) from
                                      (by
                                        unfold nb090_alpha_dummy_049;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0206 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_052 h) from
                                      (by
                                        unfold nb090_alpha_dummy_052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0208 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_055 A)
                                        from (by
                                          unfold nb090_alpha_dummy_055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0207 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_056 h) from (by
                                          unfold nb090_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0209 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_047 A) from (by
          unfold nb090_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0204 A) 0)))) (show h ≠ (nb090_alpha_dummy_048 h) from (by
          unfold nb090_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0205 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_045 A) from (by
          unfold nb090_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0202 A) 0)))) (show h ≠ (nb090_alpha_dummy_046 h) from (by
          unfold nb090_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0203 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0009 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_208 A) from (by
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
                  (nb090_support_mem_0242 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_237 A) from (by
          unfold nb090_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_238 h) from (by
          unfold nb090_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_211 A) from (by
          unfold nb090_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_212 h) from (by
          unfold nb090_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv
        (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0010 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A),
        (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
        ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A),
        (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_050 A) ≠
        (nb090_alpha_dummy_208 A) from (by
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
                  (nb090_support_mem_0242 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0244 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_237 A) from (by
          unfold nb090_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0246 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_238 h) from (by
          unfold nb090_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0247 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_211 A) from (by
          unfold nb090_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0243 A) 0)))) (show (nb090_alpha_dummy_053 h) ≠
        (nb090_alpha_dummy_212 h) from (by
          unfold nb090_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0245 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv
        (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0010 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_239 A), (nb090_alpha_dummy_240 h)), ((nb090_alpha_dummy_208 A),
        (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
        ((nb090_alpha_dummy_237 A), (nb090_alpha_dummy_238 h)), ((nb090_alpha_dummy_211 A),
        (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_051 A) from (by
                    unfold nb090_alpha_dummy_051;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
                (show h ≠ (nb090_alpha_dummy_054 h) from (by
                    unfold nb090_alpha_dummy_054;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_050 A) from (by
                      unfold nb090_alpha_dummy_050;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 1))))
                  (show h ≠ (nb090_alpha_dummy_053 h) from (by
                      unfold nb090_alpha_dummy_053;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 1))))
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
                              (mem_lt_freshVar (nb090_support_mem_0208 h) 0)))) (TAlphaVar.there
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
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_047 A) from (by
                            unfold nb090_alpha_dummy_047;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0204 A) 0))))
                        (show h ≠ (nb090_alpha_dummy_048 h) from (by
                            unfold nb090_alpha_dummy_048;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0205 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_045 A) from (by
                              unfold nb090_alpha_dummy_045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0202 A) 0))))
                          (show h ≠ (nb090_alpha_dummy_046 h) from (by
                              unfold nb090_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0203 h) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb090_wpp_notmem_0602 (A : Class) : (nb090_alpha_dummy_047 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_047, fv_syn_cid] using (nb090_compact_fv_empty_0058 A)

theorem nb090_wpp_notmem_0603 (h : Var) : (nb090_alpha_dummy_048 h) ∉ ((syn_cid)).fv := by
  simpa only [nb090_alpha_dummy_048, fv_syn_cid] using (nb090_compact_fv_empty_0059 h)

theorem nb090_wpp_notmem_0604 (A : Class) : (nb090_alpha_dummy_045 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_045, fv_syn_cid] using (nb090_compact_fv_empty_0060 A)

theorem nb090_wpp_notmem_0605 (h : Var) : (nb090_alpha_dummy_046 h) ∉ ((syn_cid)).fv := by
  simpa only [nb090_alpha_dummy_046, fv_syn_cid] using (nb090_compact_fv_empty_0061 h)

theorem nb090_wpp_notmem_0606 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_000, fv_syn_cid] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_0607 (h : Var) : h ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_0608 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_002, fv_syn_cid] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0609 (v : Var) : v ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0610 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_001, fv_syn_cid] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0611 (u : Var) : u ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0612 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_003, fv_syn_cid] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0613 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉ ((syn_cid)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_cid] using
    (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0043 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_047 A) (nb090_alpha_dummy_048 h)
      (nb090_wpp_notmem_0602 A) (nb090_wpp_notmem_0603 h)
      (TEnvFresh.consFresh (nb090_alpha_dummy_045 A) (nb090_alpha_dummy_046 h)
        (nb090_wpp_notmem_0604 A) (nb090_wpp_notmem_0605 h)
        (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0606 A)
          (nb090_wpp_notmem_0607 h)
          (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0608 A)
            (nb090_wpp_notmem_0609 v)
            (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0610 A)
              (nb090_wpp_notmem_0611 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0612 A)
                (nb090_wpp_notmem_0613 v u A h) (TEnvFresh.nil ((syn_cid)).fv)))))))

@[expose]
noncomputable def nb090_wpp_refl_0043 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0043 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
