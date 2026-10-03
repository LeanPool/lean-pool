/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part042`. -/


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
noncomputable def nb077_split_alpha_0028 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_225 F I))
          (Class.cab (nb077_alpha_dummy_219 F I)
            (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_225 F I))
            (Class.cab (nb077_alpha_dummy_219 F I)
              (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_226 x))
          (Class.cab (nb077_alpha_dummy_221 x)
            (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_226 x))
            (Class.cab (nb077_alpha_dummy_221 x)
              (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
                      unfold nb077_alpha_dummy_220;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
                  (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_222 x) from (by
                      unfold nb077_alpha_dummy_222;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
                        unfold nb077_alpha_dummy_219;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
                    (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_221 x) from (by
                        unfold nb077_alpha_dummy_221;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0210 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_225 F I) from (by
                          unfold nb077_alpha_dummy_225;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0212 F I) 0))))
                      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_226 x) from (by
                          unfold nb077_alpha_dummy_226;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0213 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_223 F I) from (by
                            unfold nb077_alpha_dummy_223;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0209 F I) 0))))
                        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_224 x) from (by
                            unfold nb077_alpha_dummy_224;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0211 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_143 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_227 F I) from
                            (by
                              unfold nb077_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                          (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_229 x) from (by
                              unfold nb077_alpha_dummy_229;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_228 F I) from (by
                                unfold nb077_alpha_dummy_228;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                            (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_230 x) from (by
                                unfold nb077_alpha_dummy_230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_220 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_222 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_234 F I) from
        (by
          unfold nb077_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I) 1)))) (show (nb077_alpha_dummy_229 x) ≠
        (nb077_alpha_dummy_237 x) from (by
          unfold nb077_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_233 F I) from (by
          unfold nb077_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  0)))) (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_236 x) from (by
          unfold nb077_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from (by
          unfold nb077_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I)
                  0)))) (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
          unfold nb077_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_235 F I), (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I),
        (nb077_alpha_dummy_237 x)), ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)),
        ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_235 F I), (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I),
        (nb077_alpha_dummy_237 x)), ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)),
        ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_234
        F I) ≠ (nb077_alpha_dummy_245 F I) from (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_245 F I) from
        (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235
        F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235
        F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                      (by
                                        unfold nb077_alpha_dummy_232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_231 F I),
                                      (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
                                      (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I),
                                      (nb077_alpha_dummy_230 x)), ((nb077_alpha_dummy_220 F I),
                                      (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
                                      (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I),
                                      (nb077_alpha_dummy_226 x)), ((nb077_alpha_dummy_223 F I),
                                      (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
                                      (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_231;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                    (by
                                      unfold nb077_alpha_dummy_232;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0217 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                      (by
                                        unfold nb077_alpha_dummy_232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_231 F I),
                                      (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
                                      (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I),
                                      (nb077_alpha_dummy_230 x)), ((nb077_alpha_dummy_220 F I),
                                      (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
                                      (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I),
                                      (nb077_alpha_dummy_226 x)), ((nb077_alpha_dummy_223 F I),
                                      (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
                                      (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_220 F I) from (by
                        unfold nb077_alpha_dummy_220;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))))
                    (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_222 x) from (by
                        unfold nb077_alpha_dummy_222;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0210 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_219 F I) from (by
                          unfold nb077_alpha_dummy_219;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))))
                      (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_221 x) from (by
                          unfold nb077_alpha_dummy_221;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0210 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_225 F I) from (by
                            unfold nb077_alpha_dummy_225;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0212 F I) 0))))
                        (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_226 x) from (by
                            unfold nb077_alpha_dummy_226;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0213 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_141 F I) ≠ (nb077_alpha_dummy_223 F I) from
                            (by
                              unfold nb077_alpha_dummy_223;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0209 F I) 0))))
                          (show (nb077_alpha_dummy_144 x) ≠ (nb077_alpha_dummy_224 x) from (by
                              unfold nb077_alpha_dummy_224;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0211 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_143 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_227 F I) from (by
                                unfold nb077_alpha_dummy_227;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                            (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_229 x) from (by
                                unfold nb077_alpha_dummy_229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_228 F I) from
                                (by
                                  unfold nb077_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0214 F I)
                                          1))))
                              (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_230 x) from
                                (by
                                  unfold nb077_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_220 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_222 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_234 F I) from (by
          unfold nb077_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  1)))) (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_237 x) from (by
          unfold nb077_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_233 F I) from (by
          unfold nb077_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I)
                  0)))) (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_236 x) from (by
          unfold nb077_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_231 F I) from (by
          unfold nb077_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I)
                  0)))) (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
          unfold nb077_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_235 F I), (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I),
        (nb077_alpha_dummy_237 x)), ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)),
        ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_235 F I), (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I),
        (nb077_alpha_dummy_237 x)), ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)),
        ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_229
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_234
        F I) ≠ (nb077_alpha_dummy_245 F I) from (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_245 F I) from
        (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235
        F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235
        F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_231 F I) from (by
                                          unfold nb077_alpha_dummy_231;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0216 F I) 0)))) (show
                                        (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x)
                                        from (by
                                          unfold nb077_alpha_dummy_232;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0217 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                                      ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                                      ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                                      ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                                      ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                                      ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
                                      ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_231;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0216 F I) 0)))) (show
                                      (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                      (by
                                        unfold nb077_alpha_dummy_232;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0217 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_231 F I) from (by
                                          unfold nb077_alpha_dummy_231;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0216 F I) 0)))) (show
                                        (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x)
                                        from (by
                                          unfold nb077_alpha_dummy_232;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0217 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                                      ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                                      ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                                      ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                                      ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                                      ((nb077_alpha_dummy_225 F I), (nb077_alpha_dummy_226 x)),
                                      ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part043`. -/


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
noncomputable def nb077_split_alpha_0029 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)),
        ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
        ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
        ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_253 F I))
          (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_253 F I))
            (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_254 x))
          (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_254 x))
            (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_227 F I) from (by
                      unfold nb077_alpha_dummy_227;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                  (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_229 x) from (by
                      unfold nb077_alpha_dummy_229;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0215 x) 0))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_228 F I) from (by
                        unfold nb077_alpha_dummy_228;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                    (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_230 x) from (by
                        unfold nb077_alpha_dummy_230;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0215 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_253 F I) from (by
                          unfold nb077_alpha_dummy_253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0244 F I) 0))))
                      (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_254 x) from (by
                          unfold nb077_alpha_dummy_254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0245 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_251 F I) from (by
                            unfold nb077_alpha_dummy_251;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0242 F I) 0))))
                        (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_252 x) from (by
                            unfold nb077_alpha_dummy_252;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0243 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_220 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_222 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_234 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_234;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0218 F I) 1)))) (show
                                      (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_237 x) from
                                      (by
                                        unfold nb077_alpha_dummy_237;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0219 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_233 F I) from (by
                                          unfold nb077_alpha_dummy_233;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0218 F I) 0)))) (show
                                        (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_236 x)
                                        from (by
                                          unfold nb077_alpha_dummy_236;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0219 x) 0))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_231 F I) from (by
          unfold nb077_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I) 0)))) (show (nb077_alpha_dummy_229 x) ≠
        (nb077_alpha_dummy_232 x) from (by
          unfold nb077_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_235 F I),
        (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I), (nb077_alpha_dummy_237 x)),
                                        ((nb077_alpha_dummy_233 F I),
        (nb077_alpha_dummy_236 x)), ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                                        ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                                        ((nb077_alpha_dummy_253 F I),
        (nb077_alpha_dummy_254 x)), ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
                                        ((nb077_alpha_dummy_220 F I),
        (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                                        ((nb077_alpha_dummy_249 F I),
        (nb077_alpha_dummy_250 x)), ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                                        ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                        ((nb077_alpha_dummy_139 F I),
        (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                        ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                        ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                        ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_241 F I) from (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_241 F I) from (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb077_alpha_dummy_235 F I),
        (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I), (nb077_alpha_dummy_237 x)),
        ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)), ((nb077_alpha_dummy_231 F I),
        (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
        ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)), ((nb077_alpha_dummy_253 F I),
        (nb077_alpha_dummy_254 x)), ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_245 F I) from (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_245 F I) from (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from (by
                                unfold nb077_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
                                unfold nb077_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                            ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                            ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                            ((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)),
                            ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
                            ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                            ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                            ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
                            ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                            ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from
                            (by
                              unfold nb077_alpha_dummy_231;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                          (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
                              unfold nb077_alpha_dummy_232;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from (by
                                unfold nb077_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
                                unfold nb077_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                            ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                            ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                            ((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)),
                            ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
                            ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                            ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                            ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
                            ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                            ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_227 F I) from (by
                        unfold nb077_alpha_dummy_227;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0214 F I) 0))))
                    (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_229 x) from (by
                        unfold nb077_alpha_dummy_229;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0215 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_228 F I) from (by
                          unfold nb077_alpha_dummy_228;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0214 F I) 1))))
                      (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_230 x) from (by
                          unfold nb077_alpha_dummy_230;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0215 x) 1))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_253 F I) from (by
                            unfold nb077_alpha_dummy_253;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0244 F I) 0))))
                        (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_254 x) from (by
                            unfold nb077_alpha_dummy_254;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0245 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_220 F I) ≠ (nb077_alpha_dummy_251 F I) from
                            (by
                              unfold nb077_alpha_dummy_251;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0242 F I) 0))))
                          (show (nb077_alpha_dummy_222 x) ≠ (nb077_alpha_dummy_252 x) from (by
                              unfold nb077_alpha_dummy_252;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0243 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_220 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_222 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_234 F I) from (by
                                          unfold nb077_alpha_dummy_234;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0218 F I) 1)))) (show
                                        (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_237 x)
                                        from (by
                                          unfold nb077_alpha_dummy_237;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0219 x) 1))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_227 F I) ≠
        (nb077_alpha_dummy_233 F I) from (by
          unfold nb077_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0218 F I) 0)))) (show (nb077_alpha_dummy_229 x) ≠
        (nb077_alpha_dummy_236 x) from (by
          unfold nb077_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0219 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from (by
          unfold nb077_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0216 F I) 0)))) (show (nb077_alpha_dummy_229 x) ≠
        (nb077_alpha_dummy_232 x) from (by
          unfold nb077_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0217 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_235 F I),
        (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I), (nb077_alpha_dummy_237 x)),
        ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)), ((nb077_alpha_dummy_231 F I),
        (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
        ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)), ((nb077_alpha_dummy_253 F I),
        (nb077_alpha_dummy_254 x)), ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
        ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I),
        (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
        ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_234 F
        I) ≠ (nb077_alpha_dummy_241 F I) from (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0222
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0223
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0220
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0221
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠ (nb077_alpha_dummy_241 F I) from
        (by
          unfold
            nb077_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0226
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_242 x) from (by
          unfold
            nb077_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0227
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_239 F I) from (by
          unfold
            nb077_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0224
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_240 x) from (by
          unfold
            nb077_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0225
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_235 F I), (nb077_alpha_dummy_238 x)), ((nb077_alpha_dummy_234 F I),
        (nb077_alpha_dummy_237 x)), ((nb077_alpha_dummy_233 F I), (nb077_alpha_dummy_236 x)),
        ((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)), ((nb077_alpha_dummy_227 F I),
        (nb077_alpha_dummy_229 x)), ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
        ((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)), ((nb077_alpha_dummy_251 F I),
        (nb077_alpha_dummy_252 x)), ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
        ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_249 F I),
        (nb077_alpha_dummy_250 x)), ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_234 F
        I) ≠ (nb077_alpha_dummy_245 F I) from (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_245 F I) from
        (by
          unfold
            nb077_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0230
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_246 x) from (by
          unfold
            nb077_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0231
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_234 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0228
                    F I)
                  0)))) (show (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0229
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_227
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235 F
        I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_235 F
        I) ≠ (nb077_alpha_dummy_247 F I) from (by
          unfold
            nb077_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0234
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_248 x) from (by
          unfold
            nb077_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0235
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_235 F I) ≠
        (nb077_alpha_dummy_243 F I) from (by
          unfold
            nb077_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0232
                    F I)
                  0)))) (show (nb077_alpha_dummy_238 x) ≠ (nb077_alpha_dummy_244 x) from (by
          unfold
            nb077_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0233
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from
                                (by
                                  unfold nb077_alpha_dummy_231;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                          0))))
                              (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                (by
                                  unfold nb077_alpha_dummy_232;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                              ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                              ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                              ((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)),
                              ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
                              ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                              ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                              ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
                              ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                              ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from (by
                                unfold nb077_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0216 F I) 0))))
                            (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from (by
                                unfold nb077_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_231 F I) from
                                (by
                                  unfold nb077_alpha_dummy_231;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0216 F I)
                                          0))))
                              (show (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_232 x) from
                                (by
                                  unfold nb077_alpha_dummy_232;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0217 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_231 F I), (nb077_alpha_dummy_232 x)),
                              ((nb077_alpha_dummy_227 F I), (nb077_alpha_dummy_229 x)),
                              ((nb077_alpha_dummy_228 F I), (nb077_alpha_dummy_230 x)),
                              ((nb077_alpha_dummy_253 F I), (nb077_alpha_dummy_254 x)),
                              ((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)),
                              ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)),
                              ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)),
                              ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)),
                              ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)),
                              ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part044`. -/


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
noncomputable def nb077_split_alpha_0030 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
        ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)),
        ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)),
        ((nb077_alpha_dummy_000 F I), x),
        ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_265 F I))
          (Class.cab (nb077_alpha_dummy_259 F I)
            (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_265 F I))
            (Class.cab (nb077_alpha_dummy_259 F I)
              (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_266 x))
          (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_266 x))
            (Class.cab (nb077_alpha_dummy_261 x)
              (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
                      unfold nb077_alpha_dummy_260;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
                  (show x ≠ (nb077_alpha_dummy_262 x) from (by
                      unfold nb077_alpha_dummy_262;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
                        unfold nb077_alpha_dummy_259;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
                    (show x ≠ (nb077_alpha_dummy_261 x) from (by
                        unfold nb077_alpha_dummy_261;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0254 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_265 F I) from (by
                          unfold nb077_alpha_dummy_265;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0256 F I) 0))))
                      (show x ≠ (nb077_alpha_dummy_266 x) from (by
                          unfold nb077_alpha_dummy_266;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0257 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_263 F I) from (by
                            unfold nb077_alpha_dummy_263;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0253 F I) 0))))
                        (show x ≠ (nb077_alpha_dummy_264 x) from (by
                            unfold nb077_alpha_dummy_264;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0255 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_255 F I) from
                            (by
                              unfold nb077_alpha_dummy_255;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0250 F I) 0))))
                          (show x ≠ (nb077_alpha_dummy_256 x) from (by
                              unfold nb077_alpha_dummy_256;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0251 x) 0))))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_255 F I))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_260 F I) ≠ (nb077_alpha_dummy_267 F I) from
                            (by
                              unfold nb077_alpha_dummy_267;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0258 F I) 0))))
                          (show (nb077_alpha_dummy_262 x) ≠ (nb077_alpha_dummy_269 x) from (by
                              unfold nb077_alpha_dummy_269;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0259 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_260 F I) ≠ (nb077_alpha_dummy_268 F I) from (by
                                unfold nb077_alpha_dummy_268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0258 F I) 1))))
                            (show (nb077_alpha_dummy_262 x) ≠ (nb077_alpha_dummy_270 x) from (by
                                unfold nb077_alpha_dummy_270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0259 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_260 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_262 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_274 F I) from
        (by
          unfold nb077_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0262 F I) 1)))) (show (nb077_alpha_dummy_269 x) ≠
        (nb077_alpha_dummy_277 x) from (by
          unfold nb077_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0263 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_273 F I) from (by
          unfold nb077_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0262 F I)
                  0)))) (show (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_276 x) from (by
          unfold nb077_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0263 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_271 F I) from (by
          unfold nb077_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0260 F I)
                  0)))) (show (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from (by
          unfold nb077_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0261 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I),
        (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)),
        ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
        (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
        ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
        (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
        ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
        (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x),
        ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I),
        (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)),
        ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
        (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
        ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
        (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
        ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
        (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x),
        ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_274
        F I) ≠ (nb077_alpha_dummy_285 F I) from (by
          unfold
            nb077_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_286 x) from (by
          unfold
            nb077_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_285 F I) from
        (by
          unfold
            nb077_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_286 x) from (by
          unfold
            nb077_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_275
        F I) ≠ (nb077_alpha_dummy_287 F I) from (by
          unfold
            nb077_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_288 x) from (by
          unfold
            nb077_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_275
        F I) ≠ (nb077_alpha_dummy_287 F I) from (by
          unfold
            nb077_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_288 x) from (by
          unfold
            nb077_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_271 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_271;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0260 F I) 0)))) (show
                                      (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from
                                      (by
                                        unfold nb077_alpha_dummy_272;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0261 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_271 F I),
                                      (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
                                      (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I),
                                      (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I),
                                      (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
                                      (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I),
                                      (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I),
                                      (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
                                      (nb077_alpha_dummy_256 x)),
                                    ((nb077_alpha_dummy_000 F I), x),
                                    ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)),
                                    ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                    ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                    ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                    ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                    ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                    ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                    ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                    ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                    ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_271 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_271;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0260 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from
                                    (by
                                      unfold nb077_alpha_dummy_272;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0261 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_271 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_271;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0260 F I) 0)))) (show
                                      (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from
                                      (by
                                        unfold nb077_alpha_dummy_272;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0261 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_271 F I),
                                      (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
                                      (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I),
                                      (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I),
                                      (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
                                      (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I),
                                      (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I),
                                      (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
                                      (nb077_alpha_dummy_256 x)),
                                    ((nb077_alpha_dummy_000 F I), x),
                                    ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)),
                                    ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                    ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                    ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                    ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                    ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                    ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                    ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                    ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                    ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_260 F I) from (by
                        unfold nb077_alpha_dummy_260;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))))
                    (show x ≠ (nb077_alpha_dummy_262 x) from (by
                        unfold nb077_alpha_dummy_262;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0254 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_259 F I) from (by
                          unfold nb077_alpha_dummy_259;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))))
                      (show x ≠ (nb077_alpha_dummy_261 x) from (by
                          unfold nb077_alpha_dummy_261;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0254 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_265 F I) from (by
                            unfold nb077_alpha_dummy_265;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0256 F I) 0))))
                        (show x ≠ (nb077_alpha_dummy_266 x) from (by
                            unfold nb077_alpha_dummy_266;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0257 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_263 F I) from
                            (by
                              unfold nb077_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0253 F I) 0))))
                          (show x ≠ (nb077_alpha_dummy_264 x) from (by
                              unfold nb077_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0255 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_000 F I) ≠ (nb077_alpha_dummy_255 F I) from (by
                                unfold nb077_alpha_dummy_255;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0250 F I) 0))))
                            (show x ≠ (nb077_alpha_dummy_256 x) from (by
                                unfold nb077_alpha_dummy_256;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0251 x) 0))))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_255 F I))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_260 F I) ≠ (nb077_alpha_dummy_267 F I) from (by
                                unfold nb077_alpha_dummy_267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0258 F I) 0))))
                            (show (nb077_alpha_dummy_262 x) ≠ (nb077_alpha_dummy_269 x) from (by
                                unfold nb077_alpha_dummy_269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0259 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_260 F I) ≠ (nb077_alpha_dummy_268 F I) from
                                (by
                                  unfold nb077_alpha_dummy_268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0258 F I)
                                          1))))
                              (show (nb077_alpha_dummy_262 x) ≠ (nb077_alpha_dummy_270 x) from
                                (by
                                  unfold nb077_alpha_dummy_270;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0259 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_260 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_262 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_274 F I) from (by
          unfold nb077_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0262 F I)
                  1)))) (show (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_277 x) from (by
          unfold nb077_alpha_dummy_277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0263 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_273 F I) from (by
          unfold nb077_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0262 F I)
                  0)))) (show (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_276 x) from (by
          unfold nb077_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0263 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_267 F I) ≠
        (nb077_alpha_dummy_271 F I) from (by
          unfold nb077_alpha_dummy_271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0260 F I)
                  0)))) (show (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from (by
          unfold nb077_alpha_dummy_272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0261 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I),
        (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)),
        ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
        (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
        ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
        (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
        ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
        (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x),
        ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0266
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0267
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0264
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0265
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠ (nb077_alpha_dummy_281 F I) from
        (by
          unfold
            nb077_alpha_dummy_281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0270
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_282 x) from (by
          unfold
            nb077_alpha_dummy_282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0271
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_279 F I) from (by
          unfold
            nb077_alpha_dummy_279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0268
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_280 x) from (by
          unfold
            nb077_alpha_dummy_280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0269
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I),
        (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)),
        ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I),
        (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
        ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I),
        (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
        ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I),
        (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x),
        ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_269
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_274
        F I) ≠ (nb077_alpha_dummy_285 F I) from (by
          unfold
            nb077_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_286 x) from (by
          unfold
            nb077_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_285 F I) from
        (by
          unfold
            nb077_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0274
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_286 x) from (by
          unfold
            nb077_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0275
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_274 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0272
                    F I)
                  0)))) (show (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0273
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_267
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_275
        F I) ≠ (nb077_alpha_dummy_287 F I) from (by
          unfold
            nb077_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_288 x) from (by
          unfold
            nb077_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_275
        F I) ≠ (nb077_alpha_dummy_287 F I) from (by
          unfold
            nb077_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0278
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_288 x) from (by
          unfold
            nb077_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0279
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_275 F I) ≠
        (nb077_alpha_dummy_283 F I) from (by
          unfold
            nb077_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0276
                    F I)
                  0)))) (show (nb077_alpha_dummy_278 x) ≠ (nb077_alpha_dummy_284 x) from (by
          unfold
            nb077_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0277
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_267 F I) ≠
        (nb077_alpha_dummy_271 F I) from (by
                                          unfold nb077_alpha_dummy_271;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0260 F I) 0)))) (show
                                        (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x)
                                        from (by
                                          unfold nb077_alpha_dummy_272;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0261 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)),
                                      ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)),
                                      ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
                                      ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)),
                                      ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)),
                                      ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
                                      ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)),
                                      ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)),
                                      ((nb077_alpha_dummy_000 F I), x),
                                      ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_271 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_271;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0260 F I) 0)))) (show
                                      (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x) from
                                      (by
                                        unfold nb077_alpha_dummy_272;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0261 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_267 F I) ≠
        (nb077_alpha_dummy_271 F I) from (by
                                          unfold nb077_alpha_dummy_271;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0260 F I) 0)))) (show
                                        (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_272 x)
                                        from (by
                                          unfold nb077_alpha_dummy_272;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0261 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)),
                                      ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)),
                                      ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)),
                                      ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)),
                                      ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)),
                                      ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)),
                                      ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)),
                                      ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)),
                                      ((nb077_alpha_dummy_000 F I), x),
                                      ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
