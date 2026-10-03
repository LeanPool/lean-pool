/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part026`. -/


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
noncomputable def nb067_split_alpha_0057 (x : Var) (y : Var) (f : Var) :
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
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_214))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_213))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_216 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_215 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_220) from (by
                              unfold nb067_alpha_dummy_220;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                          (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_223 f) from (by
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
                                      (mem_lt_freshVar (nb067_support_mem_0224) 0))))
                            (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_222 f) from (by
                                unfold nb067_alpha_dummy_222;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0225 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                                  unfold nb067_alpha_dummy_217;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                              (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from
                                (by
                                  unfold nb067_alpha_dummy_218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
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
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0056 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                      unfold nb067_alpha_dummy_217;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                  (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                      unfold nb067_alpha_dummy_218;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
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
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                    unfold nb067_alpha_dummy_217;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                    unfold nb067_alpha_dummy_218;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
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
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb067_split_alpha_0058 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
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
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠
        (nb067_alpha_dummy_213) from (by
          unfold nb067_alpha_dummy_213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_215 f) from (by
          unfold nb067_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
          unfold nb067_alpha_dummy_214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_216 f) from (by
          unfold nb067_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_239) from (by
          unfold nb067_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_240 f) from (by
          unfold nb067_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_237) from (by
          unfold nb067_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_238 f) from (by
          unfold nb067_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0057 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠
        (nb067_alpha_dummy_213) from (by
          unfold nb067_alpha_dummy_213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_215 f) from (by
          unfold nb067_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
          unfold nb067_alpha_dummy_214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_216 f) from (by
          unfold nb067_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_239) from (by
          unfold nb067_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_240 f) from (by
          unfold nb067_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_237) from (by
          unfold nb067_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_238 f) from (by
          unfold nb067_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0057 x y f)))))))))
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
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
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
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_213) from (by
          unfold nb067_alpha_dummy_213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_215 f) from (by
          unfold nb067_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
          unfold nb067_alpha_dummy_214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_216 f) from (by
          unfold nb067_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_239) from (by
          unfold nb067_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_240 f) from (by
          unfold nb067_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_237)
        from (by
          unfold nb067_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248)
                  0)))) (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_238 f) from (by
          unfold nb067_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0057 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_213) from (by
          unfold nb067_alpha_dummy_213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_215 f) from (by
          unfold nb067_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
          unfold nb067_alpha_dummy_214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_216 f) from (by
          unfold nb067_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_239) from (by
          unfold nb067_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067_alpha_dummy_208 f) ≠
        (nb067_alpha_dummy_240 f) from (by
          unfold nb067_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_237)
        from (by
          unfold nb067_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248)
                  0)))) (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_238 f) from (by
          unfold nb067_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0057 x y f)))))))))
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
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0059 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
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
                                  (TAlphaWff.neg (nb067_split_alpha_0050 x y f)))))))))
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
                                  (TAlphaWff.neg (nb067_split_alpha_0050 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0053 x y f)))))))))
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
                                    (TAlphaWff.neg (nb067_split_alpha_0055 x y f)))))))))
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
                                    (TAlphaWff.neg (nb067_split_alpha_0055 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0058 x y f))))))))
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
                (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_085) from
                    (by
                      unfold nb067_alpha_dummy_085;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))))
                  (show f ≠ (nb067_alpha_dummy_088 f) from (by
                      unfold nb067_alpha_dummy_088;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_084) from
                      (by
                        unfold nb067_alpha_dummy_084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))))
                    (show f ≠ (nb067_alpha_dummy_087 f) from (by
                        unfold nb067_alpha_dummy_087;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0258 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_083) from (by
                          unfold nb067_alpha_dummy_083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0256) 0))))
                      (show f ≠ (nb067_alpha_dummy_086 f) from (by
                          unfold nb067_alpha_dummy_086;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0258 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_089) from (by
                            unfold nb067_alpha_dummy_089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0257) 0))))
                        (show f ≠ (nb067_alpha_dummy_090 f) from (by
                            unfold nb067_alpha_dummy_090;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0259 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0060 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
        ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
        ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
        ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
        ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_255))
            (syn_cun (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_258 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_259 f))
              (Class.cv (nb067_alpha_dummy_260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
          ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
          ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
          ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
          ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
          ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
          ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_267) from (by
                                unfold nb067_alpha_dummy_267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_268 f) from (by
                                unfold nb067_alpha_dummy_268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_267) from (by
                                unfold nb067_alpha_dummy_267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_268 f) from (by
                                unfold nb067_alpha_dummy_268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_269) from (by
                                unfold nb067_alpha_dummy_269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_270 f) from (by
                                unfold nb067_alpha_dummy_270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_269) from (by
                                unfold nb067_alpha_dummy_269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_270 f) from (by
                                unfold nb067_alpha_dummy_270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part027`. -/


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
noncomputable def nb067_split_alpha_0061 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_249))
            (Class.cv (nb067_alpha_dummy_242))) (Wff.classEq (Class.cv (nb067_alpha_dummy_250))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_249))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f))
            (Class.cv (nb067_alpha_dummy_244 f)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_252 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_251 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_249) from (by
                unfold nb067_alpha_dummy_249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))))
            (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_251 f) from (by
                unfold nb067_alpha_dummy_251;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))))
            (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
                  unfold nb067_alpha_dummy_250;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))))
              (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_252 f) from (by
                  unfold nb067_alpha_dummy_252;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_256) from (by
                                  unfold nb067_alpha_dummy_256;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0274) 1))))
                              (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_259 f) from
                                (by
                                  unfold nb067_alpha_dummy_259;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0275 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_255) from (by
                                    unfold nb067_alpha_dummy_255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0274) 0)))) (show
                                  (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_258 f) from (by
                                    unfold nb067_alpha_dummy_258;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0275 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from
                                    (by
                                      unfold nb067_alpha_dummy_253;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0272)
                                              0)))) (show
                                    (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from
                                    (by
                                      unfold nb067_alpha_dummy_254;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0273 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
                                  ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
                                  ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
                                  ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                                  ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                                  ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                                  ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                                  ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                                  ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                                  ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0060 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from (by
                          unfold nb067_alpha_dummy_253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                          unfold nb067_alpha_dummy_254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from
                      (by
                        unfold nb067_alpha_dummy_253;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                    (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                        unfold nb067_alpha_dummy_254;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from (by
                          unfold nb067_alpha_dummy_253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                          unfold nb067_alpha_dummy_254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0062 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
        ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
        ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
        ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
        ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
        ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_255))
            (syn_cun (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_258 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_259 f))
              (Class.cv (nb067_alpha_dummy_260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_263) from (by
                              unfold nb067_alpha_dummy_263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_264 f) from (by
                              unfold nb067_alpha_dummy_264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_261) from (by
                                unfold nb067_alpha_dummy_261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_262 f) from (by
                                unfold nb067_alpha_dummy_262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
          ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
          ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
          ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
          ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
          ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
          ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
          ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
          ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_267) from (by
                                unfold nb067_alpha_dummy_267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_268 f) from (by
                                unfold nb067_alpha_dummy_268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_267) from (by
                                unfold nb067_alpha_dummy_267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_268 f) from (by
                                unfold nb067_alpha_dummy_268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_269) from (by
                                unfold nb067_alpha_dummy_269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_270 f) from (by
                                unfold nb067_alpha_dummy_270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_269) from (by
                                unfold nb067_alpha_dummy_269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_270 f) from (by
                                unfold nb067_alpha_dummy_270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_257) ≠ (nb067_alpha_dummy_265) from (by
                                  unfold nb067_alpha_dummy_265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067_alpha_dummy_260 f) ≠ (nb067_alpha_dummy_266 f) from
                                (by
                                  unfold nb067_alpha_dummy_266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0063 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
        ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_249))
          (Class.cv (nb067_alpha_dummy_242))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_250))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_249))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f))
          (Class.cv (nb067_alpha_dummy_244 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_252 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_251 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_249) from (by
              unfold nb067_alpha_dummy_249;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))))
          (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_251 f) from (by
              unfold nb067_alpha_dummy_251;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
                unfold nb067_alpha_dummy_250;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))))
            (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_252 f) from (by
                unfold nb067_alpha_dummy_252;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_275) from (by
                  unfold nb067_alpha_dummy_275;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0300) 0))))
              (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_276 f) from (by
                  unfold nb067_alpha_dummy_276;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0301 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_273) from (by
                    unfold nb067_alpha_dummy_273;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0298) 0))))
                (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_274 f) from (by
                    unfold nb067_alpha_dummy_274;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0299 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_256) from (by
                                  unfold nb067_alpha_dummy_256;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0274) 1))))
                              (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_259 f) from
                                (by
                                  unfold nb067_alpha_dummy_259;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0275 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_255) from (by
                                    unfold nb067_alpha_dummy_255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0274) 0)))) (show
                                  (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_258 f) from (by
                                    unfold nb067_alpha_dummy_258;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0275 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from
                                    (by
                                      unfold nb067_alpha_dummy_253;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0272)
                                              0)))) (show
                                    (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from
                                    (by
                                      unfold nb067_alpha_dummy_254;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0273 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
                                  ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
                                  ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
                                  ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                                  ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                                  ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                                  ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                                  ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                                  ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                                  ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                                  ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                                  ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0062 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from (by
                          unfold nb067_alpha_dummy_253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                          unfold nb067_alpha_dummy_254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                      ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from
                      (by
                        unfold nb067_alpha_dummy_253;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                    (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                        unfold nb067_alpha_dummy_254;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_253) from (by
                          unfold nb067_alpha_dummy_253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_254 f) from (by
                          unfold nb067_alpha_dummy_254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                      ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0064 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_271))
          (Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_271))
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_272 f))
          (Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_272 f))
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_242) from
                    (by
                      unfold nb067_alpha_dummy_242;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                  (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_244 f) from (by
                      unfold nb067_alpha_dummy_244;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_241) from
                      (by
                        unfold nb067_alpha_dummy_241;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_243 f) from (by
                        unfold nb067_alpha_dummy_243;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_271) from (by
                          unfold nb067_alpha_dummy_271;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_272 f) from (by
                          unfold nb067_alpha_dummy_272;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_245) from (by
                            unfold nb067_alpha_dummy_245;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_246 f) from (by
                            unfold nb067_alpha_dummy_246;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0063 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0063 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                          ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_242) from
                      (by
                        unfold nb067_alpha_dummy_242;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_244 f) from (by
                        unfold nb067_alpha_dummy_244;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_241) from (by
                          unfold nb067_alpha_dummy_241;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_243 f) from (by
                          unfold nb067_alpha_dummy_243;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0294 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_271) from (by
                            unfold nb067_alpha_dummy_271;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_272 f) from (by
                            unfold nb067_alpha_dummy_272;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_245) from (by
                              unfold nb067_alpha_dummy_245;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                          (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_246 f) from (by
                              unfold nb067_alpha_dummy_246;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0063 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0063 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                            ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                            ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                            ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                            ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0065 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (syn_wbr (Class.cv (nb067_alpha_dummy_083))
          (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085)))
        (Wff.neg (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_084)))))
      (Wff.imp (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb067_alpha_dummy_088 f))) (Wff.neg
          (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_128) from
                                    (by
                                      unfold nb067_alpha_dummy_128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_130 f) from
                                    (by
                                      unfold nb067_alpha_dummy_130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_127) from (by
                                        unfold nb067_alpha_dummy_127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067_alpha_dummy_086 f) ≠
                                        (nb067_alpha_dummy_129 f) from (by
                                        unfold nb067_alpha_dummy_129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_133) from
                                        (by
                                          unfold nb067_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_134 f) from (by
                                          unfold nb067_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠
        (nb067_alpha_dummy_131) from (by
          unfold nb067_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_132 f) from (by
          unfold nb067_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb067_split_alpha_0045 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_128) from
                                    (by
                                      unfold nb067_alpha_dummy_128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_130 f) from
                                    (by
                                      unfold nb067_alpha_dummy_130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_127) from (by
                                        unfold nb067_alpha_dummy_127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067_alpha_dummy_086 f) ≠
                                        (nb067_alpha_dummy_129 f) from (by
                                        unfold nb067_alpha_dummy_129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_133) from
                                        (by
                                          unfold nb067_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_134 f) from (by
                                          unfold nb067_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠
        (nb067_alpha_dummy_131) from (by
          unfold nb067_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_132 f) from (by
          unfold nb067_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb067_split_alpha_0045 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0048 x y f))))))))
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0059 x y f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_242) from (by
                                        unfold nb067_alpha_dummy_242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067_alpha_dummy_088 f) ≠
                                        (nb067_alpha_dummy_244 f) from (by
                                        unfold nb067_alpha_dummy_244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_241) from
                                        (by
                                          unfold nb067_alpha_dummy_241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_243 f) from (by
                                          unfold nb067_alpha_dummy_243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠
        (nb067_alpha_dummy_247) from (by
          unfold nb067_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_248 f) from (by
          unfold nb067_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_245) from (by
          unfold nb067_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_246 f) from (by
          unfold nb067_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb067_split_alpha_0061 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_242) from (by
                                        unfold nb067_alpha_dummy_242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067_alpha_dummy_088 f) ≠
                                        (nb067_alpha_dummy_244 f) from (by
                                        unfold nb067_alpha_dummy_244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_241) from
                                        (by
                                          unfold nb067_alpha_dummy_241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_243 f) from (by
                                          unfold nb067_alpha_dummy_243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠
        (nb067_alpha_dummy_247) from (by
          unfold nb067_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_248 f) from (by
          unfold nb067_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_245) from (by
          unfold nb067_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_246 f) from (by
          unfold nb067_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb067_split_alpha_0061 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0064 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_085) from (by
                unfold nb067_alpha_dummy_085;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))))
            (show f ≠ (nb067_alpha_dummy_088 f) from (by
                unfold nb067_alpha_dummy_088;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))))
            (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_084) from (by
                  unfold nb067_alpha_dummy_084;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))))
              (show f ≠ (nb067_alpha_dummy_087 f) from (by
                  unfold nb067_alpha_dummy_087;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 1))))
              (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_083) from (by
                    unfold nb067_alpha_dummy_083;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 0))))
                (show f ≠ (nb067_alpha_dummy_086 f) from (by
                    unfold nb067_alpha_dummy_086;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_089) from
                    (by
                      unfold nb067_alpha_dummy_089;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0257) 0))))
                  (show f ≠ (nb067_alpha_dummy_090 f) from (by
                      unfold nb067_alpha_dummy_090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0259 f) 0))))
                  (TAlphaVar.here _ _ _)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part028`. -/


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
noncomputable def nb067_split_alpha_0066 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
        ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
        ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
        ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
        ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
        ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
        ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
        ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
        ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
        ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_295))
            (syn_cun (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_298 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_299 f))
              (Class.cv (nb067_alpha_dummy_300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
          ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
          ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
          ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
          ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
          ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
          ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
          ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
          ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
          ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_307) from (by
                                unfold nb067_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_308 f) from (by
                                unfold nb067_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_307) from (by
                                unfold nb067_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_308 f) from (by
                                unfold nb067_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_309) from (by
                                unfold nb067_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_310 f) from (by
                                unfold nb067_alpha_dummy_310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_309) from (by
                                unfold nb067_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_310 f) from (by
                                unfold nb067_alpha_dummy_310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0067 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
        ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
        ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
        ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
        (syn_cphi (Class.cv (nb067_alpha_dummy_282))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
        (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
            ((Class.cv (nb067_alpha_dummy_279 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_289) from (by
                    unfold nb067_alpha_dummy_289;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 0))))
                (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_291 f) from (by
                    unfold nb067_alpha_dummy_291;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_290) from
                    (by
                      unfold nb067_alpha_dummy_290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 1))))
                  (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_292 f) from (by
                      unfold nb067_alpha_dummy_292;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_282))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_284 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_296) from
                                    (by
                                      unfold nb067_alpha_dummy_296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0312)
                                              1)))) (show
                                    (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_299 f) from
                                    (by
                                      unfold nb067_alpha_dummy_299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0313 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_295) from (by
                                        unfold nb067_alpha_dummy_295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0312)
                                                0)))) (show (nb067_alpha_dummy_291 f) ≠
                                        (nb067_alpha_dummy_298 f) from (by
                                        unfold nb067_alpha_dummy_298;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0313 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from
                                        (by
                                          unfold nb067_alpha_dummy_293;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0310)
                                                  0)))) (show (nb067_alpha_dummy_291 f) ≠
        (nb067_alpha_dummy_294 f) from (by
                                          unfold nb067_alpha_dummy_294;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0311 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
                                      ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
                                      ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
                                      ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                                      ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                                      ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                                      ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                                      ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                                      ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
                                      ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                                      ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                        (nb067_alpha_dummy_004 x y f)),
                                      ((nb067_alpha_dummy_002), y),
                                      ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005),
                                        (nb067_alpha_dummy_006 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067_split_alpha_0066 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from (by
                              unfold nb067_alpha_dummy_293;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                          (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                              unfold nb067_alpha_dummy_294;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                          ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                          ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                          ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                          ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                          ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
                          ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from (by
                            unfold nb067_alpha_dummy_293;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                        (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                            unfold nb067_alpha_dummy_294;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from (by
                              unfold nb067_alpha_dummy_293;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                          (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                              unfold nb067_alpha_dummy_294;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                          ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                          ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                          ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                          ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                          ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)),
                          ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0068 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
        ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
        ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
        ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
        ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
        ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
        ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
        ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
        ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
        ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
        ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
        ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_295))
            (syn_cun (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_299 f))
            (Class.cv (nb067_alpha_dummy_300 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_298 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_299 f))
              (Class.cv (nb067_alpha_dummy_300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_303) from (by
                              unfold nb067_alpha_dummy_303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_304 f) from (by
                              unfold nb067_alpha_dummy_304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_301) from (by
                                unfold nb067_alpha_dummy_301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_302 f) from (by
                                unfold nb067_alpha_dummy_302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
          ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
          ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
          ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
          ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
          ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
          ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
          ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
          ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
          ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
          ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
          ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
          ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
          ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_307) from (by
                                unfold nb067_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_308 f) from (by
                                unfold nb067_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_307) from (by
                                unfold nb067_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_308 f) from (by
                                unfold nb067_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_309) from (by
                                unfold nb067_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_310 f) from (by
                                unfold nb067_alpha_dummy_310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_309) from (by
                                unfold nb067_alpha_dummy_309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_310 f) from (by
                                unfold nb067_alpha_dummy_310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_297) ≠ (nb067_alpha_dummy_305) from (by
                                  unfold nb067_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067_alpha_dummy_300 f) ≠ (nb067_alpha_dummy_306 f) from
                                (by
                                  unfold nb067_alpha_dummy_306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part029`. -/


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
noncomputable def nb067_split_alpha_0069 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
        ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
        ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
        ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
        ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
        ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
        ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
        ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_289))
          (Class.cv (nb067_alpha_dummy_282))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_290))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_289))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_291 f))
          (Class.cv (nb067_alpha_dummy_284 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_292 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_291 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_289) from (by
              unfold nb067_alpha_dummy_289;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 0))))
          (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_291 f) from (by
              unfold nb067_alpha_dummy_291;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_290) from (by
                unfold nb067_alpha_dummy_290;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 1))))
            (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_292 f) from (by
                unfold nb067_alpha_dummy_292;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_315) from (by
                  unfold nb067_alpha_dummy_315;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0338) 0))))
              (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_316 f) from (by
                  unfold nb067_alpha_dummy_316;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0339 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_282) ≠ (nb067_alpha_dummy_313) from (by
                    unfold nb067_alpha_dummy_313;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0336) 0))))
                (show (nb067_alpha_dummy_284 f) ≠ (nb067_alpha_dummy_314 f) from (by
                    unfold nb067_alpha_dummy_314;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0337 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_282))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_284 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_296) from (by
                                  unfold nb067_alpha_dummy_296;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0312) 1))))
                              (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_299 f) from
                                (by
                                  unfold nb067_alpha_dummy_299;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0313 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_295) from (by
                                    unfold nb067_alpha_dummy_295;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0312) 0)))) (show
                                  (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_298 f) from (by
                                    unfold nb067_alpha_dummy_298;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0313 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from
                                    (by
                                      unfold nb067_alpha_dummy_293;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0310)
                                              0)))) (show
                                    (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from
                                    (by
                                      unfold nb067_alpha_dummy_294;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0311 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)),
                                  ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)),
                                  ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)),
                                  ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                                  ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                                  ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                                  ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
                                  ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
                                  ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                                  ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                                  ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
                                  ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                                  ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                                  ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0068 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from (by
                          unfold nb067_alpha_dummy_293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                      (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                          unfold nb067_alpha_dummy_294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                      ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                      ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                      ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
                      ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
                      ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                      ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                      ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
                      ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from
                      (by
                        unfold nb067_alpha_dummy_293;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                    (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                        unfold nb067_alpha_dummy_294;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_293) from (by
                          unfold nb067_alpha_dummy_293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                      (show (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_294 f) from (by
                          unfold nb067_alpha_dummy_294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)),
                      ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)),
                      ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)),
                      ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)),
                      ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
                      ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                      ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                      ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
                      ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                      ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                      ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0070 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
        ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_311))
          (Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_311))
            (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_312 f))
          (Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_312 f))
            (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_282) from
                    (by
                      unfold nb067_alpha_dummy_282;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))))
                  (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_284 f) from (by
                      unfold nb067_alpha_dummy_284;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_281) from
                      (by
                        unfold nb067_alpha_dummy_281;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))))
                    (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_283 f) from (by
                        unfold nb067_alpha_dummy_283;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0332 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_311) from (by
                          unfold nb067_alpha_dummy_311;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0334) 0))))
                      (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_312 f) from (by
                          unfold nb067_alpha_dummy_312;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0335 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_285) from (by
                            unfold nb067_alpha_dummy_285;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0331) 0))))
                        (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_286 f) from (by
                            unfold nb067_alpha_dummy_286;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0333 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪
                              ((syn_cvv)).fv) (by decide)) (freshVar_injective
                            (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_278))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_277))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_279 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0069 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0069 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
                          ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                          ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                          ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
                          ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
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
                  (TAlphaVar.there (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_282) from
                      (by
                        unfold nb067_alpha_dummy_282;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))))
                    (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_284 f) from (by
                        unfold nb067_alpha_dummy_284;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0332 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_281) from (by
                          unfold nb067_alpha_dummy_281;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0330) 0))))
                      (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_283 f) from (by
                          unfold nb067_alpha_dummy_283;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0332 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_311) from (by
                            unfold nb067_alpha_dummy_311;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0334) 0))))
                        (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_312 f) from (by
                            unfold nb067_alpha_dummy_312;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0335 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_285) from (by
                              unfold nb067_alpha_dummy_285;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0331) 0))))
                          (show (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_286 f) from (by
                              unfold nb067_alpha_dummy_286;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0333 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪
                                ((syn_cvv)).fv) (by decide)) (freshVar_injective
                              (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_278))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_277))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_279 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0069 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0069 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)),
                            ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)),
                            ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)),
                            ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)),
                            ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)),
                            ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
                            ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0071 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0072 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_177))
          (Class.cv (nb067_alpha_dummy_170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_178))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f))
          (Class.cv (nb067_alpha_dummy_172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_177) from (by
              unfold nb067_alpha_dummy_177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_179 f) from (by
              unfold nb067_alpha_dummy_179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
                unfold nb067_alpha_dummy_178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_180 f) from (by
                unfold nb067_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_184) from (by
                                  unfold nb067_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_187 f) from
                                (by
                                  unfold nb067_alpha_dummy_187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_183) from (by
                                    unfold nb067_alpha_dummy_183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_186 f) from (by
                                    unfold nb067_alpha_dummy_186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                                    (by
                                      unfold nb067_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from
                                    (by
                                      unfold nb067_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                                  ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                                  ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                                  ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                                  ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
                            (TAlphaWff.neg (nb067_split_alpha_0071 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
                  (TAlphaVar.there (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                      (by
                        unfold nb067_alpha_dummy_181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                        unfold nb067_alpha_dummy_182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part030`. -/


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
noncomputable def nb067_split_alpha_0073 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
          ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0074 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_177))
          (Class.cv (nb067_alpha_dummy_170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_178))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f))
          (Class.cv (nb067_alpha_dummy_172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_177) from (by
              unfold nb067_alpha_dummy_177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_179 f) from (by
              unfold nb067_alpha_dummy_179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
                unfold nb067_alpha_dummy_178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_180 f) from (by
                unfold nb067_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_203) from (by
                  unfold nb067_alpha_dummy_203;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0))))
              (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_204 f) from (by
                  unfold nb067_alpha_dummy_204;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_201) from (by
                    unfold nb067_alpha_dummy_201;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0))))
                (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_202 f) from (by
                    unfold nb067_alpha_dummy_202;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_184) from (by
                                  unfold nb067_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_187 f) from
                                (by
                                  unfold nb067_alpha_dummy_187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_183) from (by
                                    unfold nb067_alpha_dummy_183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_186 f) from (by
                                    unfold nb067_alpha_dummy_186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                                    (by
                                      unfold nb067_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from
                                    (by
                                      unfold nb067_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                                  ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                                  ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                                  ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                                  ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                                  ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                                  ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
                            (TAlphaWff.neg (nb067_split_alpha_0073 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                      ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
                  (TAlphaVar.there (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                      (by
                        unfold nb067_alpha_dummy_181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                        unfold nb067_alpha_dummy_182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                      ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
noncomputable def nb067_split_alpha_0075 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)),
        ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
          (Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
          (Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_170) from
                    (by
                      unfold nb067_alpha_dummy_170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                  (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_172 f) from (by
                      unfold nb067_alpha_dummy_172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_169) from
                      (by
                        unfold nb067_alpha_dummy_169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                    (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_171 f) from (by
                        unfold nb067_alpha_dummy_171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_199) from (by
                          unfold nb067_alpha_dummy_199;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                      (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_200 f) from (by
                          unfold nb067_alpha_dummy_200;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_173) from (by
                            unfold nb067_alpha_dummy_173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                        (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_174 f) from (by
                            unfold nb067_alpha_dummy_174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0074 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0074 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
                  (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_170) from
                      (by
                        unfold nb067_alpha_dummy_170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                    (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_172 f) from (by
                        unfold nb067_alpha_dummy_172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_169) from (by
                          unfold nb067_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                      (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_171 f) from (by
                          unfold nb067_alpha_dummy_171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0206 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_199) from (by
                            unfold nb067_alpha_dummy_199;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                        (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_200 f) from (by
                            unfold nb067_alpha_dummy_200;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_173) from (by
                              unfold nb067_alpha_dummy_173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                          (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_174 f) from (by
                              unfold nb067_alpha_dummy_174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0074 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0074 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                            ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                            ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                            ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                            ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
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
noncomputable def nb067_split_alpha_0076 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
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
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
