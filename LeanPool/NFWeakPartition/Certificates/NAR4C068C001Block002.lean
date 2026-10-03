/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part006`. -/


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

theorem nb068_fresh_192 (f : Var) :
    (nb068_alpha_dummy_160 f) ∉
      (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_160] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv)
      0

theorem nb068_fresh_193 :
    (nb068_alpha_dummy_175) ∉ (((Class.cv (nb068_alpha_dummy_168))).fv) := by
  simpa only [nb068_alpha_dummy_175] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_168))).fv) 0

theorem nb068_fresh_194 :
    (nb068_alpha_dummy_176) ∉ (((Class.cv (nb068_alpha_dummy_168))).fv) := by
  simpa only [nb068_alpha_dummy_176] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_168))).fv) 1

theorem nb068_distinct_195 : (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_176) := by
  simpa only [nb068_alpha_dummy_175, nb068_alpha_dummy_176] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_196 (f : Var) :
    (nb068_alpha_dummy_177 f) ∉ (((Class.cv (nb068_alpha_dummy_170 f))).fv) := by
  simpa only [nb068_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_170 f))).fv) 0

theorem nb068_fresh_197 (f : Var) :
    (nb068_alpha_dummy_178 f) ∉ (((Class.cv (nb068_alpha_dummy_170 f))).fv) := by
  simpa only [nb068_alpha_dummy_178] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_170 f))).fv) 1

theorem nb068_distinct_198 (f : Var) :
    (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_178 f) := by
  simpa only [nb068_alpha_dummy_177, nb068_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_199 :
    (nb068_alpha_dummy_181) ∉
      (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_181] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_200 :
    (nb068_alpha_dummy_182) ∉
      (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_182] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_201 :
    (nb068_alpha_dummy_183) ∉
      (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_183] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_202 : (nb068_alpha_dummy_181) ≠ (nb068_alpha_dummy_182) := by
  simpa only [nb068_alpha_dummy_181, nb068_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_203 : (nb068_alpha_dummy_181) ≠ (nb068_alpha_dummy_183) := by
  simpa only [nb068_alpha_dummy_181, nb068_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_204 : (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_183) := by
  simpa only [nb068_alpha_dummy_182, nb068_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_205 (f : Var) :
    (nb068_alpha_dummy_184 f) ∉
      (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_184] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_206 (f : Var) :
    (nb068_alpha_dummy_185 f) ∉
      (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_185] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_207 (f : Var) :
    (nb068_alpha_dummy_186 f) ∉
      (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_186] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_208 (f : Var) :
    (nb068_alpha_dummy_184 f) ≠ (nb068_alpha_dummy_185 f) := by
  simpa only [nb068_alpha_dummy_184, nb068_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_209 (f : Var) :
    (nb068_alpha_dummy_184 f) ≠ (nb068_alpha_dummy_186 f) := by
  simpa only [nb068_alpha_dummy_184, nb068_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_210 (f : Var) :
    (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_186 f) := by
  simpa only [nb068_alpha_dummy_185, nb068_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_211 :
    (nb068_alpha_dummy_193) ∉
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) :=
  by
  simpa only [nb068_alpha_dummy_193] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv)
      0

theorem nb068_fresh_212 :
    (nb068_alpha_dummy_189) ∉
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) :=
  by
  simpa only [nb068_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv)
      0

theorem nb068_fresh_213 :
    (nb068_alpha_dummy_195) ∉
      (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) :=
  by
  simpa only [nb068_alpha_dummy_195] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv)
      0

theorem nb068_fresh_214 (f : Var) :
    (nb068_alpha_dummy_194 f) ∉
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_194] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv)
      0

theorem nb068_fresh_215 (f : Var) :
    (nb068_alpha_dummy_190 f) ∉
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_190] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv)
      0

theorem nb068_fresh_216 (f : Var) :
    (nb068_alpha_dummy_196 f) ∉
      (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_196] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv)
      0

theorem nb068_fresh_217 :
    (nb068_alpha_dummy_211) ∉ (((Class.cv (nb068_alpha_dummy_204))).fv) := by
  simpa only [nb068_alpha_dummy_211] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_204))).fv) 0

theorem nb068_fresh_218 :
    (nb068_alpha_dummy_212) ∉ (((Class.cv (nb068_alpha_dummy_204))).fv) := by
  simpa only [nb068_alpha_dummy_212] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_204))).fv) 1

theorem nb068_distinct_219 : (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_212) := by
  simpa only [nb068_alpha_dummy_211, nb068_alpha_dummy_212] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_204))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_220 (f : Var) :
    (nb068_alpha_dummy_213 f) ∉ (((Class.cv (nb068_alpha_dummy_206 f))).fv) := by
  simpa only [nb068_alpha_dummy_213] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_206 f))).fv) 0

theorem nb068_fresh_221 (f : Var) :
    (nb068_alpha_dummy_214 f) ∉ (((Class.cv (nb068_alpha_dummy_206 f))).fv) := by
  simpa only [nb068_alpha_dummy_214] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_206 f))).fv) 1

theorem nb068_distinct_222 (f : Var) :
    (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_214 f) := by
  simpa only [nb068_alpha_dummy_213, nb068_alpha_dummy_214] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_206 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_223 :
    (nb068_alpha_dummy_217) ∉
      (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_217] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_224 :
    (nb068_alpha_dummy_218) ∉
      (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_218] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_225 :
    (nb068_alpha_dummy_219) ∉
      (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_219] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_226 : (nb068_alpha_dummy_217) ≠ (nb068_alpha_dummy_218) := by
  simpa only [nb068_alpha_dummy_217, nb068_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_227 : (nb068_alpha_dummy_217) ≠ (nb068_alpha_dummy_219) := by
  simpa only [nb068_alpha_dummy_217, nb068_alpha_dummy_219] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_228 : (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_219) := by
  simpa only [nb068_alpha_dummy_218, nb068_alpha_dummy_219] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_229 (f : Var) :
    (nb068_alpha_dummy_220 f) ∉
      (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_220] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_230 (f : Var) :
    (nb068_alpha_dummy_221 f) ∉
      (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_221] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_231 (f : Var) :
    (nb068_alpha_dummy_222 f) ∉
      (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_222] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_232 (f : Var) :
    (nb068_alpha_dummy_220 f) ≠ (nb068_alpha_dummy_221 f) := by
  simpa only [nb068_alpha_dummy_220, nb068_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_233 (f : Var) :
    (nb068_alpha_dummy_220 f) ≠ (nb068_alpha_dummy_222 f) := by
  simpa only [nb068_alpha_dummy_220, nb068_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_234 (f : Var) :
    (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_222 f) := by
  simpa only [nb068_alpha_dummy_221, nb068_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_235 :
    (nb068_alpha_dummy_229) ∉
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) :=
  by
  simpa only [nb068_alpha_dummy_229] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv)
      0

theorem nb068_fresh_236 :
    (nb068_alpha_dummy_225) ∉
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) :=
  by
  simpa only [nb068_alpha_dummy_225] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv)
      0

theorem nb068_fresh_237 :
    (nb068_alpha_dummy_231) ∉
      (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) :=
  by
  simpa only [nb068_alpha_dummy_231] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv)
      0

theorem nb068_fresh_238 (f : Var) :
    (nb068_alpha_dummy_230 f) ∉
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_230] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv)
      0

theorem nb068_fresh_239 (f : Var) :
    (nb068_alpha_dummy_226 f) ∉
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_226] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv)
      0

theorem nb068_fresh_240 (f : Var) :
    (nb068_alpha_dummy_232 f) ∉
      (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_232] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv)
      0

theorem nb068_fresh_241 :
    (nb068_alpha_dummy_243) ∉
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) :=
  by
  simpa only [nb068_alpha_dummy_243] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv)
      0

theorem nb068_fresh_242 :
    (nb068_alpha_dummy_244) ∉
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) :=
  by
  simpa only [nb068_alpha_dummy_244] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv)
      1

theorem nb068_distinct_243 : (nb068_alpha_dummy_243) ≠ (nb068_alpha_dummy_244) := by
  simpa only [nb068_alpha_dummy_243, nb068_alpha_dummy_244] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_244 (f : Var) :
    (nb068_alpha_dummy_245 f) ∉
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_245] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv)
      0

theorem nb068_fresh_245 (f : Var) :
    (nb068_alpha_dummy_246 f) ∉
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_246] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv)
      1

theorem nb068_distinct_246 (f : Var) :
    (nb068_alpha_dummy_245 f) ≠ (nb068_alpha_dummy_246 f) := by
  simpa only [nb068_alpha_dummy_245, nb068_alpha_dummy_246] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_241 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_247 :
    (nb068_alpha_dummy_251) ∉ (((Class.cv (nb068_alpha_dummy_244))).fv) := by
  simpa only [nb068_alpha_dummy_251] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_244))).fv) 0

theorem nb068_fresh_248 :
    (nb068_alpha_dummy_252) ∉ (((Class.cv (nb068_alpha_dummy_244))).fv) := by
  simpa only [nb068_alpha_dummy_252] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_244))).fv) 1

theorem nb068_distinct_249 : (nb068_alpha_dummy_251) ≠ (nb068_alpha_dummy_252) := by
  simpa only [nb068_alpha_dummy_251, nb068_alpha_dummy_252] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_244))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_250 (f : Var) :
    (nb068_alpha_dummy_253 f) ∉ (((Class.cv (nb068_alpha_dummy_246 f))).fv) := by
  simpa only [nb068_alpha_dummy_253] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_246 f))).fv) 0

theorem nb068_fresh_251 (f : Var) :
    (nb068_alpha_dummy_254 f) ∉ (((Class.cv (nb068_alpha_dummy_246 f))).fv) := by
  simpa only [nb068_alpha_dummy_254] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_246 f))).fv) 1

theorem nb068_distinct_252 (f : Var) :
    (nb068_alpha_dummy_253 f) ≠ (nb068_alpha_dummy_254 f) := by
  simpa only [nb068_alpha_dummy_253, nb068_alpha_dummy_254] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_246 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_253 :
    (nb068_alpha_dummy_257) ∉
      (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_257] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_254 :
    (nb068_alpha_dummy_258) ∉
      (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_258] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_255 :
    (nb068_alpha_dummy_259) ∉
      (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_259] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_256 : (nb068_alpha_dummy_257) ≠ (nb068_alpha_dummy_258) := by
  simpa only [nb068_alpha_dummy_257, nb068_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_257 : (nb068_alpha_dummy_257) ≠ (nb068_alpha_dummy_259) := by
  simpa only [nb068_alpha_dummy_257, nb068_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_258 : (nb068_alpha_dummy_258) ≠ (nb068_alpha_dummy_259) := by
  simpa only [nb068_alpha_dummy_258, nb068_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_259 (f : Var) :
    (nb068_alpha_dummy_260 f) ∉
      (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_260] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_260 (f : Var) :
    (nb068_alpha_dummy_261 f) ∉
      (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_261] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_261 (f : Var) :
    (nb068_alpha_dummy_262 f) ∉
      (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_262] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_262 (f : Var) :
    (nb068_alpha_dummy_260 f) ≠ (nb068_alpha_dummy_261 f) := by
  simpa only [nb068_alpha_dummy_260, nb068_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_263 (f : Var) :
    (nb068_alpha_dummy_260 f) ≠ (nb068_alpha_dummy_262 f) := by
  simpa only [nb068_alpha_dummy_260, nb068_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_264 (f : Var) :
    (nb068_alpha_dummy_261 f) ≠ (nb068_alpha_dummy_262 f) := by
  simpa only [nb068_alpha_dummy_261, nb068_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_265 :
    (nb068_alpha_dummy_269) ∉
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) :=
  by
  simpa only [nb068_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv)
      0

theorem nb068_fresh_266 :
    (nb068_alpha_dummy_265) ∉
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) :=
  by
  simpa only [nb068_alpha_dummy_265] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv)
      0

theorem nb068_fresh_267 :
    (nb068_alpha_dummy_271) ∉
      (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) :=
  by
  simpa only [nb068_alpha_dummy_271] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv)
      0

theorem nb068_fresh_268 (f : Var) :
    (nb068_alpha_dummy_270 f) ∉
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv)
      0

theorem nb068_fresh_269 (f : Var) :
    (nb068_alpha_dummy_266 f) ∉
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_266] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv)
      0

theorem nb068_fresh_270 (f : Var) :
    (nb068_alpha_dummy_272 f) ∉
      (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_272] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv)
      0

theorem nb068_fresh_271 :
    (nb068_alpha_dummy_287) ∉
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) :=
  by
  simpa only [nb068_alpha_dummy_287] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv)
      0

theorem nb068_fresh_272 :
    (nb068_alpha_dummy_288) ∉
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) :=
  by
  simpa only [nb068_alpha_dummy_288] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv)
      1

theorem nb068_distinct_273 : (nb068_alpha_dummy_287) ≠ (nb068_alpha_dummy_288) := by
  simpa only [nb068_alpha_dummy_287, nb068_alpha_dummy_288] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_274 (f : Var) :
    (nb068_alpha_dummy_289 f) ∉
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_289] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv)
      0

theorem nb068_fresh_275 (f : Var) :
    (nb068_alpha_dummy_290 f) ∉
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_290] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv)
      1

theorem nb068_distinct_276 (f : Var) :
    (nb068_alpha_dummy_289 f) ≠ (nb068_alpha_dummy_290 f) := by
  simpa only [nb068_alpha_dummy_289, nb068_alpha_dummy_290] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_285 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_277 :
    (nb068_alpha_dummy_295) ∉ (((Class.cv (nb068_alpha_dummy_288))).fv) := by
  simpa only [nb068_alpha_dummy_295] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_288))).fv) 0

theorem nb068_fresh_278 :
    (nb068_alpha_dummy_296) ∉ (((Class.cv (nb068_alpha_dummy_288))).fv) := by
  simpa only [nb068_alpha_dummy_296] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_288))).fv) 1

theorem nb068_distinct_279 : (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_296) := by
  simpa only [nb068_alpha_dummy_295, nb068_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_280 (f : Var) :
    (nb068_alpha_dummy_297 f) ∉ (((Class.cv (nb068_alpha_dummy_290 f))).fv) := by
  simpa only [nb068_alpha_dummy_297] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_290 f))).fv) 0

theorem nb068_fresh_281 (f : Var) :
    (nb068_alpha_dummy_298 f) ∉ (((Class.cv (nb068_alpha_dummy_290 f))).fv) := by
  simpa only [nb068_alpha_dummy_298] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_290 f))).fv) 1

theorem nb068_distinct_282 (f : Var) :
    (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_298 f) := by
  simpa only [nb068_alpha_dummy_297, nb068_alpha_dummy_298] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_283 :
    (nb068_alpha_dummy_301) ∉
      (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_301] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_284 :
    (nb068_alpha_dummy_302) ∉
      (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_302] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_285 :
    (nb068_alpha_dummy_303) ∉
      (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_303] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_286 : (nb068_alpha_dummy_301) ≠ (nb068_alpha_dummy_302) := by
  simpa only [nb068_alpha_dummy_301, nb068_alpha_dummy_302] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_287 : (nb068_alpha_dummy_301) ≠ (nb068_alpha_dummy_303) := by
  simpa only [nb068_alpha_dummy_301, nb068_alpha_dummy_303] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_288 : (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_303) := by
  simpa only [nb068_alpha_dummy_302, nb068_alpha_dummy_303] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_289 (f : Var) :
    (nb068_alpha_dummy_304 f) ∉
      (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_304] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_290 (f : Var) :
    (nb068_alpha_dummy_305 f) ∉
      (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_305] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_291 (f : Var) :
    (nb068_alpha_dummy_306 f) ∉
      (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_306] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_292 (f : Var) :
    (nb068_alpha_dummy_304 f) ≠ (nb068_alpha_dummy_305 f) := by
  simpa only [nb068_alpha_dummy_304, nb068_alpha_dummy_305] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_293 (f : Var) :
    (nb068_alpha_dummy_304 f) ≠ (nb068_alpha_dummy_306 f) := by
  simpa only [nb068_alpha_dummy_304, nb068_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_294 (f : Var) :
    (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_306 f) := by
  simpa only [nb068_alpha_dummy_305, nb068_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_295 :
    (nb068_alpha_dummy_313) ∉
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) :=
  by
  simpa only [nb068_alpha_dummy_313] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv)
      0

theorem nb068_fresh_296 :
    (nb068_alpha_dummy_309) ∉
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) :=
  by
  simpa only [nb068_alpha_dummy_309] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv)
      0

theorem nb068_fresh_297 :
    (nb068_alpha_dummy_315) ∉
      (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) :=
  by
  simpa only [nb068_alpha_dummy_315] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv)
      0

theorem nb068_fresh_298 (f : Var) :
    (nb068_alpha_dummy_314 f) ∉
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_314] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv)
      0

theorem nb068_fresh_299 (f : Var) :
    (nb068_alpha_dummy_310 f) ∉
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_310] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv)
      0

theorem nb068_fresh_300 (f : Var) :
    (nb068_alpha_dummy_316 f) ∉
      (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_316] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv)
      0

theorem nb068_fresh_301 :
    (nb068_alpha_dummy_335) ∉
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  simpa only [nb068_alpha_dummy_335] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      0

theorem nb068_fresh_302 :
    (nb068_alpha_dummy_336) ∉
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  simpa only [nb068_alpha_dummy_336] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      1

theorem nb068_distinct_303 : (nb068_alpha_dummy_335) ≠ (nb068_alpha_dummy_336) := by
  simpa only [nb068_alpha_dummy_335, nb068_alpha_dummy_336] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_304 :
    (nb068_alpha_dummy_371) ∉
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) :=
  by
  simpa only [nb068_alpha_dummy_371] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv)
      0

theorem nb068_fresh_305 :
    (nb068_alpha_dummy_372) ∉
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) :=
  by
  simpa only [nb068_alpha_dummy_372] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv)
      1

theorem nb068_distinct_306 : (nb068_alpha_dummy_371) ≠ (nb068_alpha_dummy_372) := by
  simpa only [nb068_alpha_dummy_371, nb068_alpha_dummy_372] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_307 :
    (nb068_alpha_dummy_485) ∉
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  simpa only [nb068_alpha_dummy_485] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      0

theorem nb068_fresh_308 :
    (nb068_alpha_dummy_486) ∉
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) :=
  by
  simpa only [nb068_alpha_dummy_486] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      1

theorem nb068_distinct_309 : (nb068_alpha_dummy_485) ≠ (nb068_alpha_dummy_486) := by
  simpa only [nb068_alpha_dummy_485, nb068_alpha_dummy_486] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_310 (f : Var) :
    (nb068_alpha_dummy_337 f) ∉
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_337] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv)
      0

theorem nb068_fresh_311 (f : Var) :
    (nb068_alpha_dummy_338 f) ∉
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_338] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv)
      1

theorem nb068_distinct_312 (f : Var) :
    (nb068_alpha_dummy_337 f) ≠ (nb068_alpha_dummy_338 f) := by
  simpa only [nb068_alpha_dummy_337, nb068_alpha_dummy_338] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_313 (f : Var) :
    (nb068_alpha_dummy_373 f) ∉
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_373] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv)
      0

theorem nb068_fresh_314 (f : Var) :
    (nb068_alpha_dummy_374 f) ∉
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_374] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv)
      1

theorem nb068_distinct_315 (f : Var) :
    (nb068_alpha_dummy_373 f) ≠ (nb068_alpha_dummy_374 f) := by
  simpa only [nb068_alpha_dummy_373, nb068_alpha_dummy_374] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_332 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_316 (f : Var) :
    (nb068_alpha_dummy_487 f) ∉
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_487] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv)
      0

theorem nb068_fresh_317 (f : Var) :
    (nb068_alpha_dummy_488 f) ∉
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_488] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv)
      1

theorem nb068_distinct_318 (f : Var) :
    (nb068_alpha_dummy_487 f) ≠ (nb068_alpha_dummy_488 f) := by
  simpa only [nb068_alpha_dummy_487, nb068_alpha_dummy_488] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_319 :
    (nb068_alpha_dummy_343) ∉ (((Class.cv (nb068_alpha_dummy_336))).fv) := by
  simpa only [nb068_alpha_dummy_343] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_336))).fv) 0

theorem nb068_fresh_320 :
    (nb068_alpha_dummy_344) ∉ (((Class.cv (nb068_alpha_dummy_336))).fv) := by
  simpa only [nb068_alpha_dummy_344] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_336))).fv) 1

theorem nb068_distinct_321 : (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_344) := by
  simpa only [nb068_alpha_dummy_343, nb068_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_336))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_322 (f : Var) :
    (nb068_alpha_dummy_345 f) ∉ (((Class.cv (nb068_alpha_dummy_338 f))).fv) := by
  simpa only [nb068_alpha_dummy_345] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_338 f))).fv) 0

theorem nb068_fresh_323 (f : Var) :
    (nb068_alpha_dummy_346 f) ∉ (((Class.cv (nb068_alpha_dummy_338 f))).fv) := by
  simpa only [nb068_alpha_dummy_346] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_338 f))).fv) 1

theorem nb068_distinct_324 (f : Var) :
    (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_346 f) := by
  simpa only [nb068_alpha_dummy_345, nb068_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_338 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_325 :
    (nb068_alpha_dummy_349) ∉
      (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_349] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_326 :
    (nb068_alpha_dummy_350) ∉
      (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_350] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_327 :
    (nb068_alpha_dummy_351) ∉
      (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_351] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_328 : (nb068_alpha_dummy_349) ≠ (nb068_alpha_dummy_350) := by
  simpa only [nb068_alpha_dummy_349, nb068_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_329 : (nb068_alpha_dummy_349) ≠ (nb068_alpha_dummy_351) := by
  simpa only [nb068_alpha_dummy_349, nb068_alpha_dummy_351] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_330 : (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_351) := by
  simpa only [nb068_alpha_dummy_350, nb068_alpha_dummy_351] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_331 (f : Var) :
    (nb068_alpha_dummy_352 f) ∉
      (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_352] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_332 (f : Var) :
    (nb068_alpha_dummy_353 f) ∉
      (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_353] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_333 (f : Var) :
    (nb068_alpha_dummy_354 f) ∉
      (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_354] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_334 (f : Var) :
    (nb068_alpha_dummy_352 f) ≠ (nb068_alpha_dummy_353 f) := by
  simpa only [nb068_alpha_dummy_352, nb068_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_335 (f : Var) :
    (nb068_alpha_dummy_352 f) ≠ (nb068_alpha_dummy_354 f) := by
  simpa only [nb068_alpha_dummy_352, nb068_alpha_dummy_354] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_336 (f : Var) :
    (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_354 f) := by
  simpa only [nb068_alpha_dummy_353, nb068_alpha_dummy_354] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_337 :
    (nb068_alpha_dummy_361) ∉
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) :=
  by
  simpa only [nb068_alpha_dummy_361] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv)
      0

theorem nb068_fresh_338 :
    (nb068_alpha_dummy_357) ∉
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) :=
  by
  simpa only [nb068_alpha_dummy_357] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv)
      0

theorem nb068_fresh_339 :
    (nb068_alpha_dummy_363) ∉
      (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) :=
  by
  simpa only [nb068_alpha_dummy_363] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv)
      0

theorem nb068_fresh_340 (f : Var) :
    (nb068_alpha_dummy_362 f) ∉
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_362] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv)
      0

theorem nb068_fresh_341 (f : Var) :
    (nb068_alpha_dummy_358 f) ∉
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_358] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part007`. -/


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

theorem nb068_fresh_342 (f : Var) :
    (nb068_alpha_dummy_364 f) ∉
      (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_364] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv)
      0

theorem nb068_fresh_343 :
    (nb068_alpha_dummy_379) ∉ (((Class.cv (nb068_alpha_dummy_372))).fv) := by
  simpa only [nb068_alpha_dummy_379] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_372))).fv) 0

theorem nb068_fresh_344 :
    (nb068_alpha_dummy_380) ∉ (((Class.cv (nb068_alpha_dummy_372))).fv) := by
  simpa only [nb068_alpha_dummy_380] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_372))).fv) 1

theorem nb068_distinct_345 : (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_380) := by
  simpa only [nb068_alpha_dummy_379, nb068_alpha_dummy_380] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_346 (f : Var) :
    (nb068_alpha_dummy_381 f) ∉ (((Class.cv (nb068_alpha_dummy_374 f))).fv) := by
  simpa only [nb068_alpha_dummy_381] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_374 f))).fv) 0

theorem nb068_fresh_347 (f : Var) :
    (nb068_alpha_dummy_382 f) ∉ (((Class.cv (nb068_alpha_dummy_374 f))).fv) := by
  simpa only [nb068_alpha_dummy_382] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_374 f))).fv) 1

theorem nb068_distinct_348 (f : Var) :
    (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_382 f) := by
  simpa only [nb068_alpha_dummy_381, nb068_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_349 :
    (nb068_alpha_dummy_385) ∉
      (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_385] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_350 :
    (nb068_alpha_dummy_386) ∉
      (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_386] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_351 :
    (nb068_alpha_dummy_387) ∉
      (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_387] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_352 : (nb068_alpha_dummy_385) ≠ (nb068_alpha_dummy_386) := by
  simpa only [nb068_alpha_dummy_385, nb068_alpha_dummy_386] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_353 : (nb068_alpha_dummy_385) ≠ (nb068_alpha_dummy_387) := by
  simpa only [nb068_alpha_dummy_385, nb068_alpha_dummy_387] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_354 : (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_387) := by
  simpa only [nb068_alpha_dummy_386, nb068_alpha_dummy_387] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_355 (f : Var) :
    (nb068_alpha_dummy_388 f) ∉
      (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_388] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_356 (f : Var) :
    (nb068_alpha_dummy_389 f) ∉
      (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_389] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_357 (f : Var) :
    (nb068_alpha_dummy_390 f) ∉
      (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_390] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_358 (f : Var) :
    (nb068_alpha_dummy_388 f) ≠ (nb068_alpha_dummy_389 f) := by
  simpa only [nb068_alpha_dummy_388, nb068_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_359 (f : Var) :
    (nb068_alpha_dummy_388 f) ≠ (nb068_alpha_dummy_390 f) := by
  simpa only [nb068_alpha_dummy_388, nb068_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_360 (f : Var) :
    (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_390 f) := by
  simpa only [nb068_alpha_dummy_389, nb068_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_361 :
    (nb068_alpha_dummy_397) ∉
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) :=
  by
  simpa only [nb068_alpha_dummy_397] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv)
      0

theorem nb068_fresh_362 :
    (nb068_alpha_dummy_393) ∉
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) :=
  by
  simpa only [nb068_alpha_dummy_393] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv)
      0

theorem nb068_fresh_363 :
    (nb068_alpha_dummy_399) ∉
      (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) :=
  by
  simpa only [nb068_alpha_dummy_399] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv)
      0

theorem nb068_fresh_364 (f : Var) :
    (nb068_alpha_dummy_398 f) ∉
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_398] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv)
      0

theorem nb068_fresh_365 (f : Var) :
    (nb068_alpha_dummy_394 f) ∉
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_394] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv)
      0

theorem nb068_fresh_366 (f : Var) :
    (nb068_alpha_dummy_400 f) ∉
      (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_400] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv)
      0

theorem nb068_fresh_367 :
    (nb068_alpha_dummy_413) ∉
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) :=
  by
  simpa only [nb068_alpha_dummy_413] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv)
      0

theorem nb068_fresh_368 :
    (nb068_alpha_dummy_414) ∉
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) :=
  by
  simpa only [nb068_alpha_dummy_414] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv)
      1

theorem nb068_distinct_369 : (nb068_alpha_dummy_413) ≠ (nb068_alpha_dummy_414) := by
  simpa only [nb068_alpha_dummy_413, nb068_alpha_dummy_414] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_370 :
    (nb068_alpha_dummy_449) ∉
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) :=
  by
  simpa only [nb068_alpha_dummy_449] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv)
      0

theorem nb068_fresh_371 :
    (nb068_alpha_dummy_450) ∉
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) :=
  by
  simpa only [nb068_alpha_dummy_450] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv)
      1

theorem nb068_distinct_372 : (nb068_alpha_dummy_449) ≠ (nb068_alpha_dummy_450) := by
  simpa only [nb068_alpha_dummy_449, nb068_alpha_dummy_450] using
    (freshVar_injective
      (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_373 (f : Var) :
    (nb068_alpha_dummy_415 f) ∉
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_415] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv)
      0

theorem nb068_fresh_374 (f : Var) :
    (nb068_alpha_dummy_416 f) ∉
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_416] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv)
      1

theorem nb068_distinct_375 (f : Var) :
    (nb068_alpha_dummy_415 f) ≠ (nb068_alpha_dummy_416 f) := by
  simpa only [nb068_alpha_dummy_415, nb068_alpha_dummy_416] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_410 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_376 (f : Var) :
    (nb068_alpha_dummy_451 f) ∉
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_451] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv)
      0

theorem nb068_fresh_377 (f : Var) :
    (nb068_alpha_dummy_452 f) ∉
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_452] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv)
      1

theorem nb068_distinct_378 (f : Var) :
    (nb068_alpha_dummy_451 f) ≠ (nb068_alpha_dummy_452 f) := by
  simpa only [nb068_alpha_dummy_451, nb068_alpha_dummy_452] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_409 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_379 :
    (nb068_alpha_dummy_421) ∉ (((Class.cv (nb068_alpha_dummy_414))).fv) := by
  simpa only [nb068_alpha_dummy_421] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_414))).fv) 0

theorem nb068_fresh_380 :
    (nb068_alpha_dummy_422) ∉ (((Class.cv (nb068_alpha_dummy_414))).fv) := by
  simpa only [nb068_alpha_dummy_422] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_414))).fv) 1

theorem nb068_distinct_381 : (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_422) := by
  simpa only [nb068_alpha_dummy_421, nb068_alpha_dummy_422] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_382 (f : Var) :
    (nb068_alpha_dummy_423 f) ∉ (((Class.cv (nb068_alpha_dummy_416 f))).fv) := by
  simpa only [nb068_alpha_dummy_423] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_416 f))).fv) 0

theorem nb068_fresh_383 (f : Var) :
    (nb068_alpha_dummy_424 f) ∉ (((Class.cv (nb068_alpha_dummy_416 f))).fv) := by
  simpa only [nb068_alpha_dummy_424] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_416 f))).fv) 1

theorem nb068_distinct_384 (f : Var) :
    (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_424 f) := by
  simpa only [nb068_alpha_dummy_423, nb068_alpha_dummy_424] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_385 :
    (nb068_alpha_dummy_427) ∉
      (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_427] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_386 :
    (nb068_alpha_dummy_428) ∉
      (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_428] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_387 :
    (nb068_alpha_dummy_429) ∉
      (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_429] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_388 : (nb068_alpha_dummy_427) ≠ (nb068_alpha_dummy_428) := by
  simpa only [nb068_alpha_dummy_427, nb068_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_389 : (nb068_alpha_dummy_427) ≠ (nb068_alpha_dummy_429) := by
  simpa only [nb068_alpha_dummy_427, nb068_alpha_dummy_429] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_390 : (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_429) := by
  simpa only [nb068_alpha_dummy_428, nb068_alpha_dummy_429] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_391 (f : Var) :
    (nb068_alpha_dummy_430 f) ∉
      (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_430] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_392 (f : Var) :
    (nb068_alpha_dummy_431 f) ∉
      (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_431] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_393 (f : Var) :
    (nb068_alpha_dummy_432 f) ∉
      (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_432] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_394 (f : Var) :
    (nb068_alpha_dummy_430 f) ≠ (nb068_alpha_dummy_431 f) := by
  simpa only [nb068_alpha_dummy_430, nb068_alpha_dummy_431] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_395 (f : Var) :
    (nb068_alpha_dummy_430 f) ≠ (nb068_alpha_dummy_432 f) := by
  simpa only [nb068_alpha_dummy_430, nb068_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_396 (f : Var) :
    (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_432 f) := by
  simpa only [nb068_alpha_dummy_431, nb068_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_397 :
    (nb068_alpha_dummy_439) ∉
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) :=
  by
  simpa only [nb068_alpha_dummy_439] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv)
      0

theorem nb068_fresh_398 :
    (nb068_alpha_dummy_435) ∉
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) :=
  by
  simpa only [nb068_alpha_dummy_435] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv)
      0

theorem nb068_fresh_399 :
    (nb068_alpha_dummy_441) ∉
      (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) :=
  by
  simpa only [nb068_alpha_dummy_441] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv)
      0

theorem nb068_fresh_400 (f : Var) :
    (nb068_alpha_dummy_440 f) ∉
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_440] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv)
      0

theorem nb068_fresh_401 (f : Var) :
    (nb068_alpha_dummy_436 f) ∉
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_436] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv)
      0

theorem nb068_fresh_402 (f : Var) :
    (nb068_alpha_dummy_442 f) ∉
      (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_442] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv)
      0

theorem nb068_fresh_403 :
    (nb068_alpha_dummy_457) ∉ (((Class.cv (nb068_alpha_dummy_450))).fv) := by
  simpa only [nb068_alpha_dummy_457] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_450))).fv) 0

theorem nb068_fresh_404 :
    (nb068_alpha_dummy_458) ∉ (((Class.cv (nb068_alpha_dummy_450))).fv) := by
  simpa only [nb068_alpha_dummy_458] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_450))).fv) 1

theorem nb068_distinct_405 : (nb068_alpha_dummy_457) ≠ (nb068_alpha_dummy_458) := by
  simpa only [nb068_alpha_dummy_457, nb068_alpha_dummy_458] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_450))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_406 (f : Var) :
    (nb068_alpha_dummy_459 f) ∉ (((Class.cv (nb068_alpha_dummy_452 f))).fv) := by
  simpa only [nb068_alpha_dummy_459] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_452 f))).fv) 0

theorem nb068_fresh_407 (f : Var) :
    (nb068_alpha_dummy_460 f) ∉ (((Class.cv (nb068_alpha_dummy_452 f))).fv) := by
  simpa only [nb068_alpha_dummy_460] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_452 f))).fv) 1

theorem nb068_distinct_408 (f : Var) :
    (nb068_alpha_dummy_459 f) ≠ (nb068_alpha_dummy_460 f) := by
  simpa only [nb068_alpha_dummy_459, nb068_alpha_dummy_460] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_452 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_409 :
    (nb068_alpha_dummy_463) ∉
      (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_463] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_410 :
    (nb068_alpha_dummy_464) ∉
      (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_464] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_411 :
    (nb068_alpha_dummy_465) ∉
      (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_465] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_412 : (nb068_alpha_dummy_463) ≠ (nb068_alpha_dummy_464) := by
  simpa only [nb068_alpha_dummy_463, nb068_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_413 : (nb068_alpha_dummy_463) ≠ (nb068_alpha_dummy_465) := by
  simpa only [nb068_alpha_dummy_463, nb068_alpha_dummy_465] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_414 : (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_465) := by
  simpa only [nb068_alpha_dummy_464, nb068_alpha_dummy_465] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_415 (f : Var) :
    (nb068_alpha_dummy_466 f) ∉
      (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_466] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_416 (f : Var) :
    (nb068_alpha_dummy_467 f) ∉
      (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_467] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_417 (f : Var) :
    (nb068_alpha_dummy_468 f) ∉
      (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_468] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_418 (f : Var) :
    (nb068_alpha_dummy_466 f) ≠ (nb068_alpha_dummy_467 f) := by
  simpa only [nb068_alpha_dummy_466, nb068_alpha_dummy_467] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_419 (f : Var) :
    (nb068_alpha_dummy_466 f) ≠ (nb068_alpha_dummy_468 f) := by
  simpa only [nb068_alpha_dummy_466, nb068_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_420 (f : Var) :
    (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_468 f) := by
  simpa only [nb068_alpha_dummy_467, nb068_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_421 :
    (nb068_alpha_dummy_475) ∉
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv) :=
  by
  simpa only [nb068_alpha_dummy_475] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv)
      0

theorem nb068_fresh_422 :
    (nb068_alpha_dummy_471) ∉
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) :=
  by
  simpa only [nb068_alpha_dummy_471] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv)
      0

theorem nb068_fresh_423 :
    (nb068_alpha_dummy_477) ∉
      (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) :=
  by
  simpa only [nb068_alpha_dummy_477] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv)
      0

theorem nb068_fresh_424 (f : Var) :
    (nb068_alpha_dummy_476 f) ∉
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_467 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_476] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_467 f))).fv)
      0

theorem nb068_fresh_425 (f : Var) :
    (nb068_alpha_dummy_472 f) ∉
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_472] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv)
      0

theorem nb068_fresh_426 (f : Var) :
    (nb068_alpha_dummy_478 f) ∉
      (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_478] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv)
      0

theorem nb068_fresh_427 :
    (nb068_alpha_dummy_493) ∉ (((Class.cv (nb068_alpha_dummy_486))).fv) := by
  simpa only [nb068_alpha_dummy_493] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_486))).fv) 0

theorem nb068_fresh_428 :
    (nb068_alpha_dummy_494) ∉ (((Class.cv (nb068_alpha_dummy_486))).fv) := by
  simpa only [nb068_alpha_dummy_494] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_486))).fv) 1

theorem nb068_distinct_429 : (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_494) := by
  simpa only [nb068_alpha_dummy_493, nb068_alpha_dummy_494] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_486))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_430 (f : Var) :
    (nb068_alpha_dummy_495 f) ∉ (((Class.cv (nb068_alpha_dummy_488 f))).fv) := by
  simpa only [nb068_alpha_dummy_495] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_488 f))).fv) 0

theorem nb068_fresh_431 (f : Var) :
    (nb068_alpha_dummy_496 f) ∉ (((Class.cv (nb068_alpha_dummy_488 f))).fv) := by
  simpa only [nb068_alpha_dummy_496] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_488 f))).fv) 1

theorem nb068_distinct_432 (f : Var) :
    (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_496 f) := by
  simpa only [nb068_alpha_dummy_495, nb068_alpha_dummy_496] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_488 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_433 :
    (nb068_alpha_dummy_499) ∉
      (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_499] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_434 :
    (nb068_alpha_dummy_500) ∉
      (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_500] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_435 :
    (nb068_alpha_dummy_501) ∉
      (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_501] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_436 : (nb068_alpha_dummy_499) ≠ (nb068_alpha_dummy_500) := by
  simpa only [nb068_alpha_dummy_499, nb068_alpha_dummy_500] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_437 : (nb068_alpha_dummy_499) ≠ (nb068_alpha_dummy_501) := by
  simpa only [nb068_alpha_dummy_499, nb068_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_438 : (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_501) := by
  simpa only [nb068_alpha_dummy_500, nb068_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_439 (f : Var) :
    (nb068_alpha_dummy_502 f) ∉
      (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_502] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_440 (f : Var) :
    (nb068_alpha_dummy_503 f) ∉
      (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_503] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_441 (f : Var) :
    (nb068_alpha_dummy_504 f) ∉
      (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb068_alpha_dummy_504] using
    freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_442 (f : Var) :
    (nb068_alpha_dummy_502 f) ≠ (nb068_alpha_dummy_503 f) := by
  simpa only [nb068_alpha_dummy_502, nb068_alpha_dummy_503] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_443 (f : Var) :
    (nb068_alpha_dummy_502 f) ≠ (nb068_alpha_dummy_504 f) := by
  simpa only [nb068_alpha_dummy_502, nb068_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_444 (f : Var) :
    (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_504 f) := by
  simpa only [nb068_alpha_dummy_503, nb068_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_445 :
    (nb068_alpha_dummy_511) ∉
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) :=
  by
  simpa only [nb068_alpha_dummy_511] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv)
      0

theorem nb068_fresh_446 :
    (nb068_alpha_dummy_507) ∉
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) :=
  by
  simpa only [nb068_alpha_dummy_507] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv)
      0

theorem nb068_fresh_447 :
    (nb068_alpha_dummy_513) ∉
      (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) :=
  by
  simpa only [nb068_alpha_dummy_513] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv)
      0

theorem nb068_fresh_448 (f : Var) :
    (nb068_alpha_dummy_512 f) ∉
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_512] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv)
      0

theorem nb068_fresh_449 (f : Var) :
    (nb068_alpha_dummy_508 f) ∉
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_508] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv)
      0

theorem nb068_fresh_450 (f : Var) :
    (nb068_alpha_dummy_514 f) ∉
      (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_514] using
    freshVar_not_mem
      (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv)
      0

theorem nb068_fresh_451 (f : Var) : (nb068_alpha_dummy_127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068_alpha_dummy_127] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb068_fresh_452 (f : Var) : (nb068_alpha_dummy_128 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068_alpha_dummy_128] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb068_distinct_453 (f : Var) :
    (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_128 f) := by
  simpa only [nb068_alpha_dummy_127, nb068_alpha_dummy_128] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_454 (f : Var) :
    (nb068_alpha_dummy_048 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_048] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb068_fresh_455 (f : Var) :
    (nb068_alpha_dummy_049 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_049] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb068_fresh_456 (f : Var) :
    (nb068_alpha_dummy_050 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb068_distinct_457 (f : Var) :
    (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_049 f) := by
  simpa only [nb068_alpha_dummy_048, nb068_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb068_distinct_458 (f : Var) :
    (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_050 f) := by
  simpa only [nb068_alpha_dummy_048, nb068_alpha_dummy_050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb068_distinct_459 (f : Var) :
    (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_050 f) := by
  simpa only [nb068_alpha_dummy_049, nb068_alpha_dummy_050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb068_fresh_460 (f : Var) :
    (nb068_alpha_dummy_285 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_285] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_461 (f : Var) :
    (nb068_alpha_dummy_286 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_286] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_462 (f : Var) :
    (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_286 f) := by
  simpa only [nb068_alpha_dummy_285, nb068_alpha_dummy_286] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_463 (x : Var) (y : Var) :
    (nb068_alpha_dummy_007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_464 (x : Var) (y : Var) :
    (nb068_alpha_dummy_008 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb068_distinct_465 (x : Var) (y : Var) :
    (nb068_alpha_dummy_007 x y) ≠ (nb068_alpha_dummy_008 x y) := by
  simpa only [nb068_alpha_dummy_007, nb068_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_466 :
    (nb068_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_013))).fv) :=
  by
  simpa only [nb068_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_013))).fv)
      0

theorem nb068_fresh_467 (x : Var) (y : Var) :
    (nb068_alpha_dummy_018 x y) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_015 x y))).fv) :=
  by
  simpa only [nb068_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_015 x y))).fv)
      0

theorem nb068_fresh_468 :
    (nb068_alpha_dummy_065) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_061))).fv) :=
  by
  simpa only [nb068_alpha_dummy_065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_061))).fv)
      0

theorem nb068_fresh_469 (f : Var) :
    (nb068_alpha_dummy_066 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_063 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_063 f))).fv)
      0

theorem nb068_fresh_470 :
    (nb068_alpha_dummy_101) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_097))).fv) :=
  by
  simpa only [nb068_alpha_dummy_101] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_097))).fv)
      0

theorem nb068_fresh_471 (f : Var) :
    (nb068_alpha_dummy_102 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_099 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_102] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_099 f))).fv)
      0

theorem nb068_fresh_472 :
    (nb068_alpha_dummy_143) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_139))).fv) :=
  by
  simpa only [nb068_alpha_dummy_143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_139))).fv)
      0

theorem nb068_fresh_473 (f : Var) :
    (nb068_alpha_dummy_144 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_141 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_144] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_141 f))).fv)
      0

theorem nb068_fresh_474 :
    (nb068_alpha_dummy_179) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_175))).fv) :=
  by
  simpa only [nb068_alpha_dummy_179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_175))).fv)
      0

theorem nb068_fresh_475 (f : Var) :
    (nb068_alpha_dummy_180 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_177 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_180] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_177 f))).fv)
      0

theorem nb068_fresh_476 :
    (nb068_alpha_dummy_215) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_211))).fv) :=
  by
  simpa only [nb068_alpha_dummy_215] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_211))).fv)
      0

theorem nb068_fresh_477 (f : Var) :
    (nb068_alpha_dummy_216 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_213 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_216] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_213 f))).fv)
      0

theorem nb068_fresh_478 :
    (nb068_alpha_dummy_255) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_251))).fv) :=
  by
  simpa only [nb068_alpha_dummy_255] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_251))).fv)
      0

theorem nb068_fresh_479 (f : Var) :
    (nb068_alpha_dummy_256 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_253 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_256] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_253 f))).fv)
      0

theorem nb068_fresh_480 :
    (nb068_alpha_dummy_299) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_295))).fv) :=
  by
  simpa only [nb068_alpha_dummy_299] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_295))).fv)
      0

theorem nb068_fresh_481 (f : Var) :
    (nb068_alpha_dummy_300 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_297 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_300] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_297 f))).fv)
      0

theorem nb068_fresh_482 :
    (nb068_alpha_dummy_347) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_343))).fv) :=
  by
  simpa only [nb068_alpha_dummy_347] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_343))).fv)
      0

theorem nb068_fresh_483 (f : Var) :
    (nb068_alpha_dummy_348 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_345 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_348] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_345 f))).fv)
      0

theorem nb068_fresh_484 :
    (nb068_alpha_dummy_383) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_379))).fv) :=
  by
  simpa only [nb068_alpha_dummy_383] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_379))).fv)
      0

theorem nb068_fresh_485 (f : Var) :
    (nb068_alpha_dummy_384 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_381 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_384] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_381 f))).fv)
      0

theorem nb068_fresh_486 :
    (nb068_alpha_dummy_425) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_421))).fv) :=
  by
  simpa only [nb068_alpha_dummy_425] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_421))).fv)
      0

theorem nb068_fresh_487 (f : Var) :
    (nb068_alpha_dummy_426 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_423 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_426] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_423 f))).fv)
      0

theorem nb068_fresh_488 :
    (nb068_alpha_dummy_461) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_457))).fv) :=
  by
  simpa only [nb068_alpha_dummy_461] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_457))).fv)
      0

theorem nb068_fresh_489 (f : Var) :
    (nb068_alpha_dummy_462 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_459 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_462] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_459 f))).fv)
      0

theorem nb068_fresh_490 :
    (nb068_alpha_dummy_497) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_493))).fv) :=
  by
  simpa only [nb068_alpha_dummy_497] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_493))).fv)
      0

theorem nb068_fresh_491 (f : Var) :
    (nb068_alpha_dummy_498 f) ∉
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_495 f))).fv) :=
  by
  simpa only [nb068_alpha_dummy_498] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_495 f))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part008`. -/


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

theorem nb068_fresh_492 :
    (nb068_alpha_dummy_407) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_407] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0

theorem nb068_fresh_493 :
    (nb068_alpha_dummy_408) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_408] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1

theorem nb068_distinct_494 : (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_408) := by
  simpa only [nb068_alpha_dummy_407, nb068_alpha_dummy_408] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb068_fresh_495 :
    (nb068_alpha_dummy_327) ∉
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_327] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      0

theorem nb068_fresh_496 :
    (nb068_alpha_dummy_328) ∉
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_328] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      1

theorem nb068_fresh_497 :
    (nb068_alpha_dummy_329) ∉
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_329] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      2

theorem nb068_distinct_498 : (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_328) := by
  simpa only [nb068_alpha_dummy_327, nb068_alpha_dummy_328] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_distinct_499 : (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_329) := by
  simpa only [nb068_alpha_dummy_327, nb068_alpha_dummy_329] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb068_distinct_500 : (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_329) := by
  simpa only [nb068_alpha_dummy_328, nb068_alpha_dummy_329] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb068_fresh_501 :
    (nb068_alpha_dummy_239) ∉
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb068_alpha_dummy_239] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb068_fresh_502 :
    (nb068_alpha_dummy_240) ∉
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb068_alpha_dummy_240] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb068_distinct_503 : (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_240) := by
  simpa only [nb068_alpha_dummy_239, nb068_alpha_dummy_240] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb068_fresh_504 (f : Var) :
    (nb068_alpha_dummy_409 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_409] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 0

theorem nb068_fresh_505 (f : Var) :
    (nb068_alpha_dummy_410 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_410] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 1

theorem nb068_distinct_506 (f : Var) :
    (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_410 f) := by
  simpa only [nb068_alpha_dummy_409, nb068_alpha_dummy_410] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_507 (f : Var) :
    (nb068_alpha_dummy_330 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_330] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0

theorem nb068_fresh_508 (f : Var) :
    (nb068_alpha_dummy_331 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_331] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1

theorem nb068_fresh_509 (f : Var) :
    (nb068_alpha_dummy_332 f) ∉
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_332] using
    freshVar_not_mem
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2

theorem nb068_distinct_510 (f : Var) :
    (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_331 f) := by
  simpa only [nb068_alpha_dummy_330, nb068_alpha_dummy_331] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb068_distinct_511 (f : Var) :
    (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_332 f) := by
  simpa only [nb068_alpha_dummy_330, nb068_alpha_dummy_332] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb068_distinct_512 (f : Var) :
    (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_332 f) := by
  simpa only [nb068_alpha_dummy_331, nb068_alpha_dummy_332] using
    (freshVar_injective
      (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb068_fresh_513 (f : Var) :
    (nb068_alpha_dummy_241 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_241] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_514 (f : Var) :
    (nb068_alpha_dummy_242 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_242] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_515 (f : Var) :
    (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_242 f) := by
  simpa only [nb068_alpha_dummy_241, nb068_alpha_dummy_242] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_516 :
    (nb068_alpha_dummy_043) ∉
      (((syn_ccom (Class.cv (nb068_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb068_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb068_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb068_fresh_517 (f : Var) :
    (nb068_alpha_dummy_044 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb068_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb068_fresh_518 :
    (nb068_alpha_dummy_325) ∉
      (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb068_alpha_dummy_325] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb068_fresh_519 (f : Var) :
    (nb068_alpha_dummy_326 f) ∉
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv) :=
  by
  simpa only [nb068_alpha_dummy_326] using
    freshVar_not_mem
      (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪
        ((syn_cid)).fv)
      0

theorem nb068_fresh_520 :
    (nb068_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_521 (x : Var) (y : Var) :
    (nb068_alpha_dummy_010 x y) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_522 :
    (nb068_alpha_dummy_057) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_523 (f : Var) :
    (nb068_alpha_dummy_058 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_524 :
    (nb068_alpha_dummy_093) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_093] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_525 (f : Var) :
    (nb068_alpha_dummy_094 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_094] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_526 :
    (nb068_alpha_dummy_135) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_527 (f : Var) :
    (nb068_alpha_dummy_136 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_136] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_528 :
    (nb068_alpha_dummy_171) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_171] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_529 (f : Var) :
    (nb068_alpha_dummy_172 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_172] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_530 :
    (nb068_alpha_dummy_207) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_207] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_531 (f : Var) :
    (nb068_alpha_dummy_208 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_208] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_532 :
    (nb068_alpha_dummy_247) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_247] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_243)
              (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_243))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_533 (f : Var) :
    (nb068_alpha_dummy_248 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_248] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_245 f)
              (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_534 :
    (nb068_alpha_dummy_291) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_291] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_535 (f : Var) :
    (nb068_alpha_dummy_292 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_292] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_536 :
    (nb068_alpha_dummy_339) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_339] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_335)
              (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_335))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_537 (f : Var) :
    (nb068_alpha_dummy_340 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_340] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_337 f)
              (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_538 :
    (nb068_alpha_dummy_375) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_375] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_371)
              (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_371))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_539 (f : Var) :
    (nb068_alpha_dummy_376 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_376] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_373 f)
              (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_540 :
    (nb068_alpha_dummy_417) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_417] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_413)
              (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_413))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_541 (f : Var) :
    (nb068_alpha_dummy_418 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_418] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_415 f)
              (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_542 :
    (nb068_alpha_dummy_453) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_453] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_449)
              (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_543 (f : Var) :
    (nb068_alpha_dummy_454 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_454] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_451 f)
              (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_544 :
    (nb068_alpha_dummy_489) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_489] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_545 (f : Var) :
    (nb068_alpha_dummy_490 f) ∉
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_490] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb068_fresh_546 :
    (nb068_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv)
      0

theorem nb068_fresh_547 (x : Var) (y : Var) :
    (nb068_alpha_dummy_030 x y) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv)
      0

theorem nb068_fresh_548 :
    (nb068_alpha_dummy_077) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv)
      0

theorem nb068_fresh_549 (f : Var) :
    (nb068_alpha_dummy_078 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv)
      0

theorem nb068_fresh_550 :
    (nb068_alpha_dummy_113) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv)
      0

theorem nb068_fresh_551 (f : Var) :
    (nb068_alpha_dummy_114 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_114] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv)
      0

theorem nb068_fresh_552 :
    (nb068_alpha_dummy_155) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv)
      0

theorem nb068_fresh_553 (f : Var) :
    (nb068_alpha_dummy_156 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv)
      0

theorem nb068_fresh_554 :
    (nb068_alpha_dummy_191) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_191] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv)
      0

theorem nb068_fresh_555 (f : Var) :
    (nb068_alpha_dummy_192 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_192] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv)
      0

theorem nb068_fresh_556 :
    (nb068_alpha_dummy_227) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_227] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv)
      0

theorem nb068_fresh_557 (f : Var) :
    (nb068_alpha_dummy_228 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_228] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv)
      0

theorem nb068_fresh_558 :
    (nb068_alpha_dummy_267) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_267] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv)
      0

theorem nb068_fresh_559 (f : Var) :
    (nb068_alpha_dummy_268 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_268] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv)
      0

theorem nb068_fresh_560 :
    (nb068_alpha_dummy_311) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_311] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv)
      0

theorem nb068_fresh_561 (f : Var) :
    (nb068_alpha_dummy_312 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_312] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv)
      0

theorem nb068_fresh_562 :
    (nb068_alpha_dummy_359) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_359] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv)
      0

theorem nb068_fresh_563 (f : Var) :
    (nb068_alpha_dummy_360 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_360] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv)
      0

theorem nb068_fresh_564 :
    (nb068_alpha_dummy_395) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_395] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv)
      0

theorem nb068_fresh_565 (f : Var) :
    (nb068_alpha_dummy_396 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_396] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv)
      0

theorem nb068_fresh_566 :
    (nb068_alpha_dummy_437) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_437] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv)
      0

theorem nb068_fresh_567 (f : Var) :
    (nb068_alpha_dummy_438 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_438] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv)
      0

theorem nb068_fresh_568 :
    (nb068_alpha_dummy_473) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_473] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv)
      0

theorem nb068_fresh_569 (f : Var) :
    (nb068_alpha_dummy_474 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_474] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv)
      0

theorem nb068_fresh_570 :
    (nb068_alpha_dummy_509) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_509] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv)
      0

theorem nb068_fresh_571 (f : Var) :
    (nb068_alpha_dummy_510 f) ∉
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_510] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv)
      0

theorem nb068_fresh_572 :
    (nb068_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_573 (x : Var) (y : Var) :
    (nb068_alpha_dummy_038 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_574 :
    (nb068_alpha_dummy_085) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_575 (f : Var) :
    (nb068_alpha_dummy_086 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_576 :
    (nb068_alpha_dummy_121) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_577 (f : Var) :
    (nb068_alpha_dummy_122 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_122] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_578 :
    (nb068_alpha_dummy_163) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_163] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_579 (f : Var) :
    (nb068_alpha_dummy_164 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_164] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_580 :
    (nb068_alpha_dummy_199) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_199] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_581 (f : Var) :
    (nb068_alpha_dummy_200 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_200] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_582 :
    (nb068_alpha_dummy_235) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_235] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_583 (f : Var) :
    (nb068_alpha_dummy_236 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_236] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_584 :
    (nb068_alpha_dummy_275) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_275] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_585 (f : Var) :
    (nb068_alpha_dummy_276 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_276] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_586 :
    (nb068_alpha_dummy_319) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_319] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_587 (f : Var) :
    (nb068_alpha_dummy_320 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_320] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_588 :
    (nb068_alpha_dummy_367) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_367] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_589 (f : Var) :
    (nb068_alpha_dummy_368 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_368] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_590 :
    (nb068_alpha_dummy_403) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_403] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_591 (f : Var) :
    (nb068_alpha_dummy_404 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_404] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_592 :
    (nb068_alpha_dummy_445) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_445] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_593 (f : Var) :
    (nb068_alpha_dummy_446 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_446] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_594 :
    (nb068_alpha_dummy_481) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_481] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_595 (f : Var) :
    (nb068_alpha_dummy_482 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_482] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_596 :
    (nb068_alpha_dummy_517) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_517] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_597 (f : Var) :
    (nb068_alpha_dummy_518 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_518] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb068_fresh_598 :
    (nb068_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_020))
            (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv)
      0

theorem nb068_fresh_599 (x : Var) (y : Var) :
    (nb068_alpha_dummy_026 x y) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv)
      0

theorem nb068_fresh_600 :
    (nb068_alpha_dummy_073) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_068))
            (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_073] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv)
      0

theorem nb068_fresh_601 (f : Var) :
    (nb068_alpha_dummy_074 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv)
      0

theorem nb068_fresh_602 :
    (nb068_alpha_dummy_109) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_104))
            (Class.cv (nb068_alpha_dummy_105)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_109] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv)
      0

theorem nb068_fresh_603 (f : Var) :
    (nb068_alpha_dummy_110 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_110] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f)))).fv)
      0

theorem nb068_fresh_604 :
    (nb068_alpha_dummy_151) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_146))
            (Class.cv (nb068_alpha_dummy_147)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv)
      0

theorem nb068_fresh_605 (f : Var) :
    (nb068_alpha_dummy_152 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f)))).fv)
      0

theorem nb068_fresh_606 :
    (nb068_alpha_dummy_187) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_182))
            (Class.cv (nb068_alpha_dummy_183)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv)
      0

theorem nb068_fresh_607 (f : Var) :
    (nb068_alpha_dummy_188 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part009`. -/


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

theorem nb068_fresh_608 :
    (nb068_alpha_dummy_223) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_218))
            (Class.cv (nb068_alpha_dummy_219)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_223] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv)
      0

theorem nb068_fresh_609 (f : Var) :
    (nb068_alpha_dummy_224 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_224] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f)))).fv)
      0

theorem nb068_fresh_610 :
    (nb068_alpha_dummy_263) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_258))
            (Class.cv (nb068_alpha_dummy_259)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_263] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv)
      0

theorem nb068_fresh_611 (f : Var) :
    (nb068_alpha_dummy_264 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_264] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f))
            (Class.cv (nb068_alpha_dummy_262 f)))).fv)
      0

theorem nb068_fresh_612 :
    (nb068_alpha_dummy_307) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_302))
            (Class.cv (nb068_alpha_dummy_303)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_307] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv)
      0

theorem nb068_fresh_613 (f : Var) :
    (nb068_alpha_dummy_308 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_308] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f)))).fv)
      0

theorem nb068_fresh_614 :
    (nb068_alpha_dummy_355) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_350))
            (Class.cv (nb068_alpha_dummy_351)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_355] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv)
      0

theorem nb068_fresh_615 (f : Var) :
    (nb068_alpha_dummy_356 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_356] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f))
            (Class.cv (nb068_alpha_dummy_354 f)))).fv)
      0

theorem nb068_fresh_616 :
    (nb068_alpha_dummy_391) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_386))
            (Class.cv (nb068_alpha_dummy_387)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_391] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv)
      0

theorem nb068_fresh_617 (f : Var) :
    (nb068_alpha_dummy_392 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_392] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f))
            (Class.cv (nb068_alpha_dummy_390 f)))).fv)
      0

theorem nb068_fresh_618 :
    (nb068_alpha_dummy_433) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_428))
            (Class.cv (nb068_alpha_dummy_429)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_433] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv)
      0

theorem nb068_fresh_619 (f : Var) :
    (nb068_alpha_dummy_434 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_434] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f))
            (Class.cv (nb068_alpha_dummy_432 f)))).fv)
      0

theorem nb068_fresh_620 :
    (nb068_alpha_dummy_469) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_464))
            (Class.cv (nb068_alpha_dummy_465)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_469] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv)
      0

theorem nb068_fresh_621 (f : Var) :
    (nb068_alpha_dummy_470 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_470] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f))
            (Class.cv (nb068_alpha_dummy_468 f)))).fv)
      0

theorem nb068_fresh_622 :
    (nb068_alpha_dummy_505) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_500))
            (Class.cv (nb068_alpha_dummy_501)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_505] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv)
      0

theorem nb068_fresh_623 (f : Var) :
    (nb068_alpha_dummy_506 f) ∉
      (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_506] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f)))).fv)
      0

theorem nb068_fresh_624 :
    (nb068_alpha_dummy_041) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  simpa only [nb068_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv)
      0

theorem nb068_fresh_625 (f : Var) :
    (nb068_alpha_dummy_042 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb068_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb068_fresh_626 :
    (nb068_alpha_dummy_323) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) :=
  by
  simpa only [nb068_alpha_dummy_323] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
              (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv)
      0

theorem nb068_fresh_627 (f : Var) :
    (nb068_alpha_dummy_324 f) ∉
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv) :=
  by
  simpa only [nb068_alpha_dummy_324] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))
            (syn_cid))).fv)
      0

theorem nb068_fresh_628 :
    (nb068_alpha_dummy_279) ∉
      (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_279] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))).fv)
      0

theorem nb068_fresh_629 (y : Var) (f : Var) :
    (nb068_alpha_dummy_280 y f) ∉
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) :=
  by
  simpa only [nb068_alpha_dummy_280] using
    freshVar_not_mem
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv)
      0

theorem nb068_fresh_630 :
    (nb068_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv)
      0

theorem nb068_fresh_631 (x : Var) (y : Var) :
    (nb068_alpha_dummy_040 x y) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv)
      0

theorem nb068_fresh_632 :
    (nb068_alpha_dummy_087) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_087] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv)
      0

theorem nb068_fresh_633 (f : Var) :
    (nb068_alpha_dummy_088 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_088] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv)
      0

theorem nb068_fresh_634 :
    (nb068_alpha_dummy_123) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv)
      0

theorem nb068_fresh_635 (f : Var) :
    (nb068_alpha_dummy_124 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv)
      0

theorem nb068_fresh_636 :
    (nb068_alpha_dummy_165) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_165] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv)
      0

theorem nb068_fresh_637 (f : Var) :
    (nb068_alpha_dummy_166 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_166] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv)
      0

theorem nb068_fresh_638 :
    (nb068_alpha_dummy_201) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_201] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv)
      0

theorem nb068_fresh_639 (f : Var) :
    (nb068_alpha_dummy_202 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_202] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv)
      0

theorem nb068_fresh_640 :
    (nb068_alpha_dummy_237) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_237] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv)
      0

theorem nb068_fresh_641 (f : Var) :
    (nb068_alpha_dummy_238 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_238] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv)
      0

theorem nb068_fresh_642 :
    (nb068_alpha_dummy_277) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_277] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv)
      0

theorem nb068_fresh_643 (f : Var) :
    (nb068_alpha_dummy_278 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_278] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv)
      0

theorem nb068_fresh_644 :
    (nb068_alpha_dummy_321) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_321] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv)
      0

theorem nb068_fresh_645 (f : Var) :
    (nb068_alpha_dummy_322 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_322] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv)
      0

theorem nb068_fresh_646 :
    (nb068_alpha_dummy_369) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_369] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv)
      0

theorem nb068_fresh_647 (f : Var) :
    (nb068_alpha_dummy_370 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_370] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv)
      0

theorem nb068_fresh_648 :
    (nb068_alpha_dummy_405) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_405] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv)
      0

theorem nb068_fresh_649 (f : Var) :
    (nb068_alpha_dummy_406 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_406] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv)
      0

theorem nb068_fresh_650 :
    (nb068_alpha_dummy_447) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_447] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv)
      0

theorem nb068_fresh_651 (f : Var) :
    (nb068_alpha_dummy_448 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_448] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv)
      0

theorem nb068_fresh_652 :
    (nb068_alpha_dummy_483) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_483] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv)
      0

theorem nb068_fresh_653 (f : Var) :
    (nb068_alpha_dummy_484 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_484] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv)
      0

theorem nb068_fresh_654 :
    (nb068_alpha_dummy_519) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_519] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv)
      0

theorem nb068_fresh_655 (f : Var) :
    (nb068_alpha_dummy_520 f) ∉
      (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_520] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv)
      0

theorem nb068_fresh_656 :
    (nb068_alpha_dummy_281) ∉
      (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  simpa only [nb068_alpha_dummy_281] using
    freshVar_not_mem
      (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb068_alpha_dummy_002))).fv)
      0

theorem nb068_fresh_657 (y : Var) (f : Var) :
    (nb068_alpha_dummy_282 y f) ∉ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_282] using
    freshVar_not_mem (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_658 :
    (nb068_alpha_dummy_003) ∉
      (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv)
      0

theorem nb068_fresh_659 :
    (nb068_alpha_dummy_051) ∉
      (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047))
                (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_051] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047))
                (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv)
      0

theorem nb068_fresh_660 (f : Var) :
    (nb068_alpha_dummy_052 f) ∉
      (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_050 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
                (Class.cv (nb068_alpha_dummy_049 f)))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_052] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_050 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
                (Class.cv (nb068_alpha_dummy_049 f)))))).fv)
      0

theorem nb068_fresh_661 :
    (nb068_alpha_dummy_129) ∉
      (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_129] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))).fv)
      0

theorem nb068_fresh_662 (f : Var) :
    (nb068_alpha_dummy_130 f) ∉
      (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_130] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f)))).fv)
      0

theorem nb068_fresh_663 :
    (nb068_alpha_dummy_333) ∉
      (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
                (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
                (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_328)))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_333] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327))
                (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
                (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_328)))))).fv)
      0

theorem nb068_fresh_664 (f : Var) :
    (nb068_alpha_dummy_334 f) ∉
      (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_331 f)))))).fv) :=
  by
  simpa only [nb068_alpha_dummy_334] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_330 f))
                (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_331 f)))))).fv)
      0

theorem nb068_fresh_665 :
    (nb068_alpha_dummy_411) ∉
      (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_407)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_411] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_407)))).fv)
      0

theorem nb068_fresh_666 (f : Var) :
    (nb068_alpha_dummy_412 f) ∉
      (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_412] using
    freshVar_not_mem
      (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f)))).fv)
      0

theorem nb068_fresh_667 (x : Var) (y : Var) (f : Var) :
    (nb068_alpha_dummy_004 x y f) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb068_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb068_fresh_668 : (nb068_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb068_fresh_669 : (nb068_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb068_fresh_670 : (nb068_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb068_distinct_671 : (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_001) := by
  simpa only [nb068_alpha_dummy_000, nb068_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_672 : (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_002) := by
  simpa only [nb068_alpha_dummy_000, nb068_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_673 : (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_002) := by
  simpa only [nb068_alpha_dummy_001, nb068_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb068_support_mem_0000 :
    (nb068_alpha_dummy_001) ∈
      (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0001 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0002 :
    (nb068_alpha_dummy_002) ∈
      (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0003 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0004 :
    (nb068_alpha_dummy_001) ∈
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0005 :
    (nb068_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_005) from (by
          unfold nb068_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_006) from (by
            unfold nb068_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0006 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0007 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb068_alpha_dummy_007 x y) from (by
          unfold nb068_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb068_alpha_dummy_008 x y) from (by
            unfold nb068_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0008 :
    (nb068_alpha_dummy_001) ∈
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_005) from (by
          unfold nb068_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_006) from (by
            unfold nb068_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb068_alpha_dummy_007 x y) from (by
          unfold nb068_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb068_alpha_dummy_008 x y) from (by
            unfold nb068_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0010 :
    (nb068_alpha_dummy_006) ∈ (((Class.cv (nb068_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0011 (x : Var) (y : Var) :
    (nb068_alpha_dummy_008 x y) ∈ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0012 :
    (nb068_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_013))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0013 (x : Var) (y : Var) :
    (nb068_alpha_dummy_015 x y) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_015 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0014 :
    (nb068_alpha_dummy_013) ∈
      (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0015 (x : Var) (y : Var) :
    (nb068_alpha_dummy_015 x y) ∈
      (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0016 :
    (nb068_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_020))
            (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0017 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0018 :
    (nb068_alpha_dummy_020) ∈
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0019 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ∈
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0020 :
    (nb068_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_020))
            (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0021 (x : Var) (y : Var) :
    (nb068_alpha_dummy_024 x y) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0022 :
    (nb068_alpha_dummy_021) ∈
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0023 (x : Var) (y : Var) :
    (nb068_alpha_dummy_024 x y) ∈
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0024 :
    (nb068_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0025 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0026 :
    (nb068_alpha_dummy_020) ∈
      (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0027 (x : Var) (y : Var) :
    (nb068_alpha_dummy_023 x y) ∈
      (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0028 :
    (nb068_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0029 (x : Var) (y : Var) :
    (nb068_alpha_dummy_024 x y) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0030 :
    (nb068_alpha_dummy_021) ∈
      (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0031 (x : Var) (y : Var) :
    (nb068_alpha_dummy_024 x y) ∈
      (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪
        ((Class.cv (nb068_alpha_dummy_024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0032 :
    (nb068_alpha_dummy_002) ∈
      (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0033 :
    (nb068_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_005)
              (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_005) from (by
          unfold nb068_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_006) from (by
            unfold nb068_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0034 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0035 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_007 x y)
              (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb068_alpha_dummy_007 x y) from (by
          unfold nb068_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb068_alpha_dummy_008 x y) from (by
            unfold nb068_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0036 :
    (nb068_alpha_dummy_002) ∈
      (((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005)
            (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_005) from (by
          unfold nb068_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_006) from (by
            unfold nb068_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y)
            (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb068_alpha_dummy_007 x y) from (by
          unfold nb068_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb068_alpha_dummy_008 x y) from (by
            unfold nb068_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0038 :
    (nb068_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0039 (x : Var) (y : Var) :
    (nb068_alpha_dummy_008 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0040 :
    (nb068_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0041 (x : Var) (y : Var) :
    (nb068_alpha_dummy_008 x y) ∈
      (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0042 :
    (nb068_alpha_dummy_045) ∈
      (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047))
                (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0043 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_050 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
                (Class.cv (nb068_alpha_dummy_049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0044 :
    (nb068_alpha_dummy_046) ∈
      (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))
                (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047))
                (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0045 (f : Var) :
    (nb068_alpha_dummy_049 f) ∈
      (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪
        ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa
              (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb068_alpha_dummy_050 f)))
              (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
                (Class.cv (nb068_alpha_dummy_049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0046 :
    (nb068_alpha_dummy_045) ∈
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0047 :
    (nb068_alpha_dummy_045) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
            unfold nb068_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0048 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0049 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
            unfold nb068_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0050 :
    (nb068_alpha_dummy_045) ∈
      (((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
            unfold nb068_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0051 (f : Var) :
    (nb068_alpha_dummy_048 f) ∈
      (((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
            unfold nb068_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0052 :
    (nb068_alpha_dummy_054) ∈ (((Class.cv (nb068_alpha_dummy_054))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0053 (f : Var) :
    (nb068_alpha_dummy_056 f) ∈ (((Class.cv (nb068_alpha_dummy_056 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0054 :
    (nb068_alpha_dummy_061) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0055 (f : Var) :
    (nb068_alpha_dummy_063 f) ∈
      (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb068_alpha_dummy_063 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0056 :
    (nb068_alpha_dummy_061) ∈
      (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0057 (f : Var) :
    (nb068_alpha_dummy_063 f) ∈
      (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0058 :
    (nb068_alpha_dummy_068) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_068))
            (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0059 (f : Var) :
    (nb068_alpha_dummy_071 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0060 :
    (nb068_alpha_dummy_068) ∈
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0061 (f : Var) :
    (nb068_alpha_dummy_071 f) ∈
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0062 :
    (nb068_alpha_dummy_069) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_068))
            (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0063 (f : Var) :
    (nb068_alpha_dummy_072 f) ∈
      (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0064 :
    (nb068_alpha_dummy_069) ∈
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0065 (f : Var) :
    (nb068_alpha_dummy_072 f) ∈
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0066 :
    (nb068_alpha_dummy_068) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0067 (f : Var) :
    (nb068_alpha_dummy_071 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0068 :
    (nb068_alpha_dummy_068) ∈
      (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0069 (f : Var) :
    (nb068_alpha_dummy_071 f) ∈
      (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0070 :
    (nb068_alpha_dummy_069) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0071 (f : Var) :
    (nb068_alpha_dummy_072 f) ∈
      (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0072 :
    (nb068_alpha_dummy_069) ∈
      (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0073 (f : Var) :
    (nb068_alpha_dummy_072 f) ∈
      (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0074 :
    (nb068_alpha_dummy_046) ∈
      (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0075 :
    (nb068_alpha_dummy_046) ∈
      (((syn_ccompl (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_054) from (by
            unfold nb068_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
