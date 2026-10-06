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
    (nb068AlphaDummy160 f) ∉
      (((Class.cv (nb068AlphaDummy150 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv) :=
  by
  simpa only [nb068AlphaDummy160] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy150 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv)
      0

theorem nb068_fresh_193 :
    (nb068AlphaDummy175) ∉ (((Class.cv (nb068AlphaDummy168))).fv) := by
  simpa only [nb068AlphaDummy175] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy168))).fv) 0

theorem nb068_fresh_194 :
    (nb068AlphaDummy176) ∉ (((Class.cv (nb068AlphaDummy168))).fv) := by
  simpa only [nb068AlphaDummy176] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy168))).fv) 1

theorem nb068_distinct_195 : (nb068AlphaDummy175) ≠ (nb068AlphaDummy176) := by
  simpa only [nb068AlphaDummy175, nb068AlphaDummy176] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_196 (f : Var) :
    (nb068AlphaDummy177 f) ∉ (((Class.cv (nb068AlphaDummy170 f))).fv) := by
  simpa only [nb068AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy170 f))).fv) 0

theorem nb068_fresh_197 (f : Var) :
    (nb068AlphaDummy178 f) ∉ (((Class.cv (nb068AlphaDummy170 f))).fv) := by
  simpa only [nb068AlphaDummy178] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy170 f))).fv) 1

theorem nb068_distinct_198 (f : Var) :
    (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy178 f) := by
  simpa only [nb068AlphaDummy177, nb068AlphaDummy178] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_199 :
    (nb068AlphaDummy181) ∉
      (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy181] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_200 :
    (nb068AlphaDummy182) ∉
      (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy182] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_201 :
    (nb068AlphaDummy183) ∉
      (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy183] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_202 : (nb068AlphaDummy181) ≠ (nb068AlphaDummy182) := by
  simpa only [nb068AlphaDummy181, nb068AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_203 : (nb068AlphaDummy181) ≠ (nb068AlphaDummy183) := by
  simpa only [nb068AlphaDummy181, nb068AlphaDummy183] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_204 : (nb068AlphaDummy182) ≠ (nb068AlphaDummy183) := by
  simpa only [nb068AlphaDummy182, nb068AlphaDummy183] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_205 (f : Var) :
    (nb068AlphaDummy184 f) ∉
      (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy184] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_206 (f : Var) :
    (nb068AlphaDummy185 f) ∉
      (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy185] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_207 (f : Var) :
    (nb068AlphaDummy186 f) ∉
      (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy186] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_208 (f : Var) :
    (nb068AlphaDummy184 f) ≠ (nb068AlphaDummy185 f) := by
  simpa only [nb068AlphaDummy184, nb068AlphaDummy185] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_209 (f : Var) :
    (nb068AlphaDummy184 f) ≠ (nb068AlphaDummy186 f) := by
  simpa only [nb068AlphaDummy184, nb068AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_210 (f : Var) :
    (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy186 f) := by
  simpa only [nb068AlphaDummy185, nb068AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_211 :
    (nb068AlphaDummy193) ∉
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy182))).fv) :=
  by
  simpa only [nb068AlphaDummy193] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy182))).fv)
      0

theorem nb068_fresh_212 :
    (nb068AlphaDummy189) ∉
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) :=
  by
  simpa only [nb068AlphaDummy189] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv)
      0

theorem nb068_fresh_213 :
    (nb068AlphaDummy195) ∉
      (((Class.cv (nb068AlphaDummy183))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) :=
  by
  simpa only [nb068AlphaDummy195] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy183))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv)
      0

theorem nb068_fresh_214 (f : Var) :
    (nb068AlphaDummy194 f) ∉
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy185 f))).fv) :=
  by
  simpa only [nb068AlphaDummy194] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy185 f))).fv)
      0

theorem nb068_fresh_215 (f : Var) :
    (nb068AlphaDummy190 f) ∉
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv) :=
  by
  simpa only [nb068AlphaDummy190] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv)
      0

theorem nb068_fresh_216 (f : Var) :
    (nb068AlphaDummy196 f) ∉
      (((Class.cv (nb068AlphaDummy186 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv) :=
  by
  simpa only [nb068AlphaDummy196] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy186 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv)
      0

theorem nb068_fresh_217 :
    (nb068AlphaDummy211) ∉ (((Class.cv (nb068AlphaDummy204))).fv) := by
  simpa only [nb068AlphaDummy211] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy204))).fv) 0

theorem nb068_fresh_218 :
    (nb068AlphaDummy212) ∉ (((Class.cv (nb068AlphaDummy204))).fv) := by
  simpa only [nb068AlphaDummy212] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy204))).fv) 1

theorem nb068_distinct_219 : (nb068AlphaDummy211) ≠ (nb068AlphaDummy212) := by
  simpa only [nb068AlphaDummy211, nb068AlphaDummy212] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy204))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_220 (f : Var) :
    (nb068AlphaDummy213 f) ∉ (((Class.cv (nb068AlphaDummy206 f))).fv) := by
  simpa only [nb068AlphaDummy213] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy206 f))).fv) 0

theorem nb068_fresh_221 (f : Var) :
    (nb068AlphaDummy214 f) ∉ (((Class.cv (nb068AlphaDummy206 f))).fv) := by
  simpa only [nb068AlphaDummy214] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy206 f))).fv) 1

theorem nb068_distinct_222 (f : Var) :
    (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy214 f) := by
  simpa only [nb068AlphaDummy213, nb068AlphaDummy214] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy206 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_223 :
    (nb068AlphaDummy217) ∉
      (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy217] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_224 :
    (nb068AlphaDummy218) ∉
      (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy218] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_225 :
    (nb068AlphaDummy219) ∉
      (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy219] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_226 : (nb068AlphaDummy217) ≠ (nb068AlphaDummy218) := by
  simpa only [nb068AlphaDummy217, nb068AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_227 : (nb068AlphaDummy217) ≠ (nb068AlphaDummy219) := by
  simpa only [nb068AlphaDummy217, nb068AlphaDummy219] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_228 : (nb068AlphaDummy218) ≠ (nb068AlphaDummy219) := by
  simpa only [nb068AlphaDummy218, nb068AlphaDummy219] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_229 (f : Var) :
    (nb068AlphaDummy220 f) ∉
      (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy220] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_230 (f : Var) :
    (nb068AlphaDummy221 f) ∉
      (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy221] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_231 (f : Var) :
    (nb068AlphaDummy222 f) ∉
      (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy222] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_232 (f : Var) :
    (nb068AlphaDummy220 f) ≠ (nb068AlphaDummy221 f) := by
  simpa only [nb068AlphaDummy220, nb068AlphaDummy221] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_233 (f : Var) :
    (nb068AlphaDummy220 f) ≠ (nb068AlphaDummy222 f) := by
  simpa only [nb068AlphaDummy220, nb068AlphaDummy222] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_234 (f : Var) :
    (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy222 f) := by
  simpa only [nb068AlphaDummy221, nb068AlphaDummy222] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_235 :
    (nb068AlphaDummy229) ∉
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy218))).fv) :=
  by
  simpa only [nb068AlphaDummy229] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy218))).fv)
      0

theorem nb068_fresh_236 :
    (nb068AlphaDummy225) ∉
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) :=
  by
  simpa only [nb068AlphaDummy225] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv)
      0

theorem nb068_fresh_237 :
    (nb068AlphaDummy231) ∉
      (((Class.cv (nb068AlphaDummy219))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) :=
  by
  simpa only [nb068AlphaDummy231] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy219))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv)
      0

theorem nb068_fresh_238 (f : Var) :
    (nb068AlphaDummy230 f) ∉
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy221 f))).fv) :=
  by
  simpa only [nb068AlphaDummy230] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy221 f))).fv)
      0

theorem nb068_fresh_239 (f : Var) :
    (nb068AlphaDummy226 f) ∉
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv) :=
  by
  simpa only [nb068AlphaDummy226] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv)
      0

theorem nb068_fresh_240 (f : Var) :
    (nb068AlphaDummy232 f) ∉
      (((Class.cv (nb068AlphaDummy222 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv) :=
  by
  simpa only [nb068AlphaDummy232] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy222 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv)
      0

theorem nb068_fresh_241 :
    (nb068AlphaDummy243) ∉
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) :=
  by
  simpa only [nb068AlphaDummy243] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv)
      0

theorem nb068_fresh_242 :
    (nb068AlphaDummy244) ∉
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) :=
  by
  simpa only [nb068AlphaDummy244] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv)
      1

theorem nb068_distinct_243 : (nb068AlphaDummy243) ≠ (nb068AlphaDummy244) := by
  simpa only [nb068AlphaDummy243, nb068AlphaDummy244] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_244 (f : Var) :
    (nb068AlphaDummy245 f) ∉
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv) :=
  by
  simpa only [nb068AlphaDummy245] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv)
      0

theorem nb068_fresh_245 (f : Var) :
    (nb068AlphaDummy246 f) ∉
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv) :=
  by
  simpa only [nb068AlphaDummy246] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv)
      1

theorem nb068_distinct_246 (f : Var) :
    (nb068AlphaDummy245 f) ≠ (nb068AlphaDummy246 f) := by
  simpa only [nb068AlphaDummy245, nb068AlphaDummy246] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy242 f))).fv ∪
        ((Class.cv (nb068AlphaDummy241 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_247 :
    (nb068AlphaDummy251) ∉ (((Class.cv (nb068AlphaDummy244))).fv) := by
  simpa only [nb068AlphaDummy251] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy244))).fv) 0

theorem nb068_fresh_248 :
    (nb068AlphaDummy252) ∉ (((Class.cv (nb068AlphaDummy244))).fv) := by
  simpa only [nb068AlphaDummy252] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy244))).fv) 1

theorem nb068_distinct_249 : (nb068AlphaDummy251) ≠ (nb068AlphaDummy252) := by
  simpa only [nb068AlphaDummy251, nb068AlphaDummy252] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy244))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_250 (f : Var) :
    (nb068AlphaDummy253 f) ∉ (((Class.cv (nb068AlphaDummy246 f))).fv) := by
  simpa only [nb068AlphaDummy253] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy246 f))).fv) 0

theorem nb068_fresh_251 (f : Var) :
    (nb068AlphaDummy254 f) ∉ (((Class.cv (nb068AlphaDummy246 f))).fv) := by
  simpa only [nb068AlphaDummy254] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy246 f))).fv) 1

theorem nb068_distinct_252 (f : Var) :
    (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy254 f) := by
  simpa only [nb068AlphaDummy253, nb068AlphaDummy254] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy246 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_253 :
    (nb068AlphaDummy257) ∉
      (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy257] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_254 :
    (nb068AlphaDummy258) ∉
      (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy258] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_255 :
    (nb068AlphaDummy259) ∉
      (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy259] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_256 : (nb068AlphaDummy257) ≠ (nb068AlphaDummy258) := by
  simpa only [nb068AlphaDummy257, nb068AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_257 : (nb068AlphaDummy257) ≠ (nb068AlphaDummy259) := by
  simpa only [nb068AlphaDummy257, nb068AlphaDummy259] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_258 : (nb068AlphaDummy258) ≠ (nb068AlphaDummy259) := by
  simpa only [nb068AlphaDummy258, nb068AlphaDummy259] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_259 (f : Var) :
    (nb068AlphaDummy260 f) ∉
      (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy260] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_260 (f : Var) :
    (nb068AlphaDummy261 f) ∉
      (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy261] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_261 (f : Var) :
    (nb068AlphaDummy262 f) ∉
      (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy262] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_262 (f : Var) :
    (nb068AlphaDummy260 f) ≠ (nb068AlphaDummy261 f) := by
  simpa only [nb068AlphaDummy260, nb068AlphaDummy261] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_263 (f : Var) :
    (nb068AlphaDummy260 f) ≠ (nb068AlphaDummy262 f) := by
  simpa only [nb068AlphaDummy260, nb068AlphaDummy262] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_264 (f : Var) :
    (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy262 f) := by
  simpa only [nb068AlphaDummy261, nb068AlphaDummy262] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_265 :
    (nb068AlphaDummy269) ∉
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy258))).fv) :=
  by
  simpa only [nb068AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy258))).fv)
      0

theorem nb068_fresh_266 :
    (nb068AlphaDummy265) ∉
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) :=
  by
  simpa only [nb068AlphaDummy265] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv)
      0

theorem nb068_fresh_267 :
    (nb068AlphaDummy271) ∉
      (((Class.cv (nb068AlphaDummy259))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) :=
  by
  simpa only [nb068AlphaDummy271] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy259))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv)
      0

theorem nb068_fresh_268 (f : Var) :
    (nb068AlphaDummy270 f) ∉
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy261 f))).fv) :=
  by
  simpa only [nb068AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy261 f))).fv)
      0

theorem nb068_fresh_269 (f : Var) :
    (nb068AlphaDummy266 f) ∉
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv) :=
  by
  simpa only [nb068AlphaDummy266] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv)
      0

theorem nb068_fresh_270 (f : Var) :
    (nb068AlphaDummy272 f) ∉
      (((Class.cv (nb068AlphaDummy262 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv) :=
  by
  simpa only [nb068AlphaDummy272] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy262 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv)
      0

theorem nb068_fresh_271 :
    (nb068AlphaDummy287) ∉
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) :=
  by
  simpa only [nb068AlphaDummy287] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv)
      0

theorem nb068_fresh_272 :
    (nb068AlphaDummy288) ∉
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) :=
  by
  simpa only [nb068AlphaDummy288] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv)
      1

theorem nb068_distinct_273 : (nb068AlphaDummy287) ≠ (nb068AlphaDummy288) := by
  simpa only [nb068AlphaDummy287, nb068AlphaDummy288] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_274 (f : Var) :
    (nb068AlphaDummy289 f) ∉
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv) :=
  by
  simpa only [nb068AlphaDummy289] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv)
      0

theorem nb068_fresh_275 (f : Var) :
    (nb068AlphaDummy290 f) ∉
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv) :=
  by
  simpa only [nb068AlphaDummy290] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv)
      1

theorem nb068_distinct_276 (f : Var) :
    (nb068AlphaDummy289 f) ≠ (nb068AlphaDummy290 f) := by
  simpa only [nb068AlphaDummy289, nb068AlphaDummy290] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy286 f))).fv ∪
        ((Class.cv (nb068AlphaDummy285 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_277 :
    (nb068AlphaDummy295) ∉ (((Class.cv (nb068AlphaDummy288))).fv) := by
  simpa only [nb068AlphaDummy295] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy288))).fv) 0

theorem nb068_fresh_278 :
    (nb068AlphaDummy296) ∉ (((Class.cv (nb068AlphaDummy288))).fv) := by
  simpa only [nb068AlphaDummy296] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy288))).fv) 1

theorem nb068_distinct_279 : (nb068AlphaDummy295) ≠ (nb068AlphaDummy296) := by
  simpa only [nb068AlphaDummy295, nb068AlphaDummy296] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy288))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_280 (f : Var) :
    (nb068AlphaDummy297 f) ∉ (((Class.cv (nb068AlphaDummy290 f))).fv) := by
  simpa only [nb068AlphaDummy297] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy290 f))).fv) 0

theorem nb068_fresh_281 (f : Var) :
    (nb068AlphaDummy298 f) ∉ (((Class.cv (nb068AlphaDummy290 f))).fv) := by
  simpa only [nb068AlphaDummy298] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy290 f))).fv) 1

theorem nb068_distinct_282 (f : Var) :
    (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy298 f) := by
  simpa only [nb068AlphaDummy297, nb068AlphaDummy298] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy290 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_283 :
    (nb068AlphaDummy301) ∉
      (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy301] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_284 :
    (nb068AlphaDummy302) ∉
      (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy302] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_285 :
    (nb068AlphaDummy303) ∉
      (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy303] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_286 : (nb068AlphaDummy301) ≠ (nb068AlphaDummy302) := by
  simpa only [nb068AlphaDummy301, nb068AlphaDummy302] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_287 : (nb068AlphaDummy301) ≠ (nb068AlphaDummy303) := by
  simpa only [nb068AlphaDummy301, nb068AlphaDummy303] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_288 : (nb068AlphaDummy302) ≠ (nb068AlphaDummy303) := by
  simpa only [nb068AlphaDummy302, nb068AlphaDummy303] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_289 (f : Var) :
    (nb068AlphaDummy304 f) ∉
      (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy304] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_290 (f : Var) :
    (nb068AlphaDummy305 f) ∉
      (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy305] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_291 (f : Var) :
    (nb068AlphaDummy306 f) ∉
      (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy306] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_292 (f : Var) :
    (nb068AlphaDummy304 f) ≠ (nb068AlphaDummy305 f) := by
  simpa only [nb068AlphaDummy304, nb068AlphaDummy305] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_293 (f : Var) :
    (nb068AlphaDummy304 f) ≠ (nb068AlphaDummy306 f) := by
  simpa only [nb068AlphaDummy304, nb068AlphaDummy306] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_294 (f : Var) :
    (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy306 f) := by
  simpa only [nb068AlphaDummy305, nb068AlphaDummy306] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_295 :
    (nb068AlphaDummy313) ∉
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy302))).fv) :=
  by
  simpa only [nb068AlphaDummy313] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy302))).fv)
      0

theorem nb068_fresh_296 :
    (nb068AlphaDummy309) ∉
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) :=
  by
  simpa only [nb068AlphaDummy309] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv)
      0

theorem nb068_fresh_297 :
    (nb068AlphaDummy315) ∉
      (((Class.cv (nb068AlphaDummy303))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) :=
  by
  simpa only [nb068AlphaDummy315] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy303))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv)
      0

theorem nb068_fresh_298 (f : Var) :
    (nb068AlphaDummy314 f) ∉
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy305 f))).fv) :=
  by
  simpa only [nb068AlphaDummy314] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy305 f))).fv)
      0

theorem nb068_fresh_299 (f : Var) :
    (nb068AlphaDummy310 f) ∉
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv) :=
  by
  simpa only [nb068AlphaDummy310] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv)
      0

theorem nb068_fresh_300 (f : Var) :
    (nb068AlphaDummy316 f) ∉
      (((Class.cv (nb068AlphaDummy306 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv) :=
  by
  simpa only [nb068AlphaDummy316] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy306 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv)
      0

theorem nb068_fresh_301 :
    (nb068AlphaDummy335) ∉
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  simpa only [nb068AlphaDummy335] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      0

theorem nb068_fresh_302 :
    (nb068AlphaDummy336) ∉
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  simpa only [nb068AlphaDummy336] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      1

theorem nb068_distinct_303 : (nb068AlphaDummy335) ≠ (nb068AlphaDummy336) := by
  simpa only [nb068AlphaDummy335, nb068AlphaDummy336] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_304 :
    (nb068AlphaDummy371) ∉
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) :=
  by
  simpa only [nb068AlphaDummy371] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv)
      0

theorem nb068_fresh_305 :
    (nb068AlphaDummy372) ∉
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv) :=
  by
  simpa only [nb068AlphaDummy372] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv)
      1

theorem nb068_distinct_306 : (nb068AlphaDummy371) ≠ (nb068AlphaDummy372) := by
  simpa only [nb068AlphaDummy371, nb068AlphaDummy372] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy329))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_307 :
    (nb068AlphaDummy485) ∉
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  simpa only [nb068AlphaDummy485] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      0

theorem nb068_fresh_308 :
    (nb068AlphaDummy486) ∉
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  simpa only [nb068AlphaDummy486] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      1

theorem nb068_distinct_309 : (nb068AlphaDummy485) ≠ (nb068AlphaDummy486) := by
  simpa only [nb068AlphaDummy485, nb068AlphaDummy486] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_310 (f : Var) :
    (nb068AlphaDummy337 f) ∉
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  simpa only [nb068AlphaDummy337] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv)
      0

theorem nb068_fresh_311 (f : Var) :
    (nb068AlphaDummy338 f) ∉
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  simpa only [nb068AlphaDummy338] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv)
      1

theorem nb068_distinct_312 (f : Var) :
    (nb068AlphaDummy337 f) ≠ (nb068AlphaDummy338 f) := by
  simpa only [nb068AlphaDummy337, nb068AlphaDummy338] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy330 f))).fv ∪
        ((Class.cv (nb068AlphaDummy331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_313 (f : Var) :
    (nb068AlphaDummy373 f) ∉
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv) :=
  by
  simpa only [nb068AlphaDummy373] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv)
      0

theorem nb068_fresh_314 (f : Var) :
    (nb068AlphaDummy374 f) ∉
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv) :=
  by
  simpa only [nb068AlphaDummy374] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy332 f))).fv)
      1

theorem nb068_distinct_315 (f : Var) :
    (nb068AlphaDummy373 f) ≠ (nb068AlphaDummy374 f) := by
  simpa only [nb068AlphaDummy373, nb068AlphaDummy374] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy330 f))).fv ∪
        ((Class.cv (nb068AlphaDummy332 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_316 (f : Var) :
    (nb068AlphaDummy487 f) ∉
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  simpa only [nb068AlphaDummy487] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv)
      0

theorem nb068_fresh_317 (f : Var) :
    (nb068AlphaDummy488 f) ∉
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  simpa only [nb068AlphaDummy488] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy332 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv)
      1

theorem nb068_distinct_318 (f : Var) :
    (nb068AlphaDummy487 f) ≠ (nb068AlphaDummy488 f) := by
  simpa only [nb068AlphaDummy487, nb068AlphaDummy488] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy332 f))).fv ∪
        ((Class.cv (nb068AlphaDummy331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_319 :
    (nb068AlphaDummy343) ∉ (((Class.cv (nb068AlphaDummy336))).fv) := by
  simpa only [nb068AlphaDummy343] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy336))).fv) 0

theorem nb068_fresh_320 :
    (nb068AlphaDummy344) ∉ (((Class.cv (nb068AlphaDummy336))).fv) := by
  simpa only [nb068AlphaDummy344] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy336))).fv) 1

theorem nb068_distinct_321 : (nb068AlphaDummy343) ≠ (nb068AlphaDummy344) := by
  simpa only [nb068AlphaDummy343, nb068AlphaDummy344] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy336))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_322 (f : Var) :
    (nb068AlphaDummy345 f) ∉ (((Class.cv (nb068AlphaDummy338 f))).fv) := by
  simpa only [nb068AlphaDummy345] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy338 f))).fv) 0

theorem nb068_fresh_323 (f : Var) :
    (nb068AlphaDummy346 f) ∉ (((Class.cv (nb068AlphaDummy338 f))).fv) := by
  simpa only [nb068AlphaDummy346] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy338 f))).fv) 1

theorem nb068_distinct_324 (f : Var) :
    (nb068AlphaDummy345 f) ≠ (nb068AlphaDummy346 f) := by
  simpa only [nb068AlphaDummy345, nb068AlphaDummy346] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy338 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_325 :
    (nb068AlphaDummy349) ∉
      (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy349] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_326 :
    (nb068AlphaDummy350) ∉
      (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy350] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_327 :
    (nb068AlphaDummy351) ∉
      (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy351] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_328 : (nb068AlphaDummy349) ≠ (nb068AlphaDummy350) := by
  simpa only [nb068AlphaDummy349, nb068AlphaDummy350] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_329 : (nb068AlphaDummy349) ≠ (nb068AlphaDummy351) := by
  simpa only [nb068AlphaDummy349, nb068AlphaDummy351] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_330 : (nb068AlphaDummy350) ≠ (nb068AlphaDummy351) := by
  simpa only [nb068AlphaDummy350, nb068AlphaDummy351] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_331 (f : Var) :
    (nb068AlphaDummy352 f) ∉
      (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy352] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_332 (f : Var) :
    (nb068AlphaDummy353 f) ∉
      (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy353] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_333 (f : Var) :
    (nb068AlphaDummy354 f) ∉
      (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy354] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_334 (f : Var) :
    (nb068AlphaDummy352 f) ≠ (nb068AlphaDummy353 f) := by
  simpa only [nb068AlphaDummy352, nb068AlphaDummy353] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_335 (f : Var) :
    (nb068AlphaDummy352 f) ≠ (nb068AlphaDummy354 f) := by
  simpa only [nb068AlphaDummy352, nb068AlphaDummy354] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_336 (f : Var) :
    (nb068AlphaDummy353 f) ≠ (nb068AlphaDummy354 f) := by
  simpa only [nb068AlphaDummy353, nb068AlphaDummy354] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_337 :
    (nb068AlphaDummy361) ∉
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy350))).fv) :=
  by
  simpa only [nb068AlphaDummy361] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy350))).fv)
      0

theorem nb068_fresh_338 :
    (nb068AlphaDummy357) ∉
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) :=
  by
  simpa only [nb068AlphaDummy357] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy350))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv)
      0

theorem nb068_fresh_339 :
    (nb068AlphaDummy363) ∉
      (((Class.cv (nb068AlphaDummy351))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv) :=
  by
  simpa only [nb068AlphaDummy363] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy351))).fv ∪ ((Class.cv (nb068AlphaDummy351))).fv)
      0

theorem nb068_fresh_340 (f : Var) :
    (nb068AlphaDummy362 f) ∉
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy353 f))).fv) :=
  by
  simpa only [nb068AlphaDummy362] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy353 f))).fv)
      0

theorem nb068_fresh_341 (f : Var) :
    (nb068AlphaDummy358 f) ∉
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv) :=
  by
  simpa only [nb068AlphaDummy358] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy353 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv)
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
    (nb068AlphaDummy364 f) ∉
      (((Class.cv (nb068AlphaDummy354 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv) :=
  by
  simpa only [nb068AlphaDummy364] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy354 f))).fv ∪ ((Class.cv (nb068AlphaDummy354 f))).fv)
      0

theorem nb068_fresh_343 :
    (nb068AlphaDummy379) ∉ (((Class.cv (nb068AlphaDummy372))).fv) := by
  simpa only [nb068AlphaDummy379] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy372))).fv) 0

theorem nb068_fresh_344 :
    (nb068AlphaDummy380) ∉ (((Class.cv (nb068AlphaDummy372))).fv) := by
  simpa only [nb068AlphaDummy380] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy372))).fv) 1

theorem nb068_distinct_345 : (nb068AlphaDummy379) ≠ (nb068AlphaDummy380) := by
  simpa only [nb068AlphaDummy379, nb068AlphaDummy380] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy372))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_346 (f : Var) :
    (nb068AlphaDummy381 f) ∉ (((Class.cv (nb068AlphaDummy374 f))).fv) := by
  simpa only [nb068AlphaDummy381] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy374 f))).fv) 0

theorem nb068_fresh_347 (f : Var) :
    (nb068AlphaDummy382 f) ∉ (((Class.cv (nb068AlphaDummy374 f))).fv) := by
  simpa only [nb068AlphaDummy382] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy374 f))).fv) 1

theorem nb068_distinct_348 (f : Var) :
    (nb068AlphaDummy381 f) ≠ (nb068AlphaDummy382 f) := by
  simpa only [nb068AlphaDummy381, nb068AlphaDummy382] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy374 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_349 :
    (nb068AlphaDummy385) ∉
      (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy385] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_350 :
    (nb068AlphaDummy386) ∉
      (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy386] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_351 :
    (nb068AlphaDummy387) ∉
      (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy387] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_352 : (nb068AlphaDummy385) ≠ (nb068AlphaDummy386) := by
  simpa only [nb068AlphaDummy385, nb068AlphaDummy386] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_353 : (nb068AlphaDummy385) ≠ (nb068AlphaDummy387) := by
  simpa only [nb068AlphaDummy385, nb068AlphaDummy387] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_354 : (nb068AlphaDummy386) ≠ (nb068AlphaDummy387) := by
  simpa only [nb068AlphaDummy386, nb068AlphaDummy387] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy379))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_355 (f : Var) :
    (nb068AlphaDummy388 f) ∉
      (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy388] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_356 (f : Var) :
    (nb068AlphaDummy389 f) ∉
      (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy389] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_357 (f : Var) :
    (nb068AlphaDummy390 f) ∉
      (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy390] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_358 (f : Var) :
    (nb068AlphaDummy388 f) ≠ (nb068AlphaDummy389 f) := by
  simpa only [nb068AlphaDummy388, nb068AlphaDummy389] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_359 (f : Var) :
    (nb068AlphaDummy388 f) ≠ (nb068AlphaDummy390 f) := by
  simpa only [nb068AlphaDummy388, nb068AlphaDummy390] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_360 (f : Var) :
    (nb068AlphaDummy389 f) ≠ (nb068AlphaDummy390 f) := by
  simpa only [nb068AlphaDummy389, nb068AlphaDummy390] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy381 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_361 :
    (nb068AlphaDummy397) ∉
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy386))).fv) :=
  by
  simpa only [nb068AlphaDummy397] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy386))).fv)
      0

theorem nb068_fresh_362 :
    (nb068AlphaDummy393) ∉
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) :=
  by
  simpa only [nb068AlphaDummy393] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy386))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv)
      0

theorem nb068_fresh_363 :
    (nb068AlphaDummy399) ∉
      (((Class.cv (nb068AlphaDummy387))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv) :=
  by
  simpa only [nb068AlphaDummy399] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy387))).fv ∪ ((Class.cv (nb068AlphaDummy387))).fv)
      0

theorem nb068_fresh_364 (f : Var) :
    (nb068AlphaDummy398 f) ∉
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy389 f))).fv) :=
  by
  simpa only [nb068AlphaDummy398] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy389 f))).fv)
      0

theorem nb068_fresh_365 (f : Var) :
    (nb068AlphaDummy394 f) ∉
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv) :=
  by
  simpa only [nb068AlphaDummy394] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy389 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv)
      0

theorem nb068_fresh_366 (f : Var) :
    (nb068AlphaDummy400 f) ∉
      (((Class.cv (nb068AlphaDummy390 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv) :=
  by
  simpa only [nb068AlphaDummy400] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy390 f))).fv ∪ ((Class.cv (nb068AlphaDummy390 f))).fv)
      0

theorem nb068_fresh_367 :
    (nb068AlphaDummy413) ∉
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) :=
  by
  simpa only [nb068AlphaDummy413] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv)
      0

theorem nb068_fresh_368 :
    (nb068AlphaDummy414) ∉
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv) :=
  by
  simpa only [nb068AlphaDummy414] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv)
      1

theorem nb068_distinct_369 : (nb068AlphaDummy413) ≠ (nb068AlphaDummy414) := by
  simpa only [nb068AlphaDummy413, nb068AlphaDummy414] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy407))).fv ∪ ((Class.cv (nb068AlphaDummy408))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_370 :
    (nb068AlphaDummy449) ∉
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) :=
  by
  simpa only [nb068AlphaDummy449] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv)
      0

theorem nb068_fresh_371 :
    (nb068AlphaDummy450) ∉
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv) :=
  by
  simpa only [nb068AlphaDummy450] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv)
      1

theorem nb068_distinct_372 : (nb068AlphaDummy449) ≠ (nb068AlphaDummy450) := by
  simpa only [nb068AlphaDummy449, nb068AlphaDummy450] using
    (freshVar_injective
      (((Class.cv (nb068AlphaDummy408))).fv ∪ ((Class.cv (nb068AlphaDummy407))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_fresh_373 (f : Var) :
    (nb068AlphaDummy415 f) ∉
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv) :=
  by
  simpa only [nb068AlphaDummy415] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv)
      0

theorem nb068_fresh_374 (f : Var) :
    (nb068AlphaDummy416 f) ∉
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv) :=
  by
  simpa only [nb068AlphaDummy416] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy409 f))).fv ∪ ((Class.cv (nb068AlphaDummy410 f))).fv)
      1

theorem nb068_distinct_375 (f : Var) :
    (nb068AlphaDummy415 f) ≠ (nb068AlphaDummy416 f) := by
  simpa only [nb068AlphaDummy415, nb068AlphaDummy416] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy409 f))).fv ∪
        ((Class.cv (nb068AlphaDummy410 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_376 (f : Var) :
    (nb068AlphaDummy451 f) ∉
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv) :=
  by
  simpa only [nb068AlphaDummy451] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv)
      0

theorem nb068_fresh_377 (f : Var) :
    (nb068AlphaDummy452 f) ∉
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv) :=
  by
  simpa only [nb068AlphaDummy452] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy410 f))).fv ∪ ((Class.cv (nb068AlphaDummy409 f))).fv)
      1

theorem nb068_distinct_378 (f : Var) :
    (nb068AlphaDummy451 f) ≠ (nb068AlphaDummy452 f) := by
  simpa only [nb068AlphaDummy451, nb068AlphaDummy452] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy410 f))).fv ∪
        ((Class.cv (nb068AlphaDummy409 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_379 :
    (nb068AlphaDummy421) ∉ (((Class.cv (nb068AlphaDummy414))).fv) := by
  simpa only [nb068AlphaDummy421] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy414))).fv) 0

theorem nb068_fresh_380 :
    (nb068AlphaDummy422) ∉ (((Class.cv (nb068AlphaDummy414))).fv) := by
  simpa only [nb068AlphaDummy422] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy414))).fv) 1

theorem nb068_distinct_381 : (nb068AlphaDummy421) ≠ (nb068AlphaDummy422) := by
  simpa only [nb068AlphaDummy421, nb068AlphaDummy422] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy414))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_382 (f : Var) :
    (nb068AlphaDummy423 f) ∉ (((Class.cv (nb068AlphaDummy416 f))).fv) := by
  simpa only [nb068AlphaDummy423] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy416 f))).fv) 0

theorem nb068_fresh_383 (f : Var) :
    (nb068AlphaDummy424 f) ∉ (((Class.cv (nb068AlphaDummy416 f))).fv) := by
  simpa only [nb068AlphaDummy424] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy416 f))).fv) 1

theorem nb068_distinct_384 (f : Var) :
    (nb068AlphaDummy423 f) ≠ (nb068AlphaDummy424 f) := by
  simpa only [nb068AlphaDummy423, nb068AlphaDummy424] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy416 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_385 :
    (nb068AlphaDummy427) ∉
      (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy427] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_386 :
    (nb068AlphaDummy428) ∉
      (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy428] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_387 :
    (nb068AlphaDummy429) ∉
      (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy429] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_388 : (nb068AlphaDummy427) ≠ (nb068AlphaDummy428) := by
  simpa only [nb068AlphaDummy427, nb068AlphaDummy428] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_389 : (nb068AlphaDummy427) ≠ (nb068AlphaDummy429) := by
  simpa only [nb068AlphaDummy427, nb068AlphaDummy429] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_390 : (nb068AlphaDummy428) ≠ (nb068AlphaDummy429) := by
  simpa only [nb068AlphaDummy428, nb068AlphaDummy429] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy421))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_391 (f : Var) :
    (nb068AlphaDummy430 f) ∉
      (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy430] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_392 (f : Var) :
    (nb068AlphaDummy431 f) ∉
      (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy431] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_393 (f : Var) :
    (nb068AlphaDummy432 f) ∉
      (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy432] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_394 (f : Var) :
    (nb068AlphaDummy430 f) ≠ (nb068AlphaDummy431 f) := by
  simpa only [nb068AlphaDummy430, nb068AlphaDummy431] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_395 (f : Var) :
    (nb068AlphaDummy430 f) ≠ (nb068AlphaDummy432 f) := by
  simpa only [nb068AlphaDummy430, nb068AlphaDummy432] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_396 (f : Var) :
    (nb068AlphaDummy431 f) ≠ (nb068AlphaDummy432 f) := by
  simpa only [nb068AlphaDummy431, nb068AlphaDummy432] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy423 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_397 :
    (nb068AlphaDummy439) ∉
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy428))).fv) :=
  by
  simpa only [nb068AlphaDummy439] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy428))).fv)
      0

theorem nb068_fresh_398 :
    (nb068AlphaDummy435) ∉
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) :=
  by
  simpa only [nb068AlphaDummy435] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy428))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv)
      0

theorem nb068_fresh_399 :
    (nb068AlphaDummy441) ∉
      (((Class.cv (nb068AlphaDummy429))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv) :=
  by
  simpa only [nb068AlphaDummy441] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy429))).fv ∪ ((Class.cv (nb068AlphaDummy429))).fv)
      0

theorem nb068_fresh_400 (f : Var) :
    (nb068AlphaDummy440 f) ∉
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy431 f))).fv) :=
  by
  simpa only [nb068AlphaDummy440] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy431 f))).fv)
      0

theorem nb068_fresh_401 (f : Var) :
    (nb068AlphaDummy436 f) ∉
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv) :=
  by
  simpa only [nb068AlphaDummy436] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy431 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv)
      0

theorem nb068_fresh_402 (f : Var) :
    (nb068AlphaDummy442 f) ∉
      (((Class.cv (nb068AlphaDummy432 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv) :=
  by
  simpa only [nb068AlphaDummy442] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy432 f))).fv ∪ ((Class.cv (nb068AlphaDummy432 f))).fv)
      0

theorem nb068_fresh_403 :
    (nb068AlphaDummy457) ∉ (((Class.cv (nb068AlphaDummy450))).fv) := by
  simpa only [nb068AlphaDummy457] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy450))).fv) 0

theorem nb068_fresh_404 :
    (nb068AlphaDummy458) ∉ (((Class.cv (nb068AlphaDummy450))).fv) := by
  simpa only [nb068AlphaDummy458] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy450))).fv) 1

theorem nb068_distinct_405 : (nb068AlphaDummy457) ≠ (nb068AlphaDummy458) := by
  simpa only [nb068AlphaDummy457, nb068AlphaDummy458] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy450))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_406 (f : Var) :
    (nb068AlphaDummy459 f) ∉ (((Class.cv (nb068AlphaDummy452 f))).fv) := by
  simpa only [nb068AlphaDummy459] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy452 f))).fv) 0

theorem nb068_fresh_407 (f : Var) :
    (nb068AlphaDummy460 f) ∉ (((Class.cv (nb068AlphaDummy452 f))).fv) := by
  simpa only [nb068AlphaDummy460] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy452 f))).fv) 1

theorem nb068_distinct_408 (f : Var) :
    (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy460 f) := by
  simpa only [nb068AlphaDummy459, nb068AlphaDummy460] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy452 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_409 :
    (nb068AlphaDummy463) ∉
      (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy463] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_410 :
    (nb068AlphaDummy464) ∉
      (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy464] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_411 :
    (nb068AlphaDummy465) ∉
      (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy465] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_412 : (nb068AlphaDummy463) ≠ (nb068AlphaDummy464) := by
  simpa only [nb068AlphaDummy463, nb068AlphaDummy464] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_413 : (nb068AlphaDummy463) ≠ (nb068AlphaDummy465) := by
  simpa only [nb068AlphaDummy463, nb068AlphaDummy465] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_414 : (nb068AlphaDummy464) ≠ (nb068AlphaDummy465) := by
  simpa only [nb068AlphaDummy464, nb068AlphaDummy465] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_415 (f : Var) :
    (nb068AlphaDummy466 f) ∉
      (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy466] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_416 (f : Var) :
    (nb068AlphaDummy467 f) ∉
      (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy467] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_417 (f : Var) :
    (nb068AlphaDummy468 f) ∉
      (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy468] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_418 (f : Var) :
    (nb068AlphaDummy466 f) ≠ (nb068AlphaDummy467 f) := by
  simpa only [nb068AlphaDummy466, nb068AlphaDummy467] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_419 (f : Var) :
    (nb068AlphaDummy466 f) ≠ (nb068AlphaDummy468 f) := by
  simpa only [nb068AlphaDummy466, nb068AlphaDummy468] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_420 (f : Var) :
    (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy468 f) := by
  simpa only [nb068AlphaDummy467, nb068AlphaDummy468] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_421 :
    (nb068AlphaDummy475) ∉
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy464))).fv) :=
  by
  simpa only [nb068AlphaDummy475] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy464))).fv)
      0

theorem nb068_fresh_422 :
    (nb068AlphaDummy471) ∉
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) :=
  by
  simpa only [nb068AlphaDummy471] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy464))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv)
      0

theorem nb068_fresh_423 :
    (nb068AlphaDummy477) ∉
      (((Class.cv (nb068AlphaDummy465))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv) :=
  by
  simpa only [nb068AlphaDummy477] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy465))).fv ∪ ((Class.cv (nb068AlphaDummy465))).fv)
      0

theorem nb068_fresh_424 (f : Var) :
    (nb068AlphaDummy476 f) ∉
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy467 f))).fv) :=
  by
  simpa only [nb068AlphaDummy476] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy467 f))).fv)
      0

theorem nb068_fresh_425 (f : Var) :
    (nb068AlphaDummy472 f) ∉
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv) :=
  by
  simpa only [nb068AlphaDummy472] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy467 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv)
      0

theorem nb068_fresh_426 (f : Var) :
    (nb068AlphaDummy478 f) ∉
      (((Class.cv (nb068AlphaDummy468 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv) :=
  by
  simpa only [nb068AlphaDummy478] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy468 f))).fv ∪ ((Class.cv (nb068AlphaDummy468 f))).fv)
      0

theorem nb068_fresh_427 :
    (nb068AlphaDummy493) ∉ (((Class.cv (nb068AlphaDummy486))).fv) := by
  simpa only [nb068AlphaDummy493] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy486))).fv) 0

theorem nb068_fresh_428 :
    (nb068AlphaDummy494) ∉ (((Class.cv (nb068AlphaDummy486))).fv) := by
  simpa only [nb068AlphaDummy494] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy486))).fv) 1

theorem nb068_distinct_429 : (nb068AlphaDummy493) ≠ (nb068AlphaDummy494) := by
  simpa only [nb068AlphaDummy493, nb068AlphaDummy494] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy486))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_430 (f : Var) :
    (nb068AlphaDummy495 f) ∉ (((Class.cv (nb068AlphaDummy488 f))).fv) := by
  simpa only [nb068AlphaDummy495] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy488 f))).fv) 0

theorem nb068_fresh_431 (f : Var) :
    (nb068AlphaDummy496 f) ∉ (((Class.cv (nb068AlphaDummy488 f))).fv) := by
  simpa only [nb068AlphaDummy496] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy488 f))).fv) 1

theorem nb068_distinct_432 (f : Var) :
    (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy496 f) := by
  simpa only [nb068AlphaDummy495, nb068AlphaDummy496] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy488 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_433 :
    (nb068AlphaDummy499) ∉
      (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy499] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_434 :
    (nb068AlphaDummy500) ∉
      (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy500] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_435 :
    (nb068AlphaDummy501) ∉
      (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy501] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_436 : (nb068AlphaDummy499) ≠ (nb068AlphaDummy500) := by
  simpa only [nb068AlphaDummy499, nb068AlphaDummy500] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_437 : (nb068AlphaDummy499) ≠ (nb068AlphaDummy501) := by
  simpa only [nb068AlphaDummy499, nb068AlphaDummy501] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_438 : (nb068AlphaDummy500) ≠ (nb068AlphaDummy501) := by
  simpa only [nb068AlphaDummy500, nb068AlphaDummy501] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_439 (f : Var) :
    (nb068AlphaDummy502 f) ∉
      (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy502] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 0

theorem nb068_fresh_440 (f : Var) :
    (nb068AlphaDummy503 f) ∉
      (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy503] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 1

theorem nb068_fresh_441 (f : Var) :
    (nb068AlphaDummy504 f) ∉
      (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb068AlphaDummy504] using
    freshVar_not_mem (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) 2

theorem nb068_distinct_442 (f : Var) :
    (nb068AlphaDummy502 f) ≠ (nb068AlphaDummy503 f) := by
  simpa only [nb068AlphaDummy502, nb068AlphaDummy503] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb068_distinct_443 (f : Var) :
    (nb068AlphaDummy502 f) ≠ (nb068AlphaDummy504 f) := by
  simpa only [nb068AlphaDummy502, nb068AlphaDummy504] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb068_distinct_444 (f : Var) :
    (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy504 f) := by
  simpa only [nb068AlphaDummy503, nb068AlphaDummy504] using
    (freshVar_injective (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb068_fresh_445 :
    (nb068AlphaDummy511) ∉
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy500))).fv) :=
  by
  simpa only [nb068AlphaDummy511] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy500))).fv)
      0

theorem nb068_fresh_446 :
    (nb068AlphaDummy507) ∉
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) :=
  by
  simpa only [nb068AlphaDummy507] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy500))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv)
      0

theorem nb068_fresh_447 :
    (nb068AlphaDummy513) ∉
      (((Class.cv (nb068AlphaDummy501))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv) :=
  by
  simpa only [nb068AlphaDummy513] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy501))).fv ∪ ((Class.cv (nb068AlphaDummy501))).fv)
      0

theorem nb068_fresh_448 (f : Var) :
    (nb068AlphaDummy512 f) ∉
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy503 f))).fv) :=
  by
  simpa only [nb068AlphaDummy512] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy503 f))).fv)
      0

theorem nb068_fresh_449 (f : Var) :
    (nb068AlphaDummy508 f) ∉
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv) :=
  by
  simpa only [nb068AlphaDummy508] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy503 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv)
      0

theorem nb068_fresh_450 (f : Var) :
    (nb068AlphaDummy514 f) ∉
      (((Class.cv (nb068AlphaDummy504 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv) :=
  by
  simpa only [nb068AlphaDummy514] using
    freshVar_not_mem
      (((Class.cv (nb068AlphaDummy504 f))).fv ∪ ((Class.cv (nb068AlphaDummy504 f))).fv)
      0

theorem nb068_fresh_451 (f : Var) : (nb068AlphaDummy127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068AlphaDummy127] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb068_fresh_452 (f : Var) : (nb068AlphaDummy128 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068AlphaDummy128] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb068_distinct_453 (f : Var) :
    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy128 f) := by
  simpa only [nb068AlphaDummy127, nb068AlphaDummy128] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_454 (f : Var) :
    (nb068AlphaDummy048 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb068AlphaDummy048] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 0

theorem nb068_fresh_455 (f : Var) :
    (nb068AlphaDummy049 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb068AlphaDummy049] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 1

theorem nb068_fresh_456 (f : Var) :
    (nb068AlphaDummy050 f) ∉ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) := by
  simpa only [nb068AlphaDummy050] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) 2

theorem nb068_distinct_457 (f : Var) :
    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy049 f) := by
  simpa only [nb068AlphaDummy048, nb068AlphaDummy049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb068_distinct_458 (f : Var) :
    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy050 f) := by
  simpa only [nb068AlphaDummy048, nb068AlphaDummy050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb068_distinct_459 (f : Var) :
    (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy050 f) := by
  simpa only [nb068AlphaDummy049, nb068AlphaDummy050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb068_fresh_460 (f : Var) :
    (nb068AlphaDummy285 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb068AlphaDummy285] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 0

theorem nb068_fresh_461 (f : Var) :
    (nb068AlphaDummy286 f) ∉ (((Class.cv f)).fv ∪ ((synCvv)).fv) := by
  simpa only [nb068AlphaDummy286] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((synCvv)).fv) 1

theorem nb068_distinct_462 (f : Var) :
    (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy286 f) := by
  simpa only [nb068AlphaDummy285, nb068AlphaDummy286] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_463 (x : Var) (y : Var) :
    (nb068AlphaDummy007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068AlphaDummy007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_464 (x : Var) (y : Var) :
    (nb068AlphaDummy008 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068AlphaDummy008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb068_distinct_465 (x : Var) (y : Var) :
    (nb068AlphaDummy007 x y) ≠ (nb068AlphaDummy008 x y) := by
  simpa only [nb068AlphaDummy007, nb068AlphaDummy008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_466 :
    (nb068AlphaDummy017) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy013))).fv) :=
  by
  simpa only [nb068AlphaDummy017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy013))).fv)
      0

theorem nb068_fresh_467 (x : Var) (y : Var) :
    (nb068AlphaDummy018 x y) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy015 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy015 x y)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy015 x y))).fv) :=
  by
  simpa only [nb068AlphaDummy018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy015 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy015 x y)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy015 x y))).fv)
      0

theorem nb068_fresh_468 :
    (nb068AlphaDummy065) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy061))).fv) :=
  by
  simpa only [nb068AlphaDummy065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy061))).fv)
      0

theorem nb068_fresh_469 (f : Var) :
    (nb068AlphaDummy066 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy063 f))).fv) :=
  by
  simpa only [nb068AlphaDummy066] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy063 f))).fv)
      0

theorem nb068_fresh_470 :
    (nb068AlphaDummy101) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy097)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy097)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy097))).fv) :=
  by
  simpa only [nb068AlphaDummy101] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy097)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy097)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy097))).fv)
      0

theorem nb068_fresh_471 (f : Var) :
    (nb068AlphaDummy102 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy099 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy099 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy099 f))).fv) :=
  by
  simpa only [nb068AlphaDummy102] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy099 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy099 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy099 f))).fv)
      0

theorem nb068_fresh_472 :
    (nb068AlphaDummy143) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy139))).fv) :=
  by
  simpa only [nb068AlphaDummy143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy139))).fv)
      0

theorem nb068_fresh_473 (f : Var) :
    (nb068AlphaDummy144 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy141 f))).fv) :=
  by
  simpa only [nb068AlphaDummy144] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy141 f))).fv)
      0

theorem nb068_fresh_474 :
    (nb068AlphaDummy179) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy175))).fv) :=
  by
  simpa only [nb068AlphaDummy179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy175))).fv)
      0

theorem nb068_fresh_475 (f : Var) :
    (nb068AlphaDummy180 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy177 f))).fv) :=
  by
  simpa only [nb068AlphaDummy180] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy177 f))).fv)
      0

theorem nb068_fresh_476 :
    (nb068AlphaDummy215) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy211))).fv) :=
  by
  simpa only [nb068AlphaDummy215] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy211))).fv)
      0

theorem nb068_fresh_477 (f : Var) :
    (nb068AlphaDummy216 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy213 f))).fv) :=
  by
  simpa only [nb068AlphaDummy216] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy213 f))).fv)
      0

theorem nb068_fresh_478 :
    (nb068AlphaDummy255) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy251)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy251)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy251))).fv) :=
  by
  simpa only [nb068AlphaDummy255] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy251)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy251)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy251))).fv)
      0

theorem nb068_fresh_479 (f : Var) :
    (nb068AlphaDummy256 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy253 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy253 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy253 f))).fv) :=
  by
  simpa only [nb068AlphaDummy256] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy253 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy253 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy253 f))).fv)
      0

theorem nb068_fresh_480 :
    (nb068AlphaDummy299) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy295))).fv) :=
  by
  simpa only [nb068AlphaDummy299] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy295))).fv)
      0

theorem nb068_fresh_481 (f : Var) :
    (nb068AlphaDummy300 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy297 f))).fv) :=
  by
  simpa only [nb068AlphaDummy300] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy297 f))).fv)
      0

theorem nb068_fresh_482 :
    (nb068AlphaDummy347) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy343))).fv) :=
  by
  simpa only [nb068AlphaDummy347] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy343))).fv)
      0

theorem nb068_fresh_483 (f : Var) :
    (nb068AlphaDummy348 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy345 f))).fv) :=
  by
  simpa only [nb068AlphaDummy348] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy345 f))).fv)
      0

theorem nb068_fresh_484 :
    (nb068AlphaDummy383) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy379))).fv) :=
  by
  simpa only [nb068AlphaDummy383] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy379)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy379)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy379))).fv)
      0

theorem nb068_fresh_485 (f : Var) :
    (nb068AlphaDummy384 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy381 f))).fv) :=
  by
  simpa only [nb068AlphaDummy384] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy381 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy381 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy381 f))).fv)
      0

theorem nb068_fresh_486 :
    (nb068AlphaDummy425) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy421)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy421))).fv) :=
  by
  simpa only [nb068AlphaDummy425] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy421)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy421)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy421))).fv)
      0

theorem nb068_fresh_487 (f : Var) :
    (nb068AlphaDummy426 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy423 f))).fv) :=
  by
  simpa only [nb068AlphaDummy426] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy423 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy423 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy423 f))).fv)
      0

theorem nb068_fresh_488 :
    (nb068AlphaDummy461) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy457))).fv) :=
  by
  simpa only [nb068AlphaDummy461] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy457))).fv)
      0

theorem nb068_fresh_489 (f : Var) :
    (nb068AlphaDummy462 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy459 f))).fv) :=
  by
  simpa only [nb068AlphaDummy462] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy459 f))).fv)
      0

theorem nb068_fresh_490 :
    (nb068AlphaDummy497) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy493))).fv) :=
  by
  simpa only [nb068AlphaDummy497] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy493)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy493)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy493))).fv)
      0

theorem nb068_fresh_491 (f : Var) :
    (nb068AlphaDummy498 f) ∉
      (((Wff.classMem (Class.cv (nb068AlphaDummy495 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy495 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy495 f))).fv) :=
  by
  simpa only [nb068AlphaDummy498] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb068AlphaDummy495 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy495 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy495 f))).fv)
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
    (nb068AlphaDummy407) ∉ (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) := by
  simpa only [nb068AlphaDummy407] using
    freshVar_not_mem (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 0

theorem nb068_fresh_493 :
    (nb068AlphaDummy408) ∉ (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) := by
  simpa only [nb068AlphaDummy408] using
    freshVar_not_mem (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) 1

theorem nb068_distinct_494 : (nb068AlphaDummy407) ≠ (nb068AlphaDummy408) := by
  simpa only [nb068AlphaDummy407, nb068AlphaDummy408] using
    (freshVar_injective (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb068_fresh_495 :
    (nb068AlphaDummy327) ∉
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) :=
  by
  simpa only [nb068AlphaDummy327] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      0

theorem nb068_fresh_496 :
    (nb068AlphaDummy328) ∉
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) :=
  by
  simpa only [nb068AlphaDummy328] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      1

theorem nb068_fresh_497 :
    (nb068AlphaDummy329) ∉
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv) :=
  by
  simpa only [nb068AlphaDummy329] using
    freshVar_not_mem
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      2

theorem nb068_distinct_498 : (nb068AlphaDummy327) ≠ (nb068AlphaDummy328) := by
  simpa only [nb068AlphaDummy327, nb068AlphaDummy328] using
    (freshVar_injective (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb068_distinct_499 : (nb068AlphaDummy327) ≠ (nb068AlphaDummy329) := by
  simpa only [nb068AlphaDummy327, nb068AlphaDummy329] using
    (freshVar_injective (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb068_distinct_500 : (nb068AlphaDummy328) ≠ (nb068AlphaDummy329) := by
  simpa only [nb068AlphaDummy328, nb068AlphaDummy329] using
    (freshVar_injective (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb068_fresh_501 :
    (nb068AlphaDummy239) ∉
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb068AlphaDummy239] using
    freshVar_not_mem (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      0

theorem nb068_fresh_502 :
    (nb068AlphaDummy240) ∉
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb068AlphaDummy240] using
    freshVar_not_mem (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv)
      1

theorem nb068_distinct_503 : (nb068AlphaDummy239) ≠ (nb068AlphaDummy240) := by
  simpa only [nb068AlphaDummy239, nb068AlphaDummy240] using
    (freshVar_injective
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb068_fresh_504 (f : Var) :
    (nb068AlphaDummy409 f) ∉ (((synCcnv (Class.cv f))).fv) := by
  simpa only [nb068AlphaDummy409] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv) 0

theorem nb068_fresh_505 (f : Var) :
    (nb068AlphaDummy410 f) ∉ (((synCcnv (Class.cv f))).fv) := by
  simpa only [nb068AlphaDummy410] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv) 1

theorem nb068_distinct_506 (f : Var) :
    (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy410 f) := by
  simpa only [nb068AlphaDummy409, nb068AlphaDummy410] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_507 (f : Var) :
    (nb068AlphaDummy330 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068AlphaDummy330] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 0

theorem nb068_fresh_508 (f : Var) :
    (nb068AlphaDummy331 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068AlphaDummy331] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 1

theorem nb068_fresh_509 (f : Var) :
    (nb068AlphaDummy332 f) ∉
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) :=
  by
  simpa only [nb068AlphaDummy332] using
    freshVar_not_mem
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) 2

theorem nb068_distinct_510 (f : Var) :
    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy331 f) := by
  simpa only [nb068AlphaDummy330, nb068AlphaDummy331] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb068_distinct_511 (f : Var) :
    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy332 f) := by
  simpa only [nb068AlphaDummy330, nb068AlphaDummy332] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 0)
      (j := 2) (by decide))

theorem nb068_distinct_512 (f : Var) :
    (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy332 f) := by
  simpa only [nb068AlphaDummy331, nb068AlphaDummy332] using
    (freshVar_injective
      (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (i := 1)
      (j := 2) (by decide))

theorem nb068_fresh_513 (f : Var) :
    (nb068AlphaDummy241 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb068AlphaDummy241] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 0

theorem nb068_fresh_514 (f : Var) :
    (nb068AlphaDummy242 f) ∉ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) := by
  simpa only [nb068AlphaDummy242] using
    freshVar_not_mem (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) 1

theorem nb068_distinct_515 (f : Var) :
    (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy242 f) := by
  simpa only [nb068AlphaDummy241, nb068AlphaDummy242] using
    (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb068_fresh_516 :
    (nb068AlphaDummy043) ∉
      (((synCcom (Class.cv (nb068AlphaDummy000))
            (synCcnv (Class.cv (nb068AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb068AlphaDummy043] using
    freshVar_not_mem
      (((synCcom (Class.cv (nb068AlphaDummy000))
            (synCcnv (Class.cv (nb068AlphaDummy000))))).fv ∪ ((synCid)).fv)
      0

theorem nb068_fresh_517 (f : Var) :
    (nb068AlphaDummy044 f) ∉
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb068AlphaDummy044] using
    freshVar_not_mem
      (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) 0

theorem nb068_fresh_518 :
    (nb068AlphaDummy325) ∉
      (((synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
            (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000)))))).fv ∪ ((synCid)).fv) :=
  by
  simpa only [nb068AlphaDummy325] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
            (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000)))))).fv ∪ ((synCid)).fv)
      0

theorem nb068_fresh_519 (f : Var) :
    (nb068AlphaDummy326 f) ∉
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv) :=
  by
  simpa only [nb068AlphaDummy326] using
    freshVar_not_mem
      (((synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))).fv ∪
        ((synCid)).fv)
      0

theorem nb068_fresh_520 :
    (nb068AlphaDummy009) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCphi (Class.cv (nb068AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy009] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCphi (Class.cv (nb068AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_521 (x : Var) (y : Var) :
    (nb068AlphaDummy010 x y) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCphi (Class.cv (nb068AlphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy010] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCphi (Class.cv (nb068AlphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_522 :
    (nb068AlphaDummy057) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCphi (Class.cv (nb068AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy057] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCphi (Class.cv (nb068AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_523 (f : Var) :
    (nb068AlphaDummy058 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCphi (Class.cv (nb068AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy058] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCphi (Class.cv (nb068AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_524 :
    (nb068AlphaDummy093) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCphi (Class.cv (nb068AlphaDummy090)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy093] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCphi (Class.cv (nb068AlphaDummy090)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_525 (f : Var) :
    (nb068AlphaDummy094 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCphi (Class.cv (nb068AlphaDummy092 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy094] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCphi (Class.cv (nb068AlphaDummy092 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_526 :
    (nb068AlphaDummy135) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCphi (Class.cv (nb068AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy135] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCphi (Class.cv (nb068AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_527 (f : Var) :
    (nb068AlphaDummy136 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCphi (Class.cv (nb068AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy136] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCphi (Class.cv (nb068AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_528 :
    (nb068AlphaDummy171) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCphi (Class.cv (nb068AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy171] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCphi (Class.cv (nb068AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_529 (f : Var) :
    (nb068AlphaDummy172 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCphi (Class.cv (nb068AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy172] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCphi (Class.cv (nb068AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_530 :
    (nb068AlphaDummy207) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCphi (Class.cv (nb068AlphaDummy204)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy207] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCphi (Class.cv (nb068AlphaDummy204)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_531 (f : Var) :
    (nb068AlphaDummy208 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCphi (Class.cv (nb068AlphaDummy206 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy208] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCphi (Class.cv (nb068AlphaDummy206 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_532 :
    (nb068AlphaDummy247) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCphi (Class.cv (nb068AlphaDummy244)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy247] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCphi (Class.cv (nb068AlphaDummy244)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_533 (f : Var) :
    (nb068AlphaDummy248 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCphi (Class.cv (nb068AlphaDummy246 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy248] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCphi (Class.cv (nb068AlphaDummy246 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_534 :
    (nb068AlphaDummy291) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCphi (Class.cv (nb068AlphaDummy288)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy291] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCphi (Class.cv (nb068AlphaDummy288)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_535 (f : Var) :
    (nb068AlphaDummy292 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCphi (Class.cv (nb068AlphaDummy290 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy292] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCphi (Class.cv (nb068AlphaDummy290 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_536 :
    (nb068AlphaDummy339) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCphi (Class.cv (nb068AlphaDummy336)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy339] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCphi (Class.cv (nb068AlphaDummy336)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_537 (f : Var) :
    (nb068AlphaDummy340 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCphi (Class.cv (nb068AlphaDummy338 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy340] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCphi (Class.cv (nb068AlphaDummy338 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_538 :
    (nb068AlphaDummy375) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCphi (Class.cv (nb068AlphaDummy372)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy375] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCphi (Class.cv (nb068AlphaDummy372)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy371)
              (synWrex (nb068AlphaDummy372) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy371))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy372)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_539 (f : Var) :
    (nb068AlphaDummy376 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCphi (Class.cv (nb068AlphaDummy374 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy376] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCphi (Class.cv (nb068AlphaDummy374 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy373 f)
              (synWrex (nb068AlphaDummy374 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy373 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy374 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_540 :
    (nb068AlphaDummy417) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCphi (Class.cv (nb068AlphaDummy414)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy417] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCphi (Class.cv (nb068AlphaDummy414)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy413)
              (synWrex (nb068AlphaDummy414) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy413))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy414)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_541 (f : Var) :
    (nb068AlphaDummy418 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCphi (Class.cv (nb068AlphaDummy416 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy418] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCphi (Class.cv (nb068AlphaDummy416 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy415 f)
              (synWrex (nb068AlphaDummy416 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy415 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy416 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_542 :
    (nb068AlphaDummy453) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCphi (Class.cv (nb068AlphaDummy450)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy453] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy408))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCphi (Class.cv (nb068AlphaDummy450)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_543 (f : Var) :
    (nb068AlphaDummy454 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCphi (Class.cv (nb068AlphaDummy452 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy454] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy410 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCphi (Class.cv (nb068AlphaDummy452 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_544 :
    (nb068AlphaDummy489) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCphi (Class.cv (nb068AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy489] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy329))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCphi (Class.cv (nb068AlphaDummy486)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_545 (f : Var) :
    (nb068AlphaDummy490 f) ∉
      (((synCcompl (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCphi (Class.cv (nb068AlphaDummy488 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb068AlphaDummy490] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy332 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCphi (Class.cv (nb068AlphaDummy488 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                    (synCsn (synC0c)))))))).fv)
      0

theorem nb068_fresh_546 :
    (nb068AlphaDummy029) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  simpa only [nb068AlphaDummy029] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy021)))).fv)
      0

theorem nb068_fresh_547 (x : Var) (y : Var) :
    (nb068AlphaDummy030 x y) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  simpa only [nb068AlphaDummy030] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy024 x y)))).fv)
      0

theorem nb068_fresh_548 :
    (nb068AlphaDummy077) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  simpa only [nb068AlphaDummy077] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy069)))).fv)
      0

theorem nb068_fresh_549 (f : Var) :
    (nb068AlphaDummy078 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy078] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy072 f)))).fv)
      0

theorem nb068_fresh_550 :
    (nb068AlphaDummy113) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy104)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  simpa only [nb068AlphaDummy113] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy104)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy105)))).fv)
      0

theorem nb068_fresh_551 (f : Var) :
    (nb068AlphaDummy114 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy107 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy114] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy107 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy108 f)))).fv)
      0

theorem nb068_fresh_552 :
    (nb068AlphaDummy155) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  simpa only [nb068AlphaDummy155] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy147)))).fv)
      0

theorem nb068_fresh_553 (f : Var) :
    (nb068AlphaDummy156 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy156] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy150 f)))).fv)
      0

theorem nb068_fresh_554 :
    (nb068AlphaDummy191) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  simpa only [nb068AlphaDummy191] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy183)))).fv)
      0

theorem nb068_fresh_555 (f : Var) :
    (nb068AlphaDummy192 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy192] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy186 f)))).fv)
      0

theorem nb068_fresh_556 :
    (nb068AlphaDummy227) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy218)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  simpa only [nb068AlphaDummy227] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy218)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy219)))).fv)
      0

theorem nb068_fresh_557 (f : Var) :
    (nb068AlphaDummy228 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy221 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy228] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy221 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy222 f)))).fv)
      0

theorem nb068_fresh_558 :
    (nb068AlphaDummy267) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy258)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  simpa only [nb068AlphaDummy267] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy258)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy259)))).fv)
      0

theorem nb068_fresh_559 (f : Var) :
    (nb068AlphaDummy268 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy261 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy268] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy261 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy262 f)))).fv)
      0

theorem nb068_fresh_560 :
    (nb068AlphaDummy311) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy302)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  simpa only [nb068AlphaDummy311] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy302)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy303)))).fv)
      0

theorem nb068_fresh_561 (f : Var) :
    (nb068AlphaDummy312 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy305 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy312] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy305 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy306 f)))).fv)
      0

theorem nb068_fresh_562 :
    (nb068AlphaDummy359) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy350)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  simpa only [nb068AlphaDummy359] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy350)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy351)))).fv)
      0

theorem nb068_fresh_563 (f : Var) :
    (nb068AlphaDummy360 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy353 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy360] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy353 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy354 f)))).fv)
      0

theorem nb068_fresh_564 :
    (nb068AlphaDummy395) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy386)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  simpa only [nb068AlphaDummy395] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy386)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy387)))).fv)
      0

theorem nb068_fresh_565 (f : Var) :
    (nb068AlphaDummy396 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy389 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy396] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy389 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy390 f)))).fv)
      0

theorem nb068_fresh_566 :
    (nb068AlphaDummy437) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy428)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  simpa only [nb068AlphaDummy437] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy428)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy429)))).fv)
      0

theorem nb068_fresh_567 (f : Var) :
    (nb068AlphaDummy438 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy431 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy438] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy431 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy432 f)))).fv)
      0

theorem nb068_fresh_568 :
    (nb068AlphaDummy473) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy464)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  simpa only [nb068AlphaDummy473] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy464)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy465)))).fv)
      0

theorem nb068_fresh_569 (f : Var) :
    (nb068AlphaDummy474 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy467 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy474] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy467 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy468 f)))).fv)
      0

theorem nb068_fresh_570 :
    (nb068AlphaDummy509) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  simpa only [nb068AlphaDummy509] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy500)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy501)))).fv)
      0

theorem nb068_fresh_571 (f : Var) :
    (nb068AlphaDummy510 f) ∉
      (((synCcompl (Class.cv (nb068AlphaDummy503 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy510] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb068AlphaDummy503 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy504 f)))).fv)
      0

theorem nb068_fresh_572 :
    (nb068AlphaDummy037) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_573 (x : Var) (y : Var) :
    (nb068AlphaDummy038 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy008 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy008 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_574 :
    (nb068AlphaDummy085) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy085] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_575 (f : Var) :
    (nb068AlphaDummy086 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy086] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_576 :
    (nb068AlphaDummy121) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy090))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy121] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy090))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_577 (f : Var) :
    (nb068AlphaDummy122 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy092 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy122] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy092 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_578 :
    (nb068AlphaDummy163) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy163] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_579 (f : Var) :
    (nb068AlphaDummy164 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy164] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_580 :
    (nb068AlphaDummy199) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy199] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_581 (f : Var) :
    (nb068AlphaDummy200 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy200] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_582 :
    (nb068AlphaDummy235) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy204))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy235] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy204))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_583 (f : Var) :
    (nb068AlphaDummy236 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy206 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy236] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy206 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_584 :
    (nb068AlphaDummy275) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy244))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy275] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy244))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_585 (f : Var) :
    (nb068AlphaDummy276 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy246 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy276] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy246 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_586 :
    (nb068AlphaDummy319) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy288))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy319] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy288))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_587 (f : Var) :
    (nb068AlphaDummy320 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy290 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy320] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy290 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_588 :
    (nb068AlphaDummy367) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy336))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy367] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy336))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_589 (f : Var) :
    (nb068AlphaDummy368 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy338 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy368] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy338 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_590 :
    (nb068AlphaDummy403) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy372))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy403] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy372))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_591 (f : Var) :
    (nb068AlphaDummy404 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy374 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy404] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy374 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_592 :
    (nb068AlphaDummy445) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy414))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy445] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy414))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_593 (f : Var) :
    (nb068AlphaDummy446 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy416 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy446] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy416 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_594 :
    (nb068AlphaDummy481) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy450))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy481] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy450))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_595 (f : Var) :
    (nb068AlphaDummy482 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy452 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy482] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy452 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_596 :
    (nb068AlphaDummy517) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy517] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy486))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_597 (f : Var) :
    (nb068AlphaDummy518 f) ∉
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy488 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb068AlphaDummy518] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy488 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb068_fresh_598 :
    (nb068AlphaDummy025) ∉
      (((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy020))
            (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  simpa only [nb068AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv)
      0

theorem nb068_fresh_599 (x : Var) (y : Var) :
    (nb068AlphaDummy026 x y) ∉
      (((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  simpa only [nb068AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv)
      0

theorem nb068_fresh_600 :
    (nb068AlphaDummy073) ∉
      (((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy068))
            (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  simpa only [nb068AlphaDummy073] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv)
      0

theorem nb068_fresh_601 (f : Var) :
    (nb068AlphaDummy074 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy074] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv)
      0

theorem nb068_fresh_602 :
    (nb068AlphaDummy109) ∉
      (((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy104))
            (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  simpa only [nb068AlphaDummy109] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv)
      0

theorem nb068_fresh_603 (f : Var) :
    (nb068AlphaDummy110 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy110] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv)
      0

theorem nb068_fresh_604 :
    (nb068AlphaDummy151) ∉
      (((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy146))
            (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  simpa only [nb068AlphaDummy151] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv)
      0

theorem nb068_fresh_605 (f : Var) :
    (nb068AlphaDummy152 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy152] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv)
      0

theorem nb068_fresh_606 :
    (nb068AlphaDummy187) ∉
      (((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy182))
            (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  simpa only [nb068AlphaDummy187] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv)
      0

theorem nb068_fresh_607 (f : Var) :
    (nb068AlphaDummy188 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy188] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv)
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
    (nb068AlphaDummy223) ∉
      (((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy218))
            (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  simpa only [nb068AlphaDummy223] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv)
      0

theorem nb068_fresh_609 (f : Var) :
    (nb068AlphaDummy224 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy224] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv)
      0

theorem nb068_fresh_610 :
    (nb068AlphaDummy263) ∉
      (((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy258))
            (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  simpa only [nb068AlphaDummy263] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv)
      0

theorem nb068_fresh_611 (f : Var) :
    (nb068AlphaDummy264 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy264] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv)
      0

theorem nb068_fresh_612 :
    (nb068AlphaDummy307) ∉
      (((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy302))
            (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  simpa only [nb068AlphaDummy307] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv)
      0

theorem nb068_fresh_613 (f : Var) :
    (nb068AlphaDummy308 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy308] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv)
      0

theorem nb068_fresh_614 :
    (nb068AlphaDummy355) ∉
      (((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy350))
            (Class.cv (nb068AlphaDummy351)))).fv) :=
  by
  simpa only [nb068AlphaDummy355] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy350)) (Class.cv (nb068AlphaDummy351)))).fv)
      0

theorem nb068_fresh_615 (f : Var) :
    (nb068AlphaDummy356 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy356] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy353 f))
            (Class.cv (nb068AlphaDummy354 f)))).fv)
      0

theorem nb068_fresh_616 :
    (nb068AlphaDummy391) ∉
      (((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy386))
            (Class.cv (nb068AlphaDummy387)))).fv) :=
  by
  simpa only [nb068AlphaDummy391] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy386)) (Class.cv (nb068AlphaDummy387)))).fv)
      0

theorem nb068_fresh_617 (f : Var) :
    (nb068AlphaDummy392 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy392] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy389 f))
            (Class.cv (nb068AlphaDummy390 f)))).fv)
      0

theorem nb068_fresh_618 :
    (nb068AlphaDummy433) ∉
      (((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy428))
            (Class.cv (nb068AlphaDummy429)))).fv) :=
  by
  simpa only [nb068AlphaDummy433] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy428)) (Class.cv (nb068AlphaDummy429)))).fv)
      0

theorem nb068_fresh_619 (f : Var) :
    (nb068AlphaDummy434 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy434] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy431 f))
            (Class.cv (nb068AlphaDummy432 f)))).fv)
      0

theorem nb068_fresh_620 :
    (nb068AlphaDummy469) ∉
      (((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy464))
            (Class.cv (nb068AlphaDummy465)))).fv) :=
  by
  simpa only [nb068AlphaDummy469] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))).fv)
      0

theorem nb068_fresh_621 (f : Var) :
    (nb068AlphaDummy470 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy470] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f)))).fv)
      0

theorem nb068_fresh_622 :
    (nb068AlphaDummy505) ∉
      (((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy500))
            (Class.cv (nb068AlphaDummy501)))).fv) :=
  by
  simpa only [nb068AlphaDummy505] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))).fv)
      0

theorem nb068_fresh_623 (f : Var) :
    (nb068AlphaDummy506 f) ∉
      (((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy506] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f)))).fv)
      0

theorem nb068_fresh_624 :
    (nb068AlphaDummy041) ∉
      (((synCnin (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv) :=
  by
  simpa only [nb068AlphaDummy041] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv)
      0

theorem nb068_fresh_625 (f : Var) :
    (nb068AlphaDummy042 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb068AlphaDummy042] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb068_fresh_626 :
    (nb068AlphaDummy323) ∉
      (((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv) :=
  by
  simpa only [nb068AlphaDummy323] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb068AlphaDummy000)))
              (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))) (synCid))).fv)
      0

theorem nb068_fresh_627 (f : Var) :
    (nb068AlphaDummy324 f) ∉
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv) :=
  by
  simpa only [nb068AlphaDummy324] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv f)) (synCcnv (synCcnv (Class.cv f))))
            (synCid))).fv)
      0

theorem nb068_fresh_628 :
    (nb068AlphaDummy279) ∉
      (((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv) :=
  by
  simpa only [nb068AlphaDummy279] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv)
      0

theorem nb068_fresh_629 (y : Var) (f : Var) :
    (nb068AlphaDummy280 y f) ∉
      (((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv) :=
  by
  simpa only [nb068AlphaDummy280] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv)
      0

theorem nb068_fresh_630 :
    (nb068AlphaDummy039) ∉
      (((synCphi (Class.cv (nb068AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy006)))).fv) :=
  by
  simpa only [nb068AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy006)))).fv)
      0

theorem nb068_fresh_631 (x : Var) (y : Var) :
    (nb068AlphaDummy040 x y) ∉
      (((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv) :=
  by
  simpa only [nb068AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv)
      0

theorem nb068_fresh_632 :
    (nb068AlphaDummy087) ∉
      (((synCphi (Class.cv (nb068AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy054)))).fv) :=
  by
  simpa only [nb068AlphaDummy087] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy054)))).fv)
      0

theorem nb068_fresh_633 (f : Var) :
    (nb068AlphaDummy088 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy088] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv)
      0

theorem nb068_fresh_634 :
    (nb068AlphaDummy123) ∉
      (((synCphi (Class.cv (nb068AlphaDummy090)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy090)))).fv) :=
  by
  simpa only [nb068AlphaDummy123] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy090)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy090)))).fv)
      0

theorem nb068_fresh_635 (f : Var) :
    (nb068AlphaDummy124 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy124] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv)
      0

theorem nb068_fresh_636 :
    (nb068AlphaDummy165) ∉
      (((synCphi (Class.cv (nb068AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy132)))).fv) :=
  by
  simpa only [nb068AlphaDummy165] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy132)))).fv)
      0

theorem nb068_fresh_637 (f : Var) :
    (nb068AlphaDummy166 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy166] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv)
      0

theorem nb068_fresh_638 :
    (nb068AlphaDummy201) ∉
      (((synCphi (Class.cv (nb068AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy168)))).fv) :=
  by
  simpa only [nb068AlphaDummy201] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy168)))).fv)
      0

theorem nb068_fresh_639 (f : Var) :
    (nb068AlphaDummy202 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy202] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv)
      0

theorem nb068_fresh_640 :
    (nb068AlphaDummy237) ∉
      (((synCphi (Class.cv (nb068AlphaDummy204)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy204)))).fv) :=
  by
  simpa only [nb068AlphaDummy237] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy204)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy204)))).fv)
      0

theorem nb068_fresh_641 (f : Var) :
    (nb068AlphaDummy238 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy238] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv)
      0

theorem nb068_fresh_642 :
    (nb068AlphaDummy277) ∉
      (((synCphi (Class.cv (nb068AlphaDummy244)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy244)))).fv) :=
  by
  simpa only [nb068AlphaDummy277] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy244)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy244)))).fv)
      0

theorem nb068_fresh_643 (f : Var) :
    (nb068AlphaDummy278 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy278] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv)
      0

theorem nb068_fresh_644 :
    (nb068AlphaDummy321) ∉
      (((synCphi (Class.cv (nb068AlphaDummy288)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy288)))).fv) :=
  by
  simpa only [nb068AlphaDummy321] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy288)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy288)))).fv)
      0

theorem nb068_fresh_645 (f : Var) :
    (nb068AlphaDummy322 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy322] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv)
      0

theorem nb068_fresh_646 :
    (nb068AlphaDummy369) ∉
      (((synCphi (Class.cv (nb068AlphaDummy336)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy336)))).fv) :=
  by
  simpa only [nb068AlphaDummy369] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy336)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy336)))).fv)
      0

theorem nb068_fresh_647 (f : Var) :
    (nb068AlphaDummy370 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy370] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy338 f)))).fv)
      0

theorem nb068_fresh_648 :
    (nb068AlphaDummy405) ∉
      (((synCphi (Class.cv (nb068AlphaDummy372)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy372)))).fv) :=
  by
  simpa only [nb068AlphaDummy405] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy372)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy372)))).fv)
      0

theorem nb068_fresh_649 (f : Var) :
    (nb068AlphaDummy406 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy406] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy374 f)))).fv)
      0

theorem nb068_fresh_650 :
    (nb068AlphaDummy447) ∉
      (((synCphi (Class.cv (nb068AlphaDummy414)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy414)))).fv) :=
  by
  simpa only [nb068AlphaDummy447] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy414)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy414)))).fv)
      0

theorem nb068_fresh_651 (f : Var) :
    (nb068AlphaDummy448 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy448] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy416 f)))).fv)
      0

theorem nb068_fresh_652 :
    (nb068AlphaDummy483) ∉
      (((synCphi (Class.cv (nb068AlphaDummy450)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy450)))).fv) :=
  by
  simpa only [nb068AlphaDummy483] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy450)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy450)))).fv)
      0

theorem nb068_fresh_653 (f : Var) :
    (nb068AlphaDummy484 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy484] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy452 f)))).fv)
      0

theorem nb068_fresh_654 :
    (nb068AlphaDummy519) ∉
      (((synCphi (Class.cv (nb068AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy486)))).fv) :=
  by
  simpa only [nb068AlphaDummy519] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy486)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy486)))).fv)
      0

theorem nb068_fresh_655 (f : Var) :
    (nb068AlphaDummy520 f) ∉
      (((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy520] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy488 f)))).fv)
      0

theorem nb068_fresh_656 :
    (nb068AlphaDummy281) ∉
      (((synCrn (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  simpa only [nb068AlphaDummy281] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((Class.cv (nb068AlphaDummy002))).fv)
      0

theorem nb068_fresh_657 (y : Var) (f : Var) :
    (nb068AlphaDummy282 y f) ∉ (((synCrn (Class.cv f))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068AlphaDummy282] using
    freshVar_not_mem (((synCrn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_658 :
    (nb068AlphaDummy003) ∉
      (({(nb068AlphaDummy001)} : Finset Var) ∪ ({(nb068AlphaDummy002)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy000) (synWf1o (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy001)) (Class.cv (nb068AlphaDummy002))))).fv) :=
  by
  simpa only [nb068AlphaDummy003] using
    freshVar_not_mem
      (({(nb068AlphaDummy001)} : Finset Var) ∪ ({(nb068AlphaDummy002)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy000) (synWf1o (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy001)) (Class.cv (nb068AlphaDummy002))))).fv)
      0

theorem nb068_fresh_659 :
    (nb068AlphaDummy051) ∉
      (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy047))) (synWbr (Class.cv (nb068AlphaDummy047))
                (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy046)))))).fv) :=
  by
  simpa only [nb068AlphaDummy051] using
    freshVar_not_mem
      (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy047))) (synWbr (Class.cv (nb068AlphaDummy047))
                (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy046)))))).fv)
      0

theorem nb068_fresh_660 (f : Var) :
    (nb068AlphaDummy052 f) ∉
      (({(nb068AlphaDummy048 f)} : Finset Var) ∪ ({(nb068AlphaDummy049 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy050 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy050 f)))
              (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
                (Class.cv (nb068AlphaDummy049 f)))))).fv) :=
  by
  simpa only [nb068AlphaDummy052] using
    freshVar_not_mem
      (({(nb068AlphaDummy048 f)} : Finset Var) ∪ ({(nb068AlphaDummy049 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy050 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy050 f)))
              (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
                (Class.cv (nb068AlphaDummy049 f)))))).fv)
      0

theorem nb068_fresh_661 :
    (nb068AlphaDummy129) ∉
      (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))).fv) :=
  by
  simpa only [nb068AlphaDummy129] using
    freshVar_not_mem
      (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))).fv)
      0

theorem nb068_fresh_662 (f : Var) :
    (nb068AlphaDummy130 f) ∉
      (({(nb068AlphaDummy127 f)} : Finset Var) ∪ ({(nb068AlphaDummy128 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy130] using
    freshVar_not_mem
      (({(nb068AlphaDummy127 f)} : Finset Var) ∪ ({(nb068AlphaDummy128 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f)))).fv)
      0

theorem nb068_fresh_663 :
    (nb068AlphaDummy333) ∉
      (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
                (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
                (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy328)))))).fv) :=
  by
  simpa only [nb068AlphaDummy333] using
    freshVar_not_mem
      (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
                (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
                (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy328)))))).fv)
      0

theorem nb068_fresh_664 (f : Var) :
    (nb068AlphaDummy334 f) ∉
      (({(nb068AlphaDummy330 f)} : Finset Var) ∪ ({(nb068AlphaDummy331 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy332 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy330 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
              (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy331 f)))))).fv) :=
  by
  simpa only [nb068AlphaDummy334] using
    freshVar_not_mem
      (({(nb068AlphaDummy330 f)} : Finset Var) ∪ ({(nb068AlphaDummy331 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy332 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy330 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
              (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy331 f)))))).fv)
      0

theorem nb068_fresh_665 :
    (nb068AlphaDummy411) ∉
      (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy407)))).fv) :=
  by
  simpa only [nb068AlphaDummy411] using
    freshVar_not_mem
      (({(nb068AlphaDummy407)} : Finset Var) ∪ ({(nb068AlphaDummy408)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy407)))).fv)
      0

theorem nb068_fresh_666 (f : Var) :
    (nb068AlphaDummy412 f) ∉
      (({(nb068AlphaDummy409 f)} : Finset Var) ∪ ({(nb068AlphaDummy410 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f)))).fv) :=
  by
  simpa only [nb068AlphaDummy412] using
    freshVar_not_mem
      (({(nb068AlphaDummy409 f)} : Finset Var) ∪ ({(nb068AlphaDummy410 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f)))).fv)
      0

theorem nb068_fresh_667 (x : Var) (y : Var) (f : Var) :
    (nb068AlphaDummy004 x y f) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWex f (synWf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  simpa only [nb068AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWex f (synWf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv)
      0

theorem nb068_fresh_668 : (nb068AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb068_fresh_669 : (nb068AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb068_fresh_670 : (nb068AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb068_distinct_671 : (nb068AlphaDummy000) ≠ (nb068AlphaDummy001) := by
  simpa only [nb068AlphaDummy000, nb068AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_672 : (nb068AlphaDummy000) ≠ (nb068AlphaDummy002) := by
  simpa only [nb068AlphaDummy000, nb068AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_673 : (nb068AlphaDummy001) ≠ (nb068AlphaDummy002) := by
  simpa only [nb068AlphaDummy001, nb068AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb068_support_mem_0000 :
    (nb068AlphaDummy001) ∈
      (({(nb068AlphaDummy001)} : Finset Var) ∪ ({(nb068AlphaDummy002)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy000) (synWf1o (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy001)) (Class.cv (nb068AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0001 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWex f (synWf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0002 :
    (nb068AlphaDummy002) ∈
      (({(nb068AlphaDummy001)} : Finset Var) ∪ ({(nb068AlphaDummy002)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy000) (synWf1o (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy001)) (Class.cv (nb068AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0003 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
        ((synWex f (synWf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0004 :
    (nb068AlphaDummy001) ∈
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0005 :
    (nb068AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCphi (Class.cv (nb068AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy005) from (by
          unfold nb068AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy006) from (by
            unfold nb068AlphaDummy006;
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
      (((synCcompl (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCphi (Class.cv (nb068AlphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb068AlphaDummy007 x y) from (by
          unfold nb068AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb068AlphaDummy008 x y) from (by
            unfold nb068AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0008 :
    (nb068AlphaDummy001) ∈
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv ∪
        ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCphi (Class.cv (nb068AlphaDummy006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy005) from (by
          unfold nb068AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy006) from (by
            unfold nb068AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0009 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv ∪
        ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCphi (Class.cv (nb068AlphaDummy008 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb068AlphaDummy007 x y) from (by
          unfold nb068AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb068AlphaDummy008 x y) from (by
            unfold nb068AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0010 :
    (nb068AlphaDummy006) ∈ (((Class.cv (nb068AlphaDummy006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0011 (x : Var) (y : Var) :
    (nb068AlphaDummy008 x y) ∈ (((Class.cv (nb068AlphaDummy008 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0012 :
    (nb068AlphaDummy013) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy013)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy013)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy013))).fv) :=
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
    (nb068AlphaDummy015 x y) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy015 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy015 x y)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy015 x y))).fv) :=
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
    (nb068AlphaDummy013) ∈
      (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0015 (x : Var) (y : Var) :
    (nb068AlphaDummy015 x y) ∈
      (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0016 :
    (nb068AlphaDummy020) ∈
      (((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy020))
            (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0017 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ∈
      (((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0018 :
    (nb068AlphaDummy020) ∈
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0019 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ∈
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0020 :
    (nb068AlphaDummy021) ∈
      (((synCnin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy020))
            (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0021 (x : Var) (y : Var) :
    (nb068AlphaDummy024 x y) ∈
      (((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0022 :
    (nb068AlphaDummy021) ∈
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0023 (x : Var) (y : Var) :
    (nb068AlphaDummy024 x y) ∈
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0024 :
    (nb068AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0025 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0026 :
    (nb068AlphaDummy020) ∈
      (((Class.cv (nb068AlphaDummy020))).fv ∪ ((Class.cv (nb068AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0027 (x : Var) (y : Var) :
    (nb068AlphaDummy023 x y) ∈
      (((Class.cv (nb068AlphaDummy023 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy023 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0028 :
    (nb068AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0029 (x : Var) (y : Var) :
    (nb068AlphaDummy024 x y) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy023 x y)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy024 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0030 :
    (nb068AlphaDummy021) ∈
      (((Class.cv (nb068AlphaDummy021))).fv ∪ ((Class.cv (nb068AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0031 (x : Var) (y : Var) :
    (nb068AlphaDummy024 x y) ∈
      (((Class.cv (nb068AlphaDummy024 x y))).fv ∪
        ((Class.cv (nb068AlphaDummy024 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0032 :
    (nb068AlphaDummy002) ∈
      (((Class.cv (nb068AlphaDummy001))).fv ∪ ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0033 :
    (nb068AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy001))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCphi (Class.cv (nb068AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy005)
              (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
                (Wff.classEq (Class.cv (nb068AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy005) from (by
          unfold nb068AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy006) from (by
            unfold nb068AlphaDummy006;
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
      (((synCcompl (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCphi (Class.cv (nb068AlphaDummy008 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy007 x y)
              (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb068AlphaDummy007 x y) from (by
          unfold nb068AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb068AlphaDummy008 x y) from (by
            unfold nb068AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0036 :
    (nb068AlphaDummy002) ∈
      (((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy005)
            (synWrex (nb068AlphaDummy006) (Class.cv (nb068AlphaDummy002))
              (Wff.classEq (Class.cv (nb068AlphaDummy005))
                (synCun (synCphi (Class.cv (nb068AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy005) from (by
          unfold nb068AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy006) from (by
            unfold nb068AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0037 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy007 x y)
            (synWrex (nb068AlphaDummy008 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
                (synCun (synCphi (Class.cv (nb068AlphaDummy008 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb068AlphaDummy007 x y) from (by
          unfold nb068AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb068AlphaDummy008 x y) from (by
            unfold nb068AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0038 :
    (nb068AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0039 (x : Var) (y : Var) :
    (nb068AlphaDummy008 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy008 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0040 :
    (nb068AlphaDummy006) ∈
      (((synCphi (Class.cv (nb068AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0041 (x : Var) (y : Var) :
    (nb068AlphaDummy008 x y) ∈
      (((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy008 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0042 :
    (nb068AlphaDummy045) ∈
      (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy047))) (synWbr (Class.cv (nb068AlphaDummy047))
                (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0043 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (({(nb068AlphaDummy048 f)} : Finset Var) ∪ ({(nb068AlphaDummy049 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy050 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy050 f)))
              (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
                (Class.cv (nb068AlphaDummy049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0044 :
    (nb068AlphaDummy046) ∈
      (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy047))) (synWbr (Class.cv (nb068AlphaDummy047))
                (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0045 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (({(nb068AlphaDummy048 f)} : Finset Var) ∪ ({(nb068AlphaDummy049 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy050 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy050 f)))
              (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
                (Class.cv (nb068AlphaDummy049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0046 :
    (nb068AlphaDummy045) ∈
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0047 :
    (nb068AlphaDummy045) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCphi (Class.cv (nb068AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
            unfold nb068AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0048 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0049 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCphi (Class.cv (nb068AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
            unfold nb068AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0050 :
    (nb068AlphaDummy045) ∈
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv ∪
        ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCphi (Class.cv (nb068AlphaDummy054))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
            unfold nb068AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0051 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCphi (Class.cv (nb068AlphaDummy056 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
            unfold nb068AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0052 :
    (nb068AlphaDummy054) ∈ (((Class.cv (nb068AlphaDummy054))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0053 (f : Var) :
    (nb068AlphaDummy056 f) ∈ (((Class.cv (nb068AlphaDummy056 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0054 :
    (nb068AlphaDummy061) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy061)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy061)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy061))).fv) :=
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
    (nb068AlphaDummy063 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy063 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy063 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy063 f))).fv) :=
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
    (nb068AlphaDummy061) ∈
      (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0057 (f : Var) :
    (nb068AlphaDummy063 f) ∈
      (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0058 :
    (nb068AlphaDummy068) ∈
      (((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy068))
            (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0059 (f : Var) :
    (nb068AlphaDummy071 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0060 :
    (nb068AlphaDummy068) ∈
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0061 (f : Var) :
    (nb068AlphaDummy071 f) ∈
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0062 :
    (nb068AlphaDummy069) ∈
      (((synCnin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy068))
            (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0063 (f : Var) :
    (nb068AlphaDummy072 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0064 :
    (nb068AlphaDummy069) ∈
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0065 (f : Var) :
    (nb068AlphaDummy072 f) ∈
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0066 :
    (nb068AlphaDummy068) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0067 (f : Var) :
    (nb068AlphaDummy071 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0068 :
    (nb068AlphaDummy068) ∈
      (((Class.cv (nb068AlphaDummy068))).fv ∪ ((Class.cv (nb068AlphaDummy068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0069 (f : Var) :
    (nb068AlphaDummy071 f) ∈
      (((Class.cv (nb068AlphaDummy071 f))).fv ∪ ((Class.cv (nb068AlphaDummy071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0070 :
    (nb068AlphaDummy069) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy068)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0071 (f : Var) :
    (nb068AlphaDummy072 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy071 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0072 :
    (nb068AlphaDummy069) ∈
      (((Class.cv (nb068AlphaDummy069))).fv ∪ ((Class.cv (nb068AlphaDummy069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0073 (f : Var) :
    (nb068AlphaDummy072 f) ∈
      (((Class.cv (nb068AlphaDummy072 f))).fv ∪ ((Class.cv (nb068AlphaDummy072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0074 :
    (nb068AlphaDummy046) ∈
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0075 :
    (nb068AlphaDummy046) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCphi (Class.cv (nb068AlphaDummy054)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy054) from (by
            unfold nb068AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
