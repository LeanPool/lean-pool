/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block002

/-! NF weak partition development: NAR4C057C001Part007. -/


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

theorem nb057_support_mem_0246 :
    (nb057_alpha_dummy_045) ∈
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0247 (f : Var) :
    (nb057_alpha_dummy_048 f) ∈
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0248 :
    (nb057_alpha_dummy_203) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0249 (f : Var) :
    (nb057_alpha_dummy_205 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0250 :
    (nb057_alpha_dummy_203) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0251 (f : Var) :
    (nb057_alpha_dummy_205 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0252 :
    (nb057_alpha_dummy_239) ∈
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0253 :
    (nb057_alpha_dummy_239) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0254 (f : Var) :
    (nb057_alpha_dummy_241 f) ∈
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0255 (f : Var) :
    (nb057_alpha_dummy_241 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0256 :
    (nb057_alpha_dummy_239) ∈
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0257 (f : Var) :
    (nb057_alpha_dummy_241 f) ∈
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0258 :
    (nb057_alpha_dummy_243) ∈ (((Class.cv (nb057_alpha_dummy_243))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0259 (f : Var) :
    (nb057_alpha_dummy_245 f) ∈ (((Class.cv (nb057_alpha_dummy_245 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0260 :
    (nb057_alpha_dummy_250) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_250))).fv) :=
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

theorem nb057_support_mem_0261 (f : Var) :
    (nb057_alpha_dummy_252 f) ∈
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_252 f))).fv) :=
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

theorem nb057_support_mem_0262 :
    (nb057_alpha_dummy_250) ∈
      (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0263 (f : Var) :
    (nb057_alpha_dummy_252 f) ∈
      (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0264 :
    (nb057_alpha_dummy_257) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_257))
            (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0265 (f : Var) :
    (nb057_alpha_dummy_260 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0266 :
    (nb057_alpha_dummy_257) ∈
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0267 (f : Var) :
    (nb057_alpha_dummy_260 f) ∈
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0268 :
    (nb057_alpha_dummy_258) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_257))
            (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0269 (f : Var) :
    (nb057_alpha_dummy_261 f) ∈
      (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0270 :
    (nb057_alpha_dummy_258) ∈
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0271 (f : Var) :
    (nb057_alpha_dummy_261 f) ∈
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0272 :
    (nb057_alpha_dummy_257) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0273 (f : Var) :
    (nb057_alpha_dummy_260 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0274 :
    (nb057_alpha_dummy_257) ∈
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0275 (f : Var) :
    (nb057_alpha_dummy_260 f) ∈
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0276 :
    (nb057_alpha_dummy_258) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0277 (f : Var) :
    (nb057_alpha_dummy_261 f) ∈
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0278 :
    (nb057_alpha_dummy_258) ∈
      (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0279 (f : Var) :
    (nb057_alpha_dummy_261 f) ∈
      (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0280 :
    (nb057_alpha_dummy_238) ∈
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0281 :
    (nb057_alpha_dummy_238) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0282 (f : Var) :
    (nb057_alpha_dummy_240 f) ∈
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0283 (f : Var) :
    (nb057_alpha_dummy_240 f) ∈
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0284 :
    (nb057_alpha_dummy_238) ∈
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0285 (f : Var) :
    (nb057_alpha_dummy_240 f) ∈
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0286 :
    (nb057_alpha_dummy_243) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0287 (f : Var) :
    (nb057_alpha_dummy_245 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0288 :
    (nb057_alpha_dummy_243) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0289 (f : Var) :
    (nb057_alpha_dummy_245 f) ∈
      (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪
        ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0290 :
    (nb057_alpha_dummy_001) ∈
      (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0291 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_compact_fv_empty_0020 : (nb057_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0022 : (nb057_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0023 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0024 : (nb057_alpha_dummy_002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0025 (f : Var) (a : Var) :
    (nb057_alpha_dummy_003 f a) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
