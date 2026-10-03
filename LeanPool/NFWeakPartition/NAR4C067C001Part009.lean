/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block002

/-! NF weak partition development: NAR4C067C001Part009. -/


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

theorem nb067_support_mem_0320 :
    (nb067_alpha_dummy_297) ∈
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0321 (f : Var) :
    (nb067_alpha_dummy_300 f) ∈
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0322 :
    (nb067_alpha_dummy_296) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0323 (f : Var) :
    (nb067_alpha_dummy_299 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0324 :
    (nb067_alpha_dummy_296) ∈
      (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0325 (f : Var) :
    (nb067_alpha_dummy_299 f) ∈
      (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0326 :
    (nb067_alpha_dummy_297) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0327 (f : Var) :
    (nb067_alpha_dummy_300 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0328 :
    (nb067_alpha_dummy_297) ∈
      (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0329 (f : Var) :
    (nb067_alpha_dummy_300 f) ∈
      (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0330 :
    (nb067_alpha_dummy_277) ∈
      (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0331 :
    (nb067_alpha_dummy_277) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_281)
              (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0332 (f : Var) :
    (nb067_alpha_dummy_279 f) ∈
      (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0333 (f : Var) :
    (nb067_alpha_dummy_279 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_283 f)
              (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0334 :
    (nb067_alpha_dummy_277) ∈
      (((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281)
            (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_281))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0335 (f : Var) :
    (nb067_alpha_dummy_279 f) ∈
      (((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f)
            (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0336 :
    (nb067_alpha_dummy_282) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0337 (f : Var) :
    (nb067_alpha_dummy_284 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0338 :
    (nb067_alpha_dummy_282) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0339 (f : Var) :
    (nb067_alpha_dummy_284 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0340 :
    (nb067_alpha_dummy_000) ∈
      (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0341 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0342 :
    (nb067_alpha_dummy_322) ∈
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0343 :
    (nb067_alpha_dummy_322) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0344 (f : Var) :
    (nb067_alpha_dummy_324 f) ∈
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0345 (f : Var) :
    (nb067_alpha_dummy_324 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0346 :
    (nb067_alpha_dummy_322) ∈
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0347 (f : Var) :
    (nb067_alpha_dummy_324 f) ∈
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪
        ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0348 :
    (nb067_alpha_dummy_326) ∈ (((Class.cv (nb067_alpha_dummy_326))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0349 (f : Var) :
    (nb067_alpha_dummy_328 f) ∈ (((Class.cv (nb067_alpha_dummy_328 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0350 :
    (nb067_alpha_dummy_333) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_333))).fv) :=
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

theorem nb067_support_mem_0351 (f : Var) :
    (nb067_alpha_dummy_335 f) ∈
      (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb067_alpha_dummy_335 f))).fv) :=
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

theorem nb067_support_mem_0352 :
    (nb067_alpha_dummy_333) ∈
      (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0353 (f : Var) :
    (nb067_alpha_dummy_335 f) ∈
      (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0354 :
    (nb067_alpha_dummy_340) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_340))
            (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0355 (f : Var) :
    (nb067_alpha_dummy_343 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0356 :
    (nb067_alpha_dummy_340) ∈
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0357 (f : Var) :
    (nb067_alpha_dummy_343 f) ∈
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0358 :
    (nb067_alpha_dummy_341) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_340))
            (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0359 (f : Var) :
    (nb067_alpha_dummy_344 f) ∈
      (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪
        ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f))
            (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0360 :
    (nb067_alpha_dummy_341) ∈
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0361 (f : Var) :
    (nb067_alpha_dummy_344 f) ∈
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0362 :
    (nb067_alpha_dummy_340) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0363 (f : Var) :
    (nb067_alpha_dummy_343 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0364 :
    (nb067_alpha_dummy_340) ∈
      (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0365 (f : Var) :
    (nb067_alpha_dummy_343 f) ∈
      (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0366 :
    (nb067_alpha_dummy_341) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0367 (f : Var) :
    (nb067_alpha_dummy_344 f) ∈
      (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0368 :
    (nb067_alpha_dummy_341) ∈
      (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0369 (f : Var) :
    (nb067_alpha_dummy_344 f) ∈
      (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0370 :
    (nb067_alpha_dummy_321) ∈
      (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0371 :
    (nb067_alpha_dummy_321) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_325)
              (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0372 (f : Var) :
    (nb067_alpha_dummy_323 f) ∈
      (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0373 (f : Var) :
    (nb067_alpha_dummy_323 f) ∈
      (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb067_alpha_dummy_327 f)
              (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0374 :
    (nb067_alpha_dummy_321) ∈
      (((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325)
            (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_325))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0375 (f : Var) :
    (nb067_alpha_dummy_323 f) ∈
      (((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f)
            (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0376 :
    (nb067_alpha_dummy_326) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0377 (f : Var) :
    (nb067_alpha_dummy_328 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0378 :
    (nb067_alpha_dummy_326) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0379 (f : Var) :
    (nb067_alpha_dummy_328 f) ∈
      (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪
        ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0380 :
    (nb067_alpha_dummy_000) ∈
      (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0381 (x : Var) (f : Var) :
    f ∈
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0382 :
    (nb067_alpha_dummy_000) ∈
      (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0383 (x : Var) (f : Var) :
    f ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0384 :
    (nb067_alpha_dummy_000) ∈
      (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0385 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0386 :
    (nb067_alpha_dummy_001) ∈
      (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000)))
            (Class.cv (nb067_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0387 (x : Var) (f : Var) :
    x ∈
      (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0388 :
    (nb067_alpha_dummy_001) ∈
      (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪
        ((Class.cv (nb067_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0389 (x : Var) (f : Var) :
    x ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_compact_fv_empty_0028 : (nb067_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0029 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0030 : (nb067_alpha_dummy_002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0031 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0032 : (nb067_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0034 : (nb067_alpha_dummy_005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0035 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_006 x y f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
