/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part024`. -/


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

theorem nb078_support_mem_0313 (g : Var) :
    (nb078_alpha_dummy_314 g) ∈
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0314 :
    (nb078_alpha_dummy_310) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0315 (g : Var) :
    (nb078_alpha_dummy_313 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0316 :
    (nb078_alpha_dummy_310) ∈
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0317 (g : Var) :
    (nb078_alpha_dummy_313 g) ∈
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0318 :
    (nb078_alpha_dummy_311) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0319 (g : Var) :
    (nb078_alpha_dummy_314 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0320 :
    (nb078_alpha_dummy_311) ∈
      (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0321 (g : Var) :
    (nb078_alpha_dummy_314 g) ∈
      (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0322 :
    (nb078_alpha_dummy_288) ∈
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0323 :
    (nb078_alpha_dummy_288) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_295) from (by
          unfold nb078_alpha_dummy_295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_296) from (by
            unfold nb078_alpha_dummy_296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0324 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0325 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_297 g) from (by
          unfold nb078_alpha_dummy_297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_298 g) from (by
            unfold nb078_alpha_dummy_298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0326 :
    (nb078_alpha_dummy_288) ∈
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_295) from (by
          unfold nb078_alpha_dummy_295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_296) from (by
            unfold nb078_alpha_dummy_296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0327 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_297 g) from (by
          unfold nb078_alpha_dummy_297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_298 g) from (by
            unfold nb078_alpha_dummy_298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0328 :
    (nb078_alpha_dummy_296) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0329 (g : Var) :
    (nb078_alpha_dummy_298 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0330 :
    (nb078_alpha_dummy_296) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0331 (g : Var) :
    (nb078_alpha_dummy_298 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0332 :
    (nb078_alpha_dummy_287) ∈
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0333 :
    (nb078_alpha_dummy_287) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_332) from (by
            unfold nb078_alpha_dummy_332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0334 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0335 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_334 g) from (by
            unfold nb078_alpha_dummy_334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0336 :
    (nb078_alpha_dummy_287) ∈
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_332) from (by
            unfold nb078_alpha_dummy_332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0337 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_334 g) from (by
            unfold nb078_alpha_dummy_334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0338 :
    (nb078_alpha_dummy_332) ∈ (((Class.cv (nb078_alpha_dummy_332))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0339 (g : Var) :
    (nb078_alpha_dummy_334 g) ∈ (((Class.cv (nb078_alpha_dummy_334 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0340 :
    (nb078_alpha_dummy_339) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_339))).fv) :=
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

theorem nb078_support_mem_0341 (g : Var) :
    (nb078_alpha_dummy_341 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_341 g))).fv) :=
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

theorem nb078_support_mem_0342 :
    (nb078_alpha_dummy_339) ∈
      (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0343 (g : Var) :
    (nb078_alpha_dummy_341 g) ∈
      (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0344 :
    (nb078_alpha_dummy_346) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_346))
            (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0345 (g : Var) :
    (nb078_alpha_dummy_349 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0346 :
    (nb078_alpha_dummy_346) ∈
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0347 (g : Var) :
    (nb078_alpha_dummy_349 g) ∈
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0348 :
    (nb078_alpha_dummy_347) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_346))
            (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0349 (g : Var) :
    (nb078_alpha_dummy_350 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g))
            (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0350 :
    (nb078_alpha_dummy_347) ∈
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0351 (g : Var) :
    (nb078_alpha_dummy_350 g) ∈
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0352 :
    (nb078_alpha_dummy_346) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0353 (g : Var) :
    (nb078_alpha_dummy_349 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0354 :
    (nb078_alpha_dummy_346) ∈
      (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0355 (g : Var) :
    (nb078_alpha_dummy_349 g) ∈
      (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0356 :
    (nb078_alpha_dummy_347) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0357 (g : Var) :
    (nb078_alpha_dummy_350 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0358 :
    (nb078_alpha_dummy_347) ∈
      (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0359 (g : Var) :
    (nb078_alpha_dummy_350 g) ∈
      (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0360 :
    (nb078_alpha_dummy_289) ∈
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0361 :
    (nb078_alpha_dummy_289) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_331)
              (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_332) from (by
            unfold nb078_alpha_dummy_332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0362 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0363 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_333 g)
              (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_334 g) from (by
            unfold nb078_alpha_dummy_334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0364 :
    (nb078_alpha_dummy_289) ∈
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_332) from (by
            unfold nb078_alpha_dummy_332;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0365 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_334 g) from (by
            unfold nb078_alpha_dummy_334;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0366 :
    (nb078_alpha_dummy_332) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0367 (g : Var) :
    (nb078_alpha_dummy_334 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0368 :
    (nb078_alpha_dummy_332) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0369 (g : Var) :
    (nb078_alpha_dummy_334 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0370 :
    (nb078_alpha_dummy_367) ∈
      (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
            (Class.cv (nb078_alpha_dummy_367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0371 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
            (Class.cv (nb078_alpha_dummy_369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0372 :
    (nb078_alpha_dummy_368) ∈
      (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
            (Class.cv (nb078_alpha_dummy_367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0373 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
            (Class.cv (nb078_alpha_dummy_369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0374 :
    (nb078_alpha_dummy_367) ∈
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0375 :
    (nb078_alpha_dummy_367) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from (by
            unfold nb078_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0376 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0377 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
            unfold nb078_alpha_dummy_376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0378 :
    (nb078_alpha_dummy_367) ∈
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from (by
            unfold nb078_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0379 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
            unfold nb078_alpha_dummy_376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0380 :
    (nb078_alpha_dummy_374) ∈ (((Class.cv (nb078_alpha_dummy_374))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0381 (g : Var) :
    (nb078_alpha_dummy_376 g) ∈ (((Class.cv (nb078_alpha_dummy_376 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0382 :
    (nb078_alpha_dummy_381) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_381))).fv) :=
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

theorem nb078_support_mem_0383 (g : Var) :
    (nb078_alpha_dummy_383 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_383 g))).fv) :=
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

theorem nb078_support_mem_0384 :
    (nb078_alpha_dummy_381) ∈
      (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0385 (g : Var) :
    (nb078_alpha_dummy_383 g) ∈
      (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0386 :
    (nb078_alpha_dummy_388) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_388))
            (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0387 (g : Var) :
    (nb078_alpha_dummy_391 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0388 :
    (nb078_alpha_dummy_388) ∈
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0389 (g : Var) :
    (nb078_alpha_dummy_391 g) ∈
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0390 :
    (nb078_alpha_dummy_389) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_388))
            (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0391 (g : Var) :
    (nb078_alpha_dummy_392 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g))
            (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0392 :
    (nb078_alpha_dummy_389) ∈
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0393 (g : Var) :
    (nb078_alpha_dummy_392 g) ∈
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0394 :
    (nb078_alpha_dummy_388) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0395 (g : Var) :
    (nb078_alpha_dummy_391 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0396 :
    (nb078_alpha_dummy_388) ∈
      (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0397 (g : Var) :
    (nb078_alpha_dummy_391 g) ∈
      (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0398 :
    (nb078_alpha_dummy_389) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0399 (g : Var) :
    (nb078_alpha_dummy_392 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0400 :
    (nb078_alpha_dummy_389) ∈
      (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0401 (g : Var) :
    (nb078_alpha_dummy_392 g) ∈
      (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0402 :
    (nb078_alpha_dummy_368) ∈
      (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0403 :
    (nb078_alpha_dummy_368) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373) from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
            unfold nb078_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0404 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0405 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
            unfold nb078_alpha_dummy_376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0406 :
    (nb078_alpha_dummy_368) ∈
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373) from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
            unfold nb078_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0407 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
            unfold nb078_alpha_dummy_376;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0408 :
    (nb078_alpha_dummy_374) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0409 (g : Var) :
    (nb078_alpha_dummy_376 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0410 :
    (nb078_alpha_dummy_374) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0411 (g : Var) :
    (nb078_alpha_dummy_376 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0412 :
    (nb078_alpha_dummy_368) ∈
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0413 :
    (nb078_alpha_dummy_368) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_409) from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_410) from (by
            unfold nb078_alpha_dummy_410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0414 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0415 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_412 g) from (by
            unfold nb078_alpha_dummy_412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0416 :
    (nb078_alpha_dummy_368) ∈
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_409) from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_410) from (by
            unfold nb078_alpha_dummy_410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0417 (g : Var) :
    (nb078_alpha_dummy_370 g) ∈
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_412 g) from (by
            unfold nb078_alpha_dummy_412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0418 :
    (nb078_alpha_dummy_410) ∈ (((Class.cv (nb078_alpha_dummy_410))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0419 (g : Var) :
    (nb078_alpha_dummy_412 g) ∈ (((Class.cv (nb078_alpha_dummy_412 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0420 :
    (nb078_alpha_dummy_417) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_417))).fv) :=
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

theorem nb078_support_mem_0421 (g : Var) :
    (nb078_alpha_dummy_419 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_419 g))).fv) :=
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

theorem nb078_support_mem_0422 :
    (nb078_alpha_dummy_417) ∈
      (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0423 (g : Var) :
    (nb078_alpha_dummy_419 g) ∈
      (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0424 :
    (nb078_alpha_dummy_424) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_424))
            (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0425 (g : Var) :
    (nb078_alpha_dummy_427 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0426 :
    (nb078_alpha_dummy_424) ∈
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0427 (g : Var) :
    (nb078_alpha_dummy_427 g) ∈
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0428 :
    (nb078_alpha_dummy_425) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_424))
            (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0429 (g : Var) :
    (nb078_alpha_dummy_428 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g))
            (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0430 :
    (nb078_alpha_dummy_425) ∈
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0431 (g : Var) :
    (nb078_alpha_dummy_428 g) ∈
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0432 :
    (nb078_alpha_dummy_424) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0433 (g : Var) :
    (nb078_alpha_dummy_427 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0434 :
    (nb078_alpha_dummy_424) ∈
      (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0435 (g : Var) :
    (nb078_alpha_dummy_427 g) ∈
      (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0436 :
    (nb078_alpha_dummy_425) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0437 (g : Var) :
    (nb078_alpha_dummy_428 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0438 :
    (nb078_alpha_dummy_425) ∈
      (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0439 (g : Var) :
    (nb078_alpha_dummy_428 g) ∈
      (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0440 :
    (nb078_alpha_dummy_367) ∈
      (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0441 :
    (nb078_alpha_dummy_367) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409) from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
            unfold nb078_alpha_dummy_410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0442 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0443 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
            unfold nb078_alpha_dummy_412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0444 :
    (nb078_alpha_dummy_367) ∈
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409) from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
            unfold nb078_alpha_dummy_410;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0445 (g : Var) :
    (nb078_alpha_dummy_369 g) ∈
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
            unfold nb078_alpha_dummy_412;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0446 :
    (nb078_alpha_dummy_410) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0447 (g : Var) :
    (nb078_alpha_dummy_412 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0448 :
    (nb078_alpha_dummy_410) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0449 (g : Var) :
    (nb078_alpha_dummy_412 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0450 :
    (nb078_alpha_dummy_001) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0451 (g : Var) :
    g ∈
      (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0452 :
    (nb078_alpha_dummy_001) ∈
      (((syn_ccom (Class.cv (nb078_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0453 (g : Var) :
    g ∈ (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0454 :
    (nb078_alpha_dummy_001) ∈
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part025`. -/


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

theorem nb078_support_mem_0455 :
    (nb078_alpha_dummy_001) ∈
      (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_289) from (by
          unfold nb078_alpha_dummy_289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0456 (g : Var) :
    g ∈ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0457 (g : Var) :
    g ∈
      (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb078_alpha_dummy_292 g) from (by
          unfold nb078_alpha_dummy_292;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0458 :
    (nb078_alpha_dummy_001) ∈
      (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001))
            (Class.cv (nb078_alpha_dummy_367)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0459 (g : Var) :
    g ∈
      (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g)
            (Class.cv (nb078_alpha_dummy_369 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0460 :
    (nb078_alpha_dummy_001) ∈ (((Class.cv (nb078_alpha_dummy_001))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0461 (g : Var) : g ∈ (((Class.cv g)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0462 :
    (nb078_alpha_dummy_289) ∈
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0463 :
    (nb078_alpha_dummy_289) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_446) from (by
            unfold nb078_alpha_dummy_446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0464 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0465 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_448 g) from (by
            unfold nb078_alpha_dummy_448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0466 :
    (nb078_alpha_dummy_289) ∈
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_446) from (by
            unfold nb078_alpha_dummy_446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0467 (g : Var) :
    (nb078_alpha_dummy_292 g) ∈
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_448 g) from (by
            unfold nb078_alpha_dummy_448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0468 :
    (nb078_alpha_dummy_446) ∈ (((Class.cv (nb078_alpha_dummy_446))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0469 (g : Var) :
    (nb078_alpha_dummy_448 g) ∈ (((Class.cv (nb078_alpha_dummy_448 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0470 :
    (nb078_alpha_dummy_453) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_453))).fv) :=
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

theorem nb078_support_mem_0471 (g : Var) :
    (nb078_alpha_dummy_455 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_455 g))).fv) :=
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

theorem nb078_support_mem_0472 :
    (nb078_alpha_dummy_453) ∈
      (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0473 (g : Var) :
    (nb078_alpha_dummy_455 g) ∈
      (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0474 :
    (nb078_alpha_dummy_460) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_460))
            (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0475 (g : Var) :
    (nb078_alpha_dummy_463 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0476 :
    (nb078_alpha_dummy_460) ∈
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0477 (g : Var) :
    (nb078_alpha_dummy_463 g) ∈
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0478 :
    (nb078_alpha_dummy_461) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_460))
            (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0479 (g : Var) :
    (nb078_alpha_dummy_464 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g))
            (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0480 :
    (nb078_alpha_dummy_461) ∈
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0481 (g : Var) :
    (nb078_alpha_dummy_464 g) ∈
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0482 :
    (nb078_alpha_dummy_460) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0483 (g : Var) :
    (nb078_alpha_dummy_463 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0484 :
    (nb078_alpha_dummy_460) ∈
      (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0485 (g : Var) :
    (nb078_alpha_dummy_463 g) ∈
      (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0486 :
    (nb078_alpha_dummy_461) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0487 (g : Var) :
    (nb078_alpha_dummy_464 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0488 :
    (nb078_alpha_dummy_461) ∈
      (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0489 (g : Var) :
    (nb078_alpha_dummy_464 g) ∈
      (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0490 :
    (nb078_alpha_dummy_288) ∈
      (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0491 :
    (nb078_alpha_dummy_288) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_446) from (by
            unfold nb078_alpha_dummy_446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0492 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0493 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_448 g) from (by
            unfold nb078_alpha_dummy_448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0494 :
    (nb078_alpha_dummy_288) ∈
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_446) from (by
            unfold nb078_alpha_dummy_446;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0495 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_448 g) from (by
            unfold nb078_alpha_dummy_448;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0496 :
    (nb078_alpha_dummy_446) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0497 (g : Var) :
    (nb078_alpha_dummy_448 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0498 :
    (nb078_alpha_dummy_446) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0499 (g : Var) :
    (nb078_alpha_dummy_448 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0500 :
    (nb078_alpha_dummy_482) ∈
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0501 :
    (nb078_alpha_dummy_482) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_485) from (by
          unfold nb078_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_486) from (by
            unfold nb078_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0502 (g : Var) :
    (nb078_alpha_dummy_484 g) ∈
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0503 (g : Var) :
    (nb078_alpha_dummy_484 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_487 g) from (by
          unfold nb078_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_488 g) from (by
            unfold nb078_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0504 :
    (nb078_alpha_dummy_482) ∈
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_485) from (by
          unfold nb078_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_486) from (by
            unfold nb078_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0505 (g : Var) :
    (nb078_alpha_dummy_484 g) ∈
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_487 g) from (by
          unfold nb078_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_488 g) from (by
            unfold nb078_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0506 :
    (nb078_alpha_dummy_486) ∈ (((Class.cv (nb078_alpha_dummy_486))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0507 (g : Var) :
    (nb078_alpha_dummy_488 g) ∈ (((Class.cv (nb078_alpha_dummy_488 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0508 :
    (nb078_alpha_dummy_493) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_493))).fv) :=
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

theorem nb078_support_mem_0509 (g : Var) :
    (nb078_alpha_dummy_495 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_495 g))).fv) :=
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

theorem nb078_support_mem_0510 :
    (nb078_alpha_dummy_493) ∈
      (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0511 (g : Var) :
    (nb078_alpha_dummy_495 g) ∈
      (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0512 :
    (nb078_alpha_dummy_500) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_500))
            (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0513 (g : Var) :
    (nb078_alpha_dummy_503 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0514 :
    (nb078_alpha_dummy_500) ∈
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0515 (g : Var) :
    (nb078_alpha_dummy_503 g) ∈
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0516 :
    (nb078_alpha_dummy_501) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_500))
            (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0517 (g : Var) :
    (nb078_alpha_dummy_504 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g))
            (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0518 :
    (nb078_alpha_dummy_501) ∈
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0519 (g : Var) :
    (nb078_alpha_dummy_504 g) ∈
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0520 :
    (nb078_alpha_dummy_500) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0521 (g : Var) :
    (nb078_alpha_dummy_503 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0522 :
    (nb078_alpha_dummy_500) ∈
      (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0523 (g : Var) :
    (nb078_alpha_dummy_503 g) ∈
      (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0524 :
    (nb078_alpha_dummy_501) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0525 (g : Var) :
    (nb078_alpha_dummy_504 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0526 :
    (nb078_alpha_dummy_501) ∈
      (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0527 (g : Var) :
    (nb078_alpha_dummy_504 g) ∈
      (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0528 :
    (nb078_alpha_dummy_481) ∈
      (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0529 :
    (nb078_alpha_dummy_481) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_485) from (by
          unfold nb078_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_486) from (by
            unfold nb078_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0530 (g : Var) :
    (nb078_alpha_dummy_483 g) ∈
      (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0531 (g : Var) :
    (nb078_alpha_dummy_483 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_487 g) from (by
          unfold nb078_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_488 g) from (by
            unfold nb078_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0532 :
    (nb078_alpha_dummy_481) ∈
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_485) from (by
          unfold nb078_alpha_dummy_485;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_486) from (by
            unfold nb078_alpha_dummy_486;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0533 (g : Var) :
    (nb078_alpha_dummy_483 g) ∈
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_487 g) from (by
          unfold nb078_alpha_dummy_487;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_488 g) from (by
            unfold nb078_alpha_dummy_488;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0534 :
    (nb078_alpha_dummy_486) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0535 (g : Var) :
    (nb078_alpha_dummy_488 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0536 :
    (nb078_alpha_dummy_486) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0537 (g : Var) :
    (nb078_alpha_dummy_488 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0538 :
    (nb078_alpha_dummy_001) ∈
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0539 (g : Var) :
    g ∈ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0540 :
    (nb078_alpha_dummy_526) ∈
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0541 :
    (nb078_alpha_dummy_526) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_529) from (by
          unfold nb078_alpha_dummy_529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from (by
            unfold nb078_alpha_dummy_530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0542 (g : Var) :
    (nb078_alpha_dummy_528 g) ∈
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0543 (g : Var) :
    (nb078_alpha_dummy_528 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold nb078_alpha_dummy_531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
            unfold nb078_alpha_dummy_532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0544 :
    (nb078_alpha_dummy_526) ∈
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_529) from (by
          unfold nb078_alpha_dummy_529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from (by
            unfold nb078_alpha_dummy_530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0545 (g : Var) :
    (nb078_alpha_dummy_528 g) ∈
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold nb078_alpha_dummy_531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
            unfold nb078_alpha_dummy_532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0546 :
    (nb078_alpha_dummy_530) ∈ (((Class.cv (nb078_alpha_dummy_530))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0547 (g : Var) :
    (nb078_alpha_dummy_532 g) ∈ (((Class.cv (nb078_alpha_dummy_532 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0548 :
    (nb078_alpha_dummy_537) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_537))).fv) :=
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

theorem nb078_support_mem_0549 (g : Var) :
    (nb078_alpha_dummy_539 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_539 g))).fv) :=
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

theorem nb078_support_mem_0550 :
    (nb078_alpha_dummy_537) ∈
      (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0551 (g : Var) :
    (nb078_alpha_dummy_539 g) ∈
      (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0552 :
    (nb078_alpha_dummy_544) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_544))
            (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0553 (g : Var) :
    (nb078_alpha_dummy_547 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0554 :
    (nb078_alpha_dummy_544) ∈
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0555 (g : Var) :
    (nb078_alpha_dummy_547 g) ∈
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0556 :
    (nb078_alpha_dummy_545) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_544))
            (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0557 (g : Var) :
    (nb078_alpha_dummy_548 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g))
            (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0558 :
    (nb078_alpha_dummy_545) ∈
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0559 (g : Var) :
    (nb078_alpha_dummy_548 g) ∈
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0560 :
    (nb078_alpha_dummy_544) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0561 (g : Var) :
    (nb078_alpha_dummy_547 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0562 :
    (nb078_alpha_dummy_544) ∈
      (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0563 (g : Var) :
    (nb078_alpha_dummy_547 g) ∈
      (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0564 :
    (nb078_alpha_dummy_545) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0565 (g : Var) :
    (nb078_alpha_dummy_548 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0566 :
    (nb078_alpha_dummy_545) ∈
      (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0567 (g : Var) :
    (nb078_alpha_dummy_548 g) ∈
      (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0568 :
    (nb078_alpha_dummy_525) ∈
      (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0569 :
    (nb078_alpha_dummy_525) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529) from (by
          unfold nb078_alpha_dummy_529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
            unfold nb078_alpha_dummy_530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0570 (g : Var) :
    (nb078_alpha_dummy_527 g) ∈
      (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0571 (g : Var) :
    (nb078_alpha_dummy_527 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold nb078_alpha_dummy_531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
            unfold nb078_alpha_dummy_532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0572 :
    (nb078_alpha_dummy_525) ∈
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529) from (by
          unfold nb078_alpha_dummy_529;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
            unfold nb078_alpha_dummy_530;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0573 (g : Var) :
    (nb078_alpha_dummy_527 g) ∈
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold nb078_alpha_dummy_531;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
            unfold nb078_alpha_dummy_532;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0574 :
    (nb078_alpha_dummy_530) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0575 (g : Var) :
    (nb078_alpha_dummy_532 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0576 :
    (nb078_alpha_dummy_530) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0577 (g : Var) :
    (nb078_alpha_dummy_532 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0578 :
    (nb078_alpha_dummy_001) ∈
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0579 (x : Var) (g : Var) :
    g ∈
      (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0580 :
    (nb078_alpha_dummy_001) ∈
      (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0581 (x : Var) (g : Var) :
    g ∈ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0582 :
    (nb078_alpha_dummy_001) ∈
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0583 (g : Var) : g ∈ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0584 :
    (nb078_alpha_dummy_003) ∈
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0585 (x : Var) (g : Var) :
    x ∈
      (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪
        ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0586 :
    (nb078_alpha_dummy_003) ∈
      (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0587 (x : Var) (g : Var) :
    x ∈ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0588 :
    (nb078_alpha_dummy_569) ∈
      (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0589 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0590 :
    (nb078_alpha_dummy_570) ∈
      (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0591 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0592 :
    (nb078_alpha_dummy_569) ∈
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0593 :
    (nb078_alpha_dummy_569) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_577) from (by
          unfold nb078_alpha_dummy_577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_578) from (by
            unfold nb078_alpha_dummy_578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0594 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0595 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_579 g) from (by
          unfold nb078_alpha_dummy_579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_580 g) from (by
            unfold nb078_alpha_dummy_580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
