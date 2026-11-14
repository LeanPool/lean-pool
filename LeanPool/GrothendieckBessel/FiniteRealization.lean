/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.Conventions
public import LeanPool.GrothendieckBessel.BallProdromou
public import LeanPool.GrothendieckBessel.ComplexReduction
public import LeanPool.GrothendieckBessel.StepFunctions

import Mathlib.Tactic.Ring

/-!
# Finite complex Olevskii realization

This connects the finite quadratic-form condition to the real and complex
convex decompositions and their bounded measurable step-function realization.
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GrothendieckBessel

private theorem complexQuadraticFormRe_eq_kernelSum
    {F : Type*} [Fintype F]
    (h : Matrix F F ℂ) (x : F → ℂ) :
    OlevskiiGram.complexQuadraticFormRe h x =
      (∑ j, ∑ k, star (x j) * star (star (x k)) * h j k).re := by
  unfold OlevskiiGram.complexQuadraticFormRe
  apply congrArg Complex.re
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [star_star]
  ring

private theorem complexQuadraticFormRe_one
    {F : Type*} [Fintype F] [DecidableEq F]
    (x : F → ℂ) :
    OlevskiiGram.complexQuadraticFormRe (1 : Matrix F F ℂ) x =
      ∑ j, ‖x j‖ ^ 2 := by
  rw [complexQuadraticFormRe_eq_kernelSum]
  simp only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
    mul_comm, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  norm_cast

private theorem complexQuadraticFormRe_sub
    {F : Type*} [Fintype F]
    (A B : Matrix F F ℂ) (x : F → ℂ) :
    OlevskiiGram.complexQuadraticFormRe (A - B) x =
      OlevskiiGram.complexQuadraticFormRe A x -
        OlevskiiGram.complexQuadraticFormRe B x := by
  unfold OlevskiiGram.complexQuadraticFormRe
  rw [← Complex.sub_re]
  apply congrArg Complex.re
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- The finite-sum positive-contraction condition implies matrix Loewner bounds. -/
theorem FiniteHermitianPositiveContraction.toComplexLoewner
    {F : Type*} [Fintype F] [DecidableEq F]
    {h : Matrix F F ℂ} (hh : FiniteHermitianPositiveContraction h) :
    OlevskiiGram.ComplexLoewnerBetweenZeroAndOne h := by
  constructor
  · intro x
    have hq := (hh.2 Finset.univ (fun j => star (x j))).1
    rw [complexQuadraticFormRe_eq_kernelSum h x]
    simpa [mul_assoc] using hq
  · intro x
    have hq := (hh.2 Finset.univ (fun j => star (x j))).2
    have hupper :
        OlevskiiGram.complexQuadraticFormRe h x ≤ ∑ j, ‖x j‖ ^ 2 := by
      rw [complexQuadraticFormRe_eq_kernelSum h x]
      simpa [mul_assoc] using hq
    rw [complexQuadraticFormRe_sub, complexQuadraticFormRe_one]
    exact sub_nonneg.mpr hupper

/--
Finite complex Olevskii Gram realization on `[0,1]`, proved from the finite
convex-decomposition development rather than assumed as an axiom.
-/
theorem finite_complex_olevskii_gram_realization
    {F : Type*} [Finite F]
    (h : Matrix F F ℂ)
    (hh : FiniteHermitianPositiveContraction h) :
    ∃ a : F → ℝ → ℂ,
      (∀ j, AEStronglyMeasurable (a j) (μOn unitInterval)) ∧
        (∀ j t, t ∈ unitInterval → ‖a j t‖ ≤ 1) ∧
          (∀ j k, l2InnerOn unitInterval (a j) (a k) = h j k) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hHerm : OlevskiiGram.ComplexHermitian h := hh.1
  have hLoewner : OlevskiiGram.ComplexLoewnerBetweenZeroAndOne h :=
    hh.toComplexLoewner
  rcases OlevskiiGram.finiteComplexDecomposition h
      (OlevskiiGram.hasRealConvexDecomposition (Sum F F)) hHerm hLoewner with
    ⟨m, _hm, p, ζ, hp, hpsum, hζ, hentry⟩
  rcases OlevskiiGram.stepFunctionRealizationOnUnitInterval p ζ hp hpsum hζ with
    ⟨a, haMeas, haBound, haMoment⟩
  refine ⟨a, haMeas, ?_, ?_⟩
  · intro j t _ht
    exact haBound j t
  · intro j k
    unfold l2InnerOn μOn
    change (∫ t in Set.Icc (0 : ℝ) 1, a j t * star (a k t)) = h j k
    rw [haMoment j k]
    exact (hentry j k).symm

end GrothendieckBessel
