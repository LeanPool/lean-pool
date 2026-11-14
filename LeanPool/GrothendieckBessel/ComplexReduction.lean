/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.RealConvex
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Real block reduction of complex Gram matrices
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

namespace OlevskiiGram

private lemma complexRe_ite_one_zero (p : Prop) [Decidable p] :
    Complex.re (if p then (1 : ℂ) else 0) = (if p then (1 : ℝ) else 0) := by
  by_cases hp : p <;> simp [hp]

private lemma complexIm_ite_one_zero (p : Prop) [Decidable p] :
    Complex.im (if p then (1 : ℂ) else 0) = 0 := by
  by_cases hp : p <;> simp [hp]

private lemma scaled_complex_norm_le_one (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(((a : ℂ) + (b : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))‖ ≤ 1 := by
  let z : ℂ := (((a : ℂ) + (b : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))
  have hnormsq : Complex.normSq z ≤ 1 := by
    dsimp [z]
    rw [Complex.normSq_div, Complex.normSq_add_mul_I, Complex.normSq_ofReal]
    have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt (by norm_num)
    have ha2 : a ^ 2 ≤ 1 := by
      rwa [sq_le_one_iff_abs_le_one]
    have hb2 : b ^ 2 ≤ 1 := by
      rwa [sq_le_one_iff_abs_le_one]
    rw [hsqrt_sq]
    nlinarith
  have hsq : ‖z‖ ^ 2 ≤ 1 := by
    simpa [Complex.sq_norm] using hnormsq
  exact (sq_le_one_iff₀ (norm_nonneg z)).mp hsq

theorem realBlock_quadraticForm
    {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) (x : Sum n n → ℝ) :
    realQuadraticForm (realBlockMatrix (complexReMatrix G) (complexImMatrix G)) x =
      complexQuadraticFormRe G
        (fun i : n => (x (Sum.inl i) : ℂ) + Complex.I * (x (Sum.inr i) : ℂ)) := by
  simp [realQuadraticForm, complexQuadraticFormRe, realBlockMatrix,
    complexReMatrix, complexImMatrix, Finset.sum_add_distrib, add_comm]
  ring_nf

theorem realBlock_one_sub_quadraticForm
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (x : Sum n n → ℝ) :
    realQuadraticForm (1 - realBlockMatrix (complexReMatrix G) (complexImMatrix G)) x =
      complexQuadraticFormRe (1 - G)
        (fun i : n => (x (Sum.inl i) : ℂ) + Complex.I * (x (Sum.inr i) : ℂ)) := by
  simp [realQuadraticForm, complexQuadraticFormRe, realBlockMatrix,
    complexReMatrix, complexImMatrix, Matrix.one_apply, Finset.sum_add_distrib,
    add_comm, sub_eq_add_neg, complexRe_ite_one_zero, complexIm_ite_one_zero]

/-- Bridge from Mathlib's complex matrix PSD predicate to the quadratic-form predicate. -/
theorem complexPSD_of_posSemidef
    {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    A.PosSemidef → ComplexPSD A := by
  intro hA x
  have hx := hA.dotProduct_mulVec_nonneg x
  have hxre := (RCLike.nonneg_iff.mp hx).1
  simpa [complexQuadraticFormRe, Matrix.dotProduct_mulVec, dotProduct, Matrix.mulVec] using hxre

/-- The complex quadratic form is the real part of the Euclidean operator form. -/
theorem complexQuadraticFormRe_eq_operator_inner
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    complexQuadraticFormRe A x =
      Complex.re (inner ℂ (WithLp.toLp 2 x)
        (matrixL2Operator A (WithLp.toLp 2 x))) := by
  simp [complexQuadraticFormRe, matrixL2Operator, EuclideanSpace.inner_toLp_toLp,
    dotProduct, Matrix.mulVec, mul_comm]

theorem matrixL2Operator_one_sub_apply
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    matrixL2Operator (1 - A) (WithLp.toLp 2 x) =
      WithLp.toLp 2 x - matrixL2Operator A (WithLp.toLp 2 x) := by
  simp [matrixL2Operator, sub_eq_add_neg]

theorem complexPSD_one_sub_of_operatorNorm
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    matrixL2OperatorNormLE A 1 → ComplexPSD (1 - A) := by
  intro hA x
  rw [complexQuadraticFormRe_eq_operator_inner]
  rw [matrixL2Operator_one_sub_apply]
  let v : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 x
  let T := matrixL2Operator A
  have hinner : Complex.re (inner ℂ v (T v)) ≤ ‖v‖ * ‖T v‖ := by
    exact re_inner_le_norm (𝕜 := ℂ) v (T v)
  have happly : ‖T v‖ ≤ ‖v‖ := by
    simpa using T.le_of_opNorm_le hA v
  have hbound : Complex.re (inner ℂ v (T v)) ≤ ‖v‖ ^ 2 := by
    calc
      Complex.re (inner ℂ v (T v)) ≤ ‖v‖ * ‖T v‖ := hinner
      _ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_left happly (norm_nonneg v)
      _ = ‖v‖ ^ 2 := by ring
  have hnonneg : 0 ≤ ‖v‖ ^ 2 - Complex.re (inner ℂ v (T v)) := sub_nonneg.mpr hbound
  convert hnonneg using 1
  simp [v, T, inner_sub_right, inner_self_eq_norm_sq_to_K, Complex.sub_re, sq]

/--
The Gram matrix with operator norm at most one satisfies the Hermitian and
Loewner-order hypotheses needed for the decomposition.
-/
theorem gramMatrix_psd_le_one
    {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : Fin N → H) :
    matrixL2OperatorNormLE (gramMatrix z) 1 →
      ComplexHermitian (gramMatrix z) ∧
      ComplexLoewnerBetweenZeroAndOne (gramMatrix z) := by
  intro hG
  constructor
  · intro i j
    simp [gramMatrix]
  · constructor
    · have hgram : gramMatrix z = (Matrix.gram ℂ z).transpose := by
        ext i j
        simp [gramMatrix, Matrix.gram]
      have hpos : (gramMatrix z).PosSemidef := by
        rw [hgram]
        exact (Matrix.posSemidef_gram ℂ z).transpose
      exact complexPSD_of_posSemidef _ hpos
    · exact complexPSD_one_sub_of_operatorNorm (gramMatrix z) hG

/--
The real block matrix of a Hermitian complex matrix `0 ≤ G ≤ I` also satisfies
`0 ≤ G_real ≤ I`.
-/
theorem realBlock_psd_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) :
    ComplexHermitian G → ComplexLoewnerBetweenZeroAndOne G →
      let Gtilde := realBlockMatrix (complexReMatrix G) (complexImMatrix G)
      RealSymmetric Gtilde ∧ RealLoewnerBetweenZeroAndOne Gtilde := by
  intro hHerm hLoewner
  dsimp
  constructor
  · intro a b
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            dsimp [realBlockMatrix, complexReMatrix]
            have h := congrArg Complex.re (hHerm j i)
            simpa using h
        | inr j =>
            dsimp [realBlockMatrix, complexImMatrix]
            have h := congrArg Complex.im (hHerm i j)
            simpa using h.symm
    | inr i =>
        cases b with
        | inl j =>
            dsimp [realBlockMatrix, complexImMatrix]
            have h := congrArg Complex.im (hHerm j i)
            simpa using h
        | inr j =>
            dsimp [realBlockMatrix, complexReMatrix]
            have h := congrArg Complex.re (hHerm j i)
            simpa using h
  · constructor
    · intro x
      rw [realBlock_quadraticForm]
      exact hLoewner.1 _
    · intro x
      rw [realBlock_one_sub_quadraticForm]
      exact hLoewner.2 _

/--
Finite complex rank-one decomposition of a Hermitian matrix `0 ≤ G ≤ I` by
vectors with coordinatewise norm at most one.
-/
theorem finiteComplexDecomposition
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) :
    HasRealConvexDecomposition (Sum n n) →
    ComplexHermitian G → ComplexLoewnerBetweenZeroAndOne G →
      ∃ (m : ℕ) (_hm : 0 < m) (p : Fin m → ℝ) (ζ : Fin m → n → ℂ),
        (∀ r, 0 ≤ p r) ∧
        (∑ r, p r = 1) ∧
        (∀ r j, ‖ζ r j‖ ≤ 1) ∧
        ∀ j k, G j k = ∑ r, (p r : ℂ) * ζ r j * star (ζ r k) := by
  intro hdecomp hHerm hLoewner
  rcases realBlock_psd_le_one G hHerm hLoewner with ⟨hSym, hBetween⟩
  rcases hdecomp (realBlockMatrix (complexReMatrix G) (complexImMatrix G))
      hSym hBetween with
    ⟨m, hm, p, q, hp, hpsum, hcube, hentry⟩
  let ζ : Fin m → n → ℂ := fun r j =>
    ((q r (Sum.inl j) : ℂ) + (q r (Sum.inr j) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)
  refine ⟨m, hm, p, ζ, hp, hpsum, ?_, ?_⟩
  · intro r j
    exact scaled_complex_norm_le_one _ _ (hcube r (Sum.inl j)) (hcube r (Sum.inr j))
  · intro j k
    apply Complex.ext
    · have hLL := hentry (Sum.inl j) (Sum.inl k)
      have hRR := hentry (Sum.inr j) (Sum.inr k)
      dsimp [realBlockMatrix, complexReMatrix] at hLL hRR
      simp [ζ]
      have hsqrt_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
        rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      ring_nf
      rw [hsqrt_inv_sq]
      ring_nf at hLL hRR ⊢
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [← hLL, ← hRR]
      ring
    · have hIL := hentry (Sum.inr j) (Sum.inl k)
      have hLI := hentry (Sum.inl j) (Sum.inr k)
      dsimp [realBlockMatrix, complexImMatrix] at hIL hLI
      simp [ζ]
      have hsqrt_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
        rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      ring_nf
      rw [hsqrt_inv_sq]
      ring_nf at hIL hLI ⊢
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [← hLI, ← hIL]
      ring

end OlevskiiGram
