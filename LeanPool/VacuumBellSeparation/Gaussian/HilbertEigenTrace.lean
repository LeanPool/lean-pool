/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactPositiveEigenbasis
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Power traces and two-basis overlap sums

All formulas concern actual bounded operators and their actual CFC powers.
The extended sums allow infinite traces. An explicit Hilbert eigenbasis is
used in the generic formulas; compact positive operators obtain one from
the preceding construction, rather than from a new spectral assumption.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hilbertEigenbasis_rpow_apply (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, A (b i) = a i • b i) {p : ℝ} (hp : 0 < p) (i : ι) :
    (A ^ p) (b i) = (a i ^ p) • b i := by
  have hi : b i ≠ 0 := by
    intro h
    simpa [h] using b.orthonormal.norm_eq_one i
  exact rpow_apply_eigenvector hA (eigenvalue_mem_real_spectrum hi (ha i)) (ha i) hp

theorem hilbertEigenbasis_sqrt_apply (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, A (b i) = a i • b i) (i : ι) :
    CFC.sqrt A (b i) = Real.sqrt (a i) • b i := by
  rw [CFC.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hilbertEigenbasis_rpow_apply b hA ha (by norm_num) i

theorem positiveTrace_rpow_eq_hilbertEigenvalue_sum (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, A (b i) = a i • b i) {p : ℝ} (hp : 0 < p) :
    positiveTrace (A ^ p) = ∑' i, ENNReal.ofReal (a i ^ p) := by
  rw [positiveTrace_eq_tsum_diagonal b (CFC.rpow_nonneg (a := A) (y := p))]
  apply tsum_congr
  intro i
  change ENNReal.ofReal (RCLike.re (inner ℂ (b i) ((A ^ p) (b i)))) = _
  rw [hilbertEigenbasis_rpow_apply b hA ha hp, inner_smul_right_eq_smul,
    RCLike.smul_re, inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
  simp

/-- Hilbert basis overlap given by `ENNReal.ofReal (‖inner ℂ (b i) (c j)‖ ^ 2)`. -/
def hilbertBasisOverlap (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (i : ι) (j : κ) : ℝ≥0∞ := ENNReal.ofReal (‖inner ℂ (b i) (c j)‖ ^ 2)

omit [CompleteSpace E] in
theorem hilbertBasisOverlap_tsum_left (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) (j : κ) : ∑' i, hilbertBasisOverlap b c i j = 1 := by
  simp only [hilbertBasisOverlap]
  rw [tsum_basis_inner_norm_sq b (c j), c.orthonormal.norm_eq_one]
  norm_num

omit [CompleteSpace E] in
theorem hilbertBasisOverlap_tsum_right (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) (i : ι) : ∑' j, hilbertBasisOverlap b c i j = 1 := by
  have hterm (j : κ) : hilbertBasisOverlap b c i j = hilbertBasisOverlap c b j i := by
    unfold hilbertBasisOverlap
    rw [norm_inner_symm]
  simp only [hterm, hilbertBasisOverlap_tsum_left]

theorem positiveTrace_sandwich_eq_hilbertEigenvalue_overlap
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {a : ι → ℝ} {d : κ → ℝ} (ha₀ : ∀ i, 0 ≤ a i) (hd₀ : ∀ j, 0 ≤ d j)
    (ha : ∀ i, A (b i) = a i • b i) (hd : ∀ j, B (c j) = d j • c j) :
    positiveTrace (CFC.sqrt B * A * CFC.sqrt B) =
      ∑' i, ∑' j, ENNReal.ofReal (a i) * ENNReal.ofReal (d j) *
        hilbertBasisOverlap b c i j := by
  let T := CFC.sqrt A * CFC.sqrt B
  have hT : T.adjoint.comp T = CFC.sqrt B * A * CFC.sqrt B := by
    change star (CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt A * CFC.sqrt B) = _
    rw [star_mul, (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq,
      (CFC.sqrt_nonneg B).isSelfAdjoint.star_eq]
    calc
      _ = CFC.sqrt B * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt B := by noncomm_ring
      _ = _ := by rw [← pow_two, CFC.sq_sqrt A hA]
  have hentry (i : ι) (j : κ) : ‖inner ℂ (b i) (T (c j))‖ ^ 2 =
      a i * d j * ‖inner ℂ (b i) (c j)‖ ^ 2 := by
    dsimp only [T]
    rw [mul_apply_eq_comp, ← adjoint_inner_left,
      (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq,
      hilbertEigenbasis_sqrt_apply b hA ha, hilbertEigenbasis_sqrt_apply c hB hd,
      inner_smul_left_eq_smul, inner_smul_right_eq_smul, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt (ha₀ i), Real.sq_sqrt (hd₀ j)]
    ring
  rw [← hT, positiveTrace_adjoint_comp c T, basisHilbertSchmidtSquare]
  calc
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (T (c j))‖ ^ 2) := by
      exact tsum_congr fun j => (tsum_basis_inner_norm_sq b (T (c j))).symm
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (b i) (T (c j))‖ ^ 2) := tsum_comm
    _ = _ := by
      apply tsum_congr
      intro i
      apply tsum_congr
      intro j
      rw [hentry, ENNReal.ofReal_mul (mul_nonneg (ha₀ i) (hd₀ j)),
        ENNReal.ofReal_mul (ha₀ i)]
      rfl

end VacuumBellSeparation.Gaussian
