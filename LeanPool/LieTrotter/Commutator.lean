/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import LeanPool.LieTrotter.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The commutator-scaling error bound

For `A, B` in a complete normed algebra over `ℝ` with `‖1‖ = 1` and every `n ≥ 1`,

  `‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ ‖AB − BA‖ / (2n) · e^{‖A‖ + ‖B‖}`.

The bound vanishes when `A` and `B` commute. The constant `1/2` is sharp (not proved here): for
small `A, B` the product is `exp (A + B + [A, B]/(2n) + O(1/n²))`. The exponential factor is not
sharp.
Adapted for Lean Pool's module paths and imports from the Apache-2.0 upstream development.

The chain:

* `norm_exp_smul_mul_sub_le`: `‖exp (tA) B − B exp (tA)‖ ≤ t ‖AB − BA‖ e^{t‖A‖}` for `t ≥ 0`,
  from the derivative of `σ ↦ exp (σA) B exp ((t − σ)A)`, which is
  `exp (σA) (AB − BA) exp ((t − σ)A)`;
* `norm_exp_mul_exp_sub_exp_add_le_commutator`: the one-step bound
  `‖exp A exp B − exp (A + B)‖ ≤ ‖AB − BA‖/2 · e^{‖A‖+‖B‖}`. The function
  `H τ = exp ((1 − τ)(A + B)) exp (τA) exp (τB)` runs from `exp (A + B)` to `exp A exp B`, and its
  derivative is `exp ((1 − τ)(A + B)) (exp (τA) B − B exp (τA)) exp (τB)`, of norm at most
  `τ ‖AB − BA‖ e^{‖A‖+‖B‖}`. The mean value inequality against `τ²/2` gives the factor `1/2`;
* `norm_pow_succ_sub_pow_succ_le`: telescoping, `‖Sⁿ⁺¹ − Tⁿ⁺¹‖ ≤ (n + 1) Cⁿ ‖S − T‖` when
  `‖S‖, ‖T‖ ≤ C`;
* `norm_trotter_sub_le_commutator`: the bound above, with `n` steps of size `1/n`.
-/

@[expose] public section

open NormedSpace Set

namespace LieTrotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- `‖exp (t • X)‖ ≤ e^{t ‖X‖}` for `t ≥ 0`. -/
theorem norm_exp_smul_le (X : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • X)‖ ≤ Real.exp (t * ‖X‖) := by
  calc ‖exp (t • X)‖ ≤ Real.exp ‖t • X‖ := norm_exp_le_exp_norm _
    _ = Real.exp (t * ‖X‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

omit [NormOneClass 𝔸] in
/-- The derivative of `σ ↦ exp ((c − σ) • X)` is `-(X * exp ((c − σ) • X))`. -/
theorem hasDerivAt_exp_const_sub_smul (X : 𝔸) (c σ : ℝ) :
    HasDerivAt (fun σ : ℝ => exp ((c - σ) • X)) (-(X * exp ((c - σ) • X))) σ := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (c - σ)).scomp σ
    ((hasDerivAt_id' σ).const_sub c)
  simpa [Function.comp_def] using h

omit [NormOneClass 𝔸] in
/-- The derivative of `σ ↦ exp ((c − σ) • X)`, with `X` on the right. -/
theorem hasDerivAt_exp_const_sub_smul' (X : 𝔸) (c σ : ℝ) :
    HasDerivAt (fun σ : ℝ => exp ((c - σ) • X)) (-(exp ((c - σ) • X) * X)) σ := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (c - σ)).scomp σ
    ((hasDerivAt_id' σ).const_sub c)
  simpa [Function.comp_def] using h

/-- **The commutator with an exponential.** For `t ≥ 0`,
`‖exp (t • A) * B − B * exp (t • A)‖ ≤ t ‖AB − BA‖ e^{t ‖A‖}`. -/
theorem norm_exp_smul_mul_sub_le (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A) * B - B * exp (t • A)‖ ≤ t * ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
  set φ : ℝ → 𝔸 := fun σ => exp (σ • A) * B * exp ((t - σ) • A) with hφ
  have hderiv : ∀ σ : ℝ,
      HasDerivAt φ (exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => exp (σ • A) * B) (exp (σ • A) * A * B) σ :=
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A σ).mul_const B
    have h3 := h1.mul (hasDerivAt_exp_const_sub_smul A t σ)
    convert h3 using 1
    noncomm_ring
  have hbound : ∀ σ ∈ Ico (0 : ℝ) t,
      ‖exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)‖
        ≤ ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := hσ.1
    have hσt : 0 ≤ t - σ := by linarith [hσ.2]
    calc ‖exp (σ • A) * (A * B - B * A) * exp ((t - σ) • A)‖
        ≤ ‖exp (σ • A)‖ * ‖A * B - B * A‖ * ‖exp ((t - σ) • A)‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ Real.exp (σ * ‖A‖) * ‖A * B - B * A‖ * Real.exp ((t - σ) * ‖A‖) := by
          gcongr
          · exact norm_exp_smul_le A hσ0
          · exact norm_exp_smul_le A hσt
      _ = ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by
          rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
          ring_nf
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x _ => (hderiv x).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  have hφt : φ t = exp (t • A) * B := by simp [hφ]
  have hφ0 : φ 0 = B * exp (t • A) := by simp [hφ]
  rw [hφt, hφ0, sub_zero] at hmvt
  calc ‖exp (t • A) * B - B * exp (t • A)‖
      ≤ ‖A * B - B * A‖ * Real.exp (t * ‖A‖) * t := hmvt
    _ = t * ‖A * B - B * A‖ * Real.exp (t * ‖A‖) := by ring

/-- **The one-step bound with the commutator.**
`‖exp A * exp B − exp (A + B)‖ ≤ ‖AB − BA‖ / 2 · e^{‖A‖ + ‖B‖}`. -/
theorem norm_exp_mul_exp_sub_exp_add_le_commutator (A B : 𝔸) :
    ‖exp A * exp B - exp (A + B)‖ ≤ ‖A * B - B * A‖ / 2 * Real.exp (‖A‖ + ‖B‖) := by
  set c := ‖A * B - B * A‖ * Real.exp (‖A‖ + ‖B‖) with hc
  set H : ℝ → 𝔸 := fun τ => exp ((1 - τ) • (A + B)) * (exp (τ • A) * exp (τ • B)) with hH
  set H' : ℝ → 𝔸 := fun τ =>
    exp ((1 - τ) • (A + B)) * ((exp (τ • A) * B - B * exp (τ • A)) * exp (τ • B)) with hH'
  have hderiv : ∀ τ : ℝ, HasDerivAt H (H' τ) τ := by
    intro τ
    have hA := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A τ
    have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B τ
    have h := (hasDerivAt_exp_const_sub_smul' (A + B) 1 τ).mul (hA.mul hB)
    convert h using 1
    simp only [hH', Pi.mul_apply]
    noncomm_ring
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1, ‖H' τ‖ ≤ c * τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    have hE : ‖exp ((1 - τ) • (A + B))‖ ≤ Real.exp ((1 - τ) * (‖A‖ + ‖B‖)) :=
      (norm_exp_smul_le (A + B) h1τ).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le A B) h1τ))
    have hK := norm_exp_smul_mul_sub_le A B hτ0
    have hEB := norm_exp_smul_le B hτ0
    calc ‖H' τ‖
        ≤ ‖exp ((1 - τ) • (A + B))‖
            * (‖exp (τ • A) * B - B * exp (τ • A)‖ * ‖exp (τ • B)‖) := by
          simp only [hH']
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
            * ((τ * ‖A * B - B * A‖ * Real.exp (τ * ‖A‖)) * Real.exp (τ * ‖B‖)) := by
          gcongr
      _ = c * τ := by
          rw [hc]
          have : Real.exp ((1 - τ) * (‖A‖ + ‖B‖)) * (Real.exp (τ * ‖A‖) * Real.exp (τ * ‖B‖))
              = Real.exp (‖A‖ + ‖B‖) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
          calc Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
                * ((τ * ‖A * B - B * A‖ * Real.exp (τ * ‖A‖)) * Real.exp (τ * ‖B‖))
              = τ * ‖A * B - B * A‖ * (Real.exp ((1 - τ) * (‖A‖ + ‖B‖))
                  * (Real.exp (τ * ‖A‖) * Real.exp (τ * ‖B‖))) := by ring
            _ = ‖A * B - B * A‖ * Real.exp (‖A‖ + ‖B‖) * τ := by rw [this]; ring
  -- fence `f τ = H τ − H 0` by `c τ² / 2`
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun τ => H τ - H 0) (f' := H') (a := 0) (b := 1)
    (B := fun τ => c * τ ^ 2 / 2) (B' := fun τ => c * τ)
    (fun x _ => ((hderiv x).sub_const (H 0)).continuousAt.continuousWithinAt)
    (fun x _ => ((hderiv x).sub_const (H 0)).hasDerivWithinAt)
    (by simp)
    (fun x => by
      have := ((hasDerivAt_pow 2 x).const_mul c).div_const 2
      convert this using 1
      push_cast
      ring)
    hbound (x := 1) ⟨zero_le_one, le_rfl⟩
  have hH1 : H 1 = exp A * exp B := by simp [hH]
  have hH0 : H 0 = exp (A + B) := by simp [hH]
  simp only [hH1, hH0] at hfence
  calc ‖exp A * exp B - exp (A + B)‖ ≤ c * 1 ^ 2 / 2 := hfence
    _ = ‖A * B - B * A‖ / 2 * Real.exp (‖A‖ + ‖B‖) := by rw [hc]; ring

/-- **The Lie–Trotter product formula with commutator scaling.** For `n ≥ 1`,
`‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ ‖AB − BA‖ / (2n) · e^{‖A‖ + ‖B‖}`. -/
theorem norm_trotter_sub_le_commutator (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ ‖A * B - B * A‖ / (2 * n) * Real.exp (‖A‖ + ‖B‖) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  push_cast
  set N : ℝ := (m : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  set s := ‖A‖ + ‖B‖ with hs
  set C := Real.exp (N⁻¹ * s) with hC
  have hnorm : ∀ X : 𝔸, ‖N⁻¹ • X‖ = N⁻¹ * ‖X‖ := fun X => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNinv]
  -- the factors
  have hfac : ‖exp (N⁻¹ • A) * exp (N⁻¹ • B)‖ ≤ C := by
    calc ‖exp (N⁻¹ • A) * exp (N⁻¹ • B)‖ ≤ ‖exp (N⁻¹ • A)‖ * ‖exp (N⁻¹ • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp (N⁻¹ * ‖A‖) * Real.exp (N⁻¹ * ‖B‖) :=
          mul_le_mul (norm_exp_smul_le A hNinv) (norm_exp_smul_le B hNinv) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = C := by rw [hC, ← Real.exp_add, hs, mul_add]
  have hfacAB : ‖exp (N⁻¹ • (A + B))‖ ≤ C :=
    (norm_exp_smul_le (A + B) hNinv).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le A B) hNinv))
  have hexpAB : exp (A + B) = exp (N⁻¹ • (A + B)) ^ (m + 1) := by
    rw [exp_pow_eq_exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [show ((m + 1 : ℕ) : ℝ) * N⁻¹ = 1 by push_cast; exact mul_inv_cancel₀ hNpos.ne', one_smul]
  -- the one step
  have hcomm : N⁻¹ • A * (N⁻¹ • B) - N⁻¹ • B * (N⁻¹ • A) = (N⁻¹ * N⁻¹) • (A * B - B * A) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  have hstep : ‖exp (N⁻¹ • A) * exp (N⁻¹ • B) - exp (N⁻¹ • (A + B))‖
      ≤ N⁻¹ * N⁻¹ * ‖A * B - B * A‖ / 2 * C := by
    have h := norm_exp_mul_exp_sub_exp_add_le_commutator (N⁻¹ • A) (N⁻¹ • B)
    rw [hcomm, ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      hnorm, hnorm, ← mul_add] at h
    exact h
  have htel := norm_pow_succ_sub_pow_succ_le hfac hfacAB m
  have hCpow : C ^ m * C = Real.exp s := by
    rw [← pow_succ, hC, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [← mul_assoc, ← hN, mul_inv_cancel₀ hNpos.ne', one_mul]
  calc ‖(exp (N⁻¹ • A) * exp (N⁻¹ • B)) ^ (m + 1) - exp (A + B)‖
      = ‖(exp (N⁻¹ • A) * exp (N⁻¹ • B)) ^ (m + 1) - exp (N⁻¹ • (A + B)) ^ (m + 1)‖ := by
        rw [← hexpAB]
    _ ≤ (m + 1) * C ^ m * ‖exp (N⁻¹ • A) * exp (N⁻¹ • B) - exp (N⁻¹ • (A + B))‖ := htel
    _ ≤ (m + 1) * C ^ m * (N⁻¹ * N⁻¹ * ‖A * B - B * A‖ / 2 * C) := by gcongr
    _ = ‖A * B - B * A‖ / (2 * N) * (C ^ m * C) * (N * N⁻¹) := by rw [← hN]; ring_nf
    _ = ‖A * B - B * A‖ / (2 * N) * Real.exp s := by
        rw [hCpow, mul_inv_cancel₀ hNpos.ne', mul_one]

/-- When `A` and `B` commute, the product formula is exact at every step: the error bound
vanishes. -/
theorem trotter_eq_of_commute {A B : 𝔸} (h : Commute A B) (n : ℕ) (hn : 1 ≤ n) :
    (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n = exp (A + B) := by
  have hb := norm_trotter_sub_le_commutator A B n hn
  rw [h.eq, sub_self, norm_zero, zero_div, zero_mul] at hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

end LieTrotter
