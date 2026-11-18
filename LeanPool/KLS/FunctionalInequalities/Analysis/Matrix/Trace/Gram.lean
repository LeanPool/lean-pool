/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Energy
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Trace-Gram coordinates for symmetric three-tensors

For a fully symmetric tensor `T` and a weight matrix `R`, the trace Gram matrix `(tr(R Tᵢ R Tⱼ))ᵢⱼ`
is the
coordinate form of Letwin's tensor term. This module states Letwin arXiv:2607.24164v1 (2.12) in
these coordinates
and derives the pointwise comparison `0 ≤ D`, `4 D ≤ g + 2 tr(B H B H)` used for the energy estimate
(2.14).
All finite dimensions are included; `B` may be singular. The four-sum identity is a private one-use
support.
-/

@[expose] public section

noncomputable section

open Matrix

namespace FunctionalInequalities.Analysis

private theorem tensor_trace_gram_eq_four_sum {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsHermitian)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b)
    (i j : Fin n) :
    (R * (Matrix.of fun a b => T i a b) * R * (Matrix.of fun a b => T j a b)).trace =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        R a c * R b d * T a b i * T c d j := by
  classical
  have hRs (a c : Fin n) : R c a = R a c := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a c) hR.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  rw [trace_mul_mul_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [hRs a c, hT1 i a b, hT2 a i b, hT2 j d c, hT1 j c d, hT2 c j d]
  ring

/--
Letwin's tensor comparison (arXiv:2607.24164v1 (2.12)) written in trace-Gram coordinates: for
positive definite
`H`, symmetric `B` and a fully symmetric tensor `T`, `∑ H⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ) ≤ tr(B H B G)` with
`G = (tr(H⁻¹ Tᵢ H⁻¹ Tⱼ))ᵢⱼ`. -/
theorem letwin_tensor_comparison_trace_gram {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hB : B.IsHermitian) (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
    (∑ i : Fin n,
        ∑ j : Fin n,
          H⁻¹ i j *
            (B * (Matrix.of fun a b => T i a b) * B * (Matrix.of fun a b => T j a b)).trace) ≤
      (B * H * B *
          (Matrix.of fun i j =>
            (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
                (Matrix.of fun a b => T j a b)).trace)).trace := by
  have h := letwin_tensor_comparison H B hH hB T hT1 hT2
  have he :
    (B * H * B *
          (Matrix.of fun i j =>
            (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
                (Matrix.of fun a b => T j a b)).trace)).trace =
      ∑ i : Fin n,
        ∑ j : Fin n,
          (B * H * B) i j *
            ∑ a : Fin n,
              ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
    change
      (∑ i : Fin n,
          ∑ j : Fin n,
            (B * H * B) i j *
              (H⁻¹ * (Matrix.of fun a b => T j a b) * H⁻¹ *
                  (Matrix.of fun a b => T i a b)).trace) =
        _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs :
      (H⁻¹ * (Matrix.of fun a b => T j a b) * H⁻¹ * (Matrix.of fun a b => T i a b)).trace =
        (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ * (Matrix.of fun a b => T j a b)).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (H⁻¹ * (Matrix.of fun a b => T j a b))
          (H⁻¹ * (Matrix.of fun a b => T i a b))
    rw [hs, tensor_trace_gram_eq_four_sum H⁻¹ hH.inv.isHermitian T hT1 hT2 i j]
  rw [he]
  exact h

/--
For positive semidefinite `B`, `W`, positive definite `H` and a fully symmetric tensor `T`, the
trace tensor energy
`D = ∑ H⁻¹ᵢⱼ tr(B Tᵢ B Tⱼ)` satisfies `0 ≤ D` and `4 D ≤ g + 2 tr(B H B H)`, where `g` is the weak
trace density
`2 tr(B H B (-H + H W H + G)) + 2 D`. -/
theorem four_tensor_trace_le_density_add_twice_energy {n : ℕ} (B H W : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hH : H.PosDef) (hW : W.PosSemidef) (T : Fin n → Fin n → Fin n → ℝ)
    (hT1 : ∀ a b c, T a b c = T b a c) (hT2 : ∀ a b c, T a b c = T a c b) :
    let Tm := fun i => Matrix.of fun a b => T i a b
    let G := Matrix.of fun i j => (H⁻¹ * Tm i * H⁻¹ * Tm j).trace
    let D := ∑ i : Fin n, ∑ j : Fin n, H⁻¹ i j * (B * Tm i * B * Tm j).trace
    0 ≤ D ∧
      4 * D ≤
        (2 * (B * H * B * (-H + H * W * H + G)).trace + 2 * D) + 2 * (B * H * B * H).trace := by
  classical
  dsimp only
  have hTm : ∀ i : Fin n, (Matrix.of fun a b => T i a b).IsSymm := by
    intro i
    ext a b
    exact hT2 i b a
  have hD :=
    sum_entry_mul_nonneg hH.inv.posSemidef
      (traceGram_posSemidef B hB (fun i => Matrix.of fun a b => T i a b) hTm)
  change
    0 ≤
      ∑ i : Fin n,
        ∑ j : Fin n,
          H⁻¹ i j *
            (B * (Matrix.of fun a b => T i a b) * B *
                (Matrix.of fun a b => T j a b)).trace at hD
  refine ⟨hD, ?_⟩
  have hC : (B * H * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hH.posSemidef.mul_mul_conjTranspose_same B
  have hM : (H * W * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hW.mul_mul_conjTranspose_same H
  have hA := trace_mul_nonneg hC hM
  have hCompare := letwin_tensor_comparison_trace_gram H B hH hB.isHermitian T hT1 hT2
  have he :
    (B * H * B *
          (-H + H * W * H +
            (Matrix.of fun i j =>
              (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
                  (Matrix.of fun a b => T j a b)).trace))).trace =
      -(B * H * B * H).trace + (B * H * B * (H * W * H)).trace +
        (B * H * B *
            (Matrix.of fun i j =>
              (H⁻¹ * (Matrix.of fun a b => T i a b) * H⁻¹ *
                  (Matrix.of fun a b => T j a b)).trace)).trace := by
    simp only [mul_add, mul_neg, Matrix.trace_add, Matrix.trace_neg]
  rw [he]
  linarith

end FunctionalInequalities.Analysis
