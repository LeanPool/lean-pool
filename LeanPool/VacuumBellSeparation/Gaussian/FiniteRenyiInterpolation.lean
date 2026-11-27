/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteHilbertSchmidtDual

/-!
# The actual finite sandwiched Renyi interpolation comparison

For strictly positive finite matrices with Tr(rho)<=1, genuine entire
spectral powers, actual Schatten Holder boundary bounds, and Hadamard
three-lines prove Q_2 <= Q_r^(1/(r-1)), r>=2. The normalized dual matrix
is constructed from the actual middle sandwich. Empty index types are
handled separately. No infinite spectral-compression limit is claimed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Set
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_sandwichedRenyi_interpolation {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρt : ρ.trace.re ≤ 1) {r : ℝ} (hr : 2 ≤ r) :
    ((finiteRenyiSandwich ρ σ (1 / 2)) ^ (2 : ℝ)).trace.re ≤
      ((finiteRenyiSandwich ρ σ ((r - 1) / r)) ^ r).trace.re ^ (1 / (r - 1)) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let : IsEmpty ι := hi
    rw [Matrix.trace_eq_zero_of_isEmpty, Complex.zero_re]
    exact Real.rpow_nonneg (real_trace_positive_rpow_nonneg
      (finiteRenyiSandwich_posDef hρ hσ _) r) _
  | inr hi =>
    let : Nonempty ι := hi
    let τ : ℝ := (r - 1) / r
    let q : ℝ := r / (r - 1)
    let θ : ℝ := r / (2 * (r - 1))
    let A := finiteRenyiSandwich ρ σ (1 / 2)
    have hr₀ : 0 < r := by linarith
    have hr₁ : 0 < r - 1 := by linarith
    have hτq : 2 * τ * q = 2 := by
      dsimp only [τ, q]
      field_simp [hr₀.ne', hr₁.ne']
    have hτθ : 2 * τ * θ = 1 := by
      dsimp only [τ, θ]
      field_simp [hr₀.ne', hr₁.ne']
    have hθ : θ ∈ Icc (0 : ℝ) 1 := by
      refine ⟨(div_pos hr₀ (mul_pos (by norm_num) hr₁)).le, ?_⟩
      dsimp only [θ]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hr₁)).mpr
      nlinarith
    have hpq : r.HolderConjugate q := by
      apply Real.holderConjugate_iff.mpr
      refine ⟨by linarith, ?_⟩
      dsimp only [q]
      field_simp [hr₀.ne', hr₁.ne']; ring
    have hA : A.PosDef := finiteRenyiSandwich_posDef hρ hσ _
    have hd := finiteRenyi_dual_interpolation hρ hσ (finiteHilbertSchmidtDual_posDef hA)
      hpq hτq hθ hτθ (finiteHilbertSchmidtDual_square_trace hA)
    rw [norm_trace_finiteHilbertSchmidtDual_mul hA] at hd
    have hρ₀ : 0 ≤ ρ.trace.re := by
      simpa only [CFC.rpow_one ρ hρ.posSemidef.nonneg] using real_trace_positive_rpow_nonneg hρ 1
    have hNr : 0 ≤ ((finiteRenyiSandwich ρ σ τ) ^ r).trace.re :=
      real_trace_positive_rpow_nonneg (finiteRenyiSandwich_posDef hρ hσ τ) r
    have hsimple : Real.sqrt ((A ^ (2 : ℝ)).trace.re) ≤
        ((finiteRenyiSandwich ρ σ τ) ^ r).trace.re ^ (θ / r) := by
      have hcρ : ρ.trace.re ^ (1 - θ) ≤ 1 :=
        Real.rpow_le_one hρ₀ hρt (sub_nonneg.mpr hθ.2)
      have hb := mul_le_mul_of_nonneg_right hcρ (Real.rpow_nonneg hNr (θ / r))
      exact hd.trans (by simpa only [one_mul] using hb)
    calc
      _ = (Real.sqrt ((A ^ (2 : ℝ)).trace.re)) ^ 2 :=
        (Real.sq_sqrt (real_trace_positive_square_pos hA).le).symm
      _ ≤ (((finiteRenyiSandwich ρ σ τ) ^ r).trace.re ^ (θ / r)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsimple 2
      _ = _ := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hNr]
        congr 1
        dsimp only [θ]
        field_simp [hr₀.ne', hr₁.ne']; ring

end VacuumBellSeparation.Gaussian
