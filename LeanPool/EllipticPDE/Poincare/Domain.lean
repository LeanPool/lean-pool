/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Poincare.Fubini


/-!
# Full Poincaré inequality on the domain (dependency-chain step 3)

Average the `n` directional bounds from `poincare_slice_box` to obtain the
domain Poincaré inequality. Each coordinate direction `i` of the box contributes
a bound `∫_Ω u² ≤ c i * ∫_Ω (∂_i u)²`; summing over the `n` directions and
dividing by `n` gives `∫_Ω u² ≤ (1 / n) * ∑_i c i * ∫_Ω (∂_i u)²`. The resulting
constant is the domain constant `C_P` (for equal side lengths `c i = L² / 2` this
is `L² / (2 n)`, matching the diameter-based bound).
-/

@[expose] public section

open MeasureTheory

namespace EllipticPdes.Poincare

/-- The averaging step of the domain Poincaré inequality.

Given `n` bounds of the form `∫_Ω u² ≤ c i * ∫_Ω (d i)²`, one per index `i`,
this returns their average. The family `d : Fin n → α → ℝ` is arbitrary: nothing
here requires `d i` to be a derivative of `u`, `Ω` to be a box or a bounded
domain, or `μ` to be Lebesgue measure. Read on its own this is a statement about
families of real-valued functions.

All the Poincaré content sits in the caller, which supplies `hslice` with
`d i = ∂_i u` and pays for the geometry: `poincare_H01_euclBox` for a coordinate
box, `poincare_H01_of_bounded` for a bounded domain. Cite one of those when
citing the inequality itself. -/
theorem poincare_domain
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Ω : Set α}
    {n : ℕ} (hn : 0 < n) {u : α → ℝ} {d : Fin n → α → ℝ} {c : Fin n → ℝ}
    (hslice : ∀ i, (∫ x in Ω, (u x) ^ 2 ∂μ) ≤ c i * ∫ x in Ω, (d i x) ^ 2 ∂μ) :
    (∫ x in Ω, (u x) ^ 2 ∂μ)
      ≤ (1 / n) * ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set L := ∫ x in Ω, (u x) ^ 2 ∂μ with hL
  have hsum : (n : ℝ) * L ≤ ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := by
    calc (n : ℝ) * L = ∑ _i : Fin n, L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := Finset.sum_le_sum fun i _ => hslice i
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hnpos, mul_comm L (n : ℝ)]
  exact hsum

end EllipticPdes.Poincare
