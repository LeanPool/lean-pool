/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.SliceEnergy
public import LeanPool.CIVAxisymmetric.Comparison.Direct.EnergyRepresentation
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality
public import LeanPool.CIVAxisymmetric.Comparison.ComparisonLimits
public import LeanPool.CIVAxisymmetric.Comparison.CommutatorL2SqNonneg

/-!
# The Grönwall bound for the comparison energy at fixed mollification

This is `eq:aniso:comparison:positive:energy` integrated in time, followed by Grönwall's
inequality, at a fixed mollification radius `ε` and barrier slope `σ`. On a working interval
`[τ₀, b] ⊆ I` starting at a reference time `τ₀` of the mollified equation at which the mollified
slice lies below `M`, the energy `E(τ) = ∫ G(q_ε(x, τ) - Ψ_σ(x, τ)) dx` satisfies, for almost every
`τ ∈ [τ₀, b]` and every `δ > 0`,

`E(τ) ≤ (δ |B_R| (b - τ₀) + (4δ)⁻¹ ∫_{τ₀}^b ‖R_ε(s)‖²_{L²(B_R)} ds) e^{Λ (b - τ₀)}`,

with `R = Mq / σ` the radius outside which the excess is negative. The `δ`-splitting
`|R_ε| ≤ δ + R_ε² / (4δ)` replaces the Cauchy–Schwarz step of the manuscript and leads to the same
conclusion as `ε ↓ 0` (the commutator term tends to zero, `CIV.tendsto_integral_commutatorL2Sq`).

The time regularity used is exactly the one the manuscript's representative provides: the energy
agrees at almost every time with the primitive `P(τ) = ∫_{τ₀}^τ ∫ G'(w)(H - ∂_τΨ_σ) dx ds`
(`CIV.ae_ae_comparisonProfile_eq_intervalIntegral` and Fubini), and Grönwall is applied to the
continuous function `P`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-- A property holding almost everywhere on a measurable set holds on a measurable subset of full
measure. -/
theorem exists_measurableSet_subset_forall_of_ae {J : Set ℝ} (hJ : MeasurableSet J)
    {P : ℝ → Prop} (h : ∀ᵐ s ∂(volume.restrict J), P s) :
    ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ J ∧ (∀ s ∈ T, P s) ∧ volume (J \ T) = 0 := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨J \ N, hJ.diff hNm, sdiff_subset, fun s hs => ?_, ?_⟩
  · by_contra hPs
    exact hs.2 (hNsub hPs)
  · rw [Measure.restrict_apply hNm] at hN0
    have hsub : J \ (J \ N) ⊆ N ∩ J := fun s hs => ⟨not_not.mp fun h => hs.2 ⟨hs.1, h⟩, hs.1⟩
    exact measure_mono_null hsub hN0

theorem abs_le_add_sq_div {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : |r| ≤ δ + r ^ 2 / (4 * δ) := by
  have hsq : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have h4 : 0 < 4 * δ := by positivity
  rw [hsq, ← sub_nonneg]
  have key : δ + |r| ^ 2 / (4 * δ) - |r| = (|r| - 2 * δ) ^ 2 / (4 * δ) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (sq_nonneg _) h4.le

/-- The `δ`-splitting of the commutator term against a weight with values in `[0, 1]` supported
in a closed ball. -/
theorem integral_mul_abs_le_of_support {f R : Vec m → ℝ} {ρ δ Cr : ℝ} (hδ : 0 < δ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hfs : ∀ x, x ∉ Metric.closedBall (0 : Vec m) ρ → f x = 0)
    (hRm : AEStronglyMeasurable R volume) (hRb : ∀ᵐ x ∂volume, |R x| ≤ Cr) :
    ∫ x, f x * |R x| ≤ δ * (volume (Metric.closedBall (0 : Vec m) ρ)).toReal
      + (1 / (4 * δ)) * ∫ x in Metric.closedBall (0 : Vec m) ρ, R x ^ 2 := by
  set Bl := Metric.closedBall (0 : Vec m) ρ with hBl
  have hfin : volume Bl ≠ ⊤ := measure_closedBall_lt_top.ne
  have hR2 : IntegrableOn (fun x => R x ^ 2) Bl volume :=
    Measure.integrableOn_of_bounded (M := Cr ^ 2) hfin (hRm.pow 2)
      (ae_restrict_of_ae (hRb.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2))
  have hconst : IntegrableOn (fun _ : Vec m => δ) Bl volume := integrableOn_const hfin
  have hg : IntegrableOn (fun x => δ + R x ^ 2 / (4 * δ)) Bl volume :=
    hconst.add (hR2.div_const _)
  have hle : ∀ x, f x * |R x| ≤ Bl.indicator (fun x => δ + R x ^ 2 / (4 * δ)) x := by
    intro x
    by_cases hx : x ∈ Bl
    · rw [indicator_of_mem hx]
      calc f x * |R x| ≤ 1 * |R x| := mul_le_mul_of_nonneg_right (hf1 x) (abs_nonneg _)
        _ = |R x| := one_mul _
        _ ≤ δ + R x ^ 2 / (4 * δ) := abs_le_add_sq_div hδ (R x)
    · rw [indicator_of_notMem hx, hfs x hx, zero_mul]
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg (hf0 x) (abs_nonneg (R x)))
    (hg.integrable_indicator measurableSet_closedBall) (Eventually.of_forall hle)
  rw [integral_indicator measurableSet_closedBall] at hmono
  rw [integral_add hconst (hR2.div_const _)] at hmono
  rw [setIntegral_const] at hmono
  rw [integral_div] at hmono
  have hsmul : volume.real Bl • δ = δ * (volume Bl).toReal := by
    rw [smul_eq_mul, Measure.real, mul_comm]
  rw [hsmul] at hmono
  have hdiv : (∫ x in Bl, R x ^ 2) / (4 * δ) = 1 / (4 * δ) * ∫ x in Bl, R x ^ 2 := by ring
  linarith only [hmono, hdiv]

end CIV
