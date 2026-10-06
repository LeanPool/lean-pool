/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTensorConvergence
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureRemainder

public section

open MeasureTheory Filter Set CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- The fixed pressure decomposition holds throughout each bounded past
cylinder once that cylinder fits inside the rescaled source domain. -/
theorem blowup_pressure_split_eventually_pastBox
    (p p₁ : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) :
    ∀ᶠ k in atTop, ∀ z ∈ vec3Ball 0 R ×ˢ Ioo a 0,
      blowupPressure x₀ t₀ (r k) p z =
        blowupRieszPressure x₀ t₀ (r k) p₁ z +
          blowupPressureRemainder x₀ t₀ (r k) p p₁ z := by
  have hsubset := blowupCylinder_eventually_subset_domain
    x₀ t₀ R a r hx₀ ht₀ hr hr0
  filter_upwards [hsubset] with k hk z hz
  exact blowupPressure_eq_riesz_add_remainder_of_mem
    x₀ t₀ (r k) p p₁ z (hk hz)

/-- Convergence of the whole-space pressure and vanishing of the harmonic
remainder give convergence of their sum on a fixed cylinder. -/
theorem blowup_pressure_tendsto_of_split
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p p₁ p₂ : ℕ → α → ℝ) (q : α → ℝ)
    (hsplit : ∀ᶠ k in atTop, p k =ᵐ[μ] fun z => p₁ k z + p₂ k z)
    (h₁ : Tendsto (fun k => eLpNorm (fun z => p₁ k z - q z)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0))
    (h₂ : Tendsto (fun k => eLpNorm (p₂ k)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun z => p k z - q z)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  have hp : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
      (by norm_num) (by norm_num)).2
    norm_num
  have hbound : ∀ᶠ k in atTop,
      eLpNorm (fun z => p k z - q z) (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm (fun z => p₁ k z - q z) (3 / 2 : ℝ≥0∞) μ +
          eLpNorm (p₂ k) (3 / 2 : ℝ≥0∞) μ := by
    filter_upwards [hsplit] with k hk
    have hfun : (fun z => p k z - q z) =ᵐ[μ]
        fun z => (p₁ k z - q z) + p₂ k z := by
      filter_upwards [hk] with z hz
      simp only [hz]
      ring
    rw [eLpNorm_congr_ae hfun]
    exact eLpNorm_add_le hp
  have hsum : Tendsto (fun k =>
      eLpNorm (fun z => p₁ k z - q z) (3 / 2 : ℝ≥0∞) μ +
        eLpNorm (p₂ k) (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0) := by
    simpa using h₁.add h₂
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hsum) ε hε
  filter_upwards [hbound, hev] with k hk hke
  exact hk.trans hke

/-- A uniformly bounded whole-space pressure and a vanishing remainder give
an eventual local bound for the full pressure. -/
theorem blowup_pressure_eventually_bounded_of_split
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p p₁ p₂ : ℕ → α → ℝ)
    (hsplit : ∀ᶠ k in atTop, p k =ᵐ[μ] fun z => p₁ k z + p₂ k z)
    (h₁ : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ k in atTop, eLpNorm (p₁ k) (3 / 2 : ℝ≥0∞) μ ≤ B)
    (h₂ : Tendsto (fun k => eLpNorm (p₂ k) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0)) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ k in atTop, eLpNorm (p k) (3 / 2 : ℝ≥0∞) μ ≤ B := by
  obtain ⟨B, hB, hBound⟩ := h₁
  have hp : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
      (by norm_num) (by norm_num)).2
    norm_num
  have hsmall : ∀ᶠ k in atTop,
      eLpNorm (p₂ k) (3 / 2 : ℝ≥0∞) μ ≤ 1 :=
    (ENNReal.tendsto_nhds_zero.mp h₂) 1 (by norm_num)
  refine ⟨B + 1, ENNReal.add_lt_top.mpr ⟨hB, by norm_num⟩, ?_⟩
  filter_upwards [hsplit, hBound, hsmall] with k hk hbk hsk
  calc
    eLpNorm (p k) (3 / 2 : ℝ≥0∞) μ =
        eLpNorm (fun z => p₁ k z + p₂ k z) (3 / 2 : ℝ≥0∞) μ :=
      eLpNorm_congr_ae hk
    _ ≤ eLpNorm (p₁ k) (3 / 2 : ℝ≥0∞) μ +
          eLpNorm (p₂ k) (3 / 2 : ℝ≥0∞) μ := eLpNorm_add_le hp
    _ ≤ B + 1 := add_le_add hbk hsk

/-- Once the whole-space pressure converges, the original rescaled pressure
has the same strong local `L^(3/2)` limit. -/
theorem blowupPressure_tendsto_of_riesz
    (p p₁ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (q : ParabolicPoint → ℝ)
    (h₁ : Tendsto (fun k => eLpNorm
      (fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z - q z)
      (3 / 2 : ℝ≥0∞)
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0))) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun z => blowupPressure x₀ t₀ (r k) p z - q z)
      (3 / 2 : ℝ≥0∞)
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0))) atTop (nhds 0) := by
  let C := vec3Ball 0 R ×ˢ Ioo a 0
  have hsplit := blowup_pressure_split_eventually_pastBox
    p p₁ x₀ t₀ r hx₀ ht₀ hr hr0 R a
  have hsplitAE : ∀ᶠ k in atTop,
      blowupPressure x₀ t₀ (r k) p =ᵐ[volume.restrict C]
        fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z +
          blowupPressureRemainder x₀ t₀ (r k) p p₁ z := by
    filter_upwards [hsplit] with k hk
    filter_upwards [ae_restrict_mem (by
      exact (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo)] with z hz
    exact hk z hz
  exact blowup_pressure_tendsto_of_split (volume.restrict C)
    (fun k => blowupPressure x₀ t₀ (r k) p)
    (fun k => blowupRieszPressure x₀ t₀ (r k) p₁)
    (fun k => blowupPressureRemainder x₀ t₀ (r k) p p₁)
    q hsplitAE h₁
    (blowupPressureRemainder_eLpNorm_tendsto_zero_pastBox
      p p₁ hp₂ hharm x₀ t₀ r hx₀ hr hr0 R a hR ha)

end ESS
