/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.HolderTripleProducts

public section

open MeasureTheory Filter CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- Strong `L³` convergence of two factors, with uniform `L³` bounds,
gives strong `L^(3/2)` convergence of their product. -/
theorem blowup_product_tendsto_LthreeHalves
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : ℕ → α → ℝ) (F G : α → ℝ)
    (hF : MemLp F 3 μ)
    (hG : MemLp G 3 μ)
    (hf : Tendsto (fun k => eLpNorm (fun z => f k z - F z) 3 μ)
      atTop (nhds 0))
    (hg : Tendsto (fun k => eLpNorm (fun z => g k z - G z) 3 μ)
      atTop (nhds 0))
    (hfb : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ k, eLpNorm (f k) 3 μ ≤ B)
    (hgb : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ k, eLpNorm (g k) 3 μ ≤ B) :
    Tendsto (fun k => eLpNorm
      (fun z => f k z * g k z - F z * G z)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  obtain ⟨Bf, hBf, hBfb⟩ := hfb
  obtain ⟨Bg, hBg, hBgb⟩ := hgb
  have hp : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (a := 1) (b := 2) (c := 3)
      (by norm_num) (by norm_num)).2
    norm_num
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hthree : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  have hbound (k : ℕ) :
      eLpNorm (fun z => f k z * g k z - F z * G z)
        (3 / 2 : ℝ≥0∞) μ ≤
      eLpNorm (fun z => f k z - F z) 3 μ * Bg +
        eLpNorm F 3 μ * eLpNorm (fun z => g k z - G z) 3 μ := by
    have hfun : (fun z => f k z * g k z - F z * G z) =
        (fun z => (f k z - F z) * g k z + F z * (g k z - G z)) := by
      funext z
      ring
    rw [hfun]
    have hfk : MemLp (f k) 3 μ := by
      rw [memLp_iff]
      exact lt_of_le_of_lt (hBfb k) hBf
    have hgk : MemLp (g k) 3 μ := by
      rw [memLp_iff]
      exact lt_of_le_of_lt (hBgb k) hBg
    have hfirst : eLpNorm (fun z => (f k z - F z) * g k z)
        (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm (fun z => f k z - F z) 3 μ * eLpNorm (g k) 3 μ := by
      have hh := CKN.Foundation.Measure.eLpNorm_mul_le_three_three
        (hfk.sub hF).aestronglyMeasurable hgk.aestronglyMeasurable
      rw [hcoeff, hthree] at hh
      convert hh using 1
    have hsecond : eLpNorm (fun z => F z * (g k z - G z))
        (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm F 3 μ * eLpNorm (fun z => g k z - G z) 3 μ := by
      have hh := CKN.Foundation.Measure.eLpNorm_mul_le_three_three
        hF.aestronglyMeasurable (hgk.sub hG).aestronglyMeasurable
      rw [hcoeff, hthree] at hh
      convert hh using 1
    calc
      eLpNorm (fun z => (f k z - F z) * g k z + F z * (g k z - G z))
          (3 / 2 : ℝ≥0∞) μ ≤
        eLpNorm (fun z => (f k z - F z) * g k z)
          (3 / 2 : ℝ≥0∞) μ +
        eLpNorm (fun z => F z * (g k z - G z))
          (3 / 2 : ℝ≥0∞) μ := eLpNorm_add_le hp
      _ ≤ eLpNorm (fun z => f k z - F z) 3 μ * Bg +
          eLpNorm F 3 μ * eLpNorm (fun z => g k z - G z) 3 μ := by
        exact add_le_add
          (hfirst.trans (by gcongr; exact hBgb k)) hsecond
  have hright : Tendsto (fun k =>
      eLpNorm (fun z => f k z - F z) 3 μ * Bg +
        eLpNorm F 3 μ * eLpNorm (fun z => g k z - G z) 3 μ)
      atTop (nhds 0) := by
    have h₁ := ENNReal.Tendsto.mul_const hf (Or.inr hBg.ne)
    have h₂ := ENNReal.Tendsto.const_mul hg (Or.inr hF.eLpNorm_lt_top.ne)
    simpa using h₁.add h₂
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hright) ε hε
  filter_upwards [hev] with k hk
  exact (hbound k).trans hk

/-- Each scalar component has no larger `Lᵖ` norm than a vector field. -/
theorem blowup_component_eLpNorm_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ≥0∞) (v : α → Vec3) (hv : AEStronglyMeasurable v μ)
    (i : Fin 3) :
    eLpNorm (fun z => v z i) p μ ≤ eLpNorm v p μ := by
  have hi : AEStronglyMeasurable (fun z => v z i) μ :=
    (continuous_apply i).comp_aestronglyMeasurable hv
  exact eLpNorm_mono hi (fun z => norm_le_pi_norm (v z) i)

/-- Strong local `L³` convergence of velocity gives strong `L^(3/2)`
convergence of each quadratic tensor component. -/
theorem blowup_tensor_component_tendsto_LthreeHalves
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (v : ℕ → α → Vec3) (u : α → Vec3)
    (hu : MemLp u 3 μ)
    (hv : ∀ k, MemLp (v k) 3 μ)
    (hconv : Tendsto (fun k => eLpNorm (fun z => v k z - u z) 3 μ)
      atTop (nhds 0))
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ k, eLpNorm (v k) 3 μ ≤ B)
    (i j : Fin 3) :
    Tendsto (fun k => eLpNorm
      (fun z => v k z i * v k z j - u z i * u z j)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  have hUi : MemLp (fun z => u z i) 3 μ :=
    hu.of_le ((continuous_apply i).comp_aestronglyMeasurable
      hu.aestronglyMeasurable)
      (Eventually.of_forall fun z => norm_le_pi_norm (u z) i)
  have hUj : MemLp (fun z => u z j) 3 μ :=
    hu.of_le ((continuous_apply j).comp_aestronglyMeasurable
      hu.aestronglyMeasurable)
      (Eventually.of_forall fun z => norm_le_pi_norm (u z) j)
  have hconvi : Tendsto (fun k => eLpNorm
      (fun z => v k z i - u z i) 3 μ) atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.mp hconv) ε hε
    filter_upwards [hev] with k hk
    have hsub := (hv k).sub hu
    have hle : eLpNorm (fun z => v k z i - u z i) 3 μ ≤
        eLpNorm (fun z => v k z - u z) 3 μ := by
      convert blowup_component_eLpNorm_le μ 3
        (fun z => v k z - u z) hsub.aestronglyMeasurable i using 1
    exact hle.trans hk
  have hconvj : Tendsto (fun k => eLpNorm
      (fun z => v k z j - u z j) 3 μ) atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.mp hconv) ε hε
    filter_upwards [hev] with k hk
    have hsub := (hv k).sub hu
    have hle : eLpNorm (fun z => v k z j - u z j) 3 μ ≤
        eLpNorm (fun z => v k z - u z) 3 μ := by
      convert blowup_component_eLpNorm_le μ 3
        (fun z => v k z - u z) hsub.aestronglyMeasurable j using 1
    exact hle.trans hk
  obtain ⟨B, hB, hBk⟩ := hbound
  have hbi : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k, eLpNorm (fun z => v k z i) 3 μ ≤ C := by
    refine ⟨B, hB, ?_⟩
    intro k
    exact (blowup_component_eLpNorm_le μ 3 (v k)
      (hv k).aestronglyMeasurable i).trans (hBk k)
  have hbj : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k, eLpNorm (fun z => v k z j) 3 μ ≤ C := by
    refine ⟨B, hB, ?_⟩
    intro k
    exact (blowup_component_eLpNorm_le μ 3 (v k)
      (hv k).aestronglyMeasurable j).trans (hBk k)
  exact blowup_product_tendsto_LthreeHalves μ
    (fun k z => v k z i) (fun k z => v k z j)
    (fun z => u z i) (fun z => u z j)
    hUi hUj hconvi hconvj hbi hbj

end ESS
