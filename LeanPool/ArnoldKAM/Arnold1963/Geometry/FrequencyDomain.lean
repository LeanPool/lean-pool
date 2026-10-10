/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.CorrectedChart
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyMeasure

/-!
Construct new domains from the selected corrected inverse and prove all buffer inclusions.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric
open scoped NNReal Topology ENNReal
namespace KamProject.Arnold1963

/-- The outer frequency erosion required for the corrected chart construction. -/
def frequencyOuterRadius (Θ β : ℝ≥0) : ℝ≥0 := (5 + Θ) * β
/-- The total frequency erosion budgeting a domain restriction and the corrected chart. -/
def frequencyLossRadius (Θ β b : ℝ≥0) : ℝ≥0 := 2 * Θ * b + frequencyOuterRadius Θ β

/-- The analytic chart, small correction and derivative bounds required for frequency change. -/
structure FrequencyChangeInput {n : ℕ} (A g Δ : ComplexSpace n → ComplexSpace n)
    (G Ω : Set (ComplexSpace n)) (β κ θ Θ : ℝ≥0) : Prop where
  chart : AnalyticFrequencyChart A g G Ω
  radius_pos : 0 < β
  contraction : κ < 1
  lower_pos : 0 < θ
  lower_le_upper : θ ≤ Θ
  lower : ∀ p ∈ G, ∀ v, (θ : ℝ) * ‖v‖ ≤ ‖fderiv ℂ A p v‖
  upper : ∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ Θ
  analytic : AnalyticOnNhd ℂ Δ (erosion G β)
  bounded : NormBoundOn Δ (erosion G β) β
  derivative : ∀ p ∈ erosion G β, ‖fderiv ℂ Δ p‖ ≤ (κ : ℝ) * θ
  conj : ∀ p ∈ erosion G β, Δ (conjVec p) = conjVec (Δ p)

namespace FrequencyChangeInput
variable {n : ℕ} {A g Δ : ComplexSpace n → ComplexSpace n}
  {G Ω : Set (ComplexSpace n)} {β κ θ Θ : ℝ≥0}
  (h : FrequencyChangeInput A g Δ G Ω β κ θ Θ)
include h

/-- The old frequency image of the once-eroded action domain. -/
def oldImage (_ : FrequencyChangeInput A g Δ G Ω β κ θ Θ) : Set (ComplexSpace n) := A '' erosion G β
/-- The corrected inverse chart on the old frequency image. -/
def newInverse : ComplexSpace n → ComplexSpace n := correctedFrequencyInverse g Δ h.oldImage β
/-- The outer eroded frequency domain retained by the corrected chart. -/
def outerFrequency (_ : FrequencyChangeInput A g Δ G Ω β κ θ Θ) : Set (ComplexSpace n) :=
  erosion Ω (frequencyOuterRadius Θ β)
/-- The corrected action domain obtained from the outer frequency domain. -/
def outerDomain : Set (ComplexSpace n) := h.newInverse '' h.outerFrequency
/-- The inner frequency domain with the additional localization loss budget. -/
def innerFrequency (_ : FrequencyChangeInput A g Δ G Ω β κ θ Θ)
    (Ω₀ : Set (ComplexSpace n)) (b : ℝ≥0) := erosion Ω₀ (frequencyLossRadius Θ β b)
/-- The corrected action domain obtained from the inner frequency domain. -/
def innerDomain (Ω₀ : Set (ComplexSpace n)) (b : ℝ≥0) := h.newInverse '' h.innerFrequency Ω₀ b

theorem oldImage_subset : h.oldImage ⊆ Ω := by
  rintro y ⟨p, hp, rfl⟩
  exact h.chart.maps (erosion_subset _ _ hp)

theorem oldInverse_maps : MapsTo g h.oldImage (erosion G β) := by
  rintro y ⟨p, hp, rfl⟩
  rwa [h.chart.left (erosion_subset _ _ hp)]

theorem oldImage_conj : ConjInvariant h.oldImage := by
  rintro y ⟨p, hp, rfl⟩
  exact ⟨conjVec p, star_mem_erosion h.chart.domain_conj hp,
    h.chart.map_conj _ (erosion_subset _ _ hp)⟩

theorem shiftData : FrequencyShiftData (Δ ∘ g) h.oldImage β κ :=
  frequencyShiftData_of_old_inverse h.radius_pos h.contraction h.lower_pos
    (h.chart.inverse_analytic.mono h.oldImage_subset) h.oldInverse_maps h.analytic h.bounded
    (fun _ hx => h.chart.inverse_derivative_le h.lower_pos h.lower (h.oldImage_subset hx))
    h.derivative

theorem outer_subset_target : h.outerFrequency ⊆ frequencyInverseTarget h.oldImage β := by
  have he : frequencyOuterRadius Θ β = Θ * β + (β + β + β + β + β) := by
    unfold frequencyOuterRadius; ring
  change erosion Ω _ ⊆ erosion h.oldImage _
  rw [he, ← erosion_add]
  exact erosion_mono
    (h.chart.erosion_subset_image (h.lower_pos.trans_le h.lower_le_upper) h.upper) _

theorem outer_subset : h.outerDomain ⊆ erosion G β := by
  rintro p ⟨y, hy, rfl⟩
  exact h.oldInverse_maps
    (erosion_subset _ _ (h.shiftData.inverse_spec (h.outer_subset_target hy)).1)

theorem outerChart : AnalyticFrequencyChart (fun p => A p + Δ p) h.newInverse
    h.outerDomain h.outerFrequency :=
  correctedFrequency_chart h.chart h.shiftData h.oldImage_subset h.oldInverse_maps
    (erosion_subset G β) h.analytic h.oldImage_conj h.conj
    (isCompact_erosion h.chart.image_compact _) (fun _ hx => star_mem_erosion h.chart.image_conj hx)
    h.outer_subset_target

theorem new_derivative_bounds {p} (hp : p ∈ h.outerDomain) (v : ComplexSpace n) :
    ((θ : ℝ) * (1 - (κ : ℝ))) * ‖v‖ ≤ ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ∧
      ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ≤ ((Θ : ℝ) * (1 + (κ : ℝ))) * ‖v‖ :=
  frequencyChange_derivative_bounds
    (h.chart.analytic _ (erosion_subset _ _ (h.outer_subset hp))).differentiableAt
    (h.analytic _ (h.outer_subset hp)).differentiableAt h.lower_le_upper
    (h.lower _ (erosion_subset _ _ (h.outer_subset hp)))
    (fun v => ((fderiv ℂ A p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h.upper _ (erosion_subset _ _ (h.outer_subset hp)))
        (norm_nonneg v)))
    (h.derivative _ (h.outer_subset hp)) v

theorem new_upper {p} (hp : p ∈ h.outerDomain) :
    ‖fderiv ℂ (fun x => A x + Δ x) p‖ ≤ (2 : ℝ) * Θ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (h.new_derivative_bounds hp v).2.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  have hk : (κ : ℝ) < 1 := h.contraction
  nlinarith [Θ.coe_nonneg]

theorem new_upper_sharp {p} (hp : p ∈ h.outerDomain) :
    ‖fderiv ℂ (fun x => A x + Δ x) p‖ ≤ (Θ : ℝ) * (1 + (κ : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun v => (h.new_derivative_bounds hp v).2)

theorem new_lower_pos : 0 < (θ : ℝ) * (1 - (κ : ℝ)) :=
  mul_pos h.lower_pos (sub_pos.mpr h.contraction)

theorem inner_subset_buffer {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    h.innerFrequency Ω₀ b ⊆ erosion h.outerFrequency ((2 * Θ) * b) := by
  change erosion Ω₀ _ ⊆ erosion (erosion Ω _) _
  rw [erosion_add]
  have he : frequencyLossRadius Θ β b = frequencyOuterRadius Θ β + (2 * Θ) * b := by
    unfold frequencyLossRadius; ring
  rw [← he]
  exact erosion_mono hΩ₀ _

theorem inner_subset_outerFrequency {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    h.innerFrequency Ω₀ b ⊆ h.outerFrequency :=
  (h.inner_subset_buffer hΩ₀ b).trans (erosion_subset _ _)

theorem inner_subset_outerDomain {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    h.innerDomain Ω₀ b ⊆ h.outerDomain := image_mono (h.inner_subset_outerFrequency hΩ₀ b)

theorem innerChart {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (hc : IsCompact Ω₀)
    (hj : ConjInvariant Ω₀) (b : ℝ≥0) :
    AnalyticFrequencyChart (fun p => A p + Δ p) h.newInverse
      (h.innerDomain Ω₀ b) (h.innerFrequency Ω₀ b) :=
  h.outerChart.restrict (h.inner_subset_outerFrequency hΩ₀ b) (isCompact_erosion hc _)
    (fun _ hx => star_mem_erosion hj hx)

theorem inner_subset_erosion {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    h.innerDomain Ω₀ b ⊆ erosion h.outerDomain b := by
  rintro p ⟨y, hy, rfl⟩
  exact h.outerChart.inverse_maps_erosion (show (0 : ℝ≥0) < 2 * Θ by
    exact mul_pos (by norm_num) (h.lower_pos.trans_le h.lower_le_upper))
    (fun _ hp => h.new_upper hp) (h.inner_subset_buffer hΩ₀ b hy)

theorem neighborhood_subset {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    closedBallNeighborhood (h.innerDomain Ω₀ b) b ⊆ h.outerDomain := by
  rintro p ⟨q, hq, hpq⟩
  exact h.inner_subset_erosion hΩ₀ b hq hpq

theorem neighborhood_maps {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    MapsTo (fun p => A p + Δ p) (closedBallNeighborhood (h.innerDomain Ω₀ b) b) Ω₀ := by
  rintro p ⟨q, ⟨y, hy, rfl⟩, hpq⟩
  have hq : h.newInverse y ∈ h.innerDomain Ω₀ b := ⟨y, hy, rfl⟩
  have hb : closedBall (h.newInverse y) (b : ℝ) ⊆ h.outerDomain := h.inner_subset_erosion hΩ₀ b hq
  have hseg := (convex_closedBall (h.newInverse y) (b : ℝ)).segment_subset
    (mem_closedBall_self b.coe_nonneg) hpq
  have he : A (h.newInverse y) + Δ (h.newInverse y) = y :=
    h.outerChart.right (h.inner_subset_outerFrequency hΩ₀ b hy)
  apply hy
  change dist (A p + Δ p) y ≤ (frequencyLossRadius Θ β b : ℝ)
  have hn := norm_sub_le_of_analytic_segment_bound (hseg.trans hb) h.outerChart.analytic
    (show NormBoundOn (fderiv ℂ (fun x => A x + Δ x)) h.outerDomain (2 * Θ) from
      ⟨by positivity, fun _ hx => h.new_upper hx⟩)
  rw [he] at hn
  calc
    _ ≤ (2 * (Θ : ℝ)) * dist p (h.newInverse y) := by simpa only [dist_eq_norm] using hn
    _ ≤ (2 * (Θ : ℝ)) * b := mul_le_mul_of_nonneg_left hpq (by positivity)
    _ ≤ _ := le_add_of_nonneg_right (frequencyOuterRadius Θ β).coe_nonneg

theorem old_image_covers_inner_erosion {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (b : ℝ≥0) :
    erosion (h.innerFrequency Ω₀ b) β ⊆ A '' h.innerDomain Ω₀ b := by
  intro y hy
  have hyi := erosion_subset _ _ hy
  have hyt := h.outer_subset_target (h.inner_subset_outerFrequency hΩ₀ b hyi)
  have hyV : y ∈ h.oldImage := erosion_subset _ _ hyt
  have hys : y ∈ frequencyInverseSource h.oldImage β :=
    erosion_antitone_radius _ (by
      exact (show β + β + β ≤ β + β + β + β from le_self_add).trans le_self_add) hyt
  have hTy : frequencyShift (Δ ∘ g) y ∈ h.innerFrequency Ω₀ b := by
    apply hy
    simpa [frequencyShift, dist_eq_norm] using h.shiftData.bounded.norm_le hyV
  refine ⟨g y, ?_, h.chart.right (h.oldImage_subset hyV)⟩
  refine ⟨frequencyShift (Δ ∘ g) y, hTy, ?_⟩
  change g (invFunOn (frequencyShift (Δ ∘ g)) (frequencyInverseSource h.oldImage β)
    (frequencyShift (Δ ∘ g) y)) = g y
  rw [h.shiftData.shift_injOn.leftInvOn_invFunOn hys]

theorem measure_loss {Ω₀ : Set (ComplexSpace n)} (hΩ₀ : Ω₀ ⊆ Ω) (hc : IsCompact Ω₀) (b : ℝ≥0) :
    realVolume (G \ h.innerDomain Ω₀ b) ≤ ENNReal.ofReal ((θ : ℝ)⁻¹ ^ n) *
      realVolume (Ω \ erosion Ω₀ (frequencyLossRadius Θ β b + β)) := by
  have hi : h.innerDomain Ω₀ b ⊆ G :=
    (h.inner_subset_outerDomain hΩ₀ b).trans (h.outer_subset.trans (erosion_subset _ _))
  apply h.chart.realVolume_loss_le hi (isCompact_erosion hc _).isClosed.measurableSet
    _ h.lower_pos h.lower
  rw [← erosion_add]
  exact h.old_image_covers_inner_erosion hΩ₀ b

end FrequencyChangeInput
end KamProject.Arnold1963
