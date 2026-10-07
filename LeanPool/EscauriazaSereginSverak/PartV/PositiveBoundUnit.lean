/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundScaling
public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundSource
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceWeak

/-!
# Rescaled data on the unit cylinder

Fix a Leray–Hopf solution on ℝ³ × (0, T), a point x₀, a time
0 < t₀ ≤ T and a radius R with R² ≤ t₀. The parabolic rescaling
u_R(y, s) = R u(x₀ + R y, t₀ + R² s) places the cylinder
B_R(x₀) × (t₀ - R², t₀), which may end at the terminal time T, onto the
unit cylinder B₁ × (-1, 0). This file proves the measurability, energy,
slice, pressure and weak-gradient hypotheses of `thm:ess-local` for the
rescaled fields, as used in the proof of `lem:pv-positive-bound`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The unit cylinder lies in the rescaled slab. -/
theorem pv_unit_subset_rescaled_slab {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) :
    spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) ⊆
      CKN.scalingParabolic R (x₀, t₀) ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
  intro z hz
  have hs := hz.2
  have hR2 : 0 < R ^ 2 := by positivity
  have h1 : R ^ 2 * (-1) < R ^ 2 * z.2 := mul_lt_mul_of_pos_left hs.1 hR2
  have h2 : R ^ 2 * z.2 < R ^ 2 * 0 := mul_lt_mul_of_pos_left hs.2 hR2
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · change 0 < t₀ + R ^ 2 * z.2
    linarith only [h1, hlow]
  · change t₀ + R ^ 2 * z.2 < T
    linarith only [h2, hup]

/-- The unit time interval lies in the rescaled time interval. -/
theorem pv_unit_time_subset_rescaled {T t₀ R : ℝ} (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) :
    Ioo (-1 : ℝ) 0 ⊆ CKN.rescaledTime R t₀ (Ioo 0 T) := by
  intro s hs
  have hz : ((0 : Vec3), s) ∈ spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) := by
    refine ⟨?_, hs⟩
    simp [vec3EuclideanNorm_zero]
  exact (pv_unit_subset_rescaled_slab 0 hR hlow hup hz).2

/-- A field that is almost everywhere strongly measurable on the slab rescales
to one that is almost everywhere strongly measurable on the unit cylinder. -/
theorem pv_unit_aestronglyMeasurable_comp {E : Type} [TopologicalSpace E]
    {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R) (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T)
    {f : ParabolicPoint → E}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    AEStronglyMeasurable (f ∘ CKN.scalingParabolic R (x₀, t₀))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) :=
  (pv_aestronglyMeasurable_comp_scalingParabolic R hR (x₀, t₀) hf).mono_measure
    (Measure.restrict_mono (pv_unit_subset_rescaled_slab x₀ hR hlow hup) le_rfl)

/-- Slice bounds of a homogeneous nonnegative functional pass to the unit
ball under rescaling. -/
theorem pv_unit_slice_essSup_le {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) (g : ParabolicPoint → Vec3)
    (Φ : Vec3 → ℝ≥0∞) {c K : ℝ≥0∞} (hc : c ≠ ⊤)
    (hΦ : ∀ v : Vec3, Φ (R • v) = c * Φ v)
    (hK : ∀ᵐ τ ∂volume.restrict (Ioo 0 T), ∫⁻ y : Vec3, Φ (g (y, τ)) ≤ K) :
    essSup (fun s : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        Φ (CKN.rescaleVelocity R (x₀, t₀) g (x, s)))
      (volume.restrict (Ioo (-1) 0)) ≤ c * (ENNReal.ofReal (R⁻¹ ^ 3) * K) := by
  refine essSup_le_of_ae_le _ ?_
  have hpull := blowup_ae_time_pullback_on R t₀ hR (Ioo 0 T) (Ioo (-1) 0)
    measurableSet_Ioo (pv_unit_time_subset_rescaled hR hlow hup) _ hK
  filter_upwards [hpull] with s hs
  have hspace := pv_lintegral_scalingSpace R hR x₀ Set.univ
    (fun y => Φ (g (y, CKN.scalingTime R t₀ s)))
  simp only [Set.preimage_univ, Measure.restrict_univ] at hspace
  calc
    (∫⁻ x in vec3Ball (0 : Vec3) 1, Φ (CKN.rescaleVelocity R (x₀, t₀) g (x, s)))
        ≤ ∫⁻ x : Vec3, Φ (CKN.rescaleVelocity R (x₀, t₀) g (x, s)) :=
          setLIntegral_le_lintegral _ _
    _ = ∫⁻ x : Vec3, c * Φ (g (CKN.scalingSpace R x₀ x, CKN.scalingTime R t₀ s)) := by
          apply lintegral_congr
          intro x
          exact hΦ _
    _ = c * ∫⁻ x : Vec3, Φ (g (CKN.scalingSpace R x₀ x, CKN.scalingTime R t₀ s)) :=
          lintegral_const_mul' _ _ hc
    _ = c * (ENNReal.ofReal (R⁻¹ ^ 3) *
          ∫⁻ y : Vec3, Φ (g (y, CKN.scalingTime R t₀ s))) := by rw [hspace]
    _ ≤ c * (ENNReal.ofReal (R⁻¹ ^ 3) * K) := by gcongr

/-- The rescaled velocity has essentially bounded L² norms on the unit
ball. -/
theorem pv_unit_L2_essSup_lt_top {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    (hL2 : essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    essSup (fun s : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ‖CKN.rescaleVelocity R (x₀, t₀) u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤ := by
  have hΦ : ∀ v : Vec3, ‖R • v‖ₑ ^ (2 : ℝ) = ‖R‖ₑ ^ (2 : ℝ) * ‖v‖ₑ ^ (2 : ℝ) := by
    intro v
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hle := pv_unit_slice_essSup_le x₀ hR hlow hup u (fun v => ‖v‖ₑ ^ (2 : ℝ))
    (c := ‖R‖ₑ ^ (2 : ℝ)) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
    hΦ (ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)))
  refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top hL2))
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top

/-- The rescaled velocity has essentially bounded critical L³ norms on the
unit ball. -/
theorem pv_unit_L3_essSup_lt_top {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    essSup (fun s : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm
          (CKN.rescaleVelocity R (x₀, t₀) u (x, s))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤ := by
  have hΦ : ∀ v : Vec3, ENNReal.ofReal (vec3EuclideanNorm (R • v)) ^ (3 : ℝ) =
      ENNReal.ofReal R ^ (3 : ℝ) * ENNReal.ofReal (vec3EuclideanNorm v) ^ (3 : ℝ) := by
    intro v
    rw [vec3EuclideanNorm_smul, abs_of_pos hR, ENNReal.ofReal_mul hR.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hle := pv_unit_slice_essSup_le x₀ hR hlow hup u
    (fun v => ENNReal.ofReal (vec3EuclideanNorm v) ^ (3 : ℝ))
    (c := ENNReal.ofReal R ^ (3 : ℝ))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    hΦ (ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)))
  refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top hL3))
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- The rescaled velocity and gradient have finite energy on the unit
cylinder. -/
theorem pv_unit_energy_lt_top {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hEnergy : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖CKN.rescaleVelocity R (x₀, t₀) u z‖ₑ ^ (2 : ℝ) +
        ‖CKN.rescaleGradient R (x₀, t₀) Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let e := CKN.scalingParabolic R (x₀, t₀)
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
  let a : ℝ≥0∞ := ‖R‖ₑ ^ (2 : ℝ)
  let b : ℝ≥0∞ := ‖R ^ 2‖ₑ ^ (2 : ℝ)
  have ha : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  have hb : b ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  have hpoint : ∀ z : ParabolicPoint,
      ‖CKN.rescaleVelocity R (x₀, t₀) u z‖ₑ ^ (2 : ℝ) +
          ‖CKN.rescaleGradient R (x₀, t₀) Du z‖ₑ ^ (2 : ℝ) ≤ (a + b) * G (e z) := by
    intro z
    have hv : CKN.rescaleVelocity R (x₀, t₀) u z = R • u (e z) := rfl
    have hD : CKN.rescaleGradient R (x₀, t₀) Du z = (R ^ 2) • Du (e z) := rfl
    rw [hv, hD, enorm_smul, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_add]
    exact add_le_add (mul_le_mul_left le_self_add _) (mul_le_mul_left le_add_self _)
  have hsub := pv_unit_subset_rescaled_slab x₀ hR hlow hup
  calc
    (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖CKN.rescaleVelocity R (x₀, t₀) u z‖ₑ ^ (2 : ℝ) +
        ‖CKN.rescaleGradient R (x₀, t₀) Du z‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ z in e ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            (a + b) * G (e z) :=
          (lintegral_mono_set hsub).trans (lintegral_mono hpoint)
    _ = (a + b) * (ENNReal.ofReal (R⁻¹ ^ 5) *
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), G z) := by
          rw [lintegral_const_mul' _ _ (ENNReal.add_ne_top.mpr ⟨ha, hb⟩),
            pv_lintegral_scalingParabolic R hR (x₀, t₀) _ G]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ha.lt_top, hb.lt_top⟩)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEnergy)

/-- The rescaled velocity has a weak spatial gradient on almost every slice of
the unit cylinder. -/
theorem pv_unit_weakGradient {T t₀ R : ℝ} (x₀ : Vec3) (hR : 0 < R)
    (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hU : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hGrad : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, s) i) (fun x => Du (x, s) i)) :
    ∀ᵐ s ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => CKN.rescaleVelocity R (x₀, t₀) u (x, s) i)
        (fun x => CKN.rescaleGradient R (x₀, t₀) Du (x, s) i) := by
  have hUprod : AEStronglyMeasurable (fun z : Vec3 × ℝ => u (z.1, z.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
    have h := hU
    rw [← Measure.restrict_univ (μ := (volume : Measure Vec3)), Measure.prod_restrict]
    exact h
  have hDuprod : AEStronglyMeasurable (fun z : Vec3 × ℝ => Du (z.1, z.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
    have h := hDu
    rw [← Measure.restrict_univ (μ := (volume : Measure Vec3)), Measure.prod_restrict]
    exact h
  have hsource := (hGrad.and hUprod.prodMk_right).and hDuprod.prodMk_right
  have hpull := blowup_ae_time_pullback_on R t₀ hR (Ioo 0 T) (Ioo (-1) 0)
    measurableSet_Ioo (pv_unit_time_subset_rescaled hR hlow hup) _ hsource
  filter_upwards [hpull] with s hs
  obtain ⟨⟨hg, hUs⟩, hDus⟩ := hs
  intro i j
  have hUi : AEStronglyMeasurable (fun x => u (x, CKN.scalingTime R t₀ s) i)
      (volume.restrict (Set.univ : Set Vec3)) := by
    rw [Measure.restrict_univ]
    exact (continuous_apply i).comp_aestronglyMeasurable hUs
  have hDuij : AEStronglyMeasurable (fun x => Du (x, CKN.scalingTime R t₀ s) i j)
      (volume.restrict (Set.univ : Set Vec3)) := by
    rw [Measure.restrict_univ]
    exact (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hDus)
  have himage : (Set.univ : Set Vec3) = CKN.scalingSpace R x₀ '' Set.univ := by
    symm
    rw [Set.image_univ, Set.range_eq_univ]
    intro y
    refine ⟨R⁻¹ • (y - x₀), ?_⟩
    change x₀ + R • (R⁻¹ • (y - x₀)) = y
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  have hscaled := CKN.hasWeakPartialDerivOn_scaling R hR x₀ MeasurableSet.univ j himage
    (hg i j) hUi hDuij
  have hball := hscaled.restrict (isOpen_vec3Ball (0 : Vec3) 1) (Set.subset_univ _)
  exact hball

end ESS
