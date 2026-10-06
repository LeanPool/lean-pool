/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.ParabolicRescaleSolution
public import LeanPool.CIVAxisymmetric.Reduction.SuitableWeakSolutionRestrict
public import LeanPool.CIVAxisymmetric.Regularity.ParabolicRescaling
public import LeanPool.CIVAxisymmetric.Regularity.ParabolicRescalingAxisymmetric
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# The Navier–Stokes scaling onto the unit cylinder

The scaling step of `cor:interior:nonanalytic`: for `0 < R ≤ 1` the parabolic rescaling
`u ↦ R u(R ·, R² ·)`, `π ↦ R² π(R ·, R² ·)`, `f ↦ R³ f(R ·, R² ·)` about the origin carries a
suitable weak solution on the unit cylinder `Q`, restricted to `B(R) × (-R², 0)`, to a suitable
weak solution on `Q`, and it preserves the energy class `eq:interior:energy:class`, the
axisymmetric core `eq:interior:core`, and regularity at the origin `eq:interior:regular`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The rescaled velocity about the origin, read on the components of a space-time point. -/
theorem rescaleVelocity_origin_apply (R : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u z = R • u (R • z.1, R ^ 2 * z.2) := by
  simp [rescaleVelocity, parabolicTranslate, parabolicScale]

/-- The rescaled force about the origin, read on the components of a space-time point. -/
theorem rescaleForce_origin_apply (R : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    rescaleForce R ((0 : Vec3), (0 : ℝ)) f z = R ^ 3 • f (R • z.1, R ^ 2 * z.2) := by
  simp [rescaleForce, parabolicTranslate, parabolicScale]

/-- The spatial dilation by `R > 0` pulls the ball `B(R)` back to the unit ball. -/
theorem rescaledSpace_vec3Ball_self {R : ℝ} (hR0 : 0 < R) :
    rescaledSpace R (0 : Vec3) (vec3Ball 0 R) = vec3Ball 0 1 := by
  ext x
  simp only [rescaledSpace, scalingSpace, mem_preimage, mem_vec3Ball, sub_zero, zero_add,
    vec3EuclideanNorm_smul, abs_of_pos hR0]
  constructor
  · intro h
    exact (mul_lt_iff_lt_one_right hR0).1 h
  · intro h
    exact (mul_lt_iff_lt_one_right hR0).2 h

/-- The time dilation by `R² > 0` pulls `(-R², 0)` back to `(-1, 0)`. -/
theorem rescaledTime_Ioo_self {R : ℝ} (hR0 : 0 < R) :
    rescaledTime R (0 : ℝ) (Ioo (-R ^ 2) 0) = Ioo (-1) 0 := by
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  ext s
  simp only [rescaledTime, scalingTime, mem_preimage, mem_Ioo, zero_add]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_contra hs
      have hs' : s ≤ -1 := not_lt.1 hs
      have := mul_le_mul_of_nonneg_left hs' hR2.le
      linarith only [this, h1]
    · by_contra hs
      have hs' : 0 ≤ s := not_lt.1 hs
      have := mul_nonneg hR2.le hs'
      linarith only [this, h2]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := mul_lt_mul_of_pos_left h1 hR2
      linarith only [this]
    · have := mul_lt_mul_of_pos_left h2 hR2
      linarith only [this]

/-- The scaling step of `cor:interior:nonanalytic` for the solution class: a suitable weak
solution on `Q`, restricted to `B(R) × (-R², 0)` and rescaled by `R`, is a suitable weak solution
on `Q`. -/
theorem isSuitableWeakSolution_rescale_unitCylinder {q R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f) :
    IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q
      (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u) (rescaleGradient R ((0 : Vec3), (0 : ℝ)) Du)
      (rescalePressure R ((0 : Vec3), (0 : ℝ)) p) (rescaleForce R ((0 : Vec3), (0 : ℝ)) f) := by
  have hball : vec3Ball (0 : Vec3) R ⊆ vec3Ball 0 1 := by
    intro x hx
    simp only [mem_vec3Ball] at hx ⊢
    exact lt_of_lt_of_le hx hR1
  have hR2 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
  have htime : Ioo (-R ^ 2) (0 : ℝ) ⊆ Ioo (-1) 0 := by
    intro s hs
    exact ⟨lt_of_le_of_lt (neg_le_neg hR2) hs.1, hs.2⟩
  have hres := isSuitableWeakSolution_restrict hsol (isOpen_vec3Ball 0 R) hball isOpen_Ioo
    ordConnected_Ioo htime
  have hsc := isSuitableWeakSolution_of_integrable
    (isSuitableWeakSolutionIntegrable_rescale
      (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hres) ((0 : Vec3), (0 : ℝ)) hR0)
  rwa [show ((((0 : Vec3), (0 : ℝ)) : ParabolicPoint).1) = (0 : Vec3) from rfl,
    show ((((0 : Vec3), (0 : ℝ)) : ParabolicPoint).2) = (0 : ℝ) from rfl,
    rescaledSpace_vec3Ball_self hR0, rescaledTime_Ioo_self hR0] at hsc

/-- The rescaled velocity about the origin inherits an axisymmetric core `eq:interior:core`. -/
theorem axisymmetricCore_rescale {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) {u : ParabolicPoint → Vec3}
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t})) :
    ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u)
        (spaceTimeSet (vec3Ball 0 ρ) {t}) := by
  intro t ht
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  have hR21 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
  have hts : R ^ 2 * t ∈ Ioo (-1 : ℝ) 0 := by
    refine ⟨?_, mul_neg_of_pos_of_neg hR2 ht.2⟩
    have h1 : R ^ 2 * (-1) < R ^ 2 * t := mul_lt_mul_of_pos_left ht.1 hR2
    linarith only [h1, hR21]
  obtain ⟨ρ, hρ, hρcore⟩ := hcore (R ^ 2 * t) hts
  refine ⟨min (ρ / R) (1 / 2), ⟨lt_min (div_pos hρ.1 hR0) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
  intro z hz
  obtain ⟨x, s⟩ := z
  obtain ⟨hx, hs⟩ : x ∈ vec3Ball 0 (min (ρ / R) (1 / 2)) ∧ s ∈ ({t} : Set ℝ) := hz
  rw [mem_singleton_iff] at hs
  subst hs
  have hRx : ((R • x, R ^ 2 * s) : ParabolicPoint) ∈ spaceTimeSet (vec3Ball 0 ρ) {R ^ 2 * s} := by
    refine ⟨?_, rfl⟩
    simp only [mem_vec3Ball, sub_zero] at hx ⊢
    rw [vec3EuclideanNorm_smul, abs_of_pos hR0]
    have hlt : vec3EuclideanNorm x < ρ / R := lt_of_lt_of_le hx (min_le_left _ _)
    calc R * vec3EuclideanNorm x < R * (ρ / R) := mul_lt_mul_of_pos_left hlt hR0
      _ = ρ := by field_simp
  have heq := hρcore _ hRx
  have hfun : rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u =
      fun w : ParabolicPoint => R • u (R • w.1, R ^ 2 * w.2) := by
    funext w
    exact rescaleVelocity_origin_apply R u w
  rw [hfun]
  exact (angularMean_smul_comp R R u (x, s)).trans (congrArg (fun v : Vec3 => R • v) heq)

/-- Regularity at the origin `eq:interior:regular` descends from the rescaled velocity. -/
theorem boundedNearOrigin_of_rescale {R : ℝ} (hR0 : 0 < R) {u : ParabolicPoint → Vec3}
    (h : BoundedNearOrigin (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u)) :
    BoundedNearOrigin u := by
  obtain ⟨r, δ, M, hr, hδ, hM⟩ := h
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  refine ⟨R * r, R ^ 2 * δ, M / R, mul_pos hR0 hr, mul_pos hR2 hδ, ?_⟩
  intro y hy s hs
  have hx : R⁻¹ • y ∈ vec3Ball (0 : Vec3) r := by
    simp only [mem_vec3Ball, sub_zero] at hy ⊢
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.2 hR0)]
    rw [inv_mul_lt_iff₀ hR0]
    exact hy
  have ht : s / R ^ 2 ∈ Ioo (-δ) 0 := by
    refine ⟨?_, div_neg_of_neg_of_pos hs.2 hR2⟩
    rw [lt_div_iff₀ hR2]
    linarith only [hs.1]
  have hb := hM _ hx _ ht
  rw [show rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u (R⁻¹ • y, s / R ^ 2) =
      R • u (R • R⁻¹ • y, R ^ 2 * (s / R ^ 2)) from rescaleVelocity_origin_apply R u _,
    vec3EuclideanNorm_smul, abs_of_pos hR0] at hb
  have hy' : R • R⁻¹ • y = y := by
    rw [smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
  have hs' : R ^ 2 * (s / R ^ 2) = s := by field_simp
  simp only [hy', hs'] at hb
  rw [le_div_iff₀ hR0]
  linarith only [hb]

/-- If the force vanishes on `B(R') × (-δ', 0)`, the force rescaled by `R ≤ R'` with
`R² ≤ δ'` vanishes on the unit cylinder. -/
theorem rescaleForce_eq_zero_of_vanishing {R R' δ' : ℝ} (hR0 : 0 < R) (hRR' : R ≤ R')
    (hRδ : R ^ 2 ≤ δ') {f : ParabolicPoint → Vec3}
    (hvan : ∀ z ∈ spaceTimeSet (vec3Ball 0 R') (Ioo (-δ') 0), f z = 0) :
    ∀ z ∈ unitCylinder, rescaleForce R ((0 : Vec3), (0 : ℝ)) f z = 0 := by
  intro z hz
  obtain ⟨x, t⟩ := z
  obtain ⟨hx, ht⟩ : x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0 := hz
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  rw [show rescaleForce R ((0 : Vec3), (0 : ℝ)) f (x, t) = R ^ 3 • f (R • x, R ^ 2 * t) from
    rescaleForce_origin_apply R f _]
  have hmem : ((R • x, R ^ 2 * t) : ParabolicPoint) ∈
      spaceTimeSet (vec3Ball 0 R') (Ioo (-δ') 0) := by
    refine ⟨?_, ?_, mul_neg_of_pos_of_neg hR2 ht.2⟩
    · simp only [mem_vec3Ball, sub_zero] at hx ⊢
      rw [vec3EuclideanNorm_smul, abs_of_pos hR0]
      calc R * vec3EuclideanNorm x < R * 1 := mul_lt_mul_of_pos_left hx hR0
        _ ≤ R' := by rw [mul_one]; exact hRR'
    · have h1 : R ^ 2 * (-1) < R ^ 2 * t := mul_lt_mul_of_pos_left ht.1 hR2
      linarith only [h1, hRδ]
  rw [hvan _ hmem, smul_zero]

/-- A real scalar of modulus at most one does not increase the extended norm. -/
private theorem enorm_smul_le_of_abs_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : |c| ≤ 1) (v : E) : ‖c • v‖ₑ ≤ ‖v‖ₑ := by
  rw [enorm_smul]
  calc ‖c‖ₑ * ‖v‖ₑ ≤ 1 * ‖v‖ₑ := by
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 hc
    _ = ‖v‖ₑ := one_mul _

/-- The unit cylinder lies in the preimage of the unit cylinder under the rescaling by
`0 < R ≤ 1` about the origin. -/
private theorem unitCylinder_subset_preimage_scalingParabolic {R : ℝ} (hR0 : 0 < R)
    (hR1 : R ≤ 1) :
    unitCylinder ⊆ scalingParabolic R ((0 : Vec3), (0 : ℝ)) ⁻¹' unitCylinder := by
  intro z hz
  obtain ⟨x, t⟩ := z
  obtain ⟨hx, ht⟩ : x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0 := hz
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  have hR21 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
  change ((0 : Vec3) + R • x, (0 : ℝ) + R ^ 2 * t) ∈ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)
  refine ⟨?_, ?_, ?_⟩
  · simp only [mem_vec3Ball, sub_zero, zero_add] at hx ⊢
    rw [vec3EuclideanNorm_smul, abs_of_pos hR0]
    calc R * vec3EuclideanNorm x ≤ 1 * vec3EuclideanNorm x :=
          mul_le_mul_of_nonneg_right hR1 (vec3EuclideanNorm_nonneg x)
      _ < 1 := by rw [one_mul]; exact hx
  · have h1 : R ^ 2 * (-1) < R ^ 2 * t := mul_lt_mul_of_pos_left ht.1 hR2
    linarith only [h1, hR21]
  · have h1 : R ^ 2 * t < 0 := mul_neg_of_pos_of_neg hR2 ht.2
    linarith only [h1]

/-- The rescaling by `0 < R ≤ 1` about the origin preserves the energy class
`eq:interior:energy:class` on the unit cylinder. -/
theorem globalEnergyClass_rescale {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (henergy : GlobalEnergyClass u Du p) :
    GlobalEnergyClass (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u)
      (rescaleGradient R ((0 : Vec3), (0 : ℝ)) Du)
      (rescalePressure R ((0 : Vec3), (0 : ℝ)) p) := by
  obtain ⟨h1, h2, h3⟩ := henergy
  have hR2 : 0 < R ^ 2 := pow_pos hR0 2
  have hR21 : R ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
  have hRabs : |R| ≤ 1 := by rw [abs_of_pos hR0]; exact hR1
  have hR2abs : |R ^ 2| ≤ 1 := by rw [abs_of_pos hR2]; exact hR21
  have hU : MeasurableSet (unitCylinder : Set ParabolicPoint) :=
    isOpen_unitCylinder_prod.measurableSet
  have hsub := unitCylinder_subset_preimage_scalingParabolic hR0 hR1
  refine ⟨?_, ?_, ?_⟩
  · -- the slice energies
    set E : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in vec3Ball 0 1, ‖u (x, s)‖ₑ ^ (2 : ℝ) with hEdef
    have hpt : ∀ s : ℝ,
        ∫⁻ x in vec3Ball 0 1, ‖rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u (x, s)‖ₑ ^ (2 : ℝ) ≤
          ENNReal.ofReal (R⁻¹ ^ 3) * E (R ^ 2 * s) := by
      intro s
      have hcv :=
        CKN.Foundation.Parabolic.Integration.timeSlice_setLIntegral_comp_parabolicRescale hR0 (0
        : Vec3) (0 : ℝ) 1 s
        (fun z => ‖u z‖)
      simp only [enorm_norm, mul_one, zero_add] at hcv
      calc ∫⁻ x in vec3Ball 0 1, ‖rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u (x, s)‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ x in vec3Ball 0 1,
              ‖u (parabolicTranslate 0 0 (parabolicScale R (x, s)))‖ₑ ^ (2 : ℝ) := by
            refine lintegral_mono fun x => ?_
            exact ENNReal.rpow_le_rpow (enorm_smul_le_of_abs_le_one hRabs _) (by norm_num)
        _ = ENNReal.ofReal (R⁻¹ ^ 3) * ∫⁻ y in vec3Ball 0 R, ‖u (y, R ^ 2 * s)‖ₑ ^ (2 : ℝ) := hcv
        _ ≤ ENNReal.ofReal (R⁻¹ ^ 3) * E (R ^ 2 * s) := by
            gcongr
            refine lintegral_mono_set ?_
            intro y hy
            simp only [mem_vec3Ball] at hy ⊢
            exact lt_of_lt_of_le hy hR1
    set M : ℝ≥0∞ := essSup E (volume.restrict (Ioo (-1 : ℝ) 0)) with hMdef
    have hM : ∀ᵐ s ∂(volume.restrict (Ioo (-1 : ℝ) 0)), E (R ^ 2 * s) ≤ M := by
      have hae := ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (-1 : ℝ) 0)) E
      rw [ae_restrict_iff' measurableSet_Ioo] at hae ⊢
      have hq : Measure.QuasiMeasurePreserving (fun s : ℝ => R ^ 2 • s) volume volume :=
        Measure.quasiMeasurePreserving_smul volume hR2.ne'
      filter_upwards [hq.ae hae] with s hs hsI
      refine hs ?_
      rw [smul_eq_mul]
      refine ⟨?_, mul_neg_of_pos_of_neg hR2 hsI.2⟩
      have h1 : R ^ 2 * (-1) < R ^ 2 * s := mul_lt_mul_of_pos_left hsI.1 hR2
      linarith only [h1, hR21]
    have hle : essSup (fun s => ∫⁻ x in vec3Ball 0 1,
        ‖rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo (-1) 0)) ≤ ENNReal.ofReal (R⁻¹ ^ 3) * M := by
      refine essSup_le_of_ae_le _ ?_
      filter_upwards [hM] with s hs
      exact (hpt s).trans (by gcongr)
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1)
  · -- the space-time energy
    set F : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)
    have hpt : ∀ z : ParabolicPoint,
        ‖rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u z‖ₑ ^ (2 : ℝ) +
            ‖rescaleGradient R ((0 : Vec3), (0 : ℝ)) Du z‖ₑ ^ (2 : ℝ) ≤
          F (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) := by
      intro z
      have hDu : rescaleGradient R ((0 : Vec3), (0 : ℝ)) Du z =
          R ^ 2 • Du (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) := by
        funext i
        rfl
      have hu' : rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u z =
          R • u (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) := rfl
      rw [hDu, hu']
      change _ ≤ ‖u (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)‖ₑ ^ (2 : ℝ) +
        ‖Du (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z)‖ₑ ^ (2 : ℝ)
      gcongr
      · exact enorm_smul_le_of_abs_le_one hRabs _
      · exact enorm_smul_le_of_abs_le_one hR2abs _
    calc (∫⁻ z in unitCylinder, ‖rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u z‖ₑ ^ (2 : ℝ) +
            ‖rescaleGradient R ((0 : Vec3), (0 : ℝ)) Du z‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ z in unitCylinder, F (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) :=
          lintegral_mono hpt
      _ ≤ ∫⁻ z in scalingParabolic R ((0 : Vec3), (0 : ℝ)) ⁻¹' unitCylinder,
            F (scalingParabolic R ((0 : Vec3), (0 : ℝ)) z) := lintegral_mono_set hsub
      _ = ENNReal.ofReal (R⁻¹ ^ 5) * ∫⁻ z in unitCylinder, F z :=
          setLIntegral_comp_scalingParabolic hR0 _ hU F
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  · -- the pressure
    have hmap := h3.smul_measure (c := ENNReal.ofReal (R⁻¹ ^ 5)) ENNReal.ofReal_ne_top
    rw [← map_scalingParabolic_restrict_preimage hR0 ((0 : Vec3), (0 : ℝ)) hU] at hmap
    have hcomp := (hmap.comp_of_map
      (measurable_scalingParabolic hR0 ((0 : Vec3), (0 : ℝ))).aemeasurable).mono_measure
      (Measure.restrict_mono hsub le_rfl)
    exact hcomp.const_mul (R ^ 2)

end CIV
