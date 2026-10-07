/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceAgreement

/-!
# Blowup Ten Thirds Finite

Space-time integrability of the rescaled velocity at exponent 10/3.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The ball-time interpolation bound determined by the source slice norm,
Dirichlet integral, and cylinder size. -/
@[expose] def blowupTenThirdsBound (M : ℝ≥0∞) (Cg R a : ℝ) : ℝ≥0∞ :=
  let A := M * (volume (vec3Ball (0 : Vec3) R)) ^ (1 / 6 : ℝ)
  let G := (ENNReal.ofReal Cg) ^ (1 / 2 : ℝ)
  ENNReal.ofReal (Classical.choose CKN.ball_time_sobolev) *
    (A ^ (4 / 3 : ℝ) * G ^ (2 : ℝ) +
      ENNReal.ofReal (R ^ (-2 : ℝ)) *
        A ^ (10 / 3 : ℝ) * volume (Ioo a 0))

/-- The interpolation bound is finite when the source slice bound is finite. -/
theorem blowupTenThirdsBound_lt_top
    (M : ℝ≥0∞) (hM : M < ⊤) (Cg R a : ℝ) :
    blowupTenThirdsBound M Cg R a < ⊤ := by
  let A : ℝ≥0∞ := M * (volume (vec3Ball (0 : Vec3) R)) ^ (1 / 6 : ℝ)
  let G : ℝ≥0∞ := (ENNReal.ofReal Cg) ^ (1 / 2 : ℝ)
  have hvol : volume (vec3Ball (0 : Vec3) R) < ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hA : A < ⊤ :=
    ENNReal.mul_lt_top hM
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvol.ne)
  have hG : G < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hJtop : volume (Ioo a 0) < ⊤ := by simp
  dsimp [blowupTenThirdsBound, A, G]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG.ne)
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne))
      hJtop

/-- One suitable rescaling has a uniform `L^(10/3)` bound for each
velocity component on all finite past subcylinders with the same lower time. -/
theorem blowupRescale_component_tenThirds_uniform_finite_past
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (R a : ℝ) (hR : 0 < R)
    (hsol : IsSuitableWeakSolutionIntegrable
      (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) 3
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du)
      (parabolicRescalePressure x₀ t₀ r p) 0)
    (hdom : vec3Ball 0 R ×ˢ Ioo a 0 ⊆ blowupDomain x₀ t₀ r)
    (htime : Ioo a 0 ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ M)
    (Cg : ℝ)
    (hgradInt : IntegrableOn (fun z => spatialGradientSq
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du) z)
      (vec3Ball 0 R ×ˢ Ioo a 0) volume)
    (hgradBound : (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
      spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescaleGradient x₀ t₀ r Du) z
      ∂(volume : Measure ParabolicPoint)) ≤ Cg)
    (i : Fin 3) :
    blowupTenThirdsBound M Cg R a < ⊤ ∧
      ∀ b : ℝ, a < b → b < 0 →
        MemLp (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b)) ∧
        eLpNorm (fun z => parabolicRescaleVelocity x₀ t₀ r u z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b)) ^ (10 / 3 : ℝ) ≤
            blowupTenThirdsBound M Cg R a := by
  let V := parabolicRescaleVelocity x₀ t₀ r u
  let D := parabolicRescaleGradient x₀ t₀ r Du
  let topBox := vec3Ball (0 : Vec3) R ×ˢ Ioo a 0
  let A : ℝ≥0∞ := M * (volume (vec3Ball (0 : Vec3) R)) ^ (1 / 6 : ℝ)
  let G : ℝ≥0∞ := (ENNReal.ofReal Cg) ^ (1 / 2 : ℝ)
  let Cs : ℝ := Classical.choose CKN.ball_time_sobolev
  have ⟨hCs, hSob⟩ := Classical.choose_spec CKN.ball_time_sobolev
  let K : ℝ≥0∞ := blowupTenThirdsBound M Cg R a
  have hvol : volume (vec3Ball (0 : Vec3) R) < ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hA : A < ⊤ :=
    ENNReal.mul_lt_top hM
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvol.ne)
  have hG : G < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hJtop : volume (Ioo a 0) < ⊤ := by simp
  have hK : K < ⊤ := by
    dsimp [K, blowupTenThirdsBound, Cs, A, G]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG.ne)
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne))
        hJtop
  refine ⟨hK, ?_⟩
  intro b hab hb
  let J := Ioo a b
  let S := vec3Ball (0 : Vec3) R ×ˢ J
  have hbox := blowup_inner_past_localBox R a b hR hab hb
  have hdata := hsol.toData
  have hSsub : S ⊆ topBox := Set.prod_mono Subset.rfl
    (fun t ht => ⟨ht.1, lt_trans ht.2 hb⟩)
  have hJsub : J ⊆ Ioo a 0 :=
    fun t ht => ⟨ht.1, lt_trans ht.2 hb⟩
  have hJtime : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0) :=
    hJsub.trans htime
  have hSdom : S ⊆ blowupDomain x₀ t₀ r := hSsub.trans hdom
  have hAsup :
      essSup (fun s => eLpNorm (fun x : Vec3 => V (x,s) i) 2
        (volume.restrict (vec3Ball 0 R))) (volume.restrict J) ≤ A :=
    blowupRescaledVelocity_component_slice_two_essSup_le_of_domain
      u x₀ t₀ r hr J measurableSet_Ioo hJtime M hsource
      0 R i hSdom
  have hgradIntS : IntegrableOn (fun z => spatialGradientSq V D z)
      S volume := hgradInt.mono_set hSsub
  have hgradS : (∫ (z : ParabolicPoint) in S,
      spatialGradientSq V D z ∂(volume : Measure ParabolicPoint)) ≤ Cg := by
    have hmono :
        (∫ (z : ParabolicPoint) in S,
          spatialGradientSq V D z ∂(volume : Measure ParabolicPoint)) ≤
        ∫ (z : ParabolicPoint) in topBox,
          spatialGradientSq V D z ∂(volume : Measure ParabolicPoint) := by
      apply setIntegral_mono_set hgradInt
      · filter_upwards [] with z
        dsimp [spatialGradientSq]
        positivity
      · exact Filter.Eventually.of_forall hSsub
    exact hmono.trans hgradBound
  have hDuMeas : AEStronglyMeasurable D (volume.restrict S) := by
    have h := hdata.aestronglyMeasurable_gradient hbox
    simpa only [S, J, spaceTimeSet,
      CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
        (by linarith only [hR] : 0 < R + 1)] using h
  have hg₂ : MemLp (fun z => V z i) 2 (volume.restrict S) := by
    have he := hdata.energy_lintegral_lt_top hbox
    have hu := hdata.aestronglyMeasurable_velocity hbox
    have hlt :
        (∫⁻ z in spaceTimeSet (vec3Ball 0 R) J,
          ‖V z‖ₑ ^ (2 : ℝ)) < ⊤ :=
      (lintegral_mono (fun _ => le_add_right le_rfl)).trans_lt he
    have hm := blowup_memLp_two_of_energy hu hlt
    exact memLp_pi_iff.mp hm i
  have hDg₂ : MemLp (fun z => D z i) 2 (volume.restrict S) := by
    have he := hdata.energy_lintegral_lt_top hbox
    have hDu := hdata.aestronglyMeasurable_gradient hbox
    have hlt :
        (∫⁻ z in spaceTimeSet (vec3Ball 0 R) J,
          ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ :=
      (lintegral_mono (fun _ => le_add_left le_rfl)).trans_lt he
    have hm := blowup_memLp_two_of_energy hDu hlt
    exact memLp_pi_iff.mp hm i
  have hSlice := blowup_h1_slices_of_data hdata hbox
    (x₀ := (0 : Vec3)) (r := R) (by
      exact Subset.rfl) i
  have hGbound :
      eLpNorm (fun z => vec3EuclideanNorm (D z i)) 2
        (volume.restrict S) ≤ G :=
    blowup_gradient_component_eLpNorm_le_of_integral_bound
      S V D i Cg hDuMeas hgradIntS hgradS
  have hSobolev := hSob 0 R hR J ordConnected_Ioo
    (fun z => V z i) (fun z => D z i)
    hg₂.aestronglyMeasurable hDg₂.aestronglyMeasurable
    hSlice hg₂ hDg₂ (hAsup.trans_lt hA)
  refine ⟨hSobolev.1, hSobolev.2.trans ?_⟩
  dsimp [K, blowupTenThirdsBound, Cs]
  gcongr
  · exact hGbound

end ESS
