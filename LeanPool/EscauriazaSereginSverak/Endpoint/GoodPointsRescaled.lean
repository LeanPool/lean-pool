/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.RescalingSuitable
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremA
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ForceSlotNumericalScaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Rescaled epsilon regularity

This is the radius-`r` form of CKN Theorem A used in
`lem:thmA-rescaled`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

@[expose] def goodPointRescaleHomeomorph (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x₀))
      ((Homeomorph.smulOfNeZero (r ^ 2) (sq_pos_of_pos hr).ne').trans
        (Homeomorph.addLeft t₀)))).trans parabolicHomeomorph.symm

private theorem goodPointRescaleHomeomorph_apply
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) (z : ParabolicPoint) :
    goodPointRescaleHomeomorph x₀ t₀ r hr z =
      parabolicTranslate x₀ t₀ (parabolicScale r z) := rfl

private theorem goodPointRescaleHomeomorph_eq_scaling
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    goodPointRescaleHomeomorph x₀ t₀ r hr =
      CKN.scalingParabolic r (x₀, t₀) := by
  funext z
  rfl

private theorem goodPointRescaleCylinder_image
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    goodPointRescaleHomeomorph x₀ t₀ r hr '' parabolicCylinder 0 0 1 =
      parabolicCylinder x₀ t₀ r := by
  rw [goodPointRescaleHomeomorph_eq_scaling]
  simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale]
    using CKN.Core.Endgame.force_slot_cylinder_image hr (x₀, t₀)
      (0, 0) (1 : ℝ)

private theorem goodPointRescaleHalfCylinder_image
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    goodPointRescaleHomeomorph x₀ t₀ r hr '' parabolicCylinder 0 0 (1 / 2) =
      parabolicCylinder x₀ t₀ (r / 2) := by
  rw [goodPointRescaleHomeomorph_eq_scaling]
  have h := CKN.Core.Endgame.force_slot_cylinder_image hr (x₀, t₀)
    (0, 0) (1 / 2 : ℝ)
  simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale,
    div_eq_mul_inv] using h

private theorem goodPointRescaleDomain_preimage
    (Ω : Set Vec3) (I : Set ℝ) (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    spaceTimeSet (CKN.rescaledSpace r x₀ Ω) (CKN.rescaledTime r t₀ I) =
      goodPointRescaleHomeomorph x₀ t₀ r hr ⁻¹' spaceTimeSet Ω I := by
  rw [CKN.rescaledSpaceTimeSet_eq_preimage r (x₀, t₀) Ω I]
  rfl

private theorem goodPointRescaleHomeomorph_map_symm
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    Measure.map (goodPointRescaleHomeomorph x₀ t₀ r hr).symm
        (volume : Measure ParabolicPoint) =
      ENNReal.ofReal ((r⁻¹)⁻¹ ^ 5) • volume := by
  let x₁ : Vec3 := -(r⁻¹ • x₀)
  let t₁ : ℝ := -((r⁻¹) ^ 2 * t₀)
  have hinv : (goodPointRescaleHomeomorph x₀ t₀ r hr).symm =
      CKN.scalingParabolic r⁻¹ (x₁, t₁) := by
    funext z
    apply parabolicHomeomorph.injective
    ext <;>
      simp [goodPointRescaleHomeomorph, x₁, t₁,
        Homeomorph.prodCongr, Homeomorph.smulOfNeZero,
        Homeomorph.addLeft, Units.smul_def, CKN.scalingParabolic,
        parabolicTranslate, parabolicScale, parabolicHomeomorph_apply,
        inv_pow]
  rw [hinv]
  exact CKN.map_scalingParabolic (r⁻¹) (inv_pos.mpr hr) (x₁, t₁)

private theorem goodPointRescaleQuasiMeasurePreserving_symm
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (N : Set ParabolicPoint) (hN : MeasurableSet N) :
    Measure.QuasiMeasurePreserving (goodPointRescaleHomeomorph x₀ t₀ r hr).symm
      (volume.restrict
        ((goodPointRescaleHomeomorph x₀ t₀ r hr).symm ⁻¹' N))
      (volume.restrict N) := by
  refine ⟨(goodPointRescaleHomeomorph x₀ t₀ r hr).symm.measurable, ?_⟩
  have hmap := Measure.restrict_map
    (μ := (volume : Measure ParabolicPoint))
    (goodPointRescaleHomeomorph x₀ t₀ r hr).symm.measurable hN
  rw [goodPointRescaleHomeomorph_map_symm, Measure.restrict_smul] at hmap
  rw [hmap.symm]
  exact Measure.smul_absolutelyContinuous

private theorem goodPointEnergy_rescale
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    goodPointEnergy (parabolicRescaleVelocity x₀ t₀ r u)
        (parabolicRescalePressure x₀ t₀ r p) 0 0 1 =
      ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r := by
  rw [goodPointEnergy, goodPointEnergy]
  have hscaled (z : ParabolicPoint) :
      ENNReal.ofReal
          (vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ r p z| ^ (3 / 2 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          (ENNReal.ofReal (vec3EuclideanNorm
              (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) +
            ENNReal.ofReal |p (parabolicTranslate x₀ t₀
              (parabolicScale r z))| ^ (3 / 2 : ℝ)) := by
    rw [parabolicRescaleVelocity, parabolicRescalePressure,
      vec3EuclideanNorm_smul, abs_of_pos hr, abs_mul,
      abs_of_nonneg (sq_nonneg r)]
    have hU : ENNReal.ofReal
          (r * vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          ENNReal.ofReal (vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) := by
      rw [ENNReal.ofReal_mul (p := r)
          (q := vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) hr.le,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 : ℝ)),
        ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num : 0 ≤ (3 : ℝ))]
      exact congrArg (fun a : ℝ≥0∞ => a *
          ENNReal.ofReal (vec3EuclideanNorm
            (u (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ))
        (congrArg ENNReal.ofReal (Real.rpow_natCast r 3))
    have hP : ENNReal.ofReal
          (r ^ 2 * |p (parabolicTranslate x₀ t₀ (parabolicScale r z))|) ^
            (3 / 2 : ℝ) =
        ENNReal.ofReal (r ^ 3) *
          ENNReal.ofReal |p (parabolicTranslate x₀ t₀ (parabolicScale r z))| ^
            (3 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul (p := r ^ 2)
          (q := |p (parabolicTranslate x₀ t₀ (parabolicScale r z))|)
          (sq_nonneg r),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 / 2 : ℝ)),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r)
          (by norm_num : 0 ≤ (3 / 2 : ℝ))]
      have hscalar : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3,
          ← Real.rpow_mul (le_of_lt hr)]
        norm_num
      rw [hscalar]
    rw [hU, hP]
    ring
  simp_rw [hscaled]
  have hscale := CKN.Core.Endgame.force_slot_lintegral_scaling hr (x₀, t₀)
    (0, 0) (1 : ℝ)
    (fun z : ParabolicPoint =>
      ENNReal.ofReal (r ^ 3) *
        (ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)))
  have hscale' :
      (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (r ^ 3) *
          (ENNReal.ofReal (vec3EuclideanNorm (u
            (parabolicTranslate x₀ t₀ (parabolicScale r z)))) ^ (3 : ℝ) +
            ENNReal.ofReal |p (parabolicTranslate x₀ t₀
              (parabolicScale r z))| ^ (3 / 2 : ℝ))) =
        ENNReal.ofReal (r⁻¹ ^ 5) *
          (∫⁻ z in parabolicCylinder x₀ t₀ r,
            ENNReal.ofReal (r ^ 3) *
              (ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
                ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))) := by
    simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hscale
  rw [hscale']
  rw [lintegral_const_mul' (ENNReal.ofReal (r ^ 3)) _ ENNReal.ofReal_ne_top]
  have hcoeff : ENNReal.ofReal (r⁻¹ ^ 5) * ENNReal.ofReal (r ^ 3) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (p := r⁻¹ ^ 5) (q := r ^ 3)
      (by positivity : 0 ≤ r⁻¹ ^ 5)]
    congr 1
    field_simp
  rw [← mul_assoc, hcoeff]

/-- CKN Theorem A transports from the unit cylinder to every positive radius,
with the velocity and pressure normalization used in `lem:thmA-rescaled`. -/
theorem epsilonRegularityL3_rescaled
    (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
          (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolution Ω I q u Du p (fun _ => 0) →
        ∀ (x₀ : Vec3) (t₀ r : ℝ), 0 < r →
          closure (parabolicCylinder x₀ t₀ r) ⊆ spaceTimeSet Ω I →
          goodPointEnergy u p x₀ t₀ r * ENNReal.ofReal (r⁻¹ ^ 2) <
            ENNReal.ofReal ε₀ →
          ∃ w : ParabolicPoint → Vec3,
            w =ᵐ[volume.restrict (parabolicCylinder x₀ t₀ (r / 2))] u ∧
            (∀ z ∈ closure (parabolicCylinder x₀ t₀ (r / 2)),
              vec3EuclideanNorm (w z) ≤ C₄ * r⁻¹) ∧
            (∀ z ∈ closure (parabolicCylinder x₀ t₀ (r / 2)),
              ∀ z' ∈ closure (parabolicCylinder x₀ t₀ (r / 2)),
                vec3EuclideanNorm (w z - w z') ≤
                  C₄ * (r⁻¹ * r⁻¹ ^ γ₀) * parabolicDist z z' ^ γ₀) := by
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, hA⟩ :=
    CKN.epsilonRegularityL3 q hq
  refine ⟨ε₀, γ₀, C₄, hε₀, hγ₀, ?_, hC₄, ?_⟩
  · exact hγ₀le
  · intro Ω I u Du p hSuitable x₀ t₀ r hr hclosure hsmall
    let Φ := goodPointRescaleHomeomorph x₀ t₀ r hr
    let uᵣ := parabolicRescaleVelocity x₀ t₀ r u
    let Duᵣ := parabolicRescaleGradient x₀ t₀ r Du
    let pᵣ := parabolicRescalePressure x₀ t₀ r p
    let fᵣ : ParabolicPoint → Vec3 := fun _ => 0
    have hSuitableᵣ : IsSuitableWeakSolution
        (CKN.rescaledSpace r x₀ Ω) (CKN.rescaledTime r t₀ I) q uᵣ Duᵣ pᵣ fᵣ := by
      simpa [uᵣ, Duᵣ, pᵣ, fᵣ, Φ, parabolicRescaleVelocity,
        parabolicRescaleGradient, parabolicRescalePressure,
        goodPointRescaleHomeomorph_apply] using
        isSuitableWeakSolution_parabolicRescale
          u Du p (fun _ => 0) hSuitable x₀ t₀ r hr
    have hclosureᵣ : closure (parabolicCylinder 0 0 1) ⊆
        spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
          (CKN.rescaledTime r t₀ I) := by
      intro z hz
      have hΦz : Φ z ∈ closure (parabolicCylinder x₀ t₀ r) := by
        have himage : closure (Φ '' parabolicCylinder 0 0 1) =
            Φ '' closure (parabolicCylinder 0 0 1) :=
          Φ.isClosedEmbedding.closure_image_eq _
        have hmem : Φ z ∈ Φ '' closure (parabolicCylinder 0 0 1) :=
          ⟨z, hz, rfl⟩
        rw [← himage, goodPointRescaleCylinder_image x₀ t₀ r hr] at hmem
        exact hmem
      have hpre := goodPointRescaleDomain_preimage Ω I x₀ t₀ r hr
      rw [hpre]
      exact hclosure hΦz
    have henergyᵣ : goodPointEnergy uᵣ pᵣ 0 0 1 < ENNReal.ofReal ε₀ := by
      calc
        goodPointEnergy uᵣ pᵣ 0 0 1 =
            ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p x₀ t₀ r := by
          exact goodPointEnergy_rescale u p x₀ t₀ r hr
        _ = goodPointEnergy u p x₀ t₀ r * ENNReal.ofReal (r⁻¹ ^ 2) := mul_comm _ _
        _ < ENNReal.ofReal ε₀ := hsmall
    have hAdata := hA (CKN.rescaledSpace r x₀ Ω)
      (CKN.rescaledTime r t₀ I) uᵣ Duᵣ pᵣ fᵣ hSuitableᵣ hclosureᵣ
    have hforce : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (uᵣ z)) ^ (3 : ℝ) +
          ENNReal.ofReal |pᵣ z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (fᵣ z)) ^ q) ≤
        ENNReal.ofReal ε₀ := by
      have hqpos : 0 < q := lt_trans (by norm_num) hq
      simpa only [goodPointEnergy, fᵣ, vec3EuclideanNorm_zero,
        ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hqpos, add_zero]
        using le_of_lt henergyᵣ
    obtain ⟨wᵣ, hwᵣAE, hwᵣHolder, _⟩ := hAdata hforce
    let w : ParabolicPoint → Vec3 := fun z => r⁻¹ • wᵣ (Φ.symm z)
    have himageHalf : Φ '' parabolicCylinder 0 0 (1 / 2) =
        parabolicCylinder x₀ t₀ (r / 2) := by
      simpa [Φ] using goodPointRescaleHalfCylinder_image x₀ t₀ r hr
    have hpreimageHalf : Φ.symm ⁻¹' parabolicCylinder 0 0 (1 / 2) =
        parabolicCylinder x₀ t₀ (r / 2) := by
      ext z
      constructor
      · intro hz
        have hEq : z ∈ Φ '' parabolicCylinder 0 0 (1 / 2) :=
          ⟨Φ.symm z, hz, Φ.apply_symm_apply z⟩
        rw [himageHalf] at hEq
        exact hEq
      · intro hz
        have hz' : z ∈ Φ '' parabolicCylinder 0 0 (1 / 2) := by
          rw [himageHalf]
          exact hz
        rcases hz' with ⟨z', hz', hEq⟩
        have : z' = Φ.symm z := by
          calc
            z' = Φ.symm (Φ z') := by simp
            _ = Φ.symm z := congrArg Φ.symm hEq
        simpa [this] using hz'
    have hqmp := goodPointRescaleQuasiMeasurePreserving_symm
      x₀ t₀ r hr (parabolicCylinder 0 0 (1 / 2))
      (measurableSet_parabolicCylinder 0 0 (1 / 2))
    rw [hpreimageHalf] at hqmp
    have hwAEpull := hqmp.ae hwᵣAE
    have hwAE : w =ᵐ[volume.restrict
        (parabolicCylinder x₀ t₀ (r / 2))] u := by
      filter_upwards [hwAEpull] with z hz
      have hval : wᵣ (Φ.symm z) = r • u z := by
        calc
          wᵣ (Φ.symm z) = uᵣ (Φ.symm z) := hz
          _ = r • u (Φ (Φ.symm z)) := by
            change r • u (parabolicTranslate x₀ t₀
              (parabolicScale r (Φ.symm z))) = _
            rw [← goodPointRescaleHomeomorph_apply x₀ t₀ r hr (Φ.symm z)]
          _ = r • u z := by rw [Φ.apply_symm_apply]
      change r⁻¹ • wᵣ (Φ.symm z) = u z
      rw [hval, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    have hholderBounds : ∀ y ∈ closure (parabolicCylinder 0 0 (1 / 2)),
        vec3EuclideanNorm (wᵣ y) ≤ C₄ := by
      rcases hwᵣHolder with ⟨B, K, hB, hK, hBK, hbound, hsemi⟩
      intro y hy
      exact (hbound y hy).trans (le_trans (le_add_of_nonneg_right hK) hBK)
    have hholderSemi : ∀ y ∈ closure (parabolicCylinder 0 0 (1 / 2)),
        ∀ y' ∈ closure (parabolicCylinder 0 0 (1 / 2)),
          vec3EuclideanNorm (wᵣ y - wᵣ y') ≤
            C₄ * parabolicDist y y' ^ γ₀ := by
      rcases hwᵣHolder with ⟨B, K, hB, hK, hBK, hbound, hsemi⟩
      intro y hy y' hy'
      exact (hsemi y hy y' hy').trans
        (mul_le_mul_of_nonneg_right
          (le_trans (le_add_of_nonneg_left hB) hBK)
          (Real.rpow_nonneg (parabolicDist_nonneg y y') γ₀))
    have hdist (z z' : ParabolicPoint) :
        parabolicDist (Φ.symm z) (Φ.symm z') =
          r⁻¹ * parabolicDist z z' := by
      let z₁ : ParabolicPoint := (-(r⁻¹ • x₀), -((r⁻¹) ^ 2 * t₀))
      have hinv : Φ.symm = CKN.scalingParabolic r⁻¹ z₁ := by
        funext y
        apply parabolicHomeomorph.injective
        ext <;> simp [Φ, z₁, goodPointRescaleHomeomorph,
          CKN.scalingParabolic, parabolicTranslate, parabolicScale,
          Homeomorph.prodCongr, Homeomorph.smulOfNeZero,
          Homeomorph.addLeft, Units.smul_def, inv_pow]
      rw [hinv]
      change max
          (vec3EuclideanNorm
            ((z₁.1 + r⁻¹ • z.1) - (z₁.1 + r⁻¹ • z'.1)))
          (Real.sqrt |(z₁.2 + (r⁻¹) ^ 2 * z.2) -
            (z₁.2 + (r⁻¹) ^ 2 * z'.2)|) =
        r⁻¹ * max (vec3EuclideanNorm (z.1 - z'.1))
          (Real.sqrt |z.2 - z'.2|)
      have hspace :
          vec3EuclideanNorm
              ((z₁.1 + r⁻¹ • z.1) - (z₁.1 + r⁻¹ • z'.1)) =
            r⁻¹ * vec3EuclideanNorm (z.1 - z'.1) := by
        have hdiff : (z₁.1 + r⁻¹ • z.1) -
            (z₁.1 + r⁻¹ • z'.1) = r⁻¹ • (z.1 - z'.1) := by
          module
        rw [hdiff, vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      have htime :
          Real.sqrt |(z₁.2 + (r⁻¹) ^ 2 * z.2) -
              (z₁.2 + (r⁻¹) ^ 2 * z'.2)| =
            r⁻¹ * Real.sqrt |z.2 - z'.2| := by
        have hdiff : (z₁.2 + (r⁻¹) ^ 2 * z.2) -
            (z₁.2 + (r⁻¹) ^ 2 * z'.2) =
              (r⁻¹) ^ 2 * (z.2 - z'.2) := by ring
        rw [hdiff, abs_mul, abs_of_nonneg (sq_nonneg r⁻¹), Real.sqrt_mul
          (sq_nonneg r⁻¹), Real.sqrt_sq_eq_abs,
          abs_of_pos (inv_pos.mpr hr)]
      change max _ _ = r⁻¹ * max _ _
      rw [hspace, htime]
      rcases le_total (vec3EuclideanNorm (z.1 - z'.1))
          (Real.sqrt |z.2 - z'.2|) with hle | hge
      · rw [max_eq_right hle, max_eq_right
          (mul_le_mul_of_nonneg_left hle (inv_pos.mpr hr).le)]
      · rw [max_eq_left hge, max_eq_left
          (mul_le_mul_of_nonneg_left hge (inv_pos.mpr hr).le)]
    refine ⟨w, hwAE, ?_, ?_⟩
    · intro z hz
      have hy : Φ.symm z ∈ closure (parabolicCylinder 0 0 (1 / 2)) := by
        have hmap : z ∈ Φ '' closure (parabolicCylinder 0 0 (1 / 2)) := by
          have hc := Φ.isClosedEmbedding.closure_image_eq
            (parabolicCylinder 0 0 (1 / 2))
          rw [himageHalf] at hc
          exact hc.symm ▸ hz
        rcases hmap with ⟨y, hy, heq⟩
        have hyEq : y = Φ.symm z := Φ.injective (by simpa using heq)
        simpa [hyEq] using hy
      change vec3EuclideanNorm (r⁻¹ • wᵣ (Φ.symm z)) ≤ C₄ * r⁻¹
      rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * vec3EuclideanNorm (wᵣ (Φ.symm z)) ≤ r⁻¹ * C₄ :=
          mul_le_mul_of_nonneg_left (hholderBounds _ hy) (inv_pos.mpr hr).le
        _ = C₄ * r⁻¹ := by ring
    · intro z hz z' hz'
      have hy : Φ.symm z ∈ closure (parabolicCylinder 0 0 (1 / 2)) := by
        have hc := Φ.isClosedEmbedding.closure_image_eq
          (parabolicCylinder 0 0 (1 / 2))
        rw [himageHalf] at hc
        have hzImage : z ∈ Φ '' closure (parabolicCylinder 0 0 (1 / 2)) :=
          hc.symm ▸ hz
        rcases hzImage with ⟨y, hy, heq⟩
        have : y = Φ.symm z := Φ.injective (by simpa using heq)
        simpa [this] using hy
      have hy' : Φ.symm z' ∈ closure (parabolicCylinder 0 0 (1 / 2)) := by
        have hc := Φ.isClosedEmbedding.closure_image_eq
          (parabolicCylinder 0 0 (1 / 2))
        rw [himageHalf] at hc
        have hzImage : z' ∈ Φ '' closure (parabolicCylinder 0 0 (1 / 2)) :=
          hc.symm ▸ hz'
        rcases hzImage with ⟨y, hy, heq⟩
        have : y = Φ.symm z' := Φ.injective (by simpa using heq)
        simpa [this] using hy
      have hbase := hholderSemi _ hy _ hy'
      change vec3EuclideanNorm
          (r⁻¹ • wᵣ (Φ.symm z) - r⁻¹ • wᵣ (Φ.symm z')) ≤ _
      rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      rw [hdist z z'] at hbase
      have hrpow : (r⁻¹ * parabolicDist z z') ^ γ₀ =
          r⁻¹ ^ γ₀ * parabolicDist z z' ^ γ₀ := by
        rw [Real.mul_rpow (inv_nonneg.mpr hr.le)
          (parabolicDist_nonneg z z')]
      rw [hrpow] at hbase
      have hbase' : vec3EuclideanNorm
            (wᵣ (Φ.symm z) - wᵣ (Φ.symm z')) ≤
          C₄ * r⁻¹ ^ γ₀ * parabolicDist z z' ^ γ₀ := by
        calc
          _ ≤ C₄ * (r⁻¹ ^ γ₀ * parabolicDist z z' ^ γ₀) := hbase
          _ = C₄ * r⁻¹ ^ γ₀ * parabolicDist z z' ^ γ₀ := by ring
      have hfactor : r⁻¹ * (C₄ * r⁻¹ ^ γ₀ *
          parabolicDist z z' ^ γ₀) =
          C₄ * (r⁻¹ * r⁻¹ ^ γ₀) * parabolicDist z z' ^ γ₀ := by ring
      calc
        r⁻¹ * vec3EuclideanNorm (wᵣ (Φ.symm z) - wᵣ (Φ.symm z')) ≤
            r⁻¹ * (C₄ * r⁻¹ ^ γ₀ * parabolicDist z z' ^ γ₀) :=
          mul_le_mul_of_nonneg_left hbase' (inv_pos.mpr hr).le
        _ = C₄ * (r⁻¹ * r⁻¹ ^ γ₀) * parabolicDist z z' ^ γ₀ := hfactor

end ESS
