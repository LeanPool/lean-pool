/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.RescalingSuitable
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Regular points under parabolic rescaling

The affine change of variables transports open neighborhoods, almost-everywhere
representatives, and parabolic Hölder bounds in both directions.
-/

public section

open MeasureTheory Set
open CKN
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

@[expose] def rescaleHomeomorph (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x₀))
      ((Homeomorph.smulOfNeZero (r ^ 2) (sq_pos_of_pos hr).ne').trans
        (Homeomorph.addLeft t₀)))).trans parabolicHomeomorph.symm

private theorem rescaleHomeomorph_apply (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (z : ParabolicPoint) :
    rescaleHomeomorph x₀ t₀ r hr z =
      parabolicTranslate x₀ t₀ (parabolicScale r z) := by
  rfl

private theorem rescaleHomeomorph_eq_scalingParabolic (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) :
    rescaleHomeomorph x₀ t₀ r hr = CKN.scalingParabolic r (x₀, t₀) := by
  funext z
  rfl

private theorem parabolicDist_nonneg (z w : ParabolicPoint) :
    0 ≤ parabolicDist z w := by
  simp only [parabolicDist]
  positivity

private theorem max_mul_of_nonneg_left {a b c : ℝ} (hc : 0 ≤ c) :
    max (c * a) (c * b) = c * max a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (mul_le_mul_of_nonneg_left hab hc)]
  · rw [max_eq_left hba, max_eq_left (mul_le_mul_of_nonneg_left hba hc)]

/-- Parabolic distance is multiplied by `r` under the affine rescaling map. -/
private theorem parabolicDist_rescale (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (z w : ParabolicPoint) :
    parabolicDist (rescaleHomeomorph x₀ t₀ r hr z)
        (rescaleHomeomorph x₀ t₀ r hr w) = r * parabolicDist z w := by
  rw [rescaleHomeomorph_apply, rescaleHomeomorph_apply]
  have hspace :
      vec3EuclideanNorm
          ((parabolicTranslate x₀ t₀ (parabolicScale r z)).1 -
            (parabolicTranslate x₀ t₀ (parabolicScale r w)).1) =
        r * vec3EuclideanNorm (z.1 - w.1) := by
    change vec3EuclideanNorm ((x₀ + r • z.1) - (x₀ + r • w.1)) = _
    have hdiff : (x₀ + r • z.1) - (x₀ + r • w.1) = r • (z.1 - w.1) := by
      module
    rw [hdiff, vec3EuclideanNorm_smul, abs_of_pos hr]
  have htime :
      Real.sqrt |(parabolicTranslate x₀ t₀ (parabolicScale r z)).2 -
        (parabolicTranslate x₀ t₀ (parabolicScale r w)).2| =
        r * Real.sqrt |z.2 - w.2| := by
    change Real.sqrt |(t₀ + r ^ 2 * z.2) - (t₀ + r ^ 2 * w.2)| = _
    have hdiff : (t₀ + r ^ 2 * z.2) - (t₀ + r ^ 2 * w.2) =
        r ^ 2 * (z.2 - w.2) := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (sq_nonneg r), Real.sqrt_mul
      (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]
  change max _ _ = r * max _ _
  rw [hspace, htime]
  exact max_mul_of_nonneg_left (le_of_lt hr)

private theorem parabolicDist_rescale_symm (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (z w : ParabolicPoint) :
    parabolicDist ((rescaleHomeomorph x₀ t₀ r hr).symm z)
        ((rescaleHomeomorph x₀ t₀ r hr).symm w) = r⁻¹ * parabolicDist z w := by
  have h := parabolicDist_rescale x₀ t₀ r hr
    ((rescaleHomeomorph x₀ t₀ r hr).symm z)
    ((rescaleHomeomorph x₀ t₀ r hr).symm w)
  rw [(rescaleHomeomorph x₀ t₀ r hr).apply_symm_apply,
    (rescaleHomeomorph x₀ t₀ r hr).apply_symm_apply] at h
  calc
    parabolicDist ((rescaleHomeomorph x₀ t₀ r hr).symm z)
        ((rescaleHomeomorph x₀ t₀ r hr).symm w) =
        r⁻¹ * (r * parabolicDist
          ((rescaleHomeomorph x₀ t₀ r hr).symm z)
          ((rescaleHomeomorph x₀ t₀ r hr).symm w)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    _ = r⁻¹ * parabolicDist z w := by rw [← h]

private theorem rescaleHomeomorph_image_spaceTimeSet
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) (Ω : Set Vec3) (I : Set ℝ) :
    rescaleHomeomorph x₀ t₀ r hr ''
        spaceTimeSet (CKN.rescaledSpace r x₀ Ω) (CKN.rescaledTime r t₀ I) =
      spaceTimeSet Ω I := by
  rw [show spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
      (CKN.rescaledTime r t₀ I) =
      rescaleHomeomorph x₀ t₀ r hr ⁻¹' spaceTimeSet Ω I by
      rw [CKN.rescaledSpaceTimeSet_eq_preimage r (x₀, t₀) Ω I]
      rw [rescaleHomeomorph_eq_scalingParabolic]]
  exact (rescaleHomeomorph x₀ t₀ r hr).image_preimage _

private theorem map_rescaleHomeomorph
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    Measure.map (rescaleHomeomorph x₀ t₀ r hr) (volume : Measure ParabolicPoint) =
      ENNReal.ofReal (r⁻¹ ^ 5) • volume := by
  rw [rescaleHomeomorph_eq_scalingParabolic]
  exact CKN.map_scalingParabolic r hr (x₀, t₀)

private theorem map_rescaleHomeomorph_symm
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    Measure.map (rescaleHomeomorph x₀ t₀ r hr).symm
        (volume : Measure ParabolicPoint) =
      ENNReal.ofReal ((r⁻¹)⁻¹ ^ 5) • volume := by
  let x₁ : Vec3 := -(r⁻¹ • x₀)
  let t₁ : ℝ := -((r⁻¹) ^ 2 * t₀)
  have hinv : (rescaleHomeomorph x₀ t₀ r hr).symm =
      CKN.scalingParabolic r⁻¹ (x₁, t₁) := by
    funext z
    apply parabolicHomeomorph.injective
    ext <;>
      simp [rescaleHomeomorph, x₁, t₁, Homeomorph.prodCongr,
        Homeomorph.smulOfNeZero, Homeomorph.addLeft, Units.smul_def,
        CKN.scalingParabolic, parabolicTranslate, parabolicScale,
        parabolicHomeomorph_apply, inv_pow]
  rw [hinv]
  exact CKN.map_scalingParabolic (r⁻¹) (inv_pos.mpr hr) (x₁, t₁)

private theorem quasiMeasurePreserving_rescaleHomeomorph
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (N : Set ParabolicPoint) (hN : MeasurableSet N) :
    Measure.QuasiMeasurePreserving (rescaleHomeomorph x₀ t₀ r hr)
      (volume.restrict ((rescaleHomeomorph x₀ t₀ r hr) ⁻¹' N))
      (volume.restrict N) := by
  refine ⟨(rescaleHomeomorph x₀ t₀ r hr).measurable, ?_⟩
  have hmap := Measure.restrict_map
    (μ := (volume : Measure ParabolicPoint))
    (rescaleHomeomorph x₀ t₀ r hr).measurable hN
  rw [map_rescaleHomeomorph, Measure.restrict_smul] at hmap
  rw [hmap.symm]
  exact Measure.smul_absolutelyContinuous

private theorem quasiMeasurePreserving_rescaleHomeomorph_symm
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (N : Set ParabolicPoint) (hN : MeasurableSet N) :
    Measure.QuasiMeasurePreserving (rescaleHomeomorph x₀ t₀ r hr).symm
      (volume.restrict ((rescaleHomeomorph x₀ t₀ r hr).symm ⁻¹' N))
      (volume.restrict N) := by
  refine ⟨(rescaleHomeomorph x₀ t₀ r hr).symm.measurable, ?_⟩
  have hmap := Measure.restrict_map
    (μ := (volume : Measure ParabolicPoint))
    (rescaleHomeomorph x₀ t₀ r hr).symm.measurable hN
  rw [map_rescaleHomeomorph_symm, Measure.restrict_smul] at hmap
  rw [hmap.symm]
  exact Measure.smul_absolutelyContinuous

private theorem parabolicHolderVecOn_comp_rescale
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (N : Set ParabolicPoint) (g : ParabolicPoint → Vec3) (γ : ℝ)
    (hHolder : ParabolicHolderVecOn N g γ) :
    ParabolicHolderVecOn
      ((rescaleHomeomorph x₀ t₀ r hr) ⁻¹' N)
      (fun z => r • g (rescaleHomeomorph x₀ t₀ r hr z)) γ := by
  rcases hHolder with ⟨B, K, hB, hK, hbound, hsemi⟩
  refine ⟨r * B, r * K * r ^ γ, by positivity, by positivity, ?_, ?_⟩
  · intro z hz
    rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hbound _ hz) hr.le
  · intro z hz w hw
    have hdist := parabolicDist_rescale x₀ t₀ r hr z w
    calc
      vec3EuclideanNorm
          (r • g (rescaleHomeomorph x₀ t₀ r hr z) -
            r • g (rescaleHomeomorph x₀ t₀ r hr w)) =
          r * vec3EuclideanNorm
            (g (rescaleHomeomorph x₀ t₀ r hr z) -
              g (rescaleHomeomorph x₀ t₀ r hr w)) := by
                rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos hr]
      _ ≤ r * (K * parabolicDist
          (rescaleHomeomorph x₀ t₀ r hr z)
          (rescaleHomeomorph x₀ t₀ r hr w) ^ γ) :=
            mul_le_mul_of_nonneg_left
              (hsemi _ (hbound_domain hz) _ (hbound_domain hw)) hr.le
      _ = (r * K * r ^ γ) * parabolicDist z w ^ γ := by
            rw [hdist, Real.mul_rpow hr.le (parabolicDist_nonneg z w)]
            ring
where
  hbound_domain {z : ParabolicPoint}
      (hz : z ∈ (rescaleHomeomorph x₀ t₀ r hr) ⁻¹' N) :
      rescaleHomeomorph x₀ t₀ r hr z ∈ N := hz

private theorem parabolicHolderVecOn_image_rescale_symm
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (N : Set ParabolicPoint) (g : ParabolicPoint → Vec3) (γ : ℝ)
    (hHolder : ParabolicHolderVecOn N g γ) :
    ParabolicHolderVecOn
      ((rescaleHomeomorph x₀ t₀ r hr) '' N)
      (fun z => r⁻¹ • g ((rescaleHomeomorph x₀ t₀ r hr).symm z)) γ := by
  rcases hHolder with ⟨B, K, hB, hK, hbound, hsemi⟩
  have hrInv : 0 < r⁻¹ := inv_pos.mpr hr
  refine ⟨r⁻¹ * B, r⁻¹ * K * r⁻¹ ^ γ,
    by positivity, by positivity, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    change vec3EuclideanNorm
      (r⁻¹ • g ((rescaleHomeomorph x₀ t₀ r hr).symm
        (rescaleHomeomorph x₀ t₀ r hr w))) ≤ r⁻¹ * B
    rw [(rescaleHomeomorph x₀ t₀ r hr).symm_apply_apply]
    rw [vec3EuclideanNorm_smul, abs_of_pos hrInv]
    exact mul_le_mul_of_nonneg_left (hbound _ hw) hrInv.le
  · intro z hz w hw
    have hz' : (rescaleHomeomorph x₀ t₀ r hr).symm z ∈ N := by
      rcases hz with ⟨z', hz', hzEq⟩
      rw [← hzEq, (rescaleHomeomorph x₀ t₀ r hr).symm_apply_apply]
      exact hz'
    have hw' : (rescaleHomeomorph x₀ t₀ r hr).symm w ∈ N := by
      rcases hw with ⟨w', hw', hwEq⟩
      rw [← hwEq, (rescaleHomeomorph x₀ t₀ r hr).symm_apply_apply]
      exact hw'
    have hdist := parabolicDist_rescale_symm x₀ t₀ r hr z w
    calc
      vec3EuclideanNorm
          (r⁻¹ • g ((rescaleHomeomorph x₀ t₀ r hr).symm z) -
            r⁻¹ • g ((rescaleHomeomorph x₀ t₀ r hr).symm w)) =
          r⁻¹ * vec3EuclideanNorm
            (g ((rescaleHomeomorph x₀ t₀ r hr).symm z) -
              g ((rescaleHomeomorph x₀ t₀ r hr).symm w)) := by
                rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos hrInv]
      _ ≤ r⁻¹ * (K * parabolicDist
          ((rescaleHomeomorph x₀ t₀ r hr).symm z)
          ((rescaleHomeomorph x₀ t₀ r hr).symm w) ^ γ) :=
            mul_le_mul_of_nonneg_left (hsemi _ hz' _ hw') hrInv.le
      _ = (r⁻¹ * K * r⁻¹ ^ γ) * parabolicDist z w ^ γ := by
            rw [hdist, Real.mul_rpow hrInv.le (parabolicDist_nonneg z w)]
            ring

/-- Regularity is invariant under the affine parabolic rescaling.  The
neighborhood convention is that of the CKN regular-point definition. -/
theorem isRegularPoint_parabolicRescale_iff
    (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) (z : ParabolicPoint) :
    IsRegularPoint (CKN.rescaledSpace r x₀ Ω) (CKN.rescaledTime r t₀ I)
        (parabolicRescaleVelocity x₀ t₀ r u) z ↔
      IsRegularPoint Ω I u (CKN.scalingParabolic r (x₀, t₀) z) := by
  let Φ := rescaleHomeomorph x₀ t₀ r hr
  have hdomain := rescaleHomeomorph_image_spaceTimeSet x₀ t₀ r hr Ω I
  have hΦmap (y : ParabolicPoint) :
      Φ y = parabolicTranslate x₀ t₀ (parabolicScale r y) :=
    rescaleHomeomorph_apply x₀ t₀ r hr y
  have hdomain' :
      Φ '' spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
          (CKN.rescaledTime r t₀ I) = spaceTimeSet Ω I := by
    simpa [Φ] using hdomain
  constructor
  · intro hregular
    rcases hregular with
      ⟨hz, N, hNopen, hzn, hNsub, γ, hγ, hγle, w, hEq, hHolder⟩
    let N₀ : Set ParabolicPoint := Φ '' N
    let w₀ : ParabolicPoint → Vec3 := fun y => r⁻¹ • w (Φ.symm y)
    have hN₀open : IsOpen N₀ := by
      exact Φ.isOpenMap N hNopen
    have hzn₀ : Φ z ∈ N₀ := ⟨z, hzn, rfl⟩
    have hN₀sub : N₀ ⊆ spaceTimeSet Ω I := by
      intro y hy
      rcases hy with ⟨y', hy', rfl⟩
      rw [← hdomain']
      exact ⟨y', hNsub hy', rfl⟩
    have hdomainMem : Φ z ∈ spaceTimeSet Ω I := by
      have hzimg : Φ z ∈
          Φ '' spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
            (CKN.rescaledTime r t₀ I) := ⟨z, hz, rfl⟩
      rw [hdomain'] at hzimg
      exact hzimg
    have hholder₀ := parabolicHolderVecOn_image_rescale_symm
      x₀ t₀ r hr N w γ hHolder
    have hpre : Φ.symm ⁻¹' N = Φ '' N := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy
        exact ⟨Φ.symm y, hy, Φ.apply_symm_apply y⟩
      · rintro ⟨y', hy', hyEq⟩
        rw [← hyEq, Φ.symm_apply_apply]
        exact hy'
    have hqmp := quasiMeasurePreserving_rescaleHomeomorph_symm
      x₀ t₀ r hr N hNopen.measurableSet
    rw [hpre] at hqmp
    have hEqPull := hqmp.ae hEq
    have hEq₀ : w₀ =ᵐ[volume.restrict N₀] u := by
      filter_upwards [hEqPull] with y hy
      have hy' : w (Φ.symm y) =
          r • u (parabolicTranslate x₀ t₀
            (parabolicScale r (Φ.symm y))) := by
        simpa [Function.comp_def, parabolicRescaleVelocity,
          rescaleHomeomorph_apply, Φ] using hy
      have hpoint : parabolicTranslate x₀ t₀
          (parabolicScale r (Φ.symm y)) = y := by
        rw [← hΦmap, Φ.apply_symm_apply]
      rw [hpoint] at hy'
      change r⁻¹ • w (Φ.symm y) = u y
      rw [hy', smul_smul]
      rw [inv_mul_cancel₀ hr.ne', one_smul]
    refine ⟨hdomainMem, N₀, hN₀open, hzn₀, hN₀sub, γ, hγ, hγle,
      w₀, hEq₀, ?_⟩
    simpa [N₀, w₀, Φ] using hholder₀
  · intro hregular
    rcases hregular with
      ⟨hΦz, N₀, hN₀open, hΦzN₀, hN₀sub, γ, hγ, hγle, w, hEq, hHolder⟩
    let N : Set ParabolicPoint := Φ ⁻¹' N₀
    let w' : ParabolicPoint → Vec3 := fun y => r • w (Φ y)
    have hz : z ∈ spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
        (CKN.rescaledTime r t₀ I) := by
      have hzimg : Φ z ∈
          Φ '' spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
            (CKN.rescaledTime r t₀ I) := by
        rw [hdomain']
        exact hΦz
      rcases hzimg with ⟨y, hy, hEqz⟩
      have hyz : y = z := Φ.injective hEqz
      simpa [hyz] using hy
    have hNopen : IsOpen N := hN₀open.preimage Φ.continuous
    have hzn : z ∈ N := hΦzN₀
    have hNsub : N ⊆ spaceTimeSet
        (CKN.rescaledSpace r x₀ Ω) (CKN.rescaledTime r t₀ I) := by
      intro y hy
      have hΦy : Φ y ∈ spaceTimeSet Ω I := hN₀sub hy
      have himg : Φ y ∈
          Φ '' spaceTimeSet (CKN.rescaledSpace r x₀ Ω)
            (CKN.rescaledTime r t₀ I) := by
        rw [hdomain']
        exact hΦy
      rcases himg with ⟨y', hy', hEqy⟩
      have hyy' : y' = y := Φ.injective hEqy
      simpa [hyy'] using hy'
    have hholder' := parabolicHolderVecOn_comp_rescale
      x₀ t₀ r hr N₀ w γ hHolder
    have hqmp := quasiMeasurePreserving_rescaleHomeomorph
      x₀ t₀ r hr N₀ hN₀open.measurableSet
    have hEqPull := hqmp.ae hEq
    have hEq' : w' =ᵐ[volume.restrict N]
        parabolicRescaleVelocity x₀ t₀ r u := by
      filter_upwards [hEqPull] with y hy
      change r • w (Φ y) =
        parabolicRescaleVelocity x₀ t₀ r u y
      simpa [Function.comp_def, parabolicRescaleVelocity,
        rescaleHomeomorph_apply, Φ] using congrArg (fun v : Vec3 => r • v) hy
    refine ⟨hz, N, hNopen, hzn, hNsub, γ, hγ, hγle,
      w', hEq', ?_⟩
    simpa [N, w', Φ] using hholder'

/-- A regular point of the rescaled global positive-time solution pulls back to
the corresponding regular point of the original solution, in the rescaling
used by manuscript labels `lem:thmA-rescaled` and `lem:regular-point-shift`. -/
theorem isRegularPoint_parabolicRescale
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r)
    (hRegular : IsRegularPoint (Set.univ : Set Vec3)
      (Ioi (-(t₀ / r ^ 2)))
      (parabolicRescaleVelocity x₀ t₀ r u) (0, -(1 / 8 : ℝ))) :
    IsRegularPoint (Set.univ : Set Vec3) (Ioi 0) u
      (x₀, t₀ + r ^ 2 * (-(1 / 8 : ℝ))) := by
  have hiff := isRegularPoint_parabolicRescale_iff
    (Set.univ : Set Vec3) (Ioi (0 : ℝ)) u x₀ t₀ r hr
    (0, -(1 / 8 : ℝ))
  have hRegular' : IsRegularPoint (CKN.rescaledSpace r x₀ (Set.univ : Set Vec3))
      (CKN.rescaledTime r t₀ (Ioi (0 : ℝ)))
      (parabolicRescaleVelocity x₀ t₀ r u) (0, -(1 / 8 : ℝ)) := by
    rw [rescaledTime_Ioi_zero t₀ r hr]
    exact hRegular
  have hresult := hiff.mp hRegular'
  simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hresult


end ESS
