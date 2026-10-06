/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteCompactnessInputs
public import LeanPool.CIVAxisymmetric.Zoom.FiniteLift

/-!
# The lifted finite-axis fields: divergence, bounds and measurability

In Step 2 of the proof of `prop:aniso:small` the rescaled potential vorticity `Ω_n` and the drift
`B_n = (V_n X/R, W_n)` of `eq:drift:Bn:def` are regarded as functions on `ℝ⁴ × ℝ × (-∞, -1]`
(`eq:aniso:zoom:lifted`). The divergence of the drift is `div_{X,Z} B_n = 2 V_n / R`, continued
to the axis by `2 ∂_R V_n` (`finDriftDiv`). On a compact set of the lifted variables with
`τ < -1`, for all large `n`, the three fields are almost everywhere continuous (the axis is a
null set) and bounded by a constant independent of `n`, by `eq:aniso:zoom:finite:bound` and
`eq:aniso:zoom:derivatives`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The lifted divergence `div_{X,Z} B_n = 2 V_n / R`, continued to the axis by `2 ∂_R V_n`. -/
@[expose] def finDriftDiv (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (z : Vec 5 × ℝ) : ℝ :=
  if zoomLiftRadius z.1 = 0 then 2 * dr (zoomV lam h zc u) (zoomLiftPoint z)
  else 2 * zoomV lam h zc u (zoomLiftPoint z) / zoomLiftRadius z.1

/-- The zoom map composed with the lift is continuous. -/
theorem continuous_zoomPoint_zoomLiftPoint (lam h zc : ℝ) :
    Continuous (Y := Vec3 × ℝ) (fun z : Vec 5 × ℝ => zoomPoint lam h zc (zoomLiftPoint z)) :=
  (continuous_zoomPoint lam h zc).comp continuous_zoomLiftPoint

theorem zoomLiftRadius_continuous : Continuous zoomLiftRadius := by
  unfold zoomLiftRadius; fun_prop

/-- The off-axis part of the lifted preimage of the unit cylinder. -/
@[expose] def finLiftDomain (lam h zc : ℝ) : Set (Vec 5 × ℝ) :=
  {z | 0 < zoomLiftRadius z.1 ∧ zoomPoint lam h zc (zoomLiftPoint z) ∈ unitCylinder}

theorem isOpen_finLiftDomain (lam h zc : ℝ) : IsOpen (finLiftDomain lam h zc) :=
  (isOpen_lt continuous_const (zoomLiftRadius_continuous.comp continuous_fst)).inter
    (isOpen_unitCylinder_prod.preimage (continuous_zoomPoint_zoomLiftPoint lam h zc))

/-- The three lifted fields are continuous off the axis on the lifted preimage. -/
theorem continuousOn_finLift_fields {lam h zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContinuousOn (zoomOmegaLift lam h zc u) (finLiftDomain lam h zc) ∧
      ContinuousOn (zoomDrift lam h zc u) (finLiftDomain lam h zc) ∧
      ContinuousOn (finDriftDiv lam h zc u) (finLiftDomain lam h zc) := by
  set O := finLiftDomain lam h zc with hO
  set P : Vec 5 × ℝ → Vec3 × ℝ := fun z => zoomPoint lam h zc (zoomLiftPoint z) with hP
  have hPc : Continuous P := continuous_zoomPoint_zoomLiftPoint lam h zc
  have hPO : MapsTo P O unitCylinder := fun z hz => hz.2
  have hcomp : ∀ i : Fin 3, ContinuousOn (fun z => u (P z) i) O := fun i =>
    (contDiffOn_component hu i).continuousOn.comp hPc.continuousOn hPO
  have hR : ContinuousOn (fun z : Vec 5 × ℝ => zoomLiftRadius z.1) O :=
    (zoomLiftRadius_continuous.comp continuous_fst).continuousOn
  have hRne : ∀ z ∈ O, zoomLiftRadius z.1 ≠ 0 := fun z hz => hz.1.ne'
  have hV : ContinuousOn (fun z => zoomV lam h zc u (zoomLiftPoint z)) O :=
    continuousOn_const.mul (hcomp 0)
  have hW : ContinuousOn (fun z => zoomW lam h zc u (zoomLiftPoint z)) O :=
    continuousOn_const.mul (hcomp 2)
  refine ⟨?_, ?_, ?_⟩
  · have hω : ContinuousOn (fun z => azimuthalVorticity u (P z)) O :=
      (contDiffOn_azimuthalVorticity hu).continuousOn.comp hPc.continuousOn hPO
    have hP0 : ∀ z, (P z).1 0 = lam * zoomLiftRadius z.1 := fun z => by
      simp [hP, zoomPoint, zoomLiftPoint, meridional]
    have hP0c : ContinuousOn (fun z => (P z).1 0) O :=
      ((continuous_apply 0).comp (continuous_fst.comp hPc)).continuousOn
    have hne : ∀ z ∈ O, (P z).1 0 ≠ 0 := fun z hz => by
      rw [hP0]; exact mul_ne_zero hlam.ne' hz.1.ne'
    have hmain : ContinuousOn
        (fun z => lam ^ 3 * lam ^ (2 * h) * (azimuthalVorticity u (P z) / (P z).1 0)) O :=
      continuousOn_const.mul (hω.div hP0c hne)
    refine hmain.congr fun z hz => ?_
    change zoomOmega lam h zc u (zoomLiftPoint z) = _
    unfold zoomOmega
    rw [potentialVorticity_eq_div u (hne z hz)]
  · refine continuousOn_pi.2 fun i => ?_
    by_cases hi : i = 4
    · subst hi
      exact hW.congr fun z _ => by simp [zoomDrift]
    · have hX : ContinuousOn (fun z : Vec 5 × ℝ => z.1 i / zoomLiftRadius z.1) O :=
        ((continuous_apply i).comp continuous_fst).continuousOn.div hR hRne
      exact (hV.mul hX).congr fun z _ => by simp [zoomDrift, hi]
  · have hmain : ContinuousOn
        (fun z => 2 * zoomV lam h zc u (zoomLiftPoint z) / zoomLiftRadius z.1) O :=
      (continuousOn_const.mul hV).div hR hRne
    refine hmain.congr fun z hz => ?_
    simp [finDriftDiv, hRne z hz]

/-- Almost every lifted point of a set lies off the axis, for the restricted measure. -/
theorem ae_restrict_zoomLiftRadius_pos (K : Set (Vec 5 × ℝ)) :
    ∀ᵐ z ∂(volume.restrict K), 0 < zoomLiftRadius z.1 :=
  ae_zoomLiftRadius_pos _ Measure.restrict_le_self.absolutelyContinuous

/-- A function continuous on the off-axis part of a measurable set is almost everywhere strongly
measurable for the restricted measure. -/
theorem aestronglyMeasurable_of_continuousOn_offAxis {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] {g : Vec 5 × ℝ → E} {K : Set (Vec 5 × ℝ)} (hK : MeasurableSet K)
    (hg : ContinuousOn g (K ∩ {z | 0 < zoomLiftRadius z.1})) :
    AEStronglyMeasurable g (volume.restrict K) := by
  have hm : MeasurableSet (K ∩ {z : Vec 5 × ℝ | 0 < zoomLiftRadius z.1}) :=
    hK.inter (measurableSet_lt measurable_const
      (zoomLiftRadius_continuous.comp continuous_fst).measurable)
  have h1 := hg.aestronglyMeasurable (μ := volume) hm
  have hset : (K ∩ {z : Vec 5 × ℝ | 0 < zoomLiftRadius z.1} : Set (Vec 5 × ℝ)) =ᵐ[volume] K := by
    have hnull : volume ({z : Vec 5 × ℝ | 0 < zoomLiftRadius z.1})ᶜ = 0 := by
      refine measure_mono_null (fun z hz => ?_) volume_zoomLiftAxis_eq_zero
      have hz' : ¬ 0 < zoomLiftRadius z.1 := hz
      exact le_antisymm (not_lt.mp hz') (zoomLiftRadius_nonneg z.1)
    have := (ae_eq_univ.mpr hnull).inter (ae_eq_refl K)
    simpa [inter_comm] using this
  rwa [Measure.restrict_congr_set hset] at h1

/-- `F2-B`: on a compact set of the lifted variables with `τ < -1`, for all large `n`, the lifted
scalar, drift and divergence are almost everywhere strongly measurable and bounded by `2C`. -/
theorem finDrift_bounds {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ K : Set (Vec 5 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio (-1) → ∃ M : ℝ,
      ∀ᶠ n in atTop,
        AEStronglyMeasurable (zoomOmegaLift (lam n) h (zc n) u) (volume.restrict K) ∧
        AEStronglyMeasurable (zoomDrift (lam n) h (zc n) u) (volume.restrict K) ∧
        AEStronglyMeasurable (finDriftDiv (lam n) h (zc n) u) (volume.restrict K) ∧
        ∀ z ∈ K, |zoomOmegaLift (lam n) h (zc n) u z| ≤ M ∧
          ‖zoomDrift (lam n) h (zc n) u z‖ ≤ M ∧ |finDriftDiv (lam n) h (zc n) u z| ≤ M := by
  intro K hK hKs
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  refine ⟨2 * C, ?_⟩
  have hKL : IsCompact (zoomLiftPoint '' K) := hK.image continuous_zoomLiftPoint
  have hKLt : ∀ p ∈ zoomLiftPoint '' K, p.2 < 0 := by
    rintro _ ⟨z, hz, rfl⟩
    have := (hKs hz).2
    change z.2 < 0
    linarith only [(show z.2 < -1 from this)]
  filter_upwards [eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim
      _ hKL hKLt, eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim] with n hn hl
  have hmem : ∀ z ∈ K, zoomPoint (lam n) h (zc n) (zoomLiftPoint z) ∈ unitCylinder :=
    fun z hz => hn _ (mem_image_of_mem _ hz)
  have hτ : ∀ z ∈ K, z.2 ≤ -1 := fun z hz => le_of_lt (hKs hz).2
  obtain ⟨hcΩ, hcB, hcD⟩ := continuousOn_finLift_fields (lam := lam n) (h := h) (zc := zc n)
    hl.1 hu
  have hsub : K ∩ {z | 0 < zoomLiftRadius z.1} ⊆ finLiftDomain (lam n) h (zc n) :=
    fun z hz => ⟨hz.2, hmem z hz.1⟩
  have hr1 : ∀ z ∈ K, (-z.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := fun z hz =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hτ z hz]) (by norm_num)
  refine ⟨aestronglyMeasurable_of_continuousOn_offAxis hK.measurableSet (hcΩ.mono hsub),
    aestronglyMeasurable_of_continuousOn_offAxis hK.measurableSet (hcB.mono hsub),
    aestronglyMeasurable_of_continuousOn_offAxis hK.measurableSet (hcD.mono hsub),
    fun z hz => ?_⟩
  have hCr : C * (-(zoomLiftPoint z).2) ^ (-(1 / 2 : ℝ)) ≤ C :=
    mul_le_of_le_one_right hC (hr1 z hz)
  refine ⟨?_, ?_, ?_⟩
  · exact abs_zoomOmega_le_two_mul_const hl.1 hb hu2 haxi (hmem z hz) hC hl.2.2 hh.1 hh.2 (hτ z hz)
  · have := norm_zoomDrift_le hl.1 hb (hmem z hz) hC hh.1.le (hτ z hz)
    have hCr' : C * (-z.2) ^ (-(1 / 2 : ℝ)) ≤ C := mul_le_of_le_one_right hC (hr1 z hz)
    linarith only [this, hCr', hC]
  · unfold finDriftDiv
    split_ifs with h0
    · have hax : (zoomLiftPoint z).1.1 = 0 := h0
      have := abs_dr_zoomV_le_rpow_neg_half hl.1 hb hu2 (hmem z hz) hC (hτ z hz)
      rw [abs_mul, abs_two]
      linarith only [this, hCr]
    · have := abs_zoomV_div_le hl.1 hb hu2 haxi (hmem z hz) h0 hC (hτ z hz)
      have heq : 2 * zoomV (lam n) h (zc n) u (zoomLiftPoint z) / zoomLiftRadius z.1
          = 2 * (zoomV (lam n) h (zc n) u (zoomLiftPoint z) / (zoomLiftPoint z).1.1) := by
        rw [mul_div_assoc]; rfl
      rw [heq, abs_mul, abs_two]
      linarith only [this, hCr]

end CIV

namespace CIV

/-- `F2-S` (`eq:aniso:zoom:finite:strong`): if the rescaled potential vorticities converge
uniformly on compact subsets of `{R > 0, τ ≤ -1}`, their lifts converge in `L¹` on every compact
subset of `ℝ⁵ × (-∞, -1)`: off a thin tube around the axis the convergence is uniform, and the
tube, on which both sides stay bounded, has small measure. -/
theorem tendsto_lintegral_zoomOmegaLift {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (Ω : (ℝ × ℝ) × ℝ → ℝ)
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K →
      K ⊆ {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomOmega (lam n) h (zc n) u) Ω atTop K) :
    ∀ K : Set (Vec 5 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio (-1) →
      Tendsto (fun n => ∫⁻ z in K, ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ)
        atTop (nhds 0) := by
  intro K hK hKs
  have hRc : Continuous fun z : Vec 5 × ℝ => zoomLiftRadius z.1 :=
    zoomLiftRadius_continuous.comp continuous_fst
  -- the tubes around the axis
  set T : ℕ → Set (Vec 5 × ℝ) :=
    fun k => K ∩ {z | zoomLiftRadius z.1 < 1 / ((k : ℝ) + 1)} with hT
  have hTanti : Antitone T := by
    intro i j hij z hz
    refine ⟨hz.1, show zoomLiftRadius z.1 < _ from lt_of_lt_of_le hz.2 ?_⟩
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [this])
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    hK.measurableSet.inter (measurableSet_lt hRc.measurable measurable_const)
  have hInter : volume (⋂ k, T k) = 0 := by
    refine measure_mono_null (fun z hz => ?_) volume_zoomLiftAxis_eq_zero
    have hle : ∀ k : ℕ, zoomLiftRadius z.1 < 1 / ((k : ℝ) + 1) := fun k =>
      (mem_iInter.mp hz k).2
    refine le_antisymm (le_of_forall_pos_lt_add fun e he => ?_) (zoomLiftRadius_nonneg z.1)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt he
    simpa using lt_trans (hle k) hk
  have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hTlim : Tendsto (fun k => volume (T k)) atTop (nhds 0) := by
    have := tendsto_measure_iInter_atTop (μ := volume) (fun k => (hTm k).nullMeasurableSet)
      hTanti ⟨0, ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)⟩
    rwa [hInter] at this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hMT : Tendsto (fun k => ENNReal.ofReal (3 * C) * volume (T k)) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul hTlim (Or.inr (ENNReal.ofReal_ne_top (r := 3 * C)))
    rwa [mul_zero] at h
  obtain ⟨k, hk⟩ := (hMT.eventually (gt_mem_nhds hε2)).exists
  -- the part of `K` away from the axis
  set K' : Set (Vec 5 × ℝ) := K ∩ {z | 1 / ((k : ℝ) + 1) ≤ zoomLiftRadius z.1} with hK'
  have hK'c : IsCompact K' := hK.inter_right (isClosed_le continuous_const hRc)
  have hK'img : zoomLiftPoint '' K' ⊆ {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨lt_of_lt_of_le (by positivity) hz.2, le_of_lt (hKs hz.1).2⟩
  have hunif : TendstoUniformlyOn (fun n z => zoomOmegaLift (lam n) h (zc n) u z)
      (fun z => Ω (zoomLiftPoint z)) atTop K' :=
    ((hconv _ (hK'c.image continuous_zoomLiftPoint) hK'img).comp zoomLiftPoint).mono
      (fun z hz => mem_image_of_mem _ hz)
  have hfar := tendsto_setLIntegral_enorm_sub_of_tendstoUniformlyOn (μ := volume)
    hK'c.measurableSet (ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)) hunif
  obtain ⟨M, hM⟩ := finDrift_bounds hh hρ0 hρ1 hC hb hu haxi hzc hlam_lim K hK hKs
  -- the pointwise bound of the limit off the axis
  have hΩb : ∀ z ∈ K, 0 < zoomLiftRadius z.1 → |Ω (zoomLiftPoint z)| ≤ C := by
    intro z hz hR
    have hτ : z.2 < -1 := (hKs hz).2
    have hpt := (hconv {zoomLiftPoint z} isCompact_singleton (fun x hx => by
      rw [mem_singleton_iff.mp hx]; exact ⟨hR, le_of_lt hτ⟩)).tendsto_at (mem_singleton _)
    have h1 := abs_le_of_tendsto_zoomOmega hh hρ0 hρ1 hb hu haxi hzc hlam_pos hlam_lim
      (show (zoomLiftPoint z).2 < 0 by change z.2 < 0; linarith only [hτ]) hpt
    have hr : (-(zoomLiftPoint z).2) ^ (-(3 / 2 : ℝ) - h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by change (1 : ℝ) ≤ -z.2; linarith only [hτ])
        (by linarith only [hh.1])
    exact h1.trans (mul_le_of_le_one_right hC hr)
  have hMle : ∀ᶠ n in atTop, ∀ z ∈ K, |zoomOmegaLift (lam n) h (zc n) u z| ≤ 2 * C := by
    filter_upwards [eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim,
      eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim
        (zoomLiftPoint '' K) (hK.image continuous_zoomLiftPoint) (by
          rintro _ ⟨z, hz, rfl⟩; change z.2 < 0; linarith only [(show z.2 < -1 from (hKs hz).2)])]
            with n hl hn z hz
    exact abs_zoomOmega_le_two_mul_const hl.1 hb (hu.of_le (by simp)) haxi
      (hn _ (mem_image_of_mem _ hz)) hC hl.2.2 hh.1 hh.2 (le_of_lt (hKs hz).2)
  filter_upwards [hfar.eventually (ge_mem_nhds hε2), hMle] with n hn hMn
  have hsplit : K ⊆ K' ∪ T k := by
    intro z hz
    by_cases hR : 1 / ((k : ℝ) + 1) ≤ zoomLiftRadius z.1
    · exact Or.inl ⟨hz, hR⟩
    · exact Or.inr ⟨hz, not_le.mp hR⟩
  have htube : ∫⁻ z in T k, ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ
      ≤ ENNReal.ofReal (3 * C) * volume (T k) := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_zoomLiftRadius_pos (T k), ae_restrict_mem (hTm k)] with z hR hzT
    rw [← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hMn z hzT.1
    have h2 := hΩb z hzT.1 hR
    calc |zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)|
        ≤ |zoomOmegaLift (lam n) h (zc n) u z| + |Ω (zoomLiftPoint z)| := abs_sub _ _
      _ ≤ 3 * C := by linarith only [h1, h2]
  calc ∫⁻ z in K, ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ
      ≤ ∫⁻ z in K' ∪ T k, ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ :=
        lintegral_mono_set hsplit
    _ ≤ (∫⁻ z in K', ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ)
        + ∫⁻ z in T k, ‖zoomOmegaLift (lam n) h (zc n) u z - Ω (zoomLiftPoint z)‖ₑ :=
        lintegral_union_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hn (htube.trans hk.le)
    _ = ε := ENNReal.add_halves ε

end CIV
