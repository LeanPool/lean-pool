/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffBridge
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianChangeBack
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianOperatorLocalized
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCarleman
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianParameters
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianInitialTrace
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShellCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianRadialMass
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianWeights
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatL2
public import LeanPool.EscauriazaSereginSverak.Linear.UCTrace
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverageBase

/-!
# The Gaussian average estimate for backward uniqueness

The cutoff equals the translated field on the normalized averaging box in
`lem:bu-gaussian`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

theorem buGaussian_shifted_cutoff_data_zero_late
    {ρ ε : ℝ} (hρ : 0 < ρ) (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    let κ : Vec3 × ℝ → ℝ := fun q =>
      ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) q
    (∀ z, z ∉ buCutSupportSet κ →
      buGaussianShiftedCutoffField ρ hρ ε v z = 0 ∧
        buGaussianShiftedCutoffDw ρ hρ ε v Dv z = 0 ∧
        buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v z = 0 ∧
        buGaussianShiftedCutoffDtw ρ hρ ε v Dtv z = 0) ∧
    (∀ z ∈ buCutSupportSet κ, z.2 ≤ 23 / 12) := by
  dsimp
  let θ : Vec3 → ℝ := ucSpatialCutoff ρ hρ
  let η : ℝ → ℝ := fun s => ucFinalTimeCutoff (s - 1 / 6)
  let χ : ℝ → ℝ := fun s => ucInitialTimeCutoff ε (s - 1 / 6)
  let κ : Vec3 × ℝ → ℝ := fun q => ucCutoffScalar θ η χ q
  let vσ := buGaussianShiftedField (1 / 6) v
  let Dvσ := buGaussianShiftedDw (1 / 6) Dv
  let D2vσ := buGaussianShiftedD2w (1 / 6) D2v
  let Dtvσ := buGaussianShiftedDtw (1 / 6) Dtv
  let K : Set ParabolicPoint := buCutSupportSet κ
  have hκsupport : Function.support κ ⊆ {q : Vec3 × ℝ | q.2 ≤ 23 / 12} := by
    intro q hq
    by_contra hnot
    have htime : 7 / 4 ≤ q.2 - 1 / 6 := by
      have hqtime : 23 / 12 < q.2 := lt_of_not_ge hnot
      linarith only [hqtime]
    have hfinal := ucFinalTimeCutoff_eq_zero htime
    have hzero : κ q = 0 := by
      change ucSpatialCutoff ρ hρ q.1 *
        ucFinalTimeCutoff (q.2 - 1 / 6) *
        ucInitialTimeCutoff ε (q.2 - 1 / 6) = 0
      rw [hfinal]
      ring_nf
    exact hq hzero
  have hκclosed : IsClosed {q : Vec3 × ℝ | q.2 ≤ 23 / 12} :=
    isClosed_le (continuous_snd) continuous_const
  have htsupport : tsupport κ ⊆ {q : Vec3 × ℝ | q.2 ≤ 23 / 12} :=
    closure_minimal hκsupport hκclosed
  have hKlate : ∀ z ∈ K, z.2 ≤ 23 / 12 := by
    intro z hz
    change parabolicHomeomorph z ∈ tsupport κ at hz
    have hlate := htsupport hz
    simpa only [parabolicHomeomorph_apply, Set.mem_ofPred_eq] using hlate
  have hscalarFun : buCutScalar κ = ucCutoffScalar θ η χ := by
    funext q
    rcases q with ⟨y, s⟩
    rfl
  have hfield (z : ParabolicPoint) : buGaussianShiftedCutoffField ρ hρ ε v z =
      buCutField κ vσ z := by
    change ucCutoffScalar θ η χ z • buGaussianShiftedField (1 / 6) v z =
      buCutScalar κ z • vσ z
    rw [hscalarFun]
  have hDw (z : ParabolicPoint) : buGaussianShiftedCutoffDw ρ hρ ε v Dv z =
      buCutDw κ vσ Dvσ z := by
    funext i j
    change ucCutoffScalar θ η χ z * buGaussianShiftedDw (1 / 6) Dv z i j +
        buGaussianShiftedField (1 / 6) v z i *
          spatialPartial (ucCutoffScalar θ η χ) j z =
      buCutScalar κ z * Dvσ z i j +
        vσ z i * spatialPartial (buCutScalar κ) j z
    rw [hscalarFun]
  have hD2 (z : ParabolicPoint) : buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v z =
      buCutD2 κ vσ Dvσ D2vσ z := by
    funext i j k
    change ucCutoffScalar θ η χ z *
        buGaussianShiftedD2w (1 / 6) D2v z i j k +
        spatialPartial (ucCutoffScalar θ η χ) k z *
          buGaussianShiftedDw (1 / 6) Dv z i j +
        spatialPartial (ucCutoffScalar θ η χ) j z *
          buGaussianShiftedDw (1 / 6) Dv z i k +
        buGaussianShiftedField (1 / 6) v z i *
          spatialSecondPartial (ucCutoffScalar θ η χ) j k z =
      buCutScalar κ z * D2vσ z i j k +
        spatialPartial (buCutScalar κ) k z * Dvσ z i j +
        spatialPartial (buCutScalar κ) j z * Dvσ z i k +
      vσ z i * spatialSecondPartial (buCutScalar κ) j k z
    rw [hscalarFun]
  have hDt (z : ParabolicPoint) : buGaussianShiftedCutoffDtw ρ hρ ε v Dtv z =
      buCutDt κ vσ Dtvσ z := by
    funext i
    change ucCutoffScalar θ η χ z *
        buGaussianShiftedDtw (1 / 6) Dtv z i +
        buGaussianShiftedField (1 / 6) v z i *
          timePartial (ucCutoffScalar θ η χ) z =
      buCutScalar κ z * Dtvσ z i +
        vσ z i * timePartial (buCutScalar κ) z
    rw [hscalarFun]
  constructor
  · intro z hz
    have hzero := buCut_data_zero_off_support κ vσ Dvσ D2vσ Dtvσ z hz
    exact ⟨hfield z |>.trans hzero.1, hDw z |>.trans hzero.2.1,
      hD2 z |>.trans hzero.2.2.1, hDt z |>.trans hzero.2.2.2⟩
  · exact hKlate

theorem buGaussian_sq_four_sum (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c),
    sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (c - d)]

theorem buGaussian_sq_main_sum (a b : ℝ) :
    (a + 3 * b) ^ 2 ≤ 2 * a ^ 2 + 18 * b ^ 2 := by
  nlinarith only [sq_nonneg (a - 3 * b)]

/-- The main differential term is absorbed by the Gaussian Carleman energy;
the remaining three terms retain their individual squares. -/
theorem buGaussian_weighted_four_error_bound
    {W q m g c b d e h : ℝ}
    (hW : 0 ≤ W) (hq : 1 / 2 ≤ q) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hh : 0 ≤ h)
    (hOp : h ≤ c * (Real.sqrt m + 3 * Real.sqrt g) + b + d + e) :
    W * h ^ 2 ≤ 72 * c ^ 2 * W * (q * m + g) +
      4 * W * (b ^ 2 + d ^ 2 + e ^ 2) := by
  have hsum0 : 0 ≤ c * (Real.sqrt m + 3 * Real.sqrt g) + b + d + e :=
    hh.trans hOp
  have hsq := (sq_le_sq₀ hh hsum0).2 hOp
  have hfour := buGaussian_sq_four_sum
    (c * (Real.sqrt m + 3 * Real.sqrt g)) b d e
  have hmain := buGaussian_sq_main_sum (Real.sqrt m) (Real.sqrt g)
  rw [Real.sq_sqrt hm, Real.sq_sqrt hg] at hmain
  have hqm : 2 * m ≤ 18 * q * m := by
    have hc : 0 ≤ 18 * q - 2 := by linarith only [hq]
    have hp := mul_nonneg hc hm
    nlinarith only [hp]
  have hmain' : (Real.sqrt m + 3 * Real.sqrt g) ^ 2 ≤
      18 * (q * m + g) := by
    nlinarith only [hmain, hqm]
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hsum : h ^ 2 ≤
      72 * c ^ 2 * (q * m + g) + 4 * (b ^ 2 + d ^ 2 + e ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hmain' hc2
    nlinarith only [hsq, hfour, hmul]
  have hweighted := mul_le_mul_of_nonneg_left hsum hW
  nlinarith only [hweighted]

/-- A fixed time slice of a space-time cylinder has zero volume. -/
theorem buGaussian_time_slice_null (B : Set Vec3) (s : ℝ) :
    volume (spaceTimeSet B ({s} : Set ℝ)) = 0 := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
    (B ×ˢ ({s} : Set ℝ)) = 0
  rw [Measure.prod_prod]
  simp

/-- Almost every parabolic point avoids a prescribed time. -/
theorem buGaussian_ae_time_ne (s : ℝ) :
    ∀ᵐ z : ParabolicPoint ∂volume, z.2 ≠ s := by
  rw [ae_iff]
  have hset : {z : ParabolicPoint | ¬z.2 ≠ s} =
      spaceTimeSet Set.univ ({s} : Set ℝ) := by
    ext z
    change (¬z.2 ≠ s) ↔
      z.1 ∈ (Set.univ : Set Vec3) ∧ z.2 ∈ ({s} : Set ℝ)
    simp
  rw [hset]
  exact buGaussian_time_slice_null Set.univ s

/-- Restricting a nonnegative integrand to another measurable region leaves
its integral nonnegative. -/
theorem buGaussian_indicator_integral_nonneg
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K S : Set X) (f : X → ℝ)
    (hf : 0 ≤ᵐ[μ.restrict K] f) :
    0 ≤ ∫ z in K, S.indicator f z ∂μ := by
  apply integral_nonneg_of_ae
  filter_upwards [hf] with z hz
  by_cases hS : z ∈ S
  · simpa [Set.indicator, hS] using hz
  · simp [Set.indicator, hS]

theorem buGaussian_polynomial_tail_bound_three
    {β H ρ : ℝ} (hβ : 0 < β) (hH : 0 < H) (hρ : 1 ≤ ρ) :
    (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 3 *
        Real.exp (-2 * β * ρ ^ 2) ≤
      (64 * (1 + β / (2 * H)) / (β / 2) ^ 2 /
        Real.sqrt β) * Real.exp (-β * ρ ^ 2) := by
  have hβ' : 0 < (1 / 2 : ℝ) * β := by positivity
  have hpoly := buGaussian_polynomial_tail_bound
    (β := (1 / 2 : ℝ) * β) hβ' hH hρ
  have hρpos : 0 < ρ := by linarith only [hρ]
  have hExpIn : -2 * ((1 / 2 : ℝ) * β) * ρ ^ 2 = -β * ρ ^ 2 := by ring_nf
  rw [hExpIn] at hpoly
  have hfirst : 1 + (β / H) * ρ ^ 2 ≤
      2 * (1 + ((1 / 2 : ℝ) * β / H) * ρ ^ 2) := by
    have hr : 0 ≤ (β / H) * ρ ^ 2 := by positivity
    rw [show β / H = 2 * ((1 / 2 : ℝ) * β / H) by ring_nf]
    nlinarith only [hr]
  have hExpCompare :
      (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 *
          Real.exp (-β * ρ ^ 2) ≤
        (32 * (1 + β / (2 * H)) / (β / 2) ^ 2) *
          Real.exp (-(β / 2) * ρ ^ 2) := by
    have hhalf := hpoly
    have hExpOut : -((1 / 2 : ℝ) * β) * ρ ^ 2 = -(β / 2) * ρ ^ 2 := by ring_nf
    rw [hExpOut] at hhalf
    calc
      _ ≤ 2 * (1 + ((1 / 2 : ℝ) * β / H) * ρ ^ 2) *
          (1 + ρ) ^ 2 * Real.exp (-β * ρ ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfirst (sq_nonneg (1 + ρ)))
          (Real.exp_nonneg _)
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 2)
        convert hmul using 1 <;> ring_nf
  have hx : 0 ≤ Real.sqrt β * ρ := by positivity
  have hsqrtSq : (Real.sqrt β * ρ) ^ 2 = β * ρ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hβ.le]
  have hlin : Real.sqrt β * ρ ≤ 1 + (Real.sqrt β * ρ) ^ 2 / 2 := by
    nlinarith only [sq_nonneg (Real.sqrt β * ρ - 1)]
  have hExp : 1 + (Real.sqrt β * ρ) ^ 2 / 2 ≤
      Real.exp ((Real.sqrt β * ρ) ^ 2 / 2) := by
    simpa [add_comm] using Real.add_one_le_exp
      ((Real.sqrt β * ρ) ^ 2 / 2)
  have hExtra : (1 + ρ) * Real.exp (-(β * ρ ^ 2) / 2) ≤
      2 / Real.sqrt β := by
    have hroot : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
    have hρge : 1 + ρ ≤ 2 * ρ := by linarith only [hρ]
    have hratio' : ρ = (Real.sqrt β * ρ) / Real.sqrt β := by field_simp
    calc
      (1 + ρ) * Real.exp (-(β * ρ ^ 2) / 2) ≤
          2 * ρ * Real.exp (-(β * ρ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right hρge (Real.exp_nonneg _)
      _ = (2 / Real.sqrt β) *
          ((Real.sqrt β * ρ) * Real.exp (-(β * ρ ^ 2) / 2)) := by
        rw [hratio']
        field_simp [hroot.ne']
      _ ≤ 2 / Real.sqrt β := by
        have hunit :
            (Real.sqrt β * ρ) * Real.exp (-(β * ρ ^ 2) / 2) ≤ 1 := by
          rw [← hsqrtSq]
          have hrewrite :
              Real.exp ((Real.sqrt β * ρ) ^ 2 / 2) *
                Real.exp (-((Real.sqrt β * ρ) ^ 2) / 2) = 1 := by
            rw [← Real.exp_add]
            rw [show (Real.sqrt β * ρ) ^ 2 / 2 +
                -((Real.sqrt β * ρ) ^ 2) / 2 = 0 by ring_nf,
              Real.exp_zero]
          calc
            _ ≤ (1 + (Real.sqrt β * ρ) ^ 2 / 2) *
                Real.exp (-((Real.sqrt β * ρ) ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
            _ ≤ Real.exp ((Real.sqrt β * ρ) ^ 2 / 2) *
                Real.exp (-((Real.sqrt β * ρ) ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right hExp (Real.exp_nonneg _)
            _ = 1 := hrewrite
        exact mul_le_of_le_one_right (by positivity) hunit
  have hwhole :
      (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 3 *
          Real.exp (-2 * β * ρ ^ 2) =
        ((1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 *
          Real.exp (-β * ρ ^ 2)) *
          ((1 + ρ) * Real.exp (-β * ρ ^ 2)) := by
    calc
      _ = (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 *
          (1 + ρ) * Real.exp (-2 * β * ρ ^ 2) := by
        rw [pow_succ]
        ring_nf
      _ = (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 *
          (1 + ρ) * (Real.exp (-β * ρ ^ 2) * Real.exp (-β * ρ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ = _ := by ring_nf
  rw [hwhole]
  have hbound := mul_le_mul_of_nonneg_right hExpCompare
    (mul_nonneg (by positivity : 0 ≤ 1 + ρ)
      (Real.exp_nonneg (-β * ρ ^ 2)))
  have hcombine :
      (32 * (1 + β / (2 * H)) / (β / 2) ^ 2) *
        Real.exp (-(β / 2) * ρ ^ 2) *
        ((1 + ρ) * Real.exp (-β * ρ ^ 2)) ≤
      (64 * (1 + β / (2 * H)) / (β / 2) ^ 2 /
        Real.sqrt β) * Real.exp (-β * ρ ^ 2) := by
    have hconst : 0 ≤ 32 * (1 + β / (2 * H)) / (β / 2) ^ 2 := by positivity
    calc
      _ = (32 * (1 + β / (2 * H)) / (β / 2) ^ 2) *
          ((1 + ρ) * Real.exp (-(β * ρ ^ 2) / 2)) *
          Real.exp (-β * ρ ^ 2) := by ring_nf
      _ ≤ (32 * (1 + β / (2 * H)) / (β / 2) ^ 2) *
          (2 / Real.sqrt β) * Real.exp (-β * ρ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_left hExtra hconst
      _ = (64 * (1 + β / (2 * H)) / (β / 2) ^ 2 /
          Real.sqrt β) * Real.exp (-β * ρ ^ 2) := by ring_nf
  exact hbound.trans hcombine

theorem buGaussian_shifted_trace_strip_tendsto
    {B : Set Vec3} {σ : ℝ}
    (hB : MeasurableSet B)
    (u : ParabolicPoint → Vec3)
    (htrace : Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc ε (2 * ε),
        vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let τprod : (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft σ)
  have hτpres : MeasurePreserving τprod
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (MeasurePreserving.id (volume : Measure Vec3)).prod
      (measurePreserving_add_left (volume : Measure ℝ) σ)
  have hτapply (q : Vec3 × ℝ) : τprod q = (q.1, q.2 + σ) := by
    change (q.1, σ + q.2) = (q.1, q.2 + σ)
    congr 1
    ring_nf
  have hτsymm (q : Vec3 × ℝ) : τprod.symm q = (q.1, q.2 - σ) := by
    apply τprod.injective
    rw [τprod.apply_symm_apply, hτapply]
    exact Prod.ext rfl (by ring_nf)
  have himage (ε : ℝ) :
      τprod '' (B ×ˢ Ioc ε (2 * ε)) =
        B ×ˢ Ioc (σ + ε) (σ + 2 * ε) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hτapply]
      exact ⟨hp.1, by constructor <;> linarith only [hp.2.1, hp.2.2]⟩
    · intro hq
      refine ⟨(q.1, q.2 - σ), ?_, ?_⟩
      · refine ⟨hq.1, ?_⟩
        constructor <;> linarith only [hq.2.1, hq.2.2]
      · rw [hτapply]
        exact Prod.ext rfl (by ring_nf)
  have hprodEq (ε : ℝ) :
      (∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm
            (parabolicHomeomorph.symm q))) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q in B ×ˢ Ioc ε (2 * ε),
        vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    let F : Vec3 × ℝ → ℝ := fun q =>
      vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
    have hchange := hτpres.setIntegral_image_emb τprod.measurableEmbedding
      (fun q => F (τprod.symm q)) (B ×ˢ Ioc ε (2 * ε))
    rw [himage ε] at hchange
    have hleft :
        (∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
          F (τprod.symm q) ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε),
          vec3EuclideanNorm
            (u ((buGaussianTimeShiftPoint σ).symm
              (parabolicHomeomorph.symm q))) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae
        (hB.prod measurableSet_Ioc)
      filter_upwards [] with q
      intro hqmem
      rw [hτsymm]
      rw [parabolicHomeomorph_symm_apply]
      change vec3EuclideanNorm (u (q.1, q.2 - σ)) ^ 2 =
        vec3EuclideanNorm
          (u ((buGaussianTimeShiftPoint σ).symm (q.1, q.2))) ^ 2
      have hq := buGaussian_timeShift_point_symm_apply σ
        (show ParabolicPoint from q)
      rw [← hq]
    have hright :
        (∫ q in B ×ˢ Ioc ε (2 * ε),
          F (τprod.symm (τprod q))
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in B ×ˢ Ioc ε (2 * ε),
          vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      apply setIntegral_congr_ae
        (hB.prod measurableSet_Ioc)
      filter_upwards [] with q
      simp [F]
    rw [hleft, hright] at hchange
    exact hchange
  have hfun :
      (fun ε : ℝ =>
        (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) /
          ε ^ 2) =
      (fun ε : ℝ =>
        (∫ q in B ×ˢ Ioc ε (2 * ε),
          vec3EuclideanNorm (u (parabolicHomeomorph.symm q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2) := by
    funext ε
    rw [setIntegral_parabolic_to_product]
    rw [hprodEq ε]
  rw [hfun]
  exact htrace

theorem buGaussian_local_cylinder_volume_bound {ρ : ℝ} (hρ : 0 < ρ) :
    (volume (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6 : ℝ) 2))).toReal ≤
      12 * ρ ^ 3 := by
  let U : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6 : ℝ) 2)
  have hUvol : volume U = volume (vec3Ball 0 ρ) * volume (Ioo (1 / 6 : ℝ) 2) := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball 0 ρ ×ˢ Ioo (1 / 6 : ℝ) 2) = _
    rw [Measure.prod_prod]
  rw [hUvol, volume_vec3Ball_eq, Real.volume_Ioo,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hρ.le,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3),
    show (2 : ℝ) - 1 / 6 = 11 / 6 by norm_num,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11 / 6)]
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hρ3 : 0 ≤ ρ ^ 3 := by positivity
  nlinarith only [hpi, hρ3]

end ESS
