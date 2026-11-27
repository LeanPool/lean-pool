/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import LeanPool.VenNullClockRoundRates.RoundAreaCutoffInputs
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive smooth realization of the strip densities
-/

@[expose] public section
noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Topology

namespace VenRateUpper

/-- Downstream exponential difference between the alternative and aligned energies. -/
def sphereReadGap (θ b : ℝ) (y : VenMask.UnitSphere) : ℝ :=
  Real.exp (b * VenMask.secondEnergy θ y) - Real.exp (b * VenMask.firstEnergy y)

/-- The smooth cutoff equals the transverse and longitudinal bump product times
the reciprocal signed discrepancy and reciprocal normalized area density on its support.
The vertical cutoff isolates the positive hemisphere. -/
def ambientStripCutoff (θ b s δ z : ℝ) (η β : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  (4 * Real.pi) * (p.2.2 * Real.smoothTransition (p.2.2 / z)) * η p.1 * β p.2.1 /
    cutoffDenominator δ (s * chartGap θ b p.1 p.2.1)

theorem contDiff_ambientStripCutoff {θ b s δ z : ℝ} {η β : ℝ → ℝ}
    (hδ : 0 < δ) (hη : ContDiff ℝ ∞ η) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (ambientStripCutoff θ b s δ z η β) := by
  have hX : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ ↦ p.1) := contDiff_fst
  have hY : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ ↦ p.2.1) := contDiff_fst.comp contDiff_snd
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ ↦ p.2.2) := contDiff_snd.comp contDiff_snd
  have hC := Real.smoothTransition.contDiff.comp (hZ.div_const z)
  have hG := (contDiff_chartGap θ b).comp (hX.prodMk hY)
  exact (((contDiff_const.mul (hZ.mul hC)).mul (hη.comp hX)).mul (hβ.comp hY)).div
    ((contDiff_cutoffDenominator δ).comp (contDiff_const.mul hG))
    (fun p ↦ (cutoffDenominator_pos hδ (s * chartGap θ b p.1 p.2.1)).ne')

theorem ambientStripCutoff_nonneg {θ b s δ z : ℝ} {η β : ℝ → ℝ}
    (hδ : 0 < δ) (hz : 0 < z) (hη : ∀ x, 0 ≤ η x) (hβ : ∀ y, 0 ≤ β y)
    (p : ℝ × ℝ × ℝ) : 0 ≤ ambientStripCutoff θ b s δ z η β p := by
  have hc : 0 ≤ p.2.2 * Real.smoothTransition (p.2.2 / z) := by
    by_cases h : p.2.2 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h hz.le), mul_zero]
    · exact mul_nonneg (le_of_lt (lt_of_not_ge h)) (Real.smoothTransition.nonneg _)
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hc) (hη _)) (hβ _))
    (cutoffDenominator_pos hδ _).le

private theorem graphHeight_projection {y : VenMask.UnitSphere} (hy : y ∈ upperHemisphere) :
    graphHeight (graphProjection y) = y.val.2.2 := by
  have hs : 1 - y.val.1 ^ 2 - y.val.2.1 ^ 2 = y.val.2.2 ^ 2 := by
    linarith [y.property]
  change Real.sqrt (1 - y.val.1 ^ 2 - y.val.2.1 ^ 2) = y.val.2.2
  rw [hs, Real.sqrt_sq (le_of_lt hy)]

/-- The two strip identities follow from the round-area law and one product integral. -/
theorem integral_ambientStripCutoff
    {θ b s δ z : ℝ} (hs : s ^ 2 = 1) (hδ : 0 < δ) (hz : 0 < z)
    {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    {η β : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hβ : ContDiff ℝ ∞ β)
    (hη0 : ∀ x ∉ I, η x = 0) (hβ0 : ∀ x ∉ J, β x = 0)
    (hβ1 : ∫ x, β x = 1)
    (hStrip : ∀ p ∈ I ×ˢ J, δ < s * chartGap θ b p.1 p.2 ∧ z < graphHeight p)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ q, sphereReadGap θ b q * ambientStripCutoff θ b s δ z η β q.val *
      g q.val.1 ∂roundArea) = s * ∫ t, η t * g t := by
  let W := ambientStripCutoff θ b s δ z η β
  let lift (p : ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, p.2, graphHeight p)
  let f (p : ℝ × ℝ) : ℝ := chartGap θ b p.1 p.2 * W (lift p) * g p.1
  let A (x : ℝ) : ℝ := (4 * Real.pi * s) * (η x * g x)
  have hf : Continuous f := by
    have hW : Continuous W := (contDiff_ambientStripCutoff hδ hη hβ).continuous
    have hlift : Continuous lift :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_graphHeight)
    exact (((contDiff_chartGap θ b).continuous).mul (hW.comp hlift)).mul
      (hg.comp continuous_fst)
  have hStripDisk : I ×ˢ J ⊆ graphDisk := by
    intro p hp
    have h := hz.trans (hStrip p hp).2
    exact Real.sqrt_pos.mp h
  have hPatch : ∀ p ∈ graphDisk,
      graphAreaDensity p * f p = (I ×ˢ J).indicator (fun p ↦ A p.1 * β p.2) p := by
    intro p hp
    by_cases hi : p.1 ∈ I
    · by_cases hj : p.2 ∈ J
      · have hIJ : p ∈ I ×ˢ J := ⟨hi, hj⟩
        have h := hStrip p hIJ
        have hzP : 0 < graphHeight p := hz.trans h.2
        have hsG : 0 < s * chartGap θ b p.1 p.2 := hδ.trans h.1
        have hRatio : chartGap θ b p.1 p.2 / (s * chartGap θ b p.1 p.2) = s := by
          apply (div_eq_iff hsG.ne').2
          rw [← mul_assoc, ← pow_two, hs, one_mul]
        rw [indicator_of_mem hIJ]
        dsimp [f, W, lift, A, ambientStripCutoff, graphAreaDensity]
        rw [cutoffDenominator_eq_self hδ h.1.le,
          Real.smoothTransition.one_of_one_le ((one_le_div hz).2 h.2.le), mul_one]
        calc
          _ = (chartGap θ b p.1 p.2 / (s * chartGap θ b p.1 p.2)) *
            ((4 * Real.pi) * (η p.1 * g p.1) * β p.2) := by
              field_simp [hzP.ne']
          _ = _ := by rw [hRatio]; ring
      · rw [indicator_of_notMem (show p ∉ I ×ˢ J from fun hp' ↦ hj hp'.2)]
        simp [f, W, lift, ambientStripCutoff, hβ0 _ hj]
    · rw [indicator_of_notMem (show p ∉ I ×ˢ J from fun hp' ↦ hi hp'.1)]
      simp [f, W, lift, ambientStripCutoff, hη0 _ hi]
  calc
    _ = ∫ q in upperHemisphere, sphereReadGap θ b q * W q.val * g q.val.1 ∂roundArea := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hv : q.val.2.2 ≤ 0 := le_of_not_gt hq
      simp [W, ambientStripCutoff,
        Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hv hz.le)]
    _ = ∫ q in upperHemisphere, f (graphProjection q) ∂roundArea := by
      apply setIntegral_congr_fun
      · have h : Continuous (fun q : VenMask.UnitSphere ↦ q.val) := continuous_subtype_val
        exact (isOpen_lt continuous_const h.snd.snd).measurableSet
      · intro q hq
        have hq' : lift (graphProjection q) = q.val := by
          change (q.val.1, q.val.2.1, graphHeight (graphProjection q)) = q.val
          rw [graphHeight_projection hq]
        change _ = chartGap θ b q.val.1 q.val.2.1 * W (lift (graphProjection q)) * g q.val.1
        rw [hq']
        rfl
    _ = (4 * Real.pi)⁻¹ * ∫ p in graphDisk, graphAreaDensity p * f p :=
      integral_roundArea_upperHemisphere f hf.measurable
    _ = (4 * Real.pi)⁻¹ * ∫ p in graphDisk,
        (I ×ˢ J).indicator (fun p ↦ A p.1 * β p.2) p := by
      rw [setIntegral_congr_fun isOpen_graphDisk.measurableSet hPatch]
    _ = (4 * Real.pi)⁻¹ * ∫ p in I ×ˢ J, A p.1 * β p.2 := by
      rw [setIntegral_indicator (hI.prod hJ)]
      rw [inter_eq_right.mpr hStripDisk]
    _ = (4 * Real.pi)⁻¹ * ((∫ x in I, A x) * ∫ y in J, β y) := by
      congr 1
      exact setIntegral_prod_mul A β I J
    _ = s * ∫ t, η t * g t := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hβ0, hβ1, mul_one]
      dsimp [A]
      rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by rw [hη0 x hx, zero_mul])]
      have hp : (4 * Real.pi : ℝ) ≠ 0 := by positivity
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

instance : CompactSpace VenMask.UnitSphere := metricSphereHomeomorph.compactSpace

/-- A common Cartesian cutoff and two ordinary-round-area lift functions for its
opposite signed read - gap pushforwards. The height interval lies in the unit range. -/
theorem exists_smooth_strip_cutoffs {θ b : ℝ}
    (hθ : 0 < 1 - Real.cos θ ^ 2) (hb : 0 < b) :
    ∃ h₀ h₁ Aplus Aminus : ℝ, 0 < h₀ ∧ h₀ < h₁ ∧ h₁ < 1 ∧
      0 ≤ Aplus ∧ 0 ≤ Aminus ∧
      ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        (∀ t ∈ Icc h₀ h₁, η t = 1) ∧
      ∃ Cplus Cminus : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ Cplus ∧ ContDiff ℝ ∞ Cminus ∧
        (∀ y : VenMask.UnitSphere, Cplus y.val ∈ Icc 0 Aplus) ∧
        (∀ y : VenMask.UnitSphere, Cminus y.val ∈ Icc 0 Aminus) ∧
        (∀ p : ℝ × ℝ × ℝ, Cplus p * Cminus p = 0) ∧
        (∀ g : ℝ → ℝ, Continuous g →
          (∫ y, sphereReadGap θ b y * Cplus y.val * g y.val.1 ∂roundArea) =
            ∫ t, η t * g t) ∧
        (∀ g : ℝ → ℝ, Continuous g →
          (∫ y, sphereReadGap θ b y * Cminus y.val * g y.val.1 ∂roundArea) =
            -(∫ t, η t * g t)) := by
  obtain ⟨l, u, yp, ym, rp, rm, δ, z, hl, hlu, hu, hrp, hrm, hδ, hz, hP, hM⟩ :=
    exists_chartStripRectangles hθ hb
  obtain ⟨h₀, h₁, h₀pos, h₀₁, h₁lt, η, hη, hηc, hηp, hηs, hη1⟩ :=
    exists_height_cutoff hl hlu hu
  obtain ⟨βp, hβp, hβpp, hβps, hβp1⟩ := exists_transverse_bump yp rp hrp
  obtain ⟨βm, hβm, hβmp, hβms, hβm1⟩ := exists_transverse_bump ym rm hrm
  let Cp := ambientStripCutoff θ b 1 δ z η βp
  let Cm := ambientStripCutoff θ b (-1) δ z η βm
  have hCp : ContDiff ℝ ∞ Cp := contDiff_ambientStripCutoff hδ hη hβp
  have hCm : ContDiff ℝ ∞ Cm := contDiff_ambientStripCutoff hδ hη hβm
  have bound {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f) (hn : 0 ≤ f) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ y : VenMask.UnitSphere, f y.val ∈ Icc 0 A := by
    have hc : Continuous (fun y : VenMask.UnitSphere ↦ f y.val) :=
      hf.comp continuous_subtype_val
    let y₀ : VenMask.UnitSphere := ⟨(1, 0, 0), by norm_num⟩
    obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn
      (show (univ : Set VenMask.UnitSphere).Nonempty from ⟨y₀, mem_univ _⟩) hc.continuousOn
    exact ⟨f a.val, hn _, fun y ↦ ⟨hn _, ha (mem_univ y)⟩⟩
  obtain ⟨Aplus, hAplus, hBoundsP⟩ := bound hCp.continuous
    (ambientStripCutoff_nonneg hδ hz hηp hβpp)
  obtain ⟨Aminus, hAminus, hBoundsM⟩ := bound hCm.continuous
    (ambientStripCutoff_nonneg hδ hz hηp hβmp)
  refine ⟨h₀, h₁, Aplus, Aminus, h₀pos, h₀₁, h₁lt, hAplus, hAminus,
    η, hη, hηc, hη1, Cp, Cm, hCp, hCm, hBoundsP, hBoundsM, ?_, ?_, ?_⟩
  · intro p
    by_cases hE : η p.1 = 0
    · simp [Cp, ambientStripCutoff, hE]
    by_cases hVp : βp p.2.1 = 0
    · simp [Cp, ambientStripCutoff, hVp]
    by_cases hVm : βm p.2.1 = 0
    · simp [Cm, ambientStripCutoff, hVm]
    have hI : p.1 ∈ Icc l u := by by_contra h; exact hE (hηs _ h)
    have hJp : p.2.1 ∈ Metric.closedBall yp rp := by by_contra h; exact hVp (hβps _ h)
    have hJm : p.2.1 ∈ Metric.closedBall ym rm := by by_contra h; exact hVm (hβms _ h)
    have hp := (hP (p.1, p.2.1) ⟨hI, hJp⟩).1
    have hm := (hM (p.1, p.2.1) ⟨hI, hJm⟩).1
    exfalso
    linarith only [hδ, hp, hm]
  · intro g hg
    simpa [Cp] using integral_ambientStripCutoff (by norm_num : (1 : ℝ) ^ 2 = 1)
      hδ hz measurableSet_Icc Metric.isClosed_closedBall.measurableSet hη hβp
      hηs hβps hβp1 (by simpa using hP) g hg
  · intro g hg
    simpa [Cm] using integral_ambientStripCutoff (by norm_num : (-1 : ℝ) ^ 2 = 1)
      hδ hz measurableSet_Icc Metric.isClosed_closedBall.measurableSet hη hβm
      hηs hβms hβm1 (by simpa using hM) g hg

end VenRateUpper
