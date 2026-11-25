/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorNonCharging
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScaledSmoothMax

/-! # Joint decreasing genuine smooth approximations of a maximum

The complete mathematical statement and proof preceded this file.
ROOT10 is strictly excluded from the fixed C90 batch.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.SmoothMax

/-- The scaled regularized positive part `ε P(t / ε)`. -/
def scaledPosPart (ε t : ℝ) : ℝ := ε * posPart (t / ε)

theorem scaledPosPart_nonneg {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : 0 ≤ scaledPosPart ε t :=
  mul_nonneg hε (posPart_nonneg _)

theorem le_scaledPosPart {ε : ℝ} (hε : 0 < ε) (t : ℝ) : t ≤ scaledPosPart ε t := by
  have := mul_le_mul_of_nonneg_left (le_posPart (t / ε)) hε.le
  rwa [mul_div_cancel₀ _ hε.ne'] at this

theorem scaledPosPart_eq_self {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) : scaledPosPart ε t = t := by
  rw [scaledPosPart, posPart_eq_self ((one_le_div hε).2 ht), mul_div_cancel₀ _ hε.ne']

theorem scaledPosPart_le {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε) : scaledPosPart ε t ≤ ε := by
  have := mul_le_mul_of_nonneg_left (posPart_le_one ((div_le_one hε).2 ht)) hε.le
  rwa [mul_one] at this

theorem scaledPosPart_mono_right {ε : ℝ} (hε : 0 < ε) : Monotone (scaledPosPart ε) :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left (posPart_monotone (div_le_div_of_nonneg_right h hε.le))
    hε.le

theorem scaledPosPart_le_max_add {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    scaledPosPart ε t ≤ max t 0 + ε := by
  rcases le_total t ε with h | h
  · linarith [scaledPosPart_le hε h, le_max_right t 0]
  · rw [scaledPosPart_eq_self hε h]; linarith [le_max_left t 0]

/-- The intercept of the tangent line of `P` at `s` is nonnegative. -/
theorem posPart_sub_mul_trans_nonneg (s : ℝ) : 0 ≤ posPart s - s * trans s := by
  rcases le_total s 0 with h | h
  · nlinarith [posPart_nonneg s, trans_nonneg s]
  · nlinarith [le_posPart s, trans_le_one s]

theorem scaledPosPart_mono_left {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (t : ℝ) :
    scaledPosPart ε t ≤ scaledPosPart ε' t := by
  have hd (e : ℝ) (he : 0 < e) : HasDerivAt (fun e ↦ scaledPosPart e t)
      (posPart (t / e) - t / e * trans (t / e)) e := by
    have h1 : HasDerivAt (fun e : ℝ ↦ t / e) (-(t / e ^ 2)) e := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv he.ne').const_mul t
    have h2 : HasDerivAt (fun e : ℝ ↦ posPart (t / e)) (trans (t / e) * -(t / e ^ 2)) e :=
      (hasDerivAt_posPart (t / e)).comp e h1
    have h3 : HasDerivAt (fun e : ℝ ↦ e * posPart (t / e))
        (1 * posPart (t / e) + e * (trans (t / e) * -(t / e ^ 2))) e :=
      (hasDerivAt_id' e).mul h2
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn (fun e ↦ scaledPosPart e t) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · exact fun e he ↦ (hd e he).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun e he ↦ (hd e he).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro e he
      rw [(hd e he).deriv]
      exact posPart_sub_mul_trans_nonneg _
  exact hmono hε (hε.trans_le hεε') hεε'

end SGPT.Foundations.Analysis.Pending.SmoothMax

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

/-- The scales `1 / (j + 1)`. -/
def maxScale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem maxScale_pos (j : ℕ) : 0 < maxScale j := by unfold maxScale; positivity

theorem maxScale_antitone : Antitone maxScale := fun j l h ↦
  one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ h)

theorem tendsto_maxScale : Tendsto maxScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem complexHessian_scaledPosPart_posSemidef {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hH : (complexHessian f z).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (c : ℝ) : (complexHessian (fun y ↦ scaledPosPart ε (f y - c)) z).PosSemidef := by
  have hk : ContDiffAt ℝ 2 (fun y ↦ ε⁻¹ * (f y - c)) z := contDiffAt_const.mul (hf.sub
    contDiffAt_const)
  have hP : ContDiffAt ℝ 2 (posPart ∘ fun y ↦ ε⁻¹ * (f y - c)) z :=
    (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z hk
  have hfun : (fun y ↦ scaledPosPart ε (f y - c)) = ε • (posPart ∘ fun y ↦ ε⁻¹ * (f y - c)) := by
    funext y; simp [scaledPosPart, div_eq_inv_mul]
  have hkH : complexHessian (fun y ↦ ε⁻¹ * (f y - c)) z = (ε⁻¹ : ℂ) • complexHessian f z := by
    have : (fun y ↦ ε⁻¹ * (f y - c)) = ε⁻¹ • fun y ↦ f y - c := by funext y; simp
    rw [this, complexHessian_smul (hf.sub contDiffAt_const), complexHessian_sub_const]
    simp
  rw [hfun, complexHessian_smul hP, complexHessian_comp contDiff_posPart hk, deriv_posPart, hkH]
  have hS' : 0 ≤ deriv trans (ε⁻¹ * (f z - c)) := trans_monotone.deriv_nonneg
  refine Matrix.PosSemidef.smul ?_ (by exact_mod_cast hε.le)
  exact ((hH.smul (by exact_mod_cast (inv_pos.2 hε).le)).smul (trans_nonneg _)).add
    ((Matrix.posSemidef_vecMulVec_self_star _).smul hS')

/-- The scaled regularized maxima with a constant form a decreasing approximation
of `max(w, c) - c`. -/
theorem IsDecApprox.scaledMax {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (c : ℝ) :
    IsDecApprox U (fun z ↦ max (w z) c - c)
      (fun j z ↦ scaledPosPart (maxScale j) (G j z - c)) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun j ↦ ⟨?_, fun z hz ↦ ?_⟩, fun z hz j l hjl ↦ ?_, fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · exact contDiffOn_const.mul (contDiff_posPart.comp_contDiffOn
      (((hG.1 j).1.sub contDiffOn_const).div_const _))
  · exact complexHessian_scaledPosPart_posSemidef
      (((hG.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2) ((hG.1 j).2 z hz)
      (maxScale_pos j) c
  · exact (scaledPosPart_mono_right (maxScale_pos l) (by linarith [hG.2.1 z hz hjl])).trans
      (scaledPosPart_mono_left (maxScale_pos l) (maxScale_antitone hjl) _)
  · have hlim : Tendsto (fun j ↦ max (G j z - c) 0) atTop (𝓝 (max (w z) c - c)) := by
      rw [← max_sub_sub_right, sub_self]
      exact ((hG.2.2.1 z hz).sub_const c).max tendsto_const_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim
      (by simpa using hlim.add tendsto_maxScale) (fun j ↦ max_le
        (le_scaledPosPart (maxScale_pos j) _) (scaledPosPart_nonneg (maxScale_pos j).le _))
      fun j ↦ scaledPosPart_le_max_add (maxScale_pos j) _
  · exact ⟨0, by rintro _ ⟨z, -, rfl⟩; exact sub_nonneg.2 (le_max_right _ _)⟩

theorem IsDecApprox.add_const {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (c : ℝ) :
    IsDecApprox U (fun z ↦ w z + c) (fun j z ↦ G j z + c) := by
  have hH (j : ℕ) (z : ComplexModel n) :
      complexHessian (fun y ↦ G j y + c) z = complexHessian (G j) z := by
    simpa using complexHessian_sub_const (G j) (-c) z
  refine ⟨fun j ↦ ⟨(hG.1 j).1.add contDiffOn_const, fun z hz ↦ (hH j z) ▸ (hG.1 j).2 z hz⟩,
    fun z hz j l hjl ↦ by simpa using hG.2.1 z hz hjl, fun z hz ↦ (hG.2.2.1 z hz).add_const c,
    fun K hK hKU ↦ ?_⟩
  obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
  exact ⟨m + c, by rintro _ ⟨z, hz, rfl⟩; simpa using hm ⟨z, hz, rfl⟩⟩

/-- The regularized maximum of `f` with the obstacle `g`, at scale `ε`. -/
abbrev scaledSmoothMax (ε : ℝ) (f g : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  ScaledSmoothMax.scaledSmoothMax ε f g

theorem scaledSmoothMax_apply (ε : ℝ) (f g : ComplexModel n → ℝ) (z : ComplexModel n) :
    scaledSmoothMax ε f g z = g z + scaledPosPart ε (f z - g z) := rfl

theorem scaledSmoothMax_eq_smul {ε : ℝ} (hε : 0 < ε) (f g : ComplexModel n → ℝ) :
    scaledSmoothMax ε f g = ε • smoothMax (ε⁻¹ • f) (ε⁻¹ • g) :=
  ScaledSmoothMax.scaledSmoothMax_eq_smul hε f g

theorem contDiffAt_scaledSmoothMax {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (ε : ℝ) :
    ContDiffAt ℝ 2 (scaledSmoothMax ε f g) z := by
  have hP : ContDiffAt ℝ 2 (fun y ↦ SmoothMax.posPart ((f y - g y) / ε)) z :=
    (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      ((hf.sub hg).div_const ε)
  exact hg.add (contDiffAt_const.mul hP)

/-- The regularized maximum of two functions with positive semidefinite complex
Hessians has a positive semidefinite complex Hessian. -/
theorem complexHessian_scaledSmoothMax_posSemidef {f g : ComplexModel n → ℝ}
    {z : ComplexModel n} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hHf : (complexHessian f z).PosSemidef) (hHg : (complexHessian g z).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (complexHessian (scaledSmoothMax ε f g) z).PosSemidef :=
  ScaledSmoothMax.complexHessian_scaledSmoothMax_posSemidef hf hg hHf hHg hε

theorem max_eq_add_max_sub (a b : ℝ) : max a b = b + max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), add_zero]
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- The scaled regularized maxima with a smooth positive semidefinite obstacle
form a decreasing approximation of `max(w, g)`. -/
theorem IsDecApprox.scaledSmoothMax {U : Opens (ComplexModel n)} {w g : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (hg : IsSmoothPsdOn U g) :
    IsDecApprox U (fun z ↦ max (w z) (g z))
      (fun j ↦ scaledSmoothMax (maxScale j) (G j) g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun j ↦ ⟨?_, fun z hz ↦ ?_⟩, fun z hz j l hjl ↦ ?_, fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · exact hg.1.add (contDiffOn_const.mul (contDiff_posPart.comp_contDiffOn
      (((hG.1 j).1.sub hg.1).div_const _)))
  · exact complexHessian_scaledSmoothMax_posSemidef
      (((hG.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      ((hg.1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2) ((hG.1 j).2 z hz) (hg.2 z hz)
      (maxScale_pos j)
  · change g z + scaledPosPart (maxScale l) (G l z - g z) ≤
      g z + scaledPosPart (maxScale j) (G j z - g z)
    have h := (scaledPosPart_mono_right (maxScale_pos l)
        (show G l z - g z ≤ G j z - g z by linarith [hG.2.1 z hz hjl])).trans
      (scaledPosPart_mono_left (maxScale_pos l) (maxScale_antitone hjl) (G j z - g z))
    linarith
  · have hlim : Tendsto (fun j ↦ g z + max (G j z - g z) 0) atTop (𝓝 (max (w z) (g z))) := by
      rw [max_eq_add_max_sub (w z) (g z)]
      exact tendsto_const_nhds.add (((hG.2.2.1 z hz).sub_const (g z)).max tendsto_const_nhds)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim
      (by simpa using hlim.add tendsto_maxScale) (fun j ↦ ?_) (fun j ↦ ?_)
    · change g z + max (G j z - g z) 0 ≤ g z + scaledPosPart (maxScale j) (G j z - g z)
      have := max_le (le_scaledPosPart (maxScale_pos j) (G j z - g z))
        (scaledPosPart_nonneg (maxScale_pos j).le (G j z - g z))
      linarith
    · change g z + scaledPosPart (maxScale j) (G j z - g z) ≤
        g z + max (G j z - g z) 0 + maxScale j
      have := scaledPosPart_le_max_add (maxScale_pos j) (G j z - g z)
      linarith
  · obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
    refine ⟨m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hm ⟨z, hz, rfl⟩).trans (le_max_left _ _)

/-! ### Test functions multiplied by a function continuous on `U` -/

/-- Multiplying a test function by a function continuous on `U` gives a
continuous function. -/
theorem continuous_test_mul {U : Opens (ComplexModel n)} {χ D : ComplexModel n → ℝ}
    (hχ : Continuous χ) (hχU : tsupport χ ⊆ U) (hD : ContinuousOn D U) :
    Continuous fun z ↦ χ z * D z :=
  continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport χ) hχU
    (hχ.continuousOn.mul hD) fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]

theorem tsupport_test_mul_subset {χ D : ComplexModel n → ℝ} :
    tsupport (fun z ↦ χ z * D z) ⊆ tsupport χ :=
  closure_mono fun z (hz : χ z * D z ≠ 0) ↦ fun h ↦ hz (by simp [h])

/-- A bounded strongly measurable function vanishing outside a set of finite
measure is integrable. -/
theorem integrable_of_bounded_of_support {ν : Measure (ComplexModel n)}
    {f : ComplexModel n → ℝ} {S : Set (ComplexModel n)} (hS : MeasurableSet S)
    (hνS : ν S < ⊤) (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    (h0 : ∀ z ∉ S, f z = 0) : Integrable f ν := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hbound : ∀ z, ‖f z‖ₑ ≤ S.indicator (fun _ ↦ ENNReal.ofReal C) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, Real.eNorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hC z)
    · rw [indicator_of_notMem hz, h0 z hz]
      simp
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_indicator hS, setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνS

/-- A test function times a pointwise limit of functions continuous on `U` is
strongly measurable. -/
theorem stronglyMeasurable_test_mul_limit {U : Opens (ComplexModel n)}
    {χ h : ComplexModel n → ℝ} {H : ℕ → ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχU : tsupport χ ⊆ U) (hHc : ∀ k, ContinuousOn (H k) U)
    (hlim : ∀ z ∈ U, Tendsto (fun k ↦ H k z) atTop (𝓝 (h z))) :
    StronglyMeasurable fun z ↦ χ z * h z := by
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun k z ↦ χ z * H k z) (fun k ↦ (continuous_test_mul hχ hχU (hHc k)).stronglyMeasurable)
    (tendsto_pi_nhds.2 fun z ↦ ?_)
  by_cases hz : z ∈ (U : Set (ComplexModel n))
  · exact tendsto_const_nhds.mul (hlim z hz)
  · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport fun hmem ↦ hz (hχU hmem)
    simp [hχz]

theorem exists_bound_of_continuous_of_hasCompactSupport {f : ComplexModel n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : ∃ C, 0 ≤ C ∧ ∀ z, |f z| ≤ C := by
  obtain ⟨C, hC⟩ := (hfc.image (continuous_abs.comp hf)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun z ↦ ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
    exact le_max_right _ _

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

namespace SGPT.Foundations.Analysis.Pending.JointDecreasingSmoothMax

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax BedfordTaylor

variable {n : ℕ}

/-- Two genuine decreasing smooth approximations produce a genuine approximation
of their maximum, with both branches varying at every stage. -/
theorem isDecApprox_joint_scaledSmoothMax {U : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} {F G : ℕ → ComplexModel n → ℝ}
    (hF : IsDecApprox U u F) (hG : IsDecApprox U v G) :
    IsDecApprox U (fun z ↦ max (u z) (v z))
      (fun j ↦ BedfordTaylor.scaledSmoothMax (maxScale j) (F j) (G j)) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun j ↦ ⟨?_, fun z hz ↦ ?_⟩, fun z hz j l hjl ↦ ?_,
    fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · exact (hG.1 j).1.add (contDiffOn_const.mul (contDiff_posPart.comp_contDiffOn
      (((hF.1 j).1.sub (hG.1 j).1).div_const _)))
  · exact complexHessian_scaledSmoothMax_posSemidef
      (((hF.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      (((hG.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      ((hF.1 j).2 z hz) ((hG.1 j).2 z hz) (maxScale_pos j)
  · have hbranches := ScaledSmoothMax.scaledSmoothMax_mono (maxScale_pos l)
      (hF.2.1 z hz hjl) (hG.2.1 z hz hjl)
    have hscale := scaledPosPart_mono_left (maxScale_pos l)
      (maxScale_antitone hjl) (F j z - G j z)
    refine hbranches.trans ?_
    change G j z + scaledPosPart (maxScale l) (F j z - G j z) ≤
      G j z + scaledPosPart (maxScale j) (F j z - G j z)
    linarith
  · have hlim : Tendsto (fun j ↦ max (F j z) (G j z)) atTop (𝓝 (max (u z) (v z))) :=
      (hF.2.2.1 z hz).max (hG.2.2.1 z hz)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim
      (by simpa only [add_zero] using hlim.add tendsto_maxScale) (fun j ↦ ?_) (fun j ↦ ?_)
    · rw [max_eq_add_max_sub (F j z) (G j z)]
      change G j z + max (F j z - G j z) 0 ≤
        G j z + scaledPosPart (maxScale j) (F j z - G j z)
      have := max_le (le_scaledPosPart (maxScale_pos j) (F j z - G j z))
        (scaledPosPart_nonneg (maxScale_pos j).le (F j z - G j z))
      linarith
    · rw [max_eq_add_max_sub (F j z) (G j z)]
      change G j z + scaledPosPart (maxScale j) (F j z - G j z) ≤
        G j z + max (F j z - G j z) 0 + maxScale j
      have := scaledPosPart_le_max_add (maxScale_pos j) (F j z - G j z)
      linarith
  · obtain ⟨m, hm⟩ := hF.2.2.2 K hK hKU
    refine ⟨m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hm ⟨z, hz, rfl⟩).trans (le_max_left _ _)

end SGPT.Foundations.Analysis.Pending.JointDecreasingSmoothMax
