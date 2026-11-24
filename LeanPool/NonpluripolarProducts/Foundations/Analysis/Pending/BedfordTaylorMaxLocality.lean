/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorNonCharging

/-!
# Plurifine locality of Bedford–Taylor measures for a maximum with a constant

Let `u' = max(u, c)` in one slot. With decreasing smooth approximations `f_j` of
`u` and the scaled regularized maxima `g_j = c + ε_j P((f_j - c)/ε_j)` of
`max(u, c)`, the mixed densities of the two families agree where `f_j > c + ε_j`,
while the weight `g_j - c` is at most `ε_j` elsewhere. Weighted convergence
therefore gives `(max(u, c) - c) μ = (max(u, c) - c) μ'`, and dividing by the
positive weight on `{u > c}` gives `μ = μ'` there.

Source: Bedford–Taylor locality in the plurifine topology, as invoked in BEGZ §1.2.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.SmoothMax

theorem le_posPart (t : ℝ) : t ≤ posPart t := by
  rcases le_total t 1 with h | h
  · have := sub_posPart_monotone h
    simp only [posPart_eq_self le_rfl, sub_self] at this
    linarith
  · rw [posPart_eq_self h]

theorem posPart_nonneg' (t : ℝ) : 0 ≤ posPart t := by
  rcases le_total t (-1) with h | h
  · rw [posPart_eq_zero h]
  · have := posPart_monotone h
    rwa [posPart_eq_zero le_rfl] at this

theorem posPart_le_one {t : ℝ} (ht : t ≤ 1) : posPart t ≤ 1 := by
  have := posPart_monotone ht
  rwa [posPart_eq_self le_rfl] at this

/-- The scaled regularized positive part `ε P(t / ε)`. -/
def scaledPosPart (ε t : ℝ) : ℝ := ε * posPart (t / ε)

theorem scaledPosPart_nonneg {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : 0 ≤ scaledPosPart ε t :=
  mul_nonneg hε (posPart_nonneg' _)

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
  · nlinarith [posPart_nonneg' s, trans_nonneg s]
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

/-- **Weighted locality.** Replacing one slot `u i₀` by `max(u i₀, c)` does not
change the limit measure weighted by `max(u i₀, c) - c`. -/
theorem integral_mul_maxWeight_eq {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) (c : ℝ) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) c) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, χ z * (max (u i₀ z) c - c) ∂μ = ∫ z, χ z * (max (u i₀ z) c - c) ∂μ' := by
  classical
  obtain ⟨F, hF⟩ := hex
  set W : ComplexModel n → ℝ := fun z ↦ max (u i₀ z) c - c with hW_def
  set G : ℕ → ComplexModel n → ℝ := fun j z ↦ scaledPosPart (maxScale j) (F i₀ j z - c)
    with hG_def
  have hG : IsDecApprox U W G := (hF.1 i₀).scaledMax c
  set F' : Fin n → ℕ → ComplexModel n → ℝ :=
    Function.update F i₀ (fun j z ↦ G j z + c) with hF'_def
  have hF' : IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) c) F' := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h
      simpa [hF'_def, hW_def] using hG.add_const c
    · simpa [hF'_def, Function.update_of_ne h] using hF.1 i
  have hWC := wClaim_of_pClaim (pClaim_all (n := n))
  have hA := hWC U u μ hμc hμf hμ F hF W G hG χ hχ hχc hχU
  have hB := hWC U _ μ' hμ'c hμ'f hμ' F' hF' W G hG χ hχ hχc hχU
  set a : ℕ → ℝ := fun k ↦ ∫ z, |χ z| * mixedDensity (fun i ↦ F i k) z
  set b : ℕ → ℝ := fun k ↦ ∫ z, |χ z| * mixedDensity (fun i ↦ F' i k) z
  have hχa : Continuous fun z ↦ |χ z| := hχ.abs
  have hχac : HasCompactSupport fun z ↦ |χ z| := hχc.abs
  have hs : Function.support (fun z ↦ |χ z|) ⊆ Function.support χ :=
    fun _ hz => abs_ne_zero.mp hz
  have hχaU : tsupport (fun z ↦ |χ z|) ⊆ U := (closure_mono hs).trans hχU
  have ha := hμ F hF _ hχa hχac hχaU
  have hb := hμ' F' hF' _ hχa hχac hχaU
  have hFs (k : ℕ) (i : Fin n) : IsSmoothPsdOn U (F i k) := (hF.1 i).1 k
  have hF's (k : ℕ) (i : Fin n) : IsSmoothPsdOn U (F' i k) := (hF'.1 i).1 k
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ (hFs k i).1
  have hD'c (k : ℕ) := continuousOn_mixedDensity fun i ↦ (hF's k i).1
  have hIA (k : ℕ) : Integrable fun z ↦ χ z * G k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F i k) z)
      ((hG.1 k).1.continuousOn.mul (hDc k)) hχ hχc hχU
    simpa only [mul_assoc] using this
  have hIB (k : ℕ) : Integrable fun z ↦ χ z * G k z * mixedDensity (fun i ↦ F' i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F' i k) z)
      ((hG.1 k).1.continuousOn.mul (hD'c k)) hχ hχc hχU
    simpa only [mul_assoc] using this
  have hIa (k : ℕ) : Integrable fun z ↦ |χ z| * mixedDensity (fun i ↦ F i k) z :=
    integrable_mul_of_continuousOn (hDc k) hχa hχac hχaU
  have hIb (k : ℕ) : Integrable fun z ↦ |χ z| * mixedDensity (fun i ↦ F' i k) z :=
    integrable_mul_of_continuousOn (hD'c k) hχa hχac hχaU
  have hpt (k : ℕ) (z : ComplexModel n) :
      |χ z * G k z * mixedDensity (fun i ↦ F i k) z -
        χ z * G k z * mixedDensity (fun i ↦ F' i k) z| ≤
      maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
        |χ z| * mixedDensity (fun i ↦ F' i k) z) := by
    by_cases hzU : z ∈ (U : Set (ComplexModel n))
    · have hD0 := mixedDensity_nonneg fun i ↦ (hFs k i).2 z hzU
      have hD'0 := mixedDensity_nonneg fun i ↦ (hF's k i).2 z hzU
      have hR0 : 0 ≤ maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
          |χ z| * mixedDensity (fun i ↦ F' i k) z) :=
        mul_nonneg (maxScale_pos k).le (add_nonneg (mul_nonneg (abs_nonneg _) hD0)
          (mul_nonneg (abs_nonneg _) hD'0))
      by_cases hz : c + maxScale k < F i₀ k z
      · have hev : ∀ i, F' i k =ᶠ[𝓝 z] F i k := by
          intro i
          by_cases h : i = i₀
          · subst h
            have hc : ContinuousAt (F i k) z :=
              (hFs k i).1.continuousOn.continuousAt (U.isOpen.mem_nhds hzU)
            filter_upwards [hc.eventually (lt_mem_nhds hz)] with y hy
            simp only [hF'_def, Function.update_self, hG_def]
            rw [scaledPosPart_eq_self (maxScale_pos k) (by linarith)]
            ring
          · simp [hF'_def, Function.update_of_ne h]
        have h0 : χ z * G k z * mixedDensity (fun i ↦ F i k) z -
            χ z * G k z * mixedDensity (fun i ↦ F' i k) z = 0 := by
          rw [mixedDensity_congr hev, sub_self]
        rw [h0, abs_zero]
        exact hR0
      · have hG0 : 0 ≤ G k z := scaledPosPart_nonneg (maxScale_pos k).le _
        have hGe : G k z ≤ maxScale k :=
          scaledPosPart_le (maxScale_pos k) (by linarith [not_lt.mp hz])
        rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg hG0]
        calc |χ z| * G k z * |mixedDensity (fun i ↦ F i k) z -
              mixedDensity (fun i ↦ F' i k) z|
            ≤ |χ z| * maxScale k * (mixedDensity (fun i ↦ F i k) z +
              mixedDensity (fun i ↦ F' i k) z) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hGe (abs_nonneg _)) ?_
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) (maxScale_pos k).le)
              rw [abs_le]; constructor <;> linarith
          _ = _ := by ring
    · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzU (hχU h)
      simp [hχz]
  have hdiff : Tendsto (fun k ↦ (∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, χ z * G k z * mixedDensity (fun i ↦ F' i k) z) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k ↦ ?_) (?_ : Tendsto (fun k ↦ maxScale k * (a k + b k))
      atTop (𝓝 0))
    · rw [← integral_sub (hIA k) (hIB k), Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_add (hIa k) (hIb k), ← integral_const_mul]
      exact integral_mono (hIA k |>.sub (hIB k)).abs
        (((hIa k).add (hIb k)).const_mul _) (hpt k)
    · simpa using tendsto_maxScale.mul (ha.add hb)
  have := tendsto_nhds_unique (hA.sub hB) hdiff
  exact sub_eq_zero.mp this

theorem IsDecApprox.measurableSet_lt {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (c : ℝ) :
    MeasurableSet {z | z ∈ U ∧ c < w z} := by
  have heq : {z | z ∈ U ∧ c < w z} =
      ⋃ m : ℕ, ⋂ k : ℕ, ((U : Set (ComplexModel n)) ∩ G k ⁻¹' Ioi (c + 1 / ((m : ℝ) + 1))) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨hzU, hz⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      exact ⟨m, fun k ↦ ⟨hzU, by linarith [hG.le_of_mem hzU k]⟩⟩
    · rintro ⟨m, hm⟩
      obtain ⟨hzU, -⟩ := hm 0
      refine ⟨hzU, lt_of_lt_of_le (by linarith [show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity])
        (ge_of_tendsto' (hG.2.2.1 z hzU) fun k ↦ (hm k).2.le)⟩
  rw [heq]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iInter fun k ↦
    ((hG.1 k).1.continuousOn.isOpen_inter_preimage U.isOpen isOpen_Ioi).measurableSet

/-- **Locality for one slot.** On `{u i₀ > c}` the limit measures for `u` and for
`u` with `max(u i₀, c)` in slot `i₀` coincide. -/
theorem restrict_eq_of_max_slot {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) (c : ℝ) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) c) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) :
    μ.restrict {z | z ∈ U ∧ c < u i₀ z} = μ'.restrict {z | z ∈ U ∧ c < u i₀ z} := by
  classical
  obtain ⟨F, hF⟩ := id hex
  have hGw := hF.1 i₀
  set P := {z | z ∈ U ∧ c < u i₀ z} with hP_def
  have hPm : MeasurableSet P := hGw.measurableSet_lt c
  have hPU : P ⊆ U := fun z hz ↦ hz.1
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) c - c) with hf_def
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) c - c) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact ((ContinuousOn.sup (hGw.1 j).1.continuousOn continuousOn_const).sub
        continuousOn_const).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max tendsto_const_nhds).sub_const c
  set ρ := (μ.restrict U).withDensity f
  set ρ' := (μ'.restrict U).withDensity f
  have hfin (ν : Measure (ComplexModel n)) (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ U → (ν.restrict U).withDensity f K < ⊤ := by
    intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, f z ∂ν.restrict U ≤ ∫⁻ z in K, ENNReal.ofReal (|C| + |c|) ∂ν.restrict U := by
          refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
          refine Eventually.of_forall fun z hz ↦ ENNReal.ofReal_le_ofReal ?_
          have := hGw.abs_le_of_mem hKU hC hz
          rw [abs_le] at this
          have := le_abs_self C
          have := neg_abs_le c
          have := le_abs_self c
          rcases le_total (u i₀ z) c with h | h
          · rw [max_eq_right h]; linarith [abs_nonneg C]
          · rw [max_eq_left h]; linarith
      _ = ENNReal.ofReal (|C| + |c|) * ν.restrict U K := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((Measure.restrict_apply_le _ _).trans_lt (hνf K hK hKU))
  have hint (ν : Measure (ComplexModel n)) (φ : ComplexModel n → ℝ)
      (hφU : tsupport φ ⊆ U) :
      ∫ z, φ z ∂(ν.restrict U).withDensity f = ∫ z, φ z * (max (u i₀ z) c - c) ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hfm ν)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (sub_nonneg.2 (le_max_right _ _)), smul_eq_mul, mul_comm]
  have hρ : ρ.restrict U = ρ'.restrict U :=
    restrict_eq_of_testFunction_integral_eq (hfin μ hμf) (hfin μ' hμ'f) fun φ ↦ by
      rw [hint μ φ φ.tsupport_subset, hint μ' φ φ.tsupport_subset]
      exact integral_mul_maxWeight_eq i₀ c hμc hμf hμ hμ'c hμ'f hμ' hex φ.continuous
        φ.hasCompactSupport φ.tsupport_subset
  have hself (ν : Measure (ComplexModel n)) :
      ((ν.restrict U).withDensity f).restrict U = (ν.restrict U).withDensity f := by
    rw [restrict_withDensity hUm, Measure.restrict_restrict hUm, inter_self]
  rw [hself, hself] at hρ
  have hinv (ν : Measure (ComplexModel n)) :
      ν.restrict P = (((ν.restrict U).withDensity f).restrict P).withDensity
        fun z ↦ (f z)⁻¹ := by
    rw [restrict_withDensity hPm, withDensity_inv_same₀ ((hfm ν).mono_measure
      Measure.restrict_le_self)]
    · rw [Measure.restrict_restrict_of_subset hPU]
    · filter_upwards [ae_restrict_mem hPm] with z hz
      simp only [hf_def, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact lt_max_of_lt_left hz.2
    · exact Eventually.of_forall fun _ ↦ ENNReal.ofReal_ne_top
  rw [hinv μ, hinv μ', hρ]

/-- The tuple with `max(·, c)` applied in the slots of index below `k`. -/
def maxTuple (u : Fin n → ComplexModel n → ℝ) (c : ℝ) (k : ℕ) : Fin n → ComplexModel n → ℝ :=
  fun i ↦ if i.val < k then fun z ↦ max (u i z) c else u i

theorem maxTuple_zero (u : Fin n → ComplexModel n → ℝ) (c : ℝ) : maxTuple u c 0 = u := by
  funext i; simp [maxTuple]

theorem maxTuple_succ (u : Fin n → ComplexModel n → ℝ) (c : ℝ) {k : ℕ} (hk : k < n) :
    maxTuple u c (k + 1) =
      Function.update (maxTuple u c k) ⟨k, hk⟩ fun z ↦ max (maxTuple u c k ⟨k, hk⟩ z) c := by
  funext i
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp [maxTuple]
  · have hik : i.val ≠ k := fun h' ↦ h (Fin.ext h')
    simp only [maxTuple, Function.update_of_ne h]
    by_cases hlt : i.val < k
    · simp [hlt, show i.val < k + 1 by omega]
    · simp [hlt, show ¬ i.val < k + 1 by omega]

theorem maxTuple_apply_self (u : Fin n → ComplexModel n → ℝ) (c : ℝ) {k : ℕ} (hk : k < n) :
    maxTuple u c k ⟨k, hk⟩ = u ⟨k, hk⟩ := by
  simp [maxTuple]

theorem exists_isAdmissible_maxTuple {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (c : ℝ) (k : ℕ) : ∃ F', IsAdmissible n U (maxTuple u c k) F' := by
  classical
  refine ⟨fun i ↦ if i.val < k then
    (fun j z ↦ scaledPosPart (maxScale j) (F i j z - c) + c) else F i,
    fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i.val < k
  · simpa [maxTuple, h] using ((hF.1 i).scaledMax c).add_const c
  · simpa [maxTuple, h] using hF.1 i

/-- **Locality in all slots on a relatively compact set.** -/
theorem restrict_eq_maxTuple {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (c : ℝ) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTuple u c k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, c < u i z} = μ.restrict {z | z ∈ U ∧ ∀ i, c < u i z} := by
  obtain ⟨F, hF⟩ := id hex
  set P := {z | z ∈ U ∧ ∀ i, c < u i z} with hP_def
  have hPU : P ⊆ U := fun z hz ↦ hz.1
  intro k
  induction k with
  | zero =>
    intro _ μ' _ hμ'f hμ'
    rw [maxTuple_zero] at hμ'
    have h := restrict_eq_of_claims le_rfl hμ'f hμf hμ' hμ hex
    rw [← Measure.restrict_restrict_of_subset hPU, h, Measure.restrict_restrict_of_subset hPU]
  | succ k ih =>
    intro hk μ' hμ'c hμ'f hμ'
    have hkn : k < n := hk
    obtain ⟨μk, hμkc, hμkf, hμkT⟩ := pClaim_all (n := n) U (maxTuple u c k)
    have hIH := ih hkn.le μk hμkc hμkf hμkT
    rw [maxTuple_succ u c hkn] at hμ'
    have hslot := restrict_eq_of_max_slot (u := maxTuple u c k) ⟨k, hkn⟩ c hμkc hμkf hμkT
      hμ'c hμ'f hμ' (exists_isAdmissible_maxTuple hF c k)
    have hPS : P ⊆ {z | z ∈ U ∧ c < maxTuple u c k ⟨k, hkn⟩ z} := fun z hz ↦
      ⟨hz.1, by rw [maxTuple_apply_self]; exact hz.2 _⟩
    rw [← hIH, ← Measure.restrict_restrict_of_subset hPS, ← hslot,
      Measure.restrict_restrict_of_subset hPS]

theorem IsDecApprox.congr {U : Opens (ComplexModel n)} {w w' : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (h : EqOn w w' U) :
    IsDecApprox U w' G := by
  refine ⟨hG.1, hG.2.1, fun z hz ↦ h hz ▸ hG.2.2.1 z hz, fun K hK hKU ↦ ?_⟩
  rw [← (h.mono hKU).image_eq]
  exact hG.2.2.2 K hK hKU

/-- **Max-constant locality on an open set.** For measures that are limits of
mixed densities of decreasing approximations on every relatively compact open
subset, replacing every slot `v i` by `max(v i, c)` does not change the measure
on the common strict superlevel set. -/
theorem restrict_eq_of_max_const {Ω : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    (c : ℝ) {μ ν : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hμT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ)
    (hνT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U w F ∧ TendstoMixed U F ν)
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} = μ.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hQ : {z | z ∈ Ω ∧ ∀ i, c < v i z} = ⋃ m, {z | z ∈ U m ∧ ∀ i, c < v i z} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hzΩ, hz⟩
      obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hzΩ)
      exact ⟨m, hm rfl, hz⟩
    · rintro ⟨m, hzm, hz⟩
      exact ⟨hUΩ m hzm, hz⟩
  rw [hQ, Measure.restrict_iUnion_congr]
  intro m
  set V := U m
  set P := {z | z ∈ V ∧ ∀ i, c < v i z}
  have hPV : P ⊆ V := fun z hz ↦ hz.1
  have hfinV (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ρ K < ⊤ := fun K hK hKV ↦ hρ K hK (hKV.trans (hUΩ m))
  obtain ⟨F, hF, hFT⟩ := hμT V (hUrc m)
  obtain ⟨μV, -, hμVf, hμVT⟩ := pClaim_all (n := n) V v
  have e1 : μ.restrict V = μV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV μ hμf) hμVf fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hμVT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  obtain ⟨G, hG, hGT⟩ := hνT V (hUrc m)
  have hG' : IsAdmissible n V (maxTuple v c n) G := by
    refine ⟨fun i ↦ (hG.1 i).congr fun z hz ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    simpa [maxTuple] using hmax i (hUΩ m hz)
  obtain ⟨νV, hνVc, hνVf, hνVT⟩ := pClaim_all (n := n) V (maxTuple v c n)
  have e2 : ν.restrict V = νV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV ν hνf) hνVf fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hνVT G hG' φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hchain := restrict_eq_maxTuple c hμVf hμVT ⟨F, hF⟩ n le_rfl νV hνVc hνVf hνVT
  rw [← Measure.restrict_restrict_of_subset hPV, e2, Measure.restrict_restrict_of_subset hPV,
    hchain, ← Measure.restrict_restrict_of_subset hPV, ← e1,
    Measure.restrict_restrict_of_subset hPV]

theorem IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed
    {Ω U : Opens (ComplexModel n)} {v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ) (hU : RelativelyCompactIn U Ω) :
    ∃ F, IsAdmissible n U (fun _ ↦ v) F ∧ TendstoMixed U F μ := by
  obtain ⟨f, hf⟩ := hμ.approximations_exist hU
  refine ⟨fun _ ↦ f, isAdmissible_diagonal hμ.1 (subset_closure.trans hU.2) hf,
    fun φ hφ hφc hφU ↦ ?_⟩
  refine ((hμ.2.2.2 U hU).2 f hf φ hφ hφc hφU).congr fun j ↦ ?_
  rw [(smoothMeasure_test_integral (hf.1 j) φ hφ hφc hφU).2.2,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]]
  simp only [mixedDensity_diagonal]

theorem IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed
    {Ω U : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hU : RelativelyCompactIn U Ω) :
    ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ := by
  obtain ⟨f, hf⟩ := hμ.approximations_exist hU
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  refine ⟨fun i k ↦ f k i, ⟨fun i ↦ isDecApprox_of_isDecreasingApproximation (hμ.1 i) hUΩ
    (hf.component i), fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩, fun φ hφ hφc hφU ↦ ?_⟩
  refine ((hμ.2.2.2 U hU).2 f hf φ hφ hφc hφU).congr fun j ↦ ?_
  have hpsd : ∀ i, IsSmoothPsdOn U (f j i) := fun i ↦
    ⟨((hf.1 j).component i).1, ((hf.1 j).component i).2.2⟩
  exact integral_densityMeasure hpsd hφU

/-- **Scalar max-constant locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalBedfordTaylorMeasure.restrict_max_const
    {Ω : Opens (ComplexModel n)} {v w : ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : EqOn w (fun z => max (v z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ c < v z} = μ.restrict {z | z ∈ Ω ∧ c < v z} := by
  have h := restrict_eq_of_max_const (v := fun _ ↦ v) (w := fun _ ↦ w) c hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) fun _ ↦ hmax
  have hS : {z | z ∈ Ω ∧ c < v z} ⊆ {z | z ∈ Ω ∧ ∀ _ : Fin n, c < v z} :=
    fun z hz ↦ ⟨hz.1, fun _ ↦ hz.2⟩
  rw [← Measure.restrict_restrict_of_subset hS, h, Measure.restrict_restrict_of_subset hS]

/-- **Mixed max-constant locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalMixedBedfordTaylorMeasure.restrict_max_const
    {Ω : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : ∀ i, EqOn (w i) (fun z => max (v i z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} = μ.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} :=
  restrict_eq_of_max_const c hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) hmax

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
