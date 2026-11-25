/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorStepW

/-!
# Weighted convergence near a point

Given the level-`q` unweighted claim, the weighted integrals of a nonnegative
test supported in a small ball converge. After subtracting constants, the
approximations are modified by the regularized maximum with a collar potential,
which leaves them unchanged near the test and makes them equal to the collar
potential near the boundary of the ball; the collar squeeze then applies, and the
limit is transferred back by comparing tests.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open MeasureLocality (integrable_of_tsupport_subset)

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

theorem exists_collar_constants (z₀ : ComplexModel n) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ A ρ : ℝ, 0 < A ∧ R / 2 < ρ ∧ ρ < R ∧
      (∀ z, ‖z - z₀‖ < R / 2 → collar z₀ A R z + 1 ≤ -M) ∧
      (∀ z, ρ < ‖z - z₀‖ → -1 / 2 ≤ collar z₀ A R z) := by
  set A := 2 * (M + 1) / R ^ 2 with hA
  have hA0 : 0 < A := by positivity
  have hAR : A * R ^ 2 = 2 * (M + 1) := by rw [hA]; field_simp
  set δ := 1 / (2 * A) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδR : δ ≤ R ^ 2 / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  refine ⟨A, Real.sqrt (R ^ 2 - δ), hA0, ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [show R / 2 = Real.sqrt ((R / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  · exact (Real.sqrt_lt' hR).2 (by linarith)
  · have h1 : ‖z - z₀‖ ^ 2 < (R / 2) ^ 2 := by
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    unfold collar SmoothMax.quadraticCollar
    nlinarith
  · have hρ0 : 0 ≤ R ^ 2 - δ := by nlinarith
    have h1 : R ^ 2 - δ < ‖z - z₀‖ ^ 2 := by
      have := pow_lt_pow_left₀ hz (Real.sqrt_nonneg _) two_ne_zero
      rwa [Real.sq_sqrt hρ0] at this
    unfold collar SmoothMax.quadraticCollar
    have hAδ : A * δ = 1 / 2 := by rw [hδ]; field_simp
    nlinarith

theorem mixedDensity_congr_hessian {f g : Fin n → ComplexModel n → ℝ} {z : ComplexModel n}
    (h : ∀ i, complexHessian (f i) z = complexHessian (g i) z) :
    mixedDensity f z = mixedDensity g z := by
  simp only [mixedDensity, h]

theorem IsDecApprox.tendsto_integral_mul_sub {V : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V w G)
    {ν : Measure (ComplexModel n)} (hνf : ∀ K, IsCompact K → K ⊆ V → ν K < ⊤)
    {ψ : ComplexModel n → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ V) (a : ℝ) :
    Tendsto (fun l ↦ ∫ z, ψ z * (G l z - a) ∂ν) atTop (𝓝 (∫ z, ψ z * (w z - a) ∂ν)) := by
  obtain ⟨C, hC⟩ := hG.exists_abs_le hψc hψV
  have hbound := (integrable_of_tsupport_subset hνf hψ hψc hψV).abs.const_mul (C + |a|)
  refine tendsto_integral_of_dominated_convergence (fun z ↦ (C + |a|) * |ψ z|) (fun l ↦ ?_)
    hbound (fun l ↦ Eventually.of_forall fun z ↦ ?_) (Eventually.of_forall fun z ↦ ?_)
  · exact (continuous_of_continuousOn_of_eq_zero V.isOpen (isClosed_tsupport ψ) hψV
      (hψ.continuousOn.mul ((hG.1 l).1.continuousOn.sub continuousOn_const))
      fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]).aestronglyMeasurable
  · by_cases hz : z ∈ tsupport ψ
    · rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith [hC l z hz]))
        (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · by_cases hzV : z ∈ (V : Set (ComplexModel n))
    · exact ((hG.2.2.1 z hzV).sub_const a).const_mul _
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hψV h)
      simp [this]

private theorem exists_shifts_on_closedBall {q : ℕ} {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible q U u F)
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {z₀ : ComplexModel n} {R : ℝ} (hball : closedBall z₀ (2 * R) ⊆ U) :
    ∃ (Mi mi : Fin n → ℝ) (MG mw M : ℝ),
      (∀ i z, z ∈ closedBall z₀ (2 * R) → F i 0 z ≤ Mi i) ∧
      (∀ i z, z ∈ closedBall z₀ (2 * R) → mi i ≤ u i z) ∧
      (∀ z, z ∈ closedBall z₀ (2 * R) → G 0 z ≤ MG) ∧
      (∀ z, z ∈ closedBall z₀ (2 * R) → mw ≤ w z) ∧
      0 ≤ M ∧ (∀ i, Mi i + 2 - mi i ≤ M) ∧ MG + 2 - mw ≤ M := by
  classical
  set Kb := closedBall z₀ (2 * R)
  have hKb : IsCompact Kb := isCompact_closedBall _ _
  have hup (f : ComplexModel n → ℝ) (hf : ContinuousOn f U) : ∃ M, ∀ z ∈ Kb, f z ≤ M := by
    obtain ⟨M, hM⟩ := (hKb.image_of_continuousOn (hf.mono hball)).bddAbove
    exact ⟨M, fun z hz ↦ hM ⟨z, hz, rfl⟩⟩
  have hlow (v : ComplexModel n → ℝ) (hv : BddBelow (v '' Kb)) : ∃ m, ∀ z ∈ Kb, m ≤ v z := by
    obtain ⟨m, hm⟩ := hv
    exact ⟨m, fun z hz ↦ hm ⟨z, hz, rfl⟩⟩
  choose Mi hMi using fun i ↦ hup (F i 0) ((hF.1 i).1 0).1.continuousOn
  choose mi hmi using fun i ↦ hlow (u i) ((hF.1 i).2.2.2 Kb hKb hball)
  obtain ⟨MG, hMG⟩ := hup (G 0) (hG.1 0).1.continuousOn
  obtain ⟨mw, hmw⟩ := hlow w (hG.2.2.2 Kb hKb hball)
  set c : Fin n → ℝ := fun i ↦ Mi i + 2
  set cG := MG + 2
  set M := max (cG - mw) 0 + ∑ i, max (c i - mi i) 0
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (Finset.sum_nonneg fun i _ ↦ le_max_right _ _)
  have hcM (i : Fin n) : c i - mi i ≤ M := by
    have h1 : max (c i - mi i) 0 ≤ ∑ j, max (c j - mi j) 0 :=
      Finset.single_le_sum (f := fun j ↦ max (c j - mi j) 0) (fun j _ ↦ le_max_right _ _)
        (Finset.mem_univ i)
    have := le_max_left (c i - mi i) 0
    linarith [le_max_right (cG - mw) 0]
  have hMG' : cG - mw ≤ M := by
    linarith [le_max_left (cG - mw) 0,
      Finset.sum_nonneg (s := Finset.univ)
        fun i (_ : i ∈ Finset.univ) ↦ le_max_right (c i - mi i) 0]
  exact ⟨Mi, mi, MG, mw, M, hMi, hmi, hMG, hmw, hM0, hcM, hMG'⟩

/-- **Weighted convergence for tests in a small ball.** -/
theorem tendsto_weighted_ball {q : ℕ} (hP : PClaim n q) {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hPμ : ∀ F, IsAdmissible q U u F → TendstoMixed U F μ)
    {F : Fin n → ℕ → ComplexModel n → ℝ} (hF : IsAdmissible q U u F)
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {z₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : closedBall z₀ (2 * R) ⊆ U)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχ0 : ∀ z, 0 ≤ χ z)
    (hχs : tsupport χ ⊆ ball z₀ (R / 2)) :
    Tendsto (fun k ↦ ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) atTop
      (𝓝 (∫ z, χ z * w z ∂μ)) := by
  classical
  -- sets
  set V : Opens (ComplexModel n) := ⟨ball z₀ (2 * R), isOpen_ball⟩ with hV
  have hVU : V ≤ U := fun z hz ↦ hball (ball_subset_closedBall hz)
  set W : Set (ComplexModel n) := ball z₀ R with hW
  have hWc : IsCompact (closure W) :=
    (isCompact_closedBall z₀ R).of_isClosed_subset isClosed_closure
      (closure_ball_subset_closedBall)
  have hWV : closure W ⊆ V := closure_ball_subset_closedBall.trans
    (closedBall_subset_ball (by linarith))
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall z₀ (R / 2)).of_isClosed_subset (isClosed_tsupport χ)
      (hχs.trans ball_subset_closedBall)
  have hsmallV : ball z₀ (R / 2) ⊆ V := ball_subset_ball (by linarith)
  have hχU : tsupport χ ⊆ U := hχs.trans (hsmallV.trans hVU)
  set Kb := closedBall z₀ (2 * R)
  obtain ⟨Mi, mi, MG, mw, M, hMi, hmi, hMG, hmw, hM0, hcM', hMG'⟩ :=
    exists_shifts_on_closedBall hF hG hball
  let c : Fin n → ℝ := fun i ↦ Mi i + 2
  let cG := MG + 2
  have hcM (i : Fin n) : c i - mi i ≤ M := hcM' i
  have hMGbound : cG - mw ≤ M := hMG'
  -- collar
  obtain ⟨A, ρ, hA, hρ1, hρ2, hin, hout⟩ := exists_collar_constants z₀ hR hM0
  set h := collar z₀ A R with hh_def
  have hhs : IsSmoothPsdOn V h := isSmoothPsdOn_collar V z₀ hA.le R
  set K := closedBall z₀ ρ
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKW : K ⊆ W := closedBall_subset_ball hρ2
  -- modified families
  set F' : Fin n → ℕ → ComplexModel n → ℝ := fun i k ↦
    if i.val < q then smoothMax (fun y ↦ F i k y - c i) h else F i k with hF'_def
  set u' : Fin n → ComplexModel n → ℝ := fun i ↦
    if i.val < q then smoothMax (fun y ↦ u i y - c i) h else u i with hu'_def
  set G' : ℕ → ComplexModel n → ℝ := fun k ↦ smoothMax (fun y ↦ G k y - cG) h with hG'_def
  set w' : ComplexModel n → ℝ := smoothMax (fun y ↦ w y - cG) h with hw'_def
  have hF' : IsAdmissible q V u' F' := by
    refine ⟨fun i ↦ ?_, fun i hi k z hz ↦ ?_⟩
    · by_cases hi : i.val < q
      · simpa only [hF'_def, hu'_def, hi, ite_true] using
          ((hF.1 i).mono hVU).smoothMax_sub (c i) hhs
      · simpa only [hF'_def, hu'_def, hi, ite_false] using (hF.1 i).mono hVU
    · have hi' : ¬ i.val < q := not_lt.mpr hi
      simp only [hF'_def, hi', ite_false]
      exact hF.2 i hi k (hVU hz)
  have hG' : IsDecApprox V w' G' := (hG.mono hVU).smoothMax_sub cG hhs
  have hVKb : ∀ z ∈ (V : Set (ComplexModel n)), z ∈ Kb := fun z hz ↦ ball_subset_closedBall hz
  have hFup (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      F i k z - c i ≤ -2 := by
    have := (hF.1 i).2.1 z (hVU hz) (Nat.zero_le k)
    have := hMi i z (hVKb z hz)
    simp only [c]; linarith
  have hGup (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      G k z - cG ≤ -2 := by
    have := hG.2.1 z (hVU hz) (Nat.zero_le k)
    have := hMG z (hVKb z hz)
    simp only [cG]; linarith
  have hFlow (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      -M ≤ F i k z - c i := by
    have := (hF.1 i).le_of_mem (hVU hz) k
    have := hmi i z (hVKb z hz)
    have := hcM i
    linarith
  have hGlow (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      -M ≤ G k z - cG := by
    have := hG.le_of_mem (hVU hz) k
    have := hmw z (hVKb z hz)
    linarith
  have hnotK (z : ComplexModel n) (hz : z ∉ K) : ρ < ‖z - z₀‖ := by
    simpa [K, mem_closedBall, dist_eq_norm] using hz
  have hsmall (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) : ‖z - z₀‖ < R / 2 := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hGh : ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → G' k z = h z := by
    intro k z hzV hzK
    refine smoothMax_eq_right ?_
    have := hout z (hnotK z hzK)
    linarith [hGup k z hzV]
  have hFh : ∀ i : Fin n, i.val < q → ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K →
      F' i k z = h z := by
    intro i hi k z hzV hzK
    simp only [hF'_def, hi, ite_true]
    refine smoothMax_eq_right ?_
    have := hout z (hnotK z hzK)
    linarith [hFup i k z hzV]
  have hGnear (k : ℕ) (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) : G' k z = G k z - cG := by
    refine smoothMax_eq_left ?_
    have := hin z (hsmall z hz)
    linarith [hGlow k z (hsmallV hz)]
  have hFnear (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) :
      complexHessian (F' i k) z = complexHessian (F i k) z := by
    by_cases hi : i.val < q
    · have hev : F' i k =ᶠ[𝓝 z] fun y ↦ F i k y - c i := by
        filter_upwards [isOpen_ball.mem_nhds hz] with y hy
        simp only [hF'_def, hi, ite_true]
        refine smoothMax_eq_left ?_
        have := hin y (hsmall y hy)
        linarith [hFlow i k y (hsmallV hy)]
      rw [MixedHessian.complexHessian_congr hev, complexHessian_sub_const]
    · simp only [hF'_def, hi, ite_false]
  have hMDnear (k : ℕ) (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) :
      mixedDensity (fun i ↦ F' i k) z = mixedDensity (fun i ↦ F i k) z :=
    mixedDensity_congr_hessian fun i ↦ hFnear i k z hz
  have hwnear (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) : w' z = w z - cG := by
    refine smoothMax_eq_left ?_
    have := hin z (hsmall z hz)
    have := hmw z (hVKb z (hsmallV hz))
    linarith
  -- the cutoff `ζ`
  obtain ⟨ζs, hζ1, hζ01⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := ⟨W, isOpen_ball⟩) hK hKW
  have hζK : ∀ z ∈ K, ζs z = 1 := fun z hz ↦ (hζ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  have hζW : tsupport ζs ⊆ W := ζs.tsupport_subset
  -- the modified limit measure
  obtain ⟨μ', -, hμ'f, hμ'P⟩ := hP V u'
  have hT' := hμ'P F' hF'
  -- rescaling the test below `ζ`
  obtain ⟨B, hB⟩ := hχc.exists_bound_of_continuous hχ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z₀)
  set sc := B + 1 with hsc
  have hsc0 : 0 < sc := by linarith
  set χ' : ComplexModel n → ℝ := fun z ↦ χ z / sc with hχ'_def
  have hχ'c : Continuous χ' := hχ.div_const sc
  have hχ'0 : ∀ z, 0 ≤ χ' z := fun z ↦ div_nonneg (hχ0 z) hsc0.le
  have hsuppK : tsupport χ ⊆ K := hχs.trans (ball_subset_closedBall.trans
    (closedBall_subset_closedBall hρ1.le))
  have hχ'ζ : ∀ z, χ' z ≤ ζs z := by
    intro z
    by_cases hz : z ∈ tsupport χ
    · rw [hζK z (hsuppK hz), hχ'_def, div_le_one hsc0]
      have := hB z
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (χ z)]
    · simp only [hχ'_def, image_eq_zero_of_notMem_tsupport hz, zero_div]
      exact (hζ01 z).1
  have hmod := tendsto_weighted_of_collar hF' hG' hμ'f hT' hhs hK hKW isOpen_ball hWc hWV hGh hFh
    ζs.continuous hζ01 hζK hζW hχ'c hχ'0 hχ'ζ
  have hχ'supp : tsupport χ' ⊆ tsupport χ := closure_mono fun z hz ↦ by
    simp only [Function.mem_support, hχ'_def, ne_eq, div_eq_zero_iff, not_or] at hz
    exact hz.1
  have hχ'cs : HasCompactSupport χ' := hχc.mono' ((subset_tsupport χ').trans hχ'supp)
  have hχ'V : tsupport χ' ⊆ V := hχ'supp.trans (hχs.trans hsmallV)
  have hχ'U : tsupport χ' ⊆ U := hχ'V.trans hVU
  -- transfer of the approximating integrals
  have hT1 : (fun k ↦ ∫ z, χ' z * G' k z * mixedDensity (fun i ↦ F' i k) z) =
      fun k ↦ ∫ z, χ' z * (G k z - cG) * mixedDensity (fun i ↦ F i k) z := by
    funext k
    congr 1
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [hGnear k z (hχs hz), hMDnear k z (hχs hz)]
    · simp [hχ'_def, image_eq_zero_of_notMem_tsupport hz]
  rw [hT1] at hmod
  -- transfer of the limit
  have hstepa : ∫ z, χ' z * w' z ∂μ' = ∫ z, χ' z * (w z - cG) ∂μ' := by
    congr 1
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [hwnear z (hχs hz)]
    · simp [hχ'_def, image_eq_zero_of_notMem_tsupport hz]
  have hstepb (l : ℕ) : ∫ z, χ' z * (G l z - cG) ∂μ' = ∫ z, χ' z * (G l z - cG) ∂μ := by
    have hψ : Continuous fun z ↦ χ' z * (G l z - cG) :=
      continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport χ') hχ'U
        (hχ'c.continuousOn.mul ((hG.1 l).1.continuousOn.sub continuousOn_const))
        fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]
    have hψc : HasCompactSupport fun z ↦ χ' z * (G l z - cG) := hχ'cs.mul_right
    have hψs : tsupport (fun z ↦ χ' z * (G l z - cG)) ⊆ tsupport χ' := tsupport_mul_subset_left
    have h1 := hT' _ hψ hψc (hψs.trans hχ'V)
    have h2 := hPμ F hF _ hψ hψc (hψs.trans hχ'U)
    refine tendsto_nhds_unique (h1.congr fun k ↦ ?_) h2
    congr 1
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [hMDnear k z (hχs hz)]
    · simp [hχ'_def, image_eq_zero_of_notMem_tsupport hz]
  have hstepc : ∫ z, χ' z * (w z - cG) ∂μ' = ∫ z, χ' z * (w z - cG) ∂μ := by
    have hG'V := hG.mono hVU
    have l1 := hG'V.tendsto_integral_mul_sub hμ'f hχ'c hχ'cs hχ'V cG
    have l2 := hG.tendsto_integral_mul_sub hμf hχ'c hχ'cs hχ'U cG
    exact tendsto_nhds_unique (l1.congr hstepb) l2
  rw [hstepa, hstepc] at hmod
  -- undoing the constant and the rescaling
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1
  have hIa (k : ℕ) : Integrable fun z ↦ χ' z * (G k z - cG) * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ (G k z - cG) * mixedDensity (fun i ↦ F i k) z)
      (((hG.1 k).1.continuousOn.sub continuousOn_const).mul (hDc k)) hχ'c hχ'cs hχ'U
    simpa only [mul_assoc] using this
  have hIb (k : ℕ) : Integrable fun z ↦ χ' z * mixedDensity (fun i ↦ F i k) z :=
    integrable_mul_of_continuousOn (hDc k) hχ'c hχ'cs hχ'U
  have hconst := hPμ F hF χ' hχ'c hχ'cs hχ'U
  have hsum := hmod.add (hconst.const_mul cG)
  have hlimeq : ∫ z, χ' z * (w z - cG) ∂μ + cG * ∫ z, χ' z ∂μ = ∫ z, χ' z * w z ∂μ := by
    have hI1 : Integrable (fun z ↦ χ' z * (w z - cG)) μ := by
      refine ((hG.integrable_mul hμf hχ'c hχ'cs hχ'U).sub
        ((integrable_of_tsupport_subset hμf hχ'c hχ'cs hχ'U).const_mul cG)).congr
        (Eventually.of_forall fun z ↦ ?_)
      simp only [Pi.sub_apply]; ring
    rw [← integral_const_mul, ← integral_add hI1
      ((integrable_of_tsupport_subset hμf hχ'c hχ'cs hχ'U).const_mul cG)]
    congr 1; funext z; ring
  rw [hlimeq] at hsum
  have hscale := hsum.const_mul sc
  have hfin : sc * ∫ z, χ' z * w z ∂μ = ∫ z, χ z * w z ∂μ := by
    rw [← integral_const_mul]; congr 1; funext z; simp only [hχ'_def]; field_simp
  rw [hfin] at hscale
  refine hscale.congr fun k ↦ ?_
  rw [← integral_const_mul, ← integral_add (hIa k) ((hIb k).const_mul cG), ← integral_const_mul]
  congr 1; funext z; simp only [hχ'_def]; field_simp; ring

/-- Weighted convergence for nonnegative tests, by a partition of unity into
tests supported in small balls. -/
theorem tendsto_weighted_nonneg {q : ℕ} (hP : PClaim n q) {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hPμ : ∀ F, IsAdmissible q U u F → TendstoMixed U F μ)
    {F : Fin n → ℕ → ComplexModel n → ℝ} (hF : IsAdmissible q U u F)
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hχ0 : ∀ z, 0 ≤ χ z) :
    Tendsto (fun k ↦ ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) atTop
      (𝓝 (∫ z, χ z * w z ∂μ)) := by
  classical
  have hrad : ∀ z ∈ tsupport χ, ∃ R > 0, closedBall z (2 * R) ⊆ U := fun z hz ↦ by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp U.isOpen z (hχU hz)
    exact ⟨ε / 3, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose! R hR hRU using hrad
  obtain ⟨t, htK, hcover⟩ := hχc.elim_nhds_subcover (fun z ↦ ball z (R z / 2))
    fun z hz ↦ ball_mem_nhds z (by have := hR z hz; positivity)
  set e := t.equivFin
  set s : Fin t.card → Set (ComplexModel n) := fun j ↦ ball (e.symm j : ComplexModel n)
    (R (e.symm j) / 2)
  have hcov' : tsupport χ ⊆ ⋃ j, s j := by
    intro z hz
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨e ⟨x, hxt⟩, by simpa [s] using hzx⟩
  obtain ⟨f, hfs, hfsum, hf01, hfc⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun j ↦ isOpen_ball) hχc hcov'
  set χj : Fin t.card → ComplexModel n → ℝ := fun j z ↦ f j z * χ z
  have hχj (j : Fin t.card) : Continuous (χj j) := (f j).continuous.mul hχ
  have hχj0 (j : Fin t.card) (z : ComplexModel n) : 0 ≤ χj j z :=
    mul_nonneg (hf01 j z).1 (hχ0 z)
  have hχjs (j : Fin t.card) : tsupport (χj j) ⊆ ball (e.symm j : ComplexModel n)
      (R (e.symm j) / 2) := (tsupport_mul_subset_left).trans (hfs j)
  have hχjc (j : Fin t.card) : HasCompactSupport (χj j) := (hfc j).mul_right
  have hχjU (j : Fin t.card) : tsupport (χj j) ⊆ U := (tsupport_mul_subset_right).trans hχU
  have hsum (z : ComplexModel n) : χ z = ∑ j, χj j z := by
    by_cases hz : z ∈ tsupport χ
    · have h1 := hfsum hz
      simp only [Finset.sum_apply, Pi.one_apply] at h1
      simp only [χj, ← Finset.sum_mul, h1, one_mul]
    · simp [χj, image_eq_zero_of_notMem_tsupport hz]
  have hpiece (j : Fin t.card) := tendsto_weighted_ball hP hμf hPμ hF hG
    (hR _ (htK _ (e.symm j).2)) (hRU _ (htK _ (e.symm j).2)) (hχj j) (hχj0 j) (hχjs j)
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1
  have hIk (j : Fin t.card) (k : ℕ) :
      Integrable fun z ↦ χj j z * G k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F i k) z)
      ((hG.1 k).1.continuousOn.mul (hDc k)) (hχj j) (hχjc j) (hχjU j)
    simpa only [mul_assoc] using this
  have hlim := tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) ↦ hpiece j
  rw [← integral_finsetSum _ fun j _ ↦ hG.integrable_mul hμf (hχj j) (hχjc j) (hχjU j)] at hlim
  have hL : (fun z ↦ ∑ j, χj j z * w z) = fun z ↦ χ z * w z := by
    funext z; rw [hsum z, Finset.sum_mul]
  rw [hL] at hlim
  refine hlim.congr fun k ↦ ?_
  rw [← integral_finsetSum _ fun j _ ↦ hIk j k]
  congr 1; funext z; rw [hsum z, Finset.sum_mul, Finset.sum_mul]

/-- **The weighted induction step.** -/
theorem wClaim_of_pClaim {q : ℕ} (hP : PClaim n q) : WClaim n q := by
  intro U u μ _ hμf hPμ F hF w G hG χ hχ hχc hχU
  set χp : ComplexModel n → ℝ := fun z ↦ max (χ z) 0
  set χm : ComplexModel n → ℝ := fun z ↦ max (-χ z) 0
  have hχp : Continuous χp := hχ.max continuous_const
  have hχm : Continuous χm := hχ.neg.max continuous_const
  have hsp : tsupport χp ⊆ tsupport χ := closure_mono fun z hz ↦ by
    intro h0; exact hz (by simp [χp, h0])
  have hsm : tsupport χm ⊆ tsupport χ := closure_mono fun z hz ↦ by
    intro h0; exact hz (by simp [χm, h0])
  have hp := tendsto_weighted_nonneg hP hμf hPμ hF hG hχp (hχc.mono' ((subset_tsupport _).trans
    hsp)) (hsp.trans hχU) fun z ↦ le_max_right _ _
  have hm := tendsto_weighted_nonneg hP hμf hPμ hF hG hχm (hχc.mono' ((subset_tsupport _).trans
    hsm)) (hsm.trans hχU) fun z ↦ le_max_right _ _
  have hdecomp (z : ComplexModel n) : χ z = χp z - χm z := by
    simp only [χp, χm]
    rcases le_total (χ z) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1
  have hIk (ψ : ComplexModel n → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
      (hψU : tsupport ψ ⊆ U) (k : ℕ) :
      Integrable fun z ↦ ψ z * G k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F i k) z)
      ((hG.1 k).1.continuousOn.mul (hDc k)) hψ hψc hψU
    simpa only [mul_assoc] using this
  have hpc : HasCompactSupport χp := hχc.mono' ((subset_tsupport _).trans hsp)
  have hmc : HasCompactSupport χm := hχc.mono' ((subset_tsupport _).trans hsm)
  have hlim := hp.sub hm
  rw [← integral_sub (hG.integrable_mul hμf hχp hpc (hsp.trans hχU))
    (hG.integrable_mul hμf hχm hmc (hsm.trans hχU))] at hlim
  have hL : (fun z ↦ χp z * w z - χm z * w z) = fun z ↦ χ z * w z := by
    funext z; rw [hdecomp z]; ring
  rw [hL] at hlim
  refine hlim.congr fun k ↦ ?_
  rw [← integral_sub (hIk χp hχp hpc (hsp.trans hχU) k) (hIk χm hχm hmc (hsm.trans hχU) k)]
  congr 1; funext z; rw [hdecomp z]; ring

/-- **Bedford–Taylor convergence for decreasing smooth approximations.** All
slots may vary. -/
theorem pClaim_all : PClaim n n := by
  suffices h : ∀ q, PClaim n q from h n
  intro q
  induction q with
  | zero => exact pClaim_zero
  | succ q ih => exact pClaim_succ ih (wClaim_of_pClaim ih)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
