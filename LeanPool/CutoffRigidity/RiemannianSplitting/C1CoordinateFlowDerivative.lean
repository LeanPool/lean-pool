/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.C1CoordinateTaylor
public import LeanPool.CutoffRigidity.RiemannianSplitting.ShortLinearVariation
public import Mathlib.Analysis.ODE.Gronwall

/-! # Initial-point differentiation of actual coordinate ODE solutions
The derivative is obtained by a uniform C¹ Taylor estimate and Grönwall on the
actual nonlinear and linear variational equations. Differentiability of the
solution map is the conclusion, never an input.
-/

@[expose] public section
open Set Filter Metric
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine local family of ODE solutions has the actual variational equation
as its initial-point Fréchet derivative. The Lipschitz dependence and linear
variation data are explicit analytic obligations, to be obtained from Picard. -/
theorem hasFDerivAt_coordinateFlow_of_variation
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ t ∈ Icc 0 T, HasDerivAt (α y) (F (α y t)) t)
    {L : ℝ≥0} (hαLip : ∀ t ∈ Icc 0 T, LipschitzOnWith L (fun y ↦ α y t) (ball x r))
    {J : ℝ → E →L[ℝ] E} (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ t ∈ Icc 0 T, HasDerivAt J
      ((fderiv ℝ F (α x t)).comp (J t)) t) :
    HasFDerivAt (fun y ↦ α y T) (J T) x := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hXC : ContinuousOn (α x) (Icc 0 T) :=
    fun t ht ↦ (hαD x hx t ht).continuousAt.continuousWithinAt
  have hJC : ContinuousOn J (Icc 0 T) :=
    fun t ht ↦ (hJD t ht).continuousAt.continuousWithinAt
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hXC
  have hAC : ContinuousOn (fun t ↦ fderiv ℝ F (α x t)) (Icc 0 T) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn hXC
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hAC
  let K := max K₀ 0
  let L' := max (L : ℝ) 1
  let S := max 1 |gronwallBound 0 K 1 T|
  have hK : 0 ≤ K := le_max_right _ _
  have hL : 0 < L' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let e := ε / (L' * S)
  have he : 0 < e := div_pos hε (mul_pos hL hS)
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_c1_taylor_remainder_closedBall hF R he
  let d := min (r / 2) (δ / L')
  have hd : 0 < d := lt_min (half_pos hr) (div_pos hδ hL)
  filter_upwards [ball_mem_nhds (0 : E) hd] with h hh
  have hhn : ‖h‖ ≤ d := (by simpa only [mem_ball, dist_zero_right] using hh : ‖h‖ < d).le
  have hxh : x + h ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_le_of_lt (hhn.trans (min_le_left _ _)) (half_lt_self hr)
  let X := fun t ↦ α x t
  let Y := fun t ↦ α (x + h) t
  let A := fun t ↦ fderiv ℝ F (X t)
  let Z := fun t ↦ Y t - X t - J t h
  let Z' := fun t ↦ F (Y t) - F (X t) - A t (J t h)
  have hYC : ContinuousOn Y (Icc 0 T) :=
    fun t ht ↦ (hαD (x + h) hxh t ht).continuousAt.continuousWithinAt
  have hZC : ContinuousOn Z (Icc 0 T) :=
    (hYC.sub hXC).sub (hJC.clm_apply continuousOn_const)
  have hZzero : Z 0 = 0 := by
    dsimp only [Z, X, Y]
    rw [hαzero (x + h) hxh, hαzero x hx, hJzero, ContinuousLinearMap.id_apply]
    abel
  have hZD (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt Z (Z' t) t := by
    have hh := ((hαD (x + h) hxh t ht).sub (hαD x hx t ht)).sub
      ((hJD t ht).clm_apply (hasDerivAt_const t h))
    convert! hh using 1
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
    rfl
  have hΔ (t : ℝ) (ht : t ∈ Icc 0 T) : ‖Y t - X t‖ ≤ L' * ‖h‖ := by
    have hh := (hαLip t ht).norm_sub_le hxh hx
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hZbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖Z' t‖ ≤ K * ‖Z t‖ + e * L' * ‖h‖ := by
    have hbase : X t ∈ closedBall (0 : E) R := by
      simpa only [mem_closedBall, dist_zero_right, X] using hR t ht
    have hsmall : ‖Y t - X t‖ ≤ δ := by
      apply (hΔ t ht).trans
      have hhδ : ‖h‖ ≤ δ / L' := hhn.trans (min_le_right _ _)
      nlinarith [(le_div_iff₀ hL).mp hhδ]
    have hrem := hTaylor (X t) hbase (Y t - X t) hsmall
    have hid : X t + (Y t - X t) = Y t := by abel
    rw [hid] at hrem
    have heq : Z' t = A t (Z t) + (F (Y t) - F (X t) - A t (Y t - X t)) := by
      dsimp only [Z', Z]
      rw [map_sub, map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖A t (Z t)‖ + ‖F (Y t) - F (X t) - A t (Y t - X t)‖ := norm_add_le _ _
      _ ≤ K * ‖Z t‖ + e * L' * ‖h‖ := by
        have hAK : ‖A t‖ ≤ K := (hK₀ t ht).trans (le_max_left _ _)
        have hAZ := (A t).le_opNorm (Z t)
        have hrem' := hrem.trans (mul_le_mul_of_nonneg_left (hΔ t ht) he.le)
        rw [← mul_assoc] at hrem'
        exact add_le_add (hAZ.trans (mul_le_mul_of_nonneg_right hAK (norm_nonneg _))) hrem'
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hZC
    (fun t ht ↦ (hZD t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hZzero] : ‖Z 0‖ ≤ 0)
    (fun t ht ↦ hZbound t (Ico_subset_Icc_self ht)) T ⟨hT, le_rfl⟩
  have hscale : gronwallBound 0 K (e * L' * ‖h‖) T =
      (e * L' * ‖h‖) * gronwallBound 0 K 1 T := by
    unfold gronwallBound
    split_ifs <;> ring
  rw [sub_zero, hscale] at hgron
  have hBS : gronwallBound 0 K 1 T ≤ S :=
    (le_abs_self _).trans (le_max_right _ _)
  have heLS : e * L' * S = ε := by dsimp [e]; field_simp
  change ‖Z T‖ ≤ ε * ‖h‖
  calc
    _ ≤ (e * L' * ‖h‖) * gronwallBound 0 K 1 T := hgron
    _ ≤ (e * L' * ‖h‖) * S := mul_le_mul_of_nonneg_left hBS
      (mul_nonneg (mul_nonneg he.le hL.le) (norm_nonneg _))
    _ = ε * ‖h‖ := by rw [mul_right_comm, heLS]

/-- A common actual coefficient bound gives a common time window for
initial-point differentiation, independent of the chosen initial point. -/
theorem differentiableAt_coordinateFlow_short_of_bound
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ t ∈ Icc (-T) T, HasDerivAt (α y) (F (α y t)) t)
    {L : ℝ≥0} (hαLip : ∀ t ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y t) (ball x r))
    {M : ℝ≥0} (hM : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ F (α x s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 (T / 2)) :
    DifferentiableAt ℝ (fun y ↦ α y t) x := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hA : ContinuousOn (fun s ↦ fderiv ℝ F (α x s)) (Icc (-T) T) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun s hs ↦ (hαD x hx s hs).continuousAt.continuousWithinAt)
  obtain ⟨J, hJzero, _, hJD⟩ := exists_linear_variation_short_interval hT.le hA hM hshort
  have hsub : Icc 0 t ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [ht.2, hs.1, hs.2]
  apply (hasFDerivAt_coordinateFlow_of_variation hF x hr ht.1 hαzero
    (fun y hy s hs ↦ hαD y hy s (hsub hs))
    (fun s hs ↦ hαLip s (hsub hs)) hJzero ?_).differentiableAt
  intro s hs
  have hsT : s ∈ Ioo (-T) T := by
    constructor <;> linarith [hs.1, hs.2, ht.2]
  exact (hJD s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)

/-- The same actual construction differentiates negative-time coordinate
solutions by time reversal of the actual nonlinear equation. -/
theorem differentiableAt_coordinateFlow_symmetric_short_of_bound
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (ball x r))
    {M : ℝ≥0} (hM : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ F (α x s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) {t : ℝ} (ht : |t| ≤ T / 2) :
    DifferentiableAt ℝ (fun y ↦ α y t) x := by
  by_cases htpos : 0 ≤ t
  · exact differentiableAt_coordinateFlow_short_of_bound hF x hr hT hαzero hαD
      hαLip hM hshort ⟨htpos, (le_abs_self t).trans ht⟩
  · have hreflect (s : ℝ) (hs : s ∈ Icc (-T) T) : -s ∈ Icc (-T) T :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T,
        HasDerivAt (fun u ↦ α y (-u)) (-F (α y (-s))) s := by
      intro y hy s hs
      simpa only [Function.comp_def, neg_one_smul] using
        (hαD y hy (-s) (hreflect s hs)).scomp s (hasDerivAt_neg s)
    have hMneg : ∀ s ∈ Icc (-T) T,
        ‖fderiv ℝ (fun z ↦ -F z) (α x (-s))‖ ≤ M := by
      intro s hs
      simpa only [fderiv_fun_neg, norm_neg] using hM (-s) (hreflect s hs)
    have hh := differentiableAt_coordinateFlow_short_of_bound hF.neg x hr hT
      (α := fun y s ↦ α y (-s)) (by simpa using hαzero) hD
      (fun s hs ↦ hαLip (-s) (hreflect s hs)) hMneg hshort
      (t := -t) ⟨by linarith, (neg_le_abs t).trans ht⟩
    simpa only [neg_neg] using hh

/-- Initial-point differentiability on a genuine short time window, with the
variational solution constructed from the actual coordinate field. No linear
variation or solution-map differentiability is supplied as an assumption. -/
theorem exists_short_differentiableAt_coordinateFlow
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ t ∈ Icc (-T) T, HasDerivAt (α y) (F (α y t)) t)
    {L : ℝ≥0} (hαLip : ∀ t ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y t) (ball x r)) :
    ∃ ε > (0 : ℝ), ε < T ∧ ∀ t ∈ Icc 0 ε,
      DifferentiableAt ℝ (fun y ↦ α y t) x := by
  have hx : x ∈ ball x r := mem_ball_self hr
  let A := fun t ↦ fderiv ℝ F (α x t)
  have hAC : ContinuousOn A (Icc (-T) T) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun t ht ↦ (hαD x hx t ht).continuousAt.continuousWithinAt)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hAC
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  have hAM (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖A t‖ ≤ M :=
    (hM₀ t ht).trans (le_max_left _ _)
  let θ := min (T / 2) (1 / (4 * ((M : ℝ) + 1)))
  have hden : 0 < 4 * ((M : ℝ) + 1) := by positivity
  have hθ : 0 < θ := lt_min (half_pos hT) (div_pos zero_lt_one hden)
  have hθT : θ < T := (min_le_left _ _).trans_lt (half_lt_self hT)
  have hθsub : Icc (-θ) θ ⊆ Icc (-T) T :=
    Icc_subset_Icc (neg_le_neg hθT.le) hθT.le
  have hshort : 2 * (M : ℝ) * θ ≤ 1 := by
    have hb := (le_div_iff₀ hden).mp (min_le_right (T / 2) (1 / (4 * ((M : ℝ) + 1))))
    nlinarith [mul_nonneg M.coe_nonneg hθ.le]
  obtain ⟨J, hJzero, _, hJD⟩ := exists_linear_variation_short_interval
    hθ.le (hAC.mono hθsub) (fun t ht ↦ hAM t (hθsub ht)) hshort
  refine ⟨θ / 2, half_pos hθ, (half_lt_self hθ).trans hθT, ?_⟩
  intro t ht
  have hsub : Icc 0 t ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [ht.2, hs.1, hs.2]
  apply (hasFDerivAt_coordinateFlow_of_variation hF x hr ht.1 hαzero
    (fun y hy s hs ↦ hαD y hy s (hsub hs))
    (fun s hs ↦ hαLip s (hsub hs)) hJzero ?_).differentiableAt
  intro s hs
  have hsθ : s ∈ Ioo (-θ) θ := by
    constructor <;> linarith [hs.1, hs.2, ht.2]
  exact (hJD s (Ioo_subset_Icc_self hsθ)).hasDerivAt (Icc_mem_nhds hsθ.1 hsθ.2)

end CutoffRigidity
