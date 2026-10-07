/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteDriftLipschitz
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.LineDeriv.Measurable

/-!
# The drift hypotheses of the finite-axis limit equation

The lifted drift `B_n = (V_n X/R, W_n)` of `eq:drift:Bn:def` and its divergence
`div_{X,Z} B_n = 2 V_n / R` (continued to the axis by `2 ∂_R V_n`), at the moving axis points
`(0, z_n)` of `eq:aniso:zoom:finite:variables`, have the three properties from which the admissible
limiting drift of `eq:aniso:zoom:finite:limit` is extracted:

* continuity on every compact subset of `ℝ⁵ × (-∞, -1]`, for all large `n`;
* for every compact set of times in `(-∞, -1]`, one constant bounding `B_n`, `div B_n` and their
  spatial Lipschitz constants on every ball, for all large `n` (the footnote to
  `eq:drift:Bn:def`);
* on every time slice, `div B_n` is the weak divergence of `B_n` (`div_{X,Z} B_n = 2 V_n/R` off
  the axis, the axis being a null set crossed by a Lipschitz field).
-/

public section

open Set Filter Topology Metric MeasureTheory
open CKN.Foundation.Parabolic CKN
open scoped NNReal

noncomputable section

namespace CIV

/-- A function Lipschitz in space, uniformly in time, and continuous in time at every point, is
jointly continuous. -/
theorem continuousOn_prod_of_lipschitz_of_continuousOn {E : Type*} [SeminormedAddCommGroup E]
    (F : Vec 5 × ℝ → E) (A : Set (Vec 5)) (J : Set ℝ) (L : ℝ)
    (hlip : ∀ τ ∈ J, ∀ x ∈ A, ∀ y ∈ A, ‖F (x, τ) - F (y, τ)‖ ≤ L * ‖x - y‖)
    (htime : ∀ x ∈ A, ContinuousOn (fun τ => F (x, τ)) J) :
    ContinuousOn F (A ×ˢ J) := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hd₁⟩ := Metric.continuousWithinAt_iff.mp (htime z.1 hz.1 z.2 hz.2) (ε / 2)
    (by positivity)
  set L' := |L| + 1 with hL'
  have hL'pos : 0 < L' := by positivity
  refine ⟨min δ₁ (ε / (2 * L')), lt_min hδ₁ (by positivity), fun w hw hwz => ?_⟩
  have hd1 : dist w.1 z.1 < ε / (2 * L') :=
    lt_of_le_of_lt ((le_max_left _ _).trans_eq Prod.dist_eq.symm) (lt_of_lt_of_le hwz
      (min_le_right _ _))
  have hd2 : dist w.2 z.2 < δ₁ :=
    lt_of_le_of_lt ((le_max_right _ _).trans_eq Prod.dist_eq.symm) (lt_of_lt_of_le hwz
      (min_le_left _ _))
  have h1 := hlip w.2 hw.2 w.1 hw.1 z.1 hz.1
  have h2 := hd₁ hw.2 hd2
  rw [dist_eq_norm] at hd1 h2 ⊢
  have hL : L * ‖w.1 - z.1‖ ≤ ε / 2 := by
    calc L * ‖w.1 - z.1‖ ≤ L' * ‖w.1 - z.1‖ :=
          mul_le_mul_of_nonneg_right (by rw [hL']; linarith only [le_abs_self L])
            (norm_nonneg _)
      _ ≤ L' * (ε / (2 * L')) := mul_le_mul_of_nonneg_left hd1.le hL'pos.le
      _ = ε / 2 := by field_simp
  calc ‖F w - F z‖ = ‖(F (w.1, w.2) - F (z.1, w.2)) + (F (z.1, w.2) - F (z.1, z.2))‖ := by
        congr 1; abel
    _ ≤ ‖F (w.1, w.2) - F (z.1, w.2)‖ + ‖F (z.1, w.2) - F (z.1, z.2)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans hL) h2
    _ = ε := add_halves ε

/-- The lifted drift and divergence are continuous in time at a fixed lifted point, on a set of
times at which the zoomed point stays in the cylinder. -/
theorem continuousOn_time_zoomDrift_finDriftDiv {lam h zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (x : Vec 5)
    (J : Set ℝ) (hJ : ∀ τ ∈ J, zoomPoint lam h zc (zoomLiftPoint (x, τ)) ∈ unitCylinder) :
    ContinuousOn (fun τ => zoomDrift lam h zc u (x, τ)) J ∧
      ContinuousOn (fun τ => finDriftDiv lam h zc u (x, τ)) J := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hPc : Continuous (Y := Vec3 × ℝ)
      (fun τ : ℝ => zoomPoint lam h zc (zoomLiftPoint (x, τ))) :=
    (continuous_zoomPoint_zoomLiftPoint lam h zc).comp (Continuous.prodMk_right x)
  have hcomp : ∀ i : Fin 3, ContinuousOn (fun τ => u (zoomPoint lam h zc (zoomLiftPoint (x, τ))) i)
      J := fun i => (contDiffOn_component hu i).continuousOn.comp hPc.continuousOn hJ
  have hV : ContinuousOn (fun τ => zoomV lam h zc u (zoomLiftPoint (x, τ))) J :=
    continuousOn_const.mul (hcomp 0)
  have hW : ContinuousOn (fun τ => zoomW lam h zc u (zoomLiftPoint (x, τ))) J :=
    continuousOn_const.mul (hcomp 2)
  refine ⟨continuousOn_pi.2 fun i => ?_, ?_⟩
  · by_cases hi : i = 4
    · subst hi; exact hW.congr fun τ _ => by simp [zoomDrift]
    · exact (hV.mul (continuousOn_const (c := x i / zoomLiftRadius x))).congr fun τ _ => by simp
      [zoomDrift, hi]
  · by_cases h0 : zoomLiftRadius x = 0
    · have hp : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial (fun w => u w 0) 0 z)
          unitCylinder :=
        contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component (hu.of_le (by simp)) 0) 0
      have hdr : ContinuousOn (fun τ => spatialPartial (fun w => u w 0) 0
          (zoomPoint lam h zc (zoomLiftPoint (x, τ)))) J :=
        hp.continuousOn.comp hPc.continuousOn hJ
      have hmain : ContinuousOn (fun τ => 2 * (lam ^ 2 * spatialPartial (fun w => u w 0) 0
          (zoomPoint lam h zc (zoomLiftPoint (x, τ))))) J :=
        continuousOn_const.mul (continuousOn_const.mul hdr)
      refine hmain.congr fun τ hτ => ?_
      simp only [finDriftDiv, h0, ↓reduceIte]
      rw [dr_zoomV lam h zc u hu1 _ (hJ τ hτ)]
    · exact (((continuousOn_const (c := (2 : ℝ))).mul hV).div
        (continuousOn_const (c := zoomLiftRadius x)) fun _ _ => h0).congr fun τ _ => by
        simp [finDriftDiv, h0]

/-- For every radius and compact set of times in `(-∞, -1]`, eventually the zoom maps the
rectangle `[0, 2r] × [-r, r]` into the cylinder at every such time. -/
theorem eventually_forall_rect_zoomPoint_mem {h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) (r : ℝ) (J : Set ℝ) (hJ : IsCompact J)
    (hJt : ∀ τ ∈ J, τ ≤ -1) :
    ∀ᶠ n in atTop, (0 < lam n ∧ lam n < 1 ∧ lam n ^ (2 * h) ≤ 1) ∧
      ∀ τ ∈ J, ∀ y ∈ Icc 0 (2 * r) ×ˢ Icc (-r) r, zoomPoint (lam n) h (zc n) (y, τ) ∈
        unitCylinder := by
  have hK : IsCompact ((Icc 0 (2 * r) ×ˢ Icc (-r) r) ×ˢ J) :=
    (isCompact_Icc.prod isCompact_Icc).prod hJ
  filter_upwards [eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim,
    eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim _ hK
      (fun p hp => by have := hJt p.2 hp.2; linarith only [this])] with n hl hn
  exact ⟨hl, fun τ hτ y hy => hn (y, τ) ⟨hy, hτ⟩⟩

/-- The uniform bounds and Lipschitz bounds of the lifted drift and divergence on every ball. -/
theorem finDrift_uniform_lipschitz {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1) → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ closedBall (0 : Vec 5) r, ∀ y ∈ closedBall (0 : Vec 5) r,
        ‖zoomDrift (lam n) h (zc n) u (x, τ)‖ ≤ Λ ∧
        |finDriftDiv (lam n) h (zc n) u (x, τ)| ≤ Λ ∧
        ‖zoomDrift (lam n) h (zc n) u (x, τ) - zoomDrift (lam n) h (zc n) u (y, τ)‖
          ≤ Λ * ‖x - y‖ ∧
        |finDriftDiv (lam n) h (zc n) u (x, τ) - finDriftDiv (lam n) h (zc n) u (y, τ)|
          ≤ Λ * ‖x - y‖ := by
  intro J hJ hJs
  refine ⟨12 * C, fun r => ?_⟩
  filter_upwards [eventually_forall_rect_zoomPoint_mem hh hρ0 hρ1 hzc hlam_lim r J hJ
    (fun τ hτ => hJs hτ)] with n hn τ hτ x hx y hy
  obtain ⟨hl, hmem⟩ := hn
  have hτ1 : τ ≤ -1 := hJs hτ
  have hmemτ := hmem τ hτ
  have hpx : zoomPoint (lam n) h (zc n) (zoomLiftPoint (x, τ)) ∈ unitCylinder :=
    hmemτ _ (zoomLiftPoint_fst_mem hx)
  obtain ⟨hB, hD⟩ := zoomDrift_finDriftDiv_bound hl.1 hb hu haxi hC hh.1.le hτ1 hpx
  have hn0 := norm_nonneg (x - y)
  refine ⟨by linarith only [hB, hC], by linarith only [hD, hC], ?_, ?_⟩
  · have := norm_zoomDrift_sub_le hl.1 hb hu haxi hC hh.1.le hh.2.le hτ1 hmemτ hx hy
    nlinarith only [this, hC, hn0]
  · exact abs_finDriftDiv_sub_le hl.1 hb hu haxi hC hh.2.le hτ1 hmemτ hx hy

/-- The lifted drift and divergence are eventually continuous on every compact subset of
`ℝ⁵ × (-∞, -1]`. -/
theorem finDrift_eventually_continuousOn {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    {lam : ℕ → ℝ} (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ K : Set (Vec 5 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic (-1) →
      ∀ᶠ n in atTop, ContinuousOn (zoomDrift (lam n) h (zc n) u) K ∧
        ContinuousOn (finDriftDiv (lam n) h (zc n) u) K := by
  intro K hK hKs
  set J : Set ℝ := Prod.snd '' K with hJdef
  have hJ : IsCompact J := hK.image continuous_snd
  have hJt : ∀ τ ∈ J, τ ≤ -1 := by rintro _ ⟨z, hz, rfl⟩; exact (hKs hz).2
  obtain ⟨r, hr⟩ := (hK.image continuous_fst).isBounded.subset_closedBall (0 : Vec 5)
  have hKsub : K ⊆ closedBall (0 : Vec 5) r ×ˢ J := fun z hz =>
    ⟨hr (mem_image_of_mem _ hz), mem_image_of_mem _ hz⟩
  filter_upwards [eventually_forall_rect_zoomPoint_mem hh hρ0 hρ1 hzc hlam_lim r J hJ hJt]
    with n hn
  obtain ⟨hl, hmem⟩ := hn
  have hpt : ∀ x ∈ closedBall (0 : Vec 5) r, ∀ τ ∈ J,
      zoomPoint (lam n) h (zc n) (zoomLiftPoint (x, τ)) ∈ unitCylinder :=
    fun x hx τ hτ => hmem τ hτ _ (zoomLiftPoint_fst_mem hx)
  refine ⟨?_, ?_⟩
  · refine (continuousOn_prod_of_lipschitz_of_continuousOn _ _ _ (7 * C) (fun τ hτ x hx y hy =>
      norm_zoomDrift_sub_le hl.1 hb hu haxi hC hh.1.le hh.2.le (hJt τ hτ) (hmem τ hτ) hx hy)
      (fun x hx => (continuousOn_time_zoomDrift_finDriftDiv hu x J (hpt x hx)).1)).mono hKsub
  · refine (continuousOn_prod_of_lipschitz_of_continuousOn _ _ _ (12 * C)
      (fun τ hτ x hx y hy => by
        rw [Real.norm_eq_abs]
        exact abs_finDriftDiv_sub_le hl.1 hb hu haxi hC hh.2.le (hJt τ hτ) (hmem τ hτ) hx hy)
      (fun x hx => (continuousOn_time_zoomDrift_finDriftDiv hu x J (hpt x hx)).2)).mono hKsub

/-- `x + t e_i` is `x` with its `i`-th coordinate moved by `t`. -/
theorem add_smul_basisVec_eq_update (x : Vec 5) (i : Fin 5) (t : ℝ) :
    x + t • (basisVec i : Vec 5) = Function.update x i (x i + t) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [basisVec]
  · simp [basisVec, hj]

/-- The line derivative of a function bounded by the Lipschitz constant times `‖v‖`. -/
theorem norm_lineDeriv_le_of_lipschitzWith {g : Vec 5 → ℝ} {Λ : ℝ≥0} (hg : LipschitzWith Λ g)
    (x v : Vec 5) : ‖lineDeriv ℝ g x v‖ ≤ Λ * ‖v‖ := by
  have hl : LipschitzWith (Λ * ‖v‖₊) (fun t : ℝ => g (x + t • v)) := by
    refine LipschitzWith.of_dist_le_mul fun t s => ?_
    have := hg.dist_le_mul (x + t • v) (x + s • v)
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul,
      norm_smul, Real.norm_eq_abs] at this
    rw [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm]
    calc |g (x + t • v) - g (x + s • v)| ≤ Λ * (|t - s| * ‖v‖) := by
          rwa [Real.norm_eq_abs] at this
      _ = Λ * ‖v‖ * |t - s| := by ring
  have := norm_deriv_le_of_lipschitz (x₀ := (0 : ℝ)) hl
  simpa [lineDeriv, NNReal.coe_mul] using this

/-- On one time slice, `div B_n = 2 V_n / R` is the weak divergence of the lifted drift. The drift
is Lipschitz across the axis (`norm_zoomDrift_sub_le`), so Rademacher's integration by parts
applies to (a Lipschitz extension of) each component, and its classical divergence off the null
axis is `2 V_n / R` (`zoomDriftDivergence_eq`). -/
theorem integral_finDriftDiv_mul_eq {C h lam zc r tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (hb : AnisotropicBounds C h u)
    (haxi : IsAxisymmetricOn u unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc 0 (2 * r) ×ˢ Icc (-r) r, zoomPoint lam h zc (y, tau) ∈ unitCylinder)
    (ψ : Vec 5 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψr : tsupport ψ ⊆ ball (0 : Vec 5) r) :
    ∫ x, finDriftDiv lam h zc u (x, tau) * ψ x
      = -∫ x, ∑ i, zoomDrift lam h zc u (x, tau) i * fderiv ℝ ψ x (basisVec i) := by
  have hu := hsol.1
  set A : Set (Vec 5) := closedBall (0 : Vec 5) r with hA
  set Λ : ℝ≥0 := Real.toNNReal (7 * C) with hΛ
  have hfi : ∀ i : Fin 5, LipschitzOnWith Λ (fun x => zoomDrift lam h zc u (x, tau) i) A := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 := norm_zoomDrift_sub_le hlam hb hu haxi hC hh0 hh1 htau hmem hx hy
    have h2 := norm_le_pi_norm (zoomDrift lam h zc u (x, tau) - zoomDrift lam h zc u (y, tau)) i
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h2
    exact h2.trans h1
  choose g hg hgeq using fun i => (hfi i).extend_real
  obtain ⟨Cψ, hψL⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
  -- the derivative of `ψ` vanishes off its support
  have hfd0 : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x = 0 := fun x hx =>
    Function.notMem_support.mp fun h' => hx (support_fderiv_subset ℝ h')
  have hAψ : ∀ x, x ∉ A → x ∉ tsupport ψ := fun x hx hx' =>
    hx (ball_subset_closedBall (hψr hx'))
  -- Rademacher's integration by parts, component by component
  have hR : ∀ i : Fin 5, ∫ x, lineDeriv ℝ (g i) x (basisVec i) * ψ x
      = -∫ x, zoomDrift lam h zc u (x, tau) i * fderiv ℝ ψ x (basisVec i) := by
    intro i
    rw [(hg i).integral_lineDeriv_mul_eq hψL hψc, ← integral_neg]
    congr 1
    funext x
    rw [(hψd x).lineDeriv_eq_fderiv, map_neg, neg_mul]
    congr 1
    by_cases hx : x ∈ A
    · rw [← hgeq i hx, mul_comm]
    · rw [hfd0 x (hAψ x hx)]; simp
  have hint1 : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      Integrable (fun x => lineDeriv ℝ (g i) x (basisVec i) * ψ x) := by
    intro i _
    refine hψi.bdd_mul (c := Λ * ‖(basisVec i : Vec 5)‖)
      (measurable_lineDeriv (hg i).continuous).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => norm_lineDeriv_le_of_lipschitzWith (hg i) x _
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      Integrable (fun x => zoomDrift lam h zc u (x, tau) i * fderiv ℝ ψ x (basisVec i)) := by
    intro i _
    have hc : Continuous (fun x => g i x * fderiv ℝ ψ x (basisVec i)) :=
      (hg i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hs : HasCompactSupport (fun x => g i x * fderiv ℝ ψ x (basisVec i)) :=
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).mul_left
    refine (hc.integrable_of_hasCompactSupport hs).congr (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ A
    · simp only; rw [← hgeq i hx]
    · simp only; rw [hfd0 x (hAψ x hx)]; simp
  -- the classical divergence off the axis
  have hpt : ∀ x ∈ ball (0 : Vec 5) r, 0 < zoomLiftRadius x →
      ∑ i, lineDeriv ℝ (g i) x (basisVec i) = finDriftDiv lam h zc u (x, tau) := by
    intro x hx hR0
    have hxA : x ∈ A := ball_subset_closedBall hx
    have hpx : zoomPoint lam h zc (zoomLiftPoint (x, tau)) ∈ unitCylinder :=
      hmem _ (zoomLiftPoint_fst_mem hxA)
    have hslice : ∀ i : Fin 5, lineDeriv ℝ (g i) x (basisVec i)
        = deriv (fun s : ℝ => zoomDrift lam h zc u (Function.update x i s, tau) i) (x i) := by
      intro i
      have hev : (fun t : ℝ => g i (x + t • (basisVec i : Vec 5))) =ᶠ[𝓝 0]
          (fun t : ℝ => zoomDrift lam h zc u (Function.update x i (x i + t), tau) i) := by
        have hcont : Continuous fun t : ℝ => x + t • (basisVec i : Vec 5) := by fun_prop
        have hmemb : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • (basisVec i : Vec 5) ∈ ball (0 : Vec 5) r :=
          hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hx)
        filter_upwards [hmemb] with t ht
        rw [← hgeq i (ball_subset_closedBall ht), add_smul_basisVec_eq_update]
      rw [lineDeriv, hev.deriv_eq]
      have := deriv_comp_const_add (f := fun s : ℝ =>
        zoomDrift lam h zc u (Function.update x i s, tau) i) (a := x i) (x := (0 : ℝ))
      simpa using this
    have hdiv := zoomDriftDivergence_eq lam h zc hlam u pr f hsol haxi (q := (x, tau)) hpx hR0
    simp only [zoomDriftDivergence] at hdiv
    rw [Finset.sum_congr rfl (fun i _ => hslice i), hdiv]
    simp only [finDriftDiv, hR0.ne', ↓reduceIte]
    ring
  have hae : ∀ᵐ x ∂(volume : Measure (Vec 5)),
      finDriftDiv lam h zc u (x, tau) * ψ x = ∑ i, lineDeriv ℝ (g i) x (basisVec i) * ψ x := by
    filter_upwards [ae_zoomLiftRadius_pos_vec] with x hx
    rw [← Finset.sum_mul]
    by_cases hxb : x ∈ ball (0 : Vec 5) r
    · rw [hpt x hxb hx]
    · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hxb (hψr h')
      simp [this]
  rw [integral_congr_ae hae, integral_finsetSum _ hint1, integral_finsetSum _ hint2,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hR i

/-- `F2-H`: the three hypotheses of the drift extraction for the lifted finite-axis drift at the
moving axis points: eventual continuity on compacts, uniform bounds and Lipschitz bounds on every
ball, and the slice weak divergence. -/
theorem finDrift_extraction_hypotheses {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hC : 0 ≤ C) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    (∀ K : Set (Vec 5 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic (-1) →
      ∀ᶠ n in atTop, ContinuousOn (zoomDrift (lam n) h (zc n) u) K ∧
        ContinuousOn (finDriftDiv (lam n) h (zc n) u) K) ∧
    (∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1) → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ closedBall (0 : Vec 5) r, ∀ y ∈ closedBall (0 : Vec 5) r,
        ‖zoomDrift (lam n) h (zc n) u (x, τ)‖ ≤ Λ ∧
        |finDriftDiv (lam n) h (zc n) u (x, τ)| ≤ Λ ∧
        ‖zoomDrift (lam n) h (zc n) u (x, τ) - zoomDrift (lam n) h (zc n) u (y, τ)‖
          ≤ Λ * ‖x - y‖ ∧
        |finDriftDiv (lam n) h (zc n) u (x, τ) - finDriftDiv (lam n) h (zc n) u (y, τ)|
          ≤ Λ * ‖x - y‖) ∧
    (∀ ψ : Vec 5 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1) → ∀ᶠ n in atTop, ∀ τ ∈ J,
        ∫ x, finDriftDiv (lam n) h (zc n) u (x, τ) * ψ x =
          -∫ x, ∑ i, zoomDrift (lam n) h (zc n) u (x, τ) i * fderiv ℝ ψ x (basisVec i)) := by
  refine ⟨finDrift_eventually_continuousOn hh hρ0 hρ1 hC hb hsol.1 haxi hzc hlam_lim,
    finDrift_uniform_lipschitz hh hρ0 hρ1 hC hb hsol.1 haxi hzc hlam_lim, ?_⟩
  intro ψ hψ hψc J hJ hJs
  obtain ⟨r0, hr0⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Vec 5)
  have hψr : tsupport ψ ⊆ ball (0 : Vec 5) (r0 + 1) := fun x hx =>
    closedBall_subset_ball (by linarith only) (hr0 hx)
  filter_upwards [eventually_forall_rect_zoomPoint_mem hh hρ0 hρ1 hzc hlam_lim (r0 + 1) J hJ
    (fun τ hτ => hJs hτ)] with n hn τ hτ
  exact integral_finDriftDiv_mul_eq hn.1.1 hsol hb haxi hC hh.1.le hh.2.le (hJs hτ)
    (hn.2 τ hτ) ψ hψ hψc hψr

end CIV
