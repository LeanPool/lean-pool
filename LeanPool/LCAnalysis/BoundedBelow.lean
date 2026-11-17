/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike

public import LeanPool.LCAnalysis.MBFrechet
public import LeanPool.LCAnalysis.Higher

/-!
# Maps with bounded below derivative reflect smoothness

Let `j : E → F` be a smooth map from a Banach space `E` (complete) to a normed space `F`
(complete or not) whose derivative is bounded below on an
open set `U`: `m ‖v‖ ≤ ‖dj(x) v‖` for `x ∈ U`. No complement of the range of `dj(x)` is
assumed. Then `j` reflects smoothness of continuous maps: if `γ : W → U` is continuous on an open
subset `W` of a locally convex space and `j ∘ γ` is `C^k` in the sense of Michal–Bastiani, then so
is `γ` (`ContDiffMBOn.of_comp_of_boundedBelow`).

The proof bootstraps a linear version (`ContDiffMBOn.of_fderiv_eq_of_boundedBelow`): if
`dj(γ q)(z q) = w q` with `γ, w` of class `C^k` and `z` continuous, then `z` is `C^k`. The
derivative of `z` is obtained as a limit of difference quotients, which are Cauchy because
`dj(γ q)` is bounded below and `E` is complete.

**Subtleties.**

* The Michal–Bastiani definition gives joint continuity of `(x, v) ↦ dj(x) v`, not continuity
  of `x ↦ dj(x)` in the operator norm. The proof needs the latter, to keep the lower bound near a
  point. For normed spaces it follows from Michal–Bastiani `C^{k+1}` ⇒ Fréchet `C^k`
  (`ContDiffMBOn.contDiffOn`). For Fréchet or more general locally convex models the result is
  open.
* The test domain `W` may be any open subset of a locally convex space: only lines through its
  points are used to differentiate, and joint continuity comes from the lower bound.
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal ContDiff

noncomputable section

namespace LCAnalysis

universe u v w

/-! ### Normed preliminaries -/

section Normed

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `A` is bounded below and `A z_t → R`, then `z_t` converges to a solution of `A D = R`. -/
theorem exists_tendsto_of_boundedBelow [CompleteSpace E] {A : E →L[ℝ] F} {m : ℝ} (hm : 0 < m)
    (hA : ∀ v, m * ‖v‖ ≤ ‖A v‖) {ι : Type*} {l : Filter ι} [l.NeBot] {z : ι → E} {R : F}
    (h : Tendsto (fun i ↦ A (z i)) l (𝓝 R)) : ∃ D, Tendsto z l (𝓝 D) ∧ A D = R := by
  have hanti : AntilipschitzWith (Real.toNNReal m⁻¹) A := by
    refine A.antilipschitz_of_bound fun v ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hm.le)]
    calc ‖v‖ = m⁻¹ * (m * ‖v‖) := by field_simp
      _ ≤ m⁻¹ * ‖A v‖ := by gcongr; exact hA v
  have hui := hanti.isUniformInducing A.uniformContinuous
  have hc : Cauchy (map z l) := by
    rw [← hui.cauchy_map_iff, map_map]
    exact h.cauchy_map
  obtain ⟨D, hD⟩ := CompleteSpace.complete hc
  refine ⟨D, hD, ?_⟩
  exact tendsto_nhds_unique ((A.continuous.tendsto D).comp hD) h

/-- Solutions of `A(q) z(q) = r(q)` are continuous when `A` is continuous in the operator norm
and uniformly bounded below, and `r` is continuous. -/
theorem continuousOn_of_boundedBelow {X : Type*} [TopologicalSpace X] {W : Set X}
    {A : X → E →L[ℝ] F} (hA : ContinuousOn A W) {m : ℝ} (hm : 0 < m)
    (hbd : ∀ q ∈ W, ∀ v, m * ‖v‖ ≤ ‖A q v‖) {z : X → E} {r : X → F} (hr : ContinuousOn r W)
    (heq : ∀ q ∈ W, A q (z q) = r q) : ContinuousOn z W := by
  intro q hq
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  -- `‖z q' - z q‖ ≤ m⁻¹ ‖(r q' - r q) - (A q' - A q)(z q)‖`
  have hlim : Tendsto (fun q' ↦ m⁻¹ * ‖(r q' - r q) - (A q' - A q) (z q)‖) (𝓝[W] q) (𝓝 0) := by
    have h1 : Tendsto (fun q' ↦ (r q' - r q) - (A q' - A q) (z q)) (𝓝[W] q) (𝓝 0) := by
      have hr' : Tendsto (fun q' ↦ r q' - r q) (𝓝[W] q) (𝓝 0) := by
        simpa using (hr q hq).sub_const (r q)
      have h0 : Tendsto (fun q' ↦ A q' - A q) (𝓝[W] q) (𝓝 0) := by
        simpa using (hA q hq).sub_const (A q)
      have hA' : Tendsto (fun q' ↦ (A q' - A q) (z q)) (𝓝[W] q) (𝓝 0) := by
        have := ((ContinuousLinearMap.apply ℝ F (z q)).continuous.tendsto 0).comp h0
        simp only [map_zero] at this
        exact this
      simpa using hr'.sub hA'
    simpa using (h1.norm.const_mul m⁻¹)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with q' hq'
  have h := hbd q' hq' (z q' - z q)
  have e : A q' (z q' - z q) = (r q' - r q) - (A q' - A q) (z q) := by
    rw [map_sub, heq q' hq', sub_apply, heq q hq]
    abel
  rw [e] at h
  calc ‖z q' - z q‖ = m⁻¹ * (m * ‖z q' - z q‖) := by field_simp
    _ ≤ m⁻¹ * ‖(r q' - r q) - (A q' - A q) (z q)‖ := by gcongr

/-- A continuous linear map between normed spaces which is a topological embedding is bounded
below. -/
theorem exists_boundedBelow_of_isEmbedding {L : E →L[ℝ] F} (hL : Topology.IsEmbedding L) :
    ∃ m > 0, ∀ v, m * ‖v‖ ≤ ‖L v‖ := by
  have hball : Metric.ball (0 : E) 1 ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds 0 one_pos
  rw [hL.isInducing.nhds_eq_comap, map_zero] at hball
  obtain ⟨t, ht, hts⟩ := hball
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
  have key : ∀ v, ‖L v‖ < δ → ‖v‖ < 1 := fun v hv ↦ by
    have := hts (hδt (by simpa using hv))
    simpa using this
  refine ⟨δ / 2, by positivity, fun v ↦ ?_⟩
  by_cases hv : L v = 0
  · have : v = 0 := hL.injective (by rw [hv, map_zero])
    simp [this]
  · have hLv : 0 < ‖L v‖ := norm_pos_iff.mpr hv
    set c := δ / (2 * ‖L v‖) with hcdef
    have hc : 0 < c := by positivity
    have h1 : ‖L (c • v)‖ < δ := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg hc.le]
      have : c * ‖L v‖ = δ / 2 := by rw [hcdef]; field_simp
      linarith
    have h2 := key _ h1
    rw [norm_smul, Real.norm_of_nonneg hc.le] at h2
    have : δ / 2 * ‖v‖ = c * ‖v‖ * ‖L v‖ := by rw [hcdef]; field_simp
    rw [this]
    nlinarith [norm_nonneg v]

/-- The lower bound of the derivative propagates to a neighborhood. -/
theorem exists_nhds_boundedBelow {j : E → F} {U : Set E} (hU : IsOpen U)
    (hj : ContinuousOn (fderiv ℝ j) U) {x₀ : E} (hx₀ : x₀ ∈ U) {m : ℝ} (hm : 0 < m)
    (hbd : ∀ v, m * ‖v‖ ≤ ‖fderiv ℝ j x₀ v‖) :
    ∃ V ⊆ U, IsOpen V ∧ Convex ℝ V ∧ x₀ ∈ V ∧ ∀ x ∈ V, ∀ v, m / 2 * ‖v‖ ≤ ‖fderiv ℝ j x v‖ := by
  have hc := hj.continuousAt (hU.mem_nhds hx₀)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hc (Metric.ball_mem_nhds (fderiv ℝ j x₀) (half_pos hm)))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  refine ⟨Metric.ball x₀ (min δ ε), (Metric.ball_subset_ball (min_le_right _ _)).trans hεU,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self (lt_min hδ hε), fun x hx v ↦ ?_⟩
  have hx' : fderiv ℝ j x ∈ Metric.ball (fderiv ℝ j x₀) (m / 2) :=
    hball (Metric.ball_subset_ball (min_le_left _ _) hx)
  rw [Metric.mem_ball, dist_eq_norm] at hx'
  have h1 : ‖(fderiv ℝ j x - fderiv ℝ j x₀) v‖ ≤ m / 2 * ‖v‖ :=
    ((fderiv ℝ j x - fderiv ℝ j x₀).le_opNorm v).trans (by gcongr)
  have h2 : ‖fderiv ℝ j x₀ v‖ ≤ ‖fderiv ℝ j x v‖ + ‖(fderiv ℝ j x - fderiv ℝ j x₀) v‖ := by
    calc ‖fderiv ℝ j x₀ v‖ = ‖fderiv ℝ j x v - (fderiv ℝ j x - fderiv ℝ j x₀) v‖ := by
          rw [sub_apply, sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  linarith [hbd v]

end Normed

/-! ### Bootstrapping -/

section Bootstrap

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : E → F} {U : Set E}

omit [CompleteSpace E] in
/-- A directional derivative into a normed space is the derivative of the line. -/
theorem hasDerivAt_line_of_hasDirDerivAt {H : Type u} [AddCommGroup H] [Module ℝ H]
     {γ : H → E} {q h : H} {y : E} (hγ : HasDirDerivAt γ q h y) :
    HasDerivAt (fun t : ℝ ↦ γ (q + t • h)) y 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine (show Tendsto (fun t : ℝ ↦ t⁻¹ • (γ (q + t • h) - γ q)) (𝓝[≠] 0) (𝓝 y) from hγ).congr
    fun t ↦ ?_
  simp [slope_def_module]

omit [CompleteSpace E] in
/-- The Fréchet derivatives of a Michal–Bastiani smooth map. -/
theorem SmoothMBOn.fderiv_facts (hU : IsOpen U) (hj : SmoothMBOn j U) :
    ContDiffOn ℝ ∞ j U ∧ ContDiffOn ℝ ∞ (fderiv ℝ j) U ∧
      SmoothMBOn (fun p : E × (E × E) ↦ fderiv ℝ (fderiv ℝ j) p.1 p.2.1 p.2.2) (U ×ˢ univ) := by
  have hjF : ContDiffOn ℝ ∞ j U := (smoothMBOn_iff_contDiffOn hU).mp hj
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ j) U := hjF.fderiv_of_isOpen hU (by simp)
  have hD2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ j)) U := hD1.fderiv_of_isOpen hU (by simp)
  refine ⟨hjF, hD1, ?_⟩
  rw [smoothMBOn_iff_contDiffOn (hU.prod isOpen_univ)]
  have h1 : ContDiffOn ℝ ∞ (fun p : E × (E × E) ↦ fderiv ℝ (fderiv ℝ j) p.1) (U ×ˢ univ) :=
    hD2.comp contDiff_fst.contDiffOn fun p hp ↦ hp.1
  exact (h1.clm_apply (contDiff_fst.comp contDiff_snd).contDiffOn).clm_apply
    (contDiff_snd.comp contDiff_snd).contDiffOn

/-- **Linear bootstrap.** If `dj` is bounded below on `U` and `dj(γ q)(z q) = w q` on `W`, with
`γ` and `w` of class `C^k` and `z` continuous, then `z` is of class `C^k`. -/
theorem ContDiffMBOn.of_fderiv_eq_of_boundedBelow (hU : IsOpen U) (hj : SmoothMBOn j U)
    {m : ℝ} (hm : 0 < m) (hbd : ∀ x ∈ U, ∀ v, m * ‖v‖ ≤ ‖fderiv ℝ j x v‖) :
    ∀ (k : ℕ) {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
      [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
      {W : Set H} {γ z : H → E} {w : H → F}, IsOpen W → ContDiffMBOn k γ W → MapsTo γ W U →
      ContinuousOn z W → ContDiffMBOn k w W → (∀ q ∈ W, fderiv ℝ j (γ q) (z q) = w q) →
      ContDiffMBOn k z W := by
  obtain ⟨-, hD1, hG⟩ := hj.fderiv_facts hU
  have hcont : ContinuousOn (fderiv ℝ j) U := hD1.continuousOn
  have hdiff : ∀ x ∈ U, HasFDerivAt (fderiv ℝ j) (fderiv ℝ (fderiv ℝ j) x) x := fun x hx ↦
    ((hD1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  intro k
  induction k with
  | zero =>
    intro H _ _ _ _ _ _ _ W γ z w hW hγ hγU hz hw heq
    exact hz
  | succ k ih =>
    intro H _ _ _ _ _ _ _ W γ z w hW hγ hγU hz hw heq
    have hzk : ContDiffMBOn k z W := ih hW hγ.of_succ hγU hz hw.of_succ heq
    have hγ1 : ContDiffMBOn 1 γ W := hγ.of_le (by omega)
    have hw1 : ContDiffMBOn 1 w W := hw.of_le (by omega)
    -- the derivative of `z`, as a limit of difference quotients
    have hder : ∀ q ∈ W, ∀ h : H, ∃ D : E, HasDirDerivAt z q h D ∧
        fderiv ℝ j (γ q) D =
          dMB w (q, h) - fderiv ℝ (fderiv ℝ j) (γ q) (dMB γ (q, h)) (z q) := by
      intro q hq h
      have hγq := hγU hq
      have hline : Tendsto (fun t : ℝ ↦ q + t • h) (𝓝[≠] 0) (𝓝 q) := by
        have : Continuous fun t : ℝ ↦ q + t • h := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), q + t • h ∈ W := hline (hW.mem_nhds hq)
      have hcurve := hasDerivAt_line_of_hasDirDerivAt (hγ1.hasDirDerivAt hq h)
      have hAline : HasDerivAt (fun t : ℝ ↦ fderiv ℝ j (γ (q + t • h)))
          (fderiv ℝ (fderiv ℝ j) (γ q) (dMB γ (q, h))) 0 := by
        have h1 : HasFDerivAt (fderiv ℝ j) (fderiv ℝ (fderiv ℝ j) (γ q))
            (γ (q + (0 : ℝ) • h)) := by simpa using hdiff _ hγq
        simpa [Function.comp_def] using h1.comp_hasDerivAt (0 : ℝ) hcurve
      have hAslope : Tendsto (fun t : ℝ ↦ t⁻¹ • (fderiv ℝ j (γ (q + t • h)) - fderiv ℝ j (γ q)))
          (𝓝[≠] 0) (𝓝 (fderiv ℝ (fderiv ℝ j) (γ q) (dMB γ (q, h)))) := by
        simpa using hAline.tendsto_slope_zero
      have hzline : Tendsto (fun t : ℝ ↦ z (q + t • h)) (𝓝[≠] 0) (𝓝 (z q)) :=
        ((hz.continuousAt (hW.mem_nhds hq)).tendsto).comp hline
      have hwline : Tendsto (fun t : ℝ ↦ t⁻¹ • (w (q + t • h) - w q)) (𝓝[≠] 0)
          (𝓝 (dMB w (q, h))) := hw1.hasDirDerivAt hq h
      have hprod : Tendsto (fun t : ℝ ↦
          (t⁻¹ • (fderiv ℝ j (γ (q + t • h)) - fderiv ℝ j (γ q))) (z (q + t • h))) (𝓝[≠] 0)
          (𝓝 (fderiv ℝ (fderiv ℝ j) (γ q) (dMB γ (q, h)) (z q))) :=
        (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hAslope.prodMk_nhds hzline)
      have hkey : Tendsto (fun t : ℝ ↦ fderiv ℝ j (γ q) (t⁻¹ • (z (q + t • h) - z q))) (𝓝[≠] 0)
          (𝓝 (dMB w (q, h) - fderiv ℝ (fderiv ℝ j) (γ q) (dMB γ (q, h)) (z q))) := by
        refine (hwline.sub hprod).congr' ?_
        filter_upwards [hev] with t ht
        simp only [map_smul, map_sub, smul_apply, sub_apply]
        rw [← heq _ ht, ← heq q hq, ← smul_sub]
        congr 1
        abel
      obtain ⟨D, hD, hAD⟩ := exists_tendsto_of_boundedBelow hm (hbd _ hγq) hkey
      exact ⟨D, hD, hAD⟩
    have hdz : ∀ p ∈ W ×ˢ (univ : Set H), fderiv ℝ j (γ p.1) (dMB z p) =
        dMB w p - fderiv ℝ (fderiv ℝ j) (γ p.1) (dMB γ p) (z p.1) := by
      rintro ⟨q, h⟩ ⟨hq, -⟩
      obtain ⟨D, hD, hAD⟩ := hder q hq h
      rw [hD.dMB_eq]
      exact hAD
    -- the data of the induction step, on `W × H`
    have hW2 : IsOpen (W ×ˢ (univ : Set H)) := hW.prod isOpen_univ
    have hfst : ∀ (n : ℕ), ContDiffMBOn n (fun p : H × H ↦ p.1) (W ×ˢ univ) := fun n ↦
      (ContinuousLinearMap.fst ℝ H H).contDiffMBOn n _
    have hγfst : ContDiffMBOn k (fun p : H × H ↦ γ p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := γ) (f := fun p : H × H ↦ p.1) hW2 hW hγ.of_succ (hfst k)
        fun p hp ↦ hp.1
    have hzfst : ContDiffMBOn k (fun p : H × H ↦ z p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := z) (f := fun p : H × H ↦ p.1) hW2 hW hzk (hfst k) fun p hp ↦ hp.1
    have hdγ : ContDiffMBOn k (dMB γ) (W ×ˢ univ) := hγ.2.2
    have hdw : ContDiffMBOn k (dMB w) (W ×ˢ univ) := hw.2.2
    have htriple : ContDiffMBOn k (fun p : H × H ↦ (γ p.1, (dMB γ p, z p.1))) (W ×ˢ univ) :=
      ContDiffMBOn.prodMk hW2 hγfst (ContDiffMBOn.prodMk hW2 hdγ hzfst)
    have hGk : ContDiffMBOn k (fun p : H × H ↦
        fderiv ℝ (fderiv ℝ j) (γ p.1) (dMB γ p) (z p.1)) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := fun p : E × (E × E) ↦ fderiv ℝ (fderiv ℝ j) p.1 p.2.1 p.2.2)
        (f := fun p : H × H ↦ (γ p.1, (dMB γ p, z p.1))) hW2 (hU.prod isOpen_univ) (hG k)
        htriple fun p hp ↦ ⟨hγU hp.1, mem_univ _⟩
    have hw' : ContDiffMBOn k (fun p : H × H ↦
        dMB w p - fderiv ℝ (fderiv ℝ j) (γ p.1) (dMB γ p) (z p.1)) (W ×ˢ univ) :=
      ContDiffMBOn.comp (F₁ := F × F) hW2 isOpen_univ
        ((ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
        (ContDiffMBOn.prodMk hW2 hdw hGk) (mapsTo_univ _ _)
    have hAc : ContinuousOn (fun p : H × H ↦ fderiv ℝ j (γ p.1)) (W ×ˢ univ) :=
      hcont.comp hγfst.continuousOn fun p hp ↦ hγU hp.1
    have hdzc : ContinuousOn (dMB z) (W ×ˢ univ) :=
      continuousOn_of_boundedBelow hAc hm (fun p hp ↦ hbd _ (hγU hp.1)) hw'.continuousOn hdz
    have hdzk := ih hW2 hγfst (fun p hp ↦ hγU hp.1) hdzc hw' hdz
    refine ⟨hz, fun q hq h ↦ ?_, hdzk⟩
    obtain ⟨D, hD, -⟩ := hder q hq h
    rw [hD.dMB_eq]
    exact hD

/-- **Maps with bounded below derivative reflect smoothness.** If `dj` is bounded below on the
open set `U` and `γ : W → U` is continuous with `j ∘ γ` of class `C^k`, then `γ` is of class
`C^k`. -/
theorem ContDiffMBOn.of_comp_of_boundedBelow (hU : IsOpen U) (hj : SmoothMBOn j U)
    {m : ℝ} (hm : 0 < m) (hbd : ∀ x ∈ U, ∀ v, m * ‖v‖ ≤ ‖fderiv ℝ j x v‖) :
    ∀ (k : ℕ) {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
      [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
      {W : Set H} {γ : H → E}, IsOpen W → ContinuousOn γ W → MapsTo γ W U →
      ContDiffMBOn k (j ∘ γ) W → ContDiffMBOn k γ W := by
  obtain ⟨hjF, hD1, -⟩ := hj.fderiv_facts hU
  have hcont : ContinuousOn (fderiv ℝ j) U := hD1.continuousOn
  intro k
  induction k with
  | zero =>
    intro H _ _ _ _ _ _ _ W γ hW hγc hγU hjγ
    exact hγc
  | succ k ih =>
    intro H _ _ _ _ _ _ _ W γ hW hγc hγU hjγ
    have hγk : ContDiffMBOn k γ W := ih hW hγc hγU hjγ.of_succ
    have hjγ1 : ContDiffMBOn 1 (j ∘ γ) W := hjγ.of_le (by omega)
    -- the derivative of `γ`
    have hder : ∀ q ∈ W, ∀ h : H, ∃ D : E, HasDirDerivAt γ q h D ∧
        fderiv ℝ j (γ q) D = dMB (j ∘ γ) (q, h) := by
      intro q hq h
      have hγq := hγU hq
      set A := fderiv ℝ j (γ q)
      set R := dMB (j ∘ γ) (q, h)
      have hline : Tendsto (fun t : ℝ ↦ q + t • h) (𝓝[≠] 0) (𝓝 q) := by
        have : Continuous fun t : ℝ ↦ q + t • h := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have hγline : Tendsto (fun t : ℝ ↦ γ (q + t • h)) (𝓝[≠] 0) (𝓝 (γ q)) :=
        ((hγc.continuousAt (hW.mem_nhds hq)).tendsto).comp hline
      have hpair : Tendsto (fun t : ℝ ↦ (γ (q + t • h), γ q)) (𝓝[≠] 0) (𝓝 (γ q, γ q)) :=
        hγline.prodMk_nhds tendsto_const_nhds
      have ha : Tendsto (fun t : ℝ ↦ t⁻¹ • (j (γ (q + t • h)) - j (γ q))) (𝓝[≠] 0) (𝓝 R) :=
        hjγ1.hasDirDerivAt hq h
      have hS : HasStrictFDerivAt j A (γ q) :=
        (hjF.contDiffAt (hU.mem_nhds hγq)).hasStrictFDerivAt (by simp)
      have hlo := hasStrictFDerivAt_iff_isLittleO.mp hS
      -- `A (γ_t) - a_t → 0`, where `γ_t, a_t` are the difference quotients
      have hsmall : Tendsto (fun t : ℝ ↦ A (t⁻¹ • (γ (q + t • h) - γ q)) -
          t⁻¹ • (j (γ (q + t • h)) - j (γ q))) (𝓝[≠] 0) (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro η hη
        set c := min (m / 2) (η * m / (4 * (‖R‖ + 1))) with hcdef
        have hR1 : 0 < ‖R‖ + 1 := by positivity
        have hc : 0 < c := lt_min (by positivity) (by positivity)
        have hcm : c ≤ m / 2 := min_le_left _ _
        have hcη : c ≤ η * m / (4 * (‖R‖ + 1)) := min_le_right _ _
        have hb := hpair.eventually (hlo.bound hc)
        have hR : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖t⁻¹ • (j (γ (q + t • h)) - j (γ q))‖ < ‖R‖ + 1 :=
          ha.norm.eventually (gt_mem_nhds (lt_add_one _))
        filter_upwards [hb, hR] with t hbt hRt
        set d := γ (q + t • h) - γ q
        set a := t⁻¹ • (j (γ (q + t • h)) - j (γ q))
        -- `‖A (t⁻¹ d) - a‖ ≤ c ‖t⁻¹ d‖`
        have he : ‖A (t⁻¹ • d) - a‖ ≤ c * ‖t⁻¹ • d‖ := by
          have : A (t⁻¹ • d) - a = -(t⁻¹ • (j (γ (q + t • h)) - j (γ q) - A d)) := by
            simp only [map_smul, a, smul_sub]
            abel
          rw [this, norm_neg, norm_smul, norm_smul]
          calc ‖t⁻¹‖ * ‖j (γ (q + t • h)) - j (γ q) - A d‖ ≤ ‖t⁻¹‖ * (c * ‖d‖) := by
                gcongr
            _ = c * (‖t⁻¹‖ * ‖d‖) := by ring
        -- `‖t⁻¹ d‖ ≤ (2 / m) ‖a‖`
        have hz : ‖t⁻¹ • d‖ ≤ 2 / m * ‖a‖ := by
          have h1 := hbd _ hγq (t⁻¹ • d)
          have h2 : ‖A (t⁻¹ • d)‖ ≤ ‖a‖ + c * ‖t⁻¹ • d‖ := by
            calc ‖A (t⁻¹ • d)‖ = ‖(A (t⁻¹ • d) - a) + a‖ := by rw [sub_add_cancel]
              _ ≤ ‖A (t⁻¹ • d) - a‖ + ‖a‖ := norm_add_le _ _
              _ ≤ c * ‖t⁻¹ • d‖ + ‖a‖ := by gcongr
              _ = ‖a‖ + c * ‖t⁻¹ • d‖ := by ring
          rw [div_mul_eq_mul_div, le_div_iff₀ hm]
          nlinarith [norm_nonneg (t⁻¹ • d), norm_nonneg a]
        rw [dist_zero_right]
        calc ‖A (t⁻¹ • d) - a‖ ≤ c * ‖t⁻¹ • d‖ := he
          _ ≤ c * (2 / m * ‖a‖) := by gcongr
          _ ≤ (η * m / (4 * (‖R‖ + 1))) * (2 / m * (‖R‖ + 1)) := by gcongr
          _ = η / 2 := by field_simp; ring
          _ < η := by linarith
      have hkey : Tendsto (fun t : ℝ ↦ A (t⁻¹ • (γ (q + t • h) - γ q))) (𝓝[≠] 0) (𝓝 R) := by
        have := hsmall.add ha
        simpa using this
      obtain ⟨D, hD, hAD⟩ := exists_tendsto_of_boundedBelow hm (hbd _ hγq) hkey
      exact ⟨D, hD, hAD⟩
    -- the derivative satisfies a linear equation; bootstrap it
    have hdγ : ∀ p ∈ W ×ˢ (univ : Set H), fderiv ℝ j (γ p.1) (dMB γ p) = dMB (j ∘ γ) p := by
      rintro ⟨q, h⟩ ⟨hq, -⟩
      obtain ⟨D, hD, hAD⟩ := hder q hq h
      rw [hD.dMB_eq]
      exact hAD
    have hW2 : IsOpen (W ×ˢ (univ : Set H)) := hW.prod isOpen_univ
    have hγfst : ContDiffMBOn k (fun p : H × H ↦ γ p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := γ) (f := fun p : H × H ↦ p.1) hW2 hW hγk
        ((ContinuousLinearMap.fst ℝ H H).contDiffMBOn k _) fun p hp ↦ hp.1
    have hdjγ : ContDiffMBOn k (dMB (j ∘ γ)) (W ×ˢ univ) := hjγ.2.2
    have hAc : ContinuousOn (fun p : H × H ↦ fderiv ℝ j (γ p.1)) (W ×ˢ univ) :=
      hcont.comp hγfst.continuousOn fun p hp ↦ hγU hp.1
    have hdγc : ContinuousOn (dMB γ) (W ×ˢ univ) :=
      continuousOn_of_boundedBelow hAc hm (fun p hp ↦ hbd _ (hγU hp.1)) hdjγ.continuousOn hdγ
    have hdγk := ContDiffMBOn.of_fderiv_eq_of_boundedBelow hU hj hm hbd k hW2 hγfst
      (fun p hp ↦ hγU hp.1) hdγc hdjγ hdγ
    refine ⟨hγc, fun q hq h ↦ ?_, hdγk⟩
    obtain ⟨D, hD, -⟩ := hder q hq h
    rw [hD.dMB_eq]
    exact hD

end Bootstrap

end LCAnalysis
