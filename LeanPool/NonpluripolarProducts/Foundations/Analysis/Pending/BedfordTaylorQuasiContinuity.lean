/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorBlockiInequality

/-!
# Quasi-continuity of bounded plurisubharmonic functions

A locally bounded plurisubharmonic function `v` on an open set `Ω ⊆ ℂⁿ` is
*quasi-continuous* with respect to the relative Monge–Ampère capacity: for every
`ε > 0` there is an open set `G` with `c(G, Ω) < ε` such that `v` is continuous on
`Ω \ G` (Bedford–Taylor; Błocki, *The complex Monge–Ampère operator in
pluripotential theory*, lecture notes, Theorem 2.2.2).

**Convergence in capacity** (Błocki, Proposition 2.2.4). Near a point, let
`v_k ↓ v` be smooth decreasing approximations. After subtracting a constant and
taking the regularized maximum with a collar potential `A(|z - x₀|² - R²)`, all
of them agree with the collar near the boundary of the ball `B(x₀, 2R)` and are
unchanged on `B(x₀, R/2)`. For a competitor `-1 ≤ u ≤ 0`, Błocki's inequality
gives

  `(ddᶜu)ⁿ(B(x₀, R/2) ∩ {v_k > v + δ}) ≤ δ⁻⁽ⁿ⁺¹⁾ (n+1)! ∫_K (v_k - v) (ddᶜv)ⁿ`,

with a right side independent of `u` that tends to zero by dominated convergence.

**Quasi-continuity.** Choosing `k_m` with capacity of
`G_m = B(x₀, R/2) ∩ {v_{k_m} > v + 1/(m+1)}` at most `ε 2⁻ᵐ⁻²`, the functions
`v_{k_m}` converge uniformly to `v` off the open set `⋃ G_m`. A finite cover of a
compact set, and then an exhaustion of `Ω`, give the local and the global
statements.

No Dirichlet problem is used (Cegrell's route).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Nat

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

/-! ## Auxiliary facts -/

theorem IsDecApprox.aestronglyMeasurable_restrict {V : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V w G)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKV : K ⊆ V) (ρ : Measure (ComplexModel n))
    (j p : ℕ) : AEStronglyMeasurable (fun z ↦ (G j z - w z) ^ p) (ρ.restrict K) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun l z ↦ (G j z - G l z) ^ p)
    (fun l ↦ ((((hG.1 j).1.continuousOn.mono hKV).sub ((hG.1 l).1.continuousOn.mono hKV)).pow
      _).aestronglyMeasurable hK.measurableSet) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact (tendsto_const_nhds.sub (hG.2.2.1 z (hKV hz))).pow _

theorem IsDecApprox.integrableOn_pow_sub {V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V w G) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKV : K ⊆ V) {ρ : Measure (ComplexModel n)} (hρK : ρ K < ⊤) (j p : ℕ) :
    IntegrableOn (fun z ↦ (G j z - w z) ^ p) K ρ := by
  obtain ⟨C, hC⟩ := hG.exists_abs_le hK hKV
  have hw := fun z hz => hG.abs_le_of_mem hKV hC (z := z) hz
  have : IsFiniteMeasure (ρ.restrict K) := isFiniteMeasure_restrict.2 hρK.ne
  refine (integrable_const ((2 * C) ^ p)).mono' (hG.aestronglyMeasurable_restrict hK hKV ρ j p) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hC j z hz, hw z hz])) _

theorem IsDecApprox.tendsto_setIntegral_sub {V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V w G) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKV : K ⊆ V) {ρ : Measure (ComplexModel n)} (hρK : ρ K < ⊤) :
    Tendsto (fun j ↦ ∫ z in K, (G j z - w z) ∂ρ) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hG.exists_abs_le hK hKV
  have hw := fun z hz => hG.abs_le_of_mem hKV hC (z := z) hz
  have : IsFiniteMeasure (ρ.restrict K) := isFiniteMeasure_restrict.2 hρK.ne
  have h := tendsto_integral_of_dominated_convergence (μ := ρ.restrict K)
    (F := fun j z ↦ (G j z - w z) ^ 1) (f := fun _ ↦ 0) (fun _ ↦ 2 * C)
    (fun j ↦ hG.aestronglyMeasurable_restrict hK hKV ρ j 1) (integrable_const _)
    (fun j ↦ by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      rw [pow_one, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith [hC j z hz, hw z hz]))
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      simpa using (hG.2.2.1 z (hKV hz)).sub_const (w z))
  simpa using h

/-- For `v` plurisubharmonic and `g` continuous, the set where `v + δ < g` is open. -/
theorem isOpen_inter_setOf_add_lt {U S : Set (ComplexModel n)} (hU : IsOpen U) (hSU : S ⊆ U)
    (hS : IsOpen S) {v g : ComplexModel n → ℝ} (hv : PlurisubharmonicOn (fun z ↦ (v z : EReal)) U)
    (hg : ContinuousOn g U) (δ : ℝ) : IsOpen (S ∩ {z | v z + δ < g z}) := by
  refine isOpen_iff_mem_nhds.2 fun z ⟨hzS, hz⟩ ↦ ?_
  have hz' : v z + δ < g z := hz
  set η := (g z - v z - δ) / 2 with hη
  have h1 : ∀ᶠ y in 𝓝 z, (v y : EReal) < ((v z + η : ℝ) : EReal) :=
    (hv z (hSU hzS)).upperSemicontinuousAt _ (EReal.coe_lt_coe_iff.2 (by linarith))
  have h2 : ∀ᶠ y in 𝓝 z, g z - η < g y :=
    continuousAt_const.eventually_lt (hg.continuousAt (hU.mem_nhds (hSU hzS))) (by linarith)
  filter_upwards [hS.mem_nhds hzS, h1, h2] with y hyS hy1 hy2
  exact ⟨hyS, show v y + δ < g y by have := EReal.coe_lt_coe_iff.1 hy1; linarith⟩

theorem relCapacity_biUnion_finset_le {ι : Type*} (Ω : Opens (ComplexModel n)) (s : Finset ι)
    (E : ι → Set (ComplexModel n)) :
    relCapacity Ω (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, relCapacity Ω (E i) :=
  relCapacity_le_of_forall fun _ hu hb ↦ (measure_biUnion_finset_le s E).trans
    (Finset.sum_le_sum fun i _ ↦ canonicalBedfordTaylorMeasure_le_relCapacity hu hb (E i))

/-! ## Convergence in capacity -/

/-- **Convergence in capacity of decreasing smooth approximations** (Błocki,
Proposition 2.2.4), near a point. -/
theorem IsLocallyBoundedPshOn.exists_tendsto_relCapacity {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v) {x₀ : ComplexModel n} {R : ℝ}
    (hR : 0 < R) (hball : closedBall x₀ (3 * R) ⊆ Ω) :
    ∃ g : ℕ → ComplexModel n → ℝ, (∀ k, ContinuousOn (g k) (ball x₀ (3 * R))) ∧
      (∀ z ∈ ball x₀ (3 * R), Antitone fun k ↦ g k z) ∧
      (∀ z ∈ ball x₀ (3 * R), Tendsto (fun k ↦ g k z) atTop (𝓝 (v z))) ∧
      ∀ δ : ℝ, 0 < δ → Tendsto
        (fun k ↦ relCapacity Ω (ball x₀ (R / 2) ∩ {z | v z + δ < g k z})) atTop (𝓝 0) := by
  classical
  set U : Opens (ComplexModel n) := ⟨ball x₀ (3 * R), isOpen_ball⟩ with hU_def
  have hU : RelativelyCompactIn U Ω :=
    ⟨(isCompact_closedBall x₀ _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans hball⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  obtain ⟨g, hg⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hv hU
  have hG : IsDecApprox U v g := isDecApprox_of_isDecreasingApproximation hv hUΩ hg
  refine ⟨g, fun k ↦ (hG.1 k).1.continuousOn, hG.2.1, hG.2.2.1, fun δ hδ ↦ ?_⟩
  -- the collar modification on `V = B(x₀, 2R)`
  set V : Opens (ComplexModel n) := ⟨ball x₀ (2 * R), isOpen_ball⟩ with hV_def
  have hVU : V ≤ U := ball_subset_ball (by linarith)
  have hVΩ : V ≤ Ω := hVU.trans hUΩ
  set Kb := closedBall x₀ (2 * R)
  have hKbU : Kb ⊆ U := closedBall_subset_ball (by linarith)
  obtain ⟨MG, hMG⟩ := ((isCompact_closedBall x₀ (2 * R)).image_of_continuousOn
    ((hG.1 0).1.continuousOn.mono hKbU)).bddAbove
  obtain ⟨mw, hmw⟩ := hG.2.2.2 Kb (isCompact_closedBall _ _) hKbU
  set cG := MG + 2 with hcG
  set M := max (cG - mw) 0 with hM
  obtain ⟨A, ρ, hA, hρ1, hρ2, hin, hout⟩ := exists_collar_constants x₀ hR (le_max_right (cG - mw)
    0)
  set h := collar x₀ A R with hh_def
  have hhs : IsSmoothPsdOn V h := isSmoothPsdOn_collar V x₀ hA.le R
  set G' : ℕ → ComplexModel n → ℝ := fun k ↦ smoothMax (fun y ↦ g k y - cG) h with hG'_def
  set v' : ComplexModel n → ℝ := smoothMax (fun y ↦ v y - cG) h with hv'_def
  have hG' : IsDecApprox V v' G' := (hG.mono hVU).smoothMax_sub cG hhs
  set K := closedBall x₀ ρ with hK_def
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ V := closedBall_subset_ball (by linarith)
  have hVKb : ∀ z ∈ (V : Set (ComplexModel n)), z ∈ Kb := fun z hz ↦ ball_subset_closedBall hz
  have hgup (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      g k z - cG ≤ -2 := by
    have := hG.2.1 z (hVU hz) (Nat.zero_le k)
    have := hMG ⟨z, hVKb z hz, rfl⟩
    simp only [hcG]; linarith
  have hglow (k : ℕ) (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      -M ≤ g k z - cG := by
    have := hG.le_of_mem (hVU hz) k
    have := hmw ⟨z, hVKb z hz, rfl⟩
    have := le_max_left (cG - mw) 0
    linarith
  have hvlow (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) : -M ≤ v z - cG := by
    have := hmw ⟨z, hVKb z hz, rfl⟩
    have := le_max_left (cG - mw) 0
    linarith
  have hGK : ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → G' k z = G' 0 z := by
    intro k z hzV hzK
    have hρz : ρ < ‖z - x₀‖ := by simpa [hK_def, mem_closedBall, dist_eq_norm] using hzK
    have e (l : ℕ) : G' l z = h z :=
      smoothMax_eq_right (by have := hout z hρz; linarith [hgup l z hzV])
    rw [e k, e 0]
  have hnear (k : ℕ) (z : ComplexModel n) (hz : z ∈ ball x₀ (R / 2)) :
      G' k z - v' z = g k z - v z := by
    have hzn : ‖z - x₀‖ < R / 2 := by simpa [mem_ball, dist_eq_norm] using hz
    have hzV : z ∈ (V : Set (ComplexModel n)) := ball_subset_ball (by linarith) hz
    have e1 : G' k z = g k z - cG :=
      smoothMax_eq_left (by have := hin z hzn; linarith [hglow k z hzV])
    have e2 : v' z = v z - cG :=
      smoothMax_eq_left (by have := hin z hzn; linarith [hvlow z hzV])
    rw [e1, e2]; ring
  obtain ⟨ν, hν⟩ := exists_isBTLimit (Ω := V) (u := fun _ ↦ v') fun W hW ↦
    ⟨fun _ ↦ G', fun _ ↦ hG'.mono (subset_closure.trans hW.2),
      fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  set a : ℕ → ℝ := fun j ↦ ∫ z in K, (G' j z - v' z) ∂ν with ha_def
  have ha : Tendsto a atTop (𝓝 0) := hG'.tendsto_setIntegral_sub hK hKV (hν.2.1 K hK hKV)
  set E : ℕ → Set (ComplexModel n) := fun k ↦ ball x₀ (R / 2) ∩ {z | v z + δ < g k z}
  have hEK (k : ℕ) : E k ⊆ K := fun z hz ↦
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz.1
  have hEo (k : ℕ) : IsOpen (E k) :=
    isOpen_inter_setOf_add_lt U.isOpen (ball_subset_ball (by linarith)) isOpen_ball
      (fun z hz ↦ hv.1 z (hUΩ hz)) (hG.1 k).1.continuousOn δ
  have hcap (j : ℕ) : relCapacity Ω (E j) ≤
      ENNReal.ofReal ((n + 1)! * a j / δ ^ (n + 1)) := by
    refine relCapacity_le_of_forall fun u hu hb ↦ ?_
    set μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu
    have hμV := (isBTLimit_canonicalBedfordTaylorMeasure hu).restrict_opens hVΩ
    have hbl := blocki_inequality hμV hK hKV (fun _ z hz ↦ hb z (hVΩ (hKV hz))) hG' hGK hν j
    have hμK : (μ.restrict V) K < ⊤ := hμV.2.1 K hK hKV
    have hint := hG'.integrableOn_pow_sub hK hKV hμK j (n + 1)
    have hEfin : (μ.restrict V) (E j) ≠ ⊤ := (measure_mono (hEK j)).trans_lt hμK |>.ne
    have h1 : (μ.restrict V).real (E j) • δ ^ (n + 1) ≤
        ∫ z in E j, (G' j z - v' z) ^ (n + 1) ∂(μ.restrict V) :=
      setIntegral_ge_of_const_le (hEo j).measurableSet hEfin
        (fun z hz ↦ by
          rw [hnear j z hz.1]
          exact pow_le_pow_left₀ hδ.le (by have : v z + δ < g j z := hz.2; linarith) _)
        (hint.mono_set (hEK j))
    have h2 : ∫ z in E j, (G' j z - v' z) ^ (n + 1) ∂(μ.restrict V) ≤
        ∫ z in K, (G' j z - v' z) ^ (n + 1) ∂(μ.restrict V) := by
      refine setIntegral_mono_set hint ?_ (Eventually.of_forall (hEK j))
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact pow_nonneg (sub_nonneg.2 (hG'.le_of_mem (hKV hz) j)) _
    have hEV : E j ⊆ V := (hEK j).trans hKV
    rw [← Measure.restrict_eq_self μ hEV, ← ENNReal.ofReal_toReal hEfin]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (pow_pos hδ _)]
    have := h1.trans (h2.trans hbl)
    simpa [smul_eq_mul, Measure.real] using this
  have hbound : Tendsto (fun j ↦ ENNReal.ofReal ((n + 1)! * a j / δ ^ (n + 1))) atTop (𝓝 0) := by
    have : Tendsto (fun j ↦ (n + 1)! * a j / δ ^ (n + 1)) atTop (𝓝 ((n + 1)! * 0 / δ ^ (n + 1))) :=
      (ha.const_mul _).div_const _
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) hcap

/-! ## Quasi-continuity -/

/-- **Quasi-continuity near a point.** -/
theorem IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_ball
    {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : closedBall x₀ (3 * R) ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set (ComplexModel n), IsOpen G ∧ relCapacity Ω G < ENNReal.ofReal ε ∧
      ContinuousOn v (ball x₀ (R / 2) \ G) := by
  classical
  obtain ⟨g, hgc, hganti, hglim, hcap⟩ := IsLocallyBoundedPshOn.exists_tendsto_relCapacity hv hR
    hball
  have hUΩ : ball x₀ (3 * R) ⊆ Ω := ball_subset_closedBall.trans hball
  set b : ℕ → ℝ := fun m ↦ ε / 2 / 2 / 2 ^ m with hb_def
  have hb (m : ℕ) : 0 < b m := by positivity
  have hk (m : ℕ) : ∃ k, relCapacity Ω (ball x₀ (R / 2) ∩ {z | v z + 1 / ((m : ℝ) + 1) < g k z}) <
      ENNReal.ofReal (b m) :=
    ((hcap _ (by positivity)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (hb m)))).exists
  choose k hk using hk
  set Gs : ℕ → Set (ComplexModel n) := fun m ↦
    ball x₀ (R / 2) ∩ {z | v z + 1 / ((m : ℝ) + 1) < g (k m) z} with hGs
  refine ⟨⋃ m, Gs m, isOpen_iUnion fun m ↦ isOpen_inter_setOf_add_lt isOpen_ball
    (ball_subset_ball (by linarith)) isOpen_ball (fun z hz ↦ hv.1 z (hUΩ hz)) (hgc (k m)) _,
    ?_, ?_⟩
  · calc relCapacity Ω (⋃ m, Gs m) ≤ ∑' m, relCapacity Ω (Gs m) := relCapacity_iUnion_le Ω Gs
      _ ≤ ∑' m, ENNReal.ofReal (b m) := tsum_le_tsum fun m ↦ (hk m).le
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m ↦ (hb m).le) (summable_geometric_two' _),
            hb_def, tsum_geometric_two']
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · refine TendstoUniformlyOn.continuousOn (F := fun m ↦ g (k m)) (p := atTop) ?_
      (Frequently.of_forall fun m ↦ (hgc (k m)).mono fun z hz ↦
        ball_subset_ball (by linarith) hz.1)
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt hη
    filter_upwards [eventually_ge_atTop m₀] with m hm z hz
    have hzU : z ∈ ball x₀ (3 * R) := ball_subset_ball (by linarith) hz.1
    have hle : v z ≤ g (k m) z := (hganti z hzU).le_of_tendsto (hglim z hzU) (k m)
    have hnot : ¬ (v z + 1 / ((m : ℝ) + 1) < g (k m) z) := fun h ↦
      hz.2 (mem_iUnion.2 ⟨m, hz.1, h⟩)
    have hmm : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) := Nat.one_div_le_one_div hm
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
    linarith [not_lt.1 hnot]

/-- **Quasi-continuity on compact sets.** For a locally bounded plurisubharmonic
function `v` on `Ω`, a compact `K ⊆ Ω` and `ε > 0` there is an open `G` with
`c(G, Ω) < ε` such that `v` is continuous on `K \ G`. -/
theorem IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn
    {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set (ComplexModel n), IsOpen G ∧ relCapacity Ω G < ENNReal.ofReal ε ∧
      ContinuousOn v (K \ G) := by
  classical
  have hrad : ∀ x ∈ K, ∃ R > 0, closedBall x (3 * R) ⊆ Ω := fun x hx ↦ by
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x (hKΩ hx)
    exact ⟨r / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hrΩ⟩
  choose! R hR hRΩ using hrad
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (R x / 2))
    fun x hx ↦ ball_mem_nhds x (by have := hR x hx; positivity)
  set N := t.card
  have hεN : 0 < ε / (N + 1) := by positivity
  have hloc : ∀ x ∈ t, ∃ G : Set (ComplexModel n), IsOpen G ∧
      relCapacity Ω G < ENNReal.ofReal (ε / (N + 1)) ∧ ContinuousOn v (ball x (R x / 2) \ G) :=
    fun x hx ↦ IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_ball hv (hR x (htK
      x hx))
      (hRΩ x (htK x hx)) hεN
  choose! Gx hGo hGcap hGcont using hloc
  refine ⟨⋃ x ∈ t, Gx x, isOpen_biUnion fun x hx ↦ hGo x hx, ?_, fun z hz ↦ ?_⟩
  · calc relCapacity Ω (⋃ x ∈ t, Gx x) ≤ ∑ x ∈ t, relCapacity Ω (Gx x) :=
          relCapacity_biUnion_finset_le Ω t Gx
      _ ≤ ∑ _x ∈ t, ENNReal.ofReal (ε / (N + 1)) := Finset.sum_le_sum fun x hx ↦ (hGcap x hx).le
      _ = ENNReal.ofReal (N * (ε / (N + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  · obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcover hz.1)
    have hzG : z ∉ Gx x := fun h ↦ hz.2 (mem_iUnion₂.2 ⟨x, hxt, h⟩)
    have hc : ContinuousWithinAt v ((K \ ⋃ x ∈ t, Gx x) ∩ ball x (R x / 2)) z :=
      ((hGcont x hxt) z ⟨hzx, hzG⟩).mono fun y hy ↦
        ⟨hy.2, fun h ↦ hy.1.2 (mem_iUnion₂.2 ⟨x, hxt, h⟩)⟩
    exact (continuousWithinAt_inter (isOpen_ball.mem_nhds hzx)).1 hc

/-- **Quasi-continuity of bounded plurisubharmonic functions** (Błocki, Theorem 2.2.2,
for locally bounded functions). For every `ε > 0` there is an open `G` with
`c(G, Ω) < ε` such that `v` is continuous on `Ω \ G`. -/
theorem IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_diff
    {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set (ComplexModel n), IsOpen G ∧ relCapacity Ω G < ENNReal.ofReal ε ∧
      ContinuousOn v ((Ω : Set (ComplexModel n)) \ G) := by
  classical
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  set b : ℕ → ℝ := fun m ↦ ε / 2 / 2 / 2 ^ m with hb_def
  have hb (m : ℕ) : 0 < b m := by positivity
  have hloc (m : ℕ) := IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn hv (hUrc
    m).1 (hUrc m).2 (hb m)
  choose Gm hGo hGcap hGcont using hloc
  refine ⟨⋃ m, Gm m, isOpen_iUnion hGo, ?_, fun z hz ↦ ?_⟩
  · calc relCapacity Ω (⋃ m, Gm m) ≤ ∑' m, relCapacity Ω (Gm m) := relCapacity_iUnion_le Ω Gm
      _ ≤ ∑' m, ENNReal.ofReal (b m) := tsum_le_tsum fun m ↦ (hGcap m).le
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m ↦ (hb m).le) (summable_geometric_two' _),
            hb_def, tsum_geometric_two']
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hz.1)
    have hzm : z ∈ (U m : Set (ComplexModel n)) := hm rfl
    have hzG : z ∉ Gm m := fun h ↦ hz.2 (mem_iUnion.2 ⟨m, h⟩)
    have hc : ContinuousWithinAt v (((Ω : Set (ComplexModel n)) \ ⋃ m, Gm m) ∩ U m) z :=
      ((hGcont m) z ⟨subset_closure hzm, hzG⟩).mono fun y hy ↦
        ⟨subset_closure hy.2, fun h ↦ hy.1.2 (mem_iUnion.2 ⟨m, h⟩)⟩
    exact (continuousWithinAt_inter ((U m).isOpen.mem_nhds hzm)).1 hc

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
