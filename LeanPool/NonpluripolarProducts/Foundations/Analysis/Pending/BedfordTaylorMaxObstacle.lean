/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxLocality

/-!
# Plurifine locality of Bedford–Taylor measures for a maximum with a smooth obstacle

Let `u' = max(u, g)` in one slot, where `g` is smooth with positive semidefinite
complex Hessian. The regularized maxima `g + ε_j P((f_j - g)/ε_j)` of decreasing
smooth approximations `f_j` of `u` are again smooth and positive semidefinite,
because `P' ∈ [0,1]` mixes the two Hessians convexly. They decrease to
`max(u, g)`, and their mixed densities agree with those of `f_j` where
`f_j > g + ε_j`, while `(g + ε_j P((f_j - g)/ε_j)) - g ≤ ε_j` elsewhere.

Unlike the constant obstacle of `BedfordTaylorMaxLocality`, the weight
`max(u, g) - g` is not plurisubharmonic, so the weighted convergence theorem is
applied to the plurisubharmonic weight `max(u, g)` and the smooth part is
removed by the unweighted convergence theorem against the test function `χ · g`.
Dividing by the positive weight on `{u > g}` then gives `μ = μ'` there.

Source: Bedford–Taylor locality in the plurifine topology, as invoked in BEGZ §1.2.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

/-- **Weighted locality for a smooth obstacle.** Replacing one slot `u i₀` by
`max(u i₀, g)`, with `g` smooth and positive semidefinite, does not change the
limit measure weighted by `max(u i₀, g) - g`. -/
theorem integral_mul_maxObstacleWeight_eq {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) (g z)) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, χ z * (max (u i₀ z) (g z) - g z) ∂μ =
      ∫ z, χ z * (max (u i₀ z) (g z) - g z) ∂μ' :=
  JointDecreasingMaxWeight.integral_mul_jointMaxWeight_eq i₀
    (isDecApprox_const hg) hμc hμf hμ hμ'c hμ'f hμ' hex hχ hχc hχU

/-- The strict superlevel set over a smooth obstacle is measurable. -/
theorem IsDecApprox.measurableSet_lt_obstacle {U : Opens (ComplexModel n)}
    {w g : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    (hg : ContinuousOn g U) : MeasurableSet {z | z ∈ U ∧ g z < w z} := by
  have heq : {z | z ∈ U ∧ g z < w z} =
      ⋃ m : ℕ, ⋂ k : ℕ, ((U : Set (ComplexModel n)) ∩
        (fun z ↦ G k z - g z) ⁻¹' Ioi (1 / ((m : ℝ) + 1))) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨hzU, hz⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      exact ⟨m, fun k ↦ ⟨hzU, by linarith [hG.le_of_mem hzU k]⟩⟩
    · rintro ⟨m, hm⟩
      obtain ⟨hzU, -⟩ := hm 0
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      refine ⟨hzU, ?_⟩
      have := ge_of_tendsto' ((hG.2.2.1 z hzU).sub_const (g z)) fun k ↦ (hm k).2.le
      linarith
  rw [heq]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iInter fun k ↦
    (((hG.1 k).1.continuousOn.sub hg).isOpen_inter_preimage U.isOpen isOpen_Ioi).measurableSet

/-- **Locality for one slot over a smooth obstacle.** On `{u i₀ > g}` the limit
measures for `u` and for `u` with `max(u i₀, g)` in slot `i₀` coincide. -/
theorem restrict_eq_of_max_slot_obstacle {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) (g z)) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) :
    μ.restrict {z | z ∈ U ∧ g z < u i₀ z} = μ'.restrict {z | z ∈ U ∧ g z < u i₀ z} := by
  classical
  obtain ⟨F, hF⟩ := id hex
  have hGw := hF.1 i₀
  set P := {z | z ∈ U ∧ g z < u i₀ z}
  have hPm : MeasurableSet P := hGw.measurableSet_lt_obstacle hg.1.continuousOn
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) (g z) - g z)
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) (g z) - g z) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact (((hGw.1 j).1.continuousOn.sup hg.1.continuousOn).sub
        hg.1.continuousOn).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max tendsto_const_nhds).sub_const (g z)
  refine restrict_eq_of_max_weight_test_integral_eq hPm hfm ?_ ?_ hμf hμ'f ?_
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    exact ⟨C, fun _ hz => hGw.abs_le_of_mem hKU hC hz⟩
  · intro K hK hKU
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hKU)
    exact ⟨D, fun z hz => by simpa only [Real.norm_eq_abs] using hD z hz⟩
  · intro φ
    exact integral_mul_maxObstacleWeight_eq i₀ hg hμc hμf hμ hμ'c hμ'f hμ' hex
      φ.continuous φ.hasCompactSupport φ.tsupport_subset

theorem IsSmoothPsdOn.mono {U V : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) (hVU : V ≤ U) : IsSmoothPsdOn V g :=
  ⟨hg.1.mono hVU, fun z hz ↦ hg.2 z (hVU hz)⟩

/-- The tuple with `max(·, g i)` applied in the slots of index below `k`. -/
def maxTupleObstacle (u g : Fin n → ComplexModel n → ℝ) (k : ℕ) :
    Fin n → ComplexModel n → ℝ :=
  fun i ↦ if i.val < k then fun z ↦ max (u i z) (g i z) else u i

theorem maxTupleObstacle_zero (u g : Fin n → ComplexModel n → ℝ) :
    maxTupleObstacle u g 0 = u := by
  funext i; simp [maxTupleObstacle]

theorem maxTupleObstacle_succ (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g (k + 1) =
      Function.update (maxTupleObstacle u g k) ⟨k, hk⟩
        (fun z ↦ max (maxTupleObstacle u g k ⟨k, hk⟩ z) (g ⟨k, hk⟩ z)) := by
  funext i
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp [maxTupleObstacle]
  · have hik : i.val ≠ k := fun h' ↦ h (Fin.ext h')
    simp only [maxTupleObstacle, Function.update_of_ne h]
    by_cases hlt : i.val < k
    · simp [hlt, show i.val < k + 1 by omega]
    · simp [hlt, show ¬ i.val < k + 1 by omega]

theorem maxTupleObstacle_apply_self (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g k ⟨k, hk⟩ = u ⟨k, hk⟩ := by
  simp [maxTupleObstacle]

theorem exists_isAdmissible_maxTupleObstacle {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (hg : ∀ i, IsSmoothPsdOn U (g i)) (k : ℕ) :
    ∃ F', IsAdmissible n U (maxTupleObstacle u g k) F' := by
  classical
  refine ⟨fun i ↦ if i.val < k then
    (fun j ↦ scaledSmoothMax (maxScale j) (F i j) (g i)) else F i,
    fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i.val < k
  · simpa [maxTupleObstacle, h] using (hF.1 i).scaledSmoothMax (hg i)
  · simpa [maxTupleObstacle, h] using hF.1 i

/-- **Locality in all slots over smooth obstacles, on a relatively compact set.** -/
theorem restrict_eq_maxTupleObstacle {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} (hg : ∀ i, IsSmoothPsdOn U (g i))
    {μ : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTupleObstacle u g k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} =
        μ.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} := by
  obtain ⟨F, hF⟩ := hex
  refine restrict_eq_of_tuple_steps (U := U) (P := {z | z ∈ U ∧ ∀ i, g i z < u i z})
    (S := fun i => {z | z ∈ U ∧ g i z < maxTupleObstacle u g i i z})
    (fun _ hz => hz.1) (maxTupleObstacle u g) (maxTupleObstacle_zero u g) ?_ hμf hμ ⟨F, hF⟩ ?_
  · intro i z hz
    exact ⟨hz.1, by rw [maxTupleObstacle_apply_self]; exact hz.2 i⟩
  · intro k hk μk μ' hμkc hμkf hμkT hμ'c hμ'f hμ'
    rw [maxTupleObstacle_succ u g hk] at hμ'
    exact restrict_eq_of_max_slot_obstacle (u := maxTupleObstacle u g k) ⟨k, hk⟩
      (hg ⟨k, hk⟩) hμkc hμkf hμkT hμ'c hμ'f hμ'
      (exists_isAdmissible_maxTupleObstacle hF hg k)

/-- **Max-obstacle locality on an open set.** Replacing every slot `v i` by
`max(v i, g i)`, with each `g i` smooth and positive semidefinite, does not
change the measure on the set where every slot strictly exceeds its obstacle. -/
theorem restrict_eq_of_max_obstacle {Ω : Opens (ComplexModel n)}
    {v w g : Fin n → ComplexModel n → ℝ} (hg : ∀ i, IsSmoothPsdOn Ω (g i))
    {μ ν : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hμT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ)
    (hνT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U w F ∧ TendstoMixed U F ν)
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) (g i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hQ : {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      ⋃ m, {z | z ∈ U m ∧ ∀ i, g i z < v i z} := by
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
  set P := {z | z ∈ V ∧ ∀ i, g i z < v i z}
  have hPV : P ⊆ V := fun z hz ↦ hz.1
  have hgV (i : Fin n) : IsSmoothPsdOn V (g i) := (hg i).mono (hUΩ m)
  have hfinV (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ρ K < ⊤ := fun K hK hKV ↦ hρ K hK (hKV.trans (hUΩ m))
  obtain ⟨F, hF, hFT⟩ := hμT V (hUrc m)
  obtain ⟨μV, -, hμVf, hμVT⟩ := pClaim_all (n := n) V v
  have e1 : μ.restrict V = μV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV μ hμf) hμVf fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hμVT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  obtain ⟨G, hG, hGT⟩ := hνT V (hUrc m)
  have hG' : IsAdmissible n V (maxTupleObstacle v g n) G := by
    refine ⟨fun i ↦ (hG.1 i).congr fun z hz ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    simpa [maxTupleObstacle] using hmax i (hUΩ m hz)
  obtain ⟨νV, hνVc, hνVf, hνVT⟩ := pClaim_all (n := n) V (maxTupleObstacle v g n)
  have e2 : ν.restrict V = νV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV ν hνf) hνVf fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hνVT G hG' φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hchain := restrict_eq_maxTupleObstacle hgV hμVf hμVT ⟨F, hF⟩ n le_rfl νV hνVc hνVf hνVT
  rw [← Measure.restrict_restrict_of_subset hPV, e2, Measure.restrict_restrict_of_subset hPV,
    hchain, ← Measure.restrict_restrict_of_subset hPV, ← e1,
    Measure.restrict_restrict_of_subset hPV]

/-- **Scalar max-obstacle locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalBedfordTaylorMeasure.restrict_max_obstacle
    {Ω : Opens (ComplexModel n)} {v w g : ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalBedfordTaylorMeasure Ω w ν) (hg : IsSmoothPsdOn Ω g)
    (hmax : EqOn w (fun z ↦ max (v z) (g z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ g z < v z} = μ.restrict {z | z ∈ Ω ∧ g z < v z} := by
  have h := restrict_eq_of_max_obstacle (v := fun _ ↦ v) (w := fun _ ↦ w) (g := fun _ ↦ g)
    (fun _ ↦ hg) hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) fun _ ↦ hmax
  have hS : {z | z ∈ Ω ∧ g z < v z} ⊆ {z | z ∈ Ω ∧ ∀ _ : Fin n, g z < v z} :=
    fun z hz ↦ ⟨hz.1, fun _ ↦ hz.2⟩
  rw [← Measure.restrict_restrict_of_subset hS, h, Measure.restrict_restrict_of_subset hS]

/-- **Mixed max-obstacle locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalMixedBedfordTaylorMeasure.restrict_max_obstacle
    {Ω : Opens (ComplexModel n)} {v w g : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω w ν) (hg : ∀ i, IsSmoothPsdOn Ω (g i))
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) (g i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} :=
  restrict_eq_of_max_obstacle hg hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) hmax

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
