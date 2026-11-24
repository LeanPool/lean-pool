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
    μ.restrict {z | z ∈ U ∧ g z < u i₀ z} = μ'.restrict {z | z ∈ U ∧ g z < u i₀ z} :=
  restrict_eq_of_joint_max_slot i₀ (isDecApprox_const hg) hμc hμf hμ hμ'c hμ'f hμ' hex

theorem IsSmoothPsdOn.mono {U V : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) (hVU : V ≤ U) : IsSmoothPsdOn V g :=
  ⟨hg.1.mono hVU, fun z hz ↦ hg.2 z (hVU hz)⟩

theorem exists_isAdmissible_maxTupleObstacle {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (hg : ∀ i, IsSmoothPsdOn U (g i)) (k : ℕ) :
    ∃ F', IsAdmissible n U (maxTupleObstacle u g k) F' :=
  exists_isAdmissible_joint_maxTuple hF (fun i ↦ isDecApprox_const (hg i)) k

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
        μ.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} :=
  restrict_eq_joint_maxTuple (fun i ↦ isDecApprox_const (hg i)) hμf hμ hex

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
  refine restrict_eq_of_relativelyCompact_model (model := maxTupleObstacle v g n)
    {z | ∀ i, g i z < v i z} hμf hνf hμT hνT ?_ ?_
  · intro i z hz
    simpa [maxTupleObstacle] using hmax i hz
  · intro V hV μV νV hμVf hμVT hF hνVc hνVf hνVT
    have hgV (i : Fin n) : IsSmoothPsdOn V (g i) := (hg i).mono (subset_closure.trans hV.2)
    exact restrict_eq_maxTupleObstacle hgV hμVf hμVT hF n le_rfl νV hνVc hνVf hνVT

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
