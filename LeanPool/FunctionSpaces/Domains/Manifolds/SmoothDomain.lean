/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphStraightening
public import LeanPool.FunctionSpaces.Domains.Manifolds.Besov

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth bounded domains as manifolds with boundary

A **smooth bounded domain** in `ℝ^n` (`Rd.SmoothDomain`) is a bounded Lipschitz domain whose graph
functions are smooth. Its closure is a compact smooth manifold with boundary modelled on the
half-space `𝓡∂ n`:

* **Boundary charts.** For the `j`-th boundary ball, the straightening
  `σ_j(x) = A_j (x - φ_j(x) e_j)` (`Rd.SmoothDomain.straighten`) flattens the graph and turns the
  upward direction `e_j` into `e₀ = (1, 0, …, 0)` by a reflection `A_j` (`Rd.alignTo`); on the
  ball, `x ∈ closure Ω ↔ 0 ≤ σ_j(x)_0`.
* **Interior charts.** Around a point `x₀` of `Ω` with `B(x₀, ρ) ⊆ Ω`, the translation
  `x ↦ x - x₀ + 2ρ e₀` maps the ball into the open half-space.

Both are instances of a **straightener** (`Rd.SmoothDomain.Straightener`): a smooth,
measure-preserving bijection `σ` of `ℝ^n` with smooth inverse and an open set `B` on which the
closure of `Ω` is `{0 ≤ σ(x)_0}`. Each straightener gives a chart of the closure
(`Rd.SmoothDomain.Straightener.chart`); the changes of charts are restrictions of the smooth maps
`σ' ∘ τ`, so the closure is a smooth manifold (`Rd.SmoothDomain.isManifold`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Manifold ContDiff

namespace Rd

variable {n : ℕ} [NeZero n]

/-! ### Aligning a unit vector with the first axis -/

/-- The **alignment** of a vector `e` with `e₀`: the reflection in `(e - e₀)^⊥`. -/
noncomputable def alignTo (e : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ℝ ∙ (e - e0))ᗮ.reflection

/-- The alignment maps a unit vector `e` to `e₀`. -/
theorem alignTo_apply_self {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) : alignTo e e = e0 :=
  Submodule.reflection_sub (by rw [he, norm_e0])

/-! ### Closures -/

omit [NeZero n] in
/-- **Closures agree on open sets where the sets agree**: if `B ∩ S = B ∩ T` for an open `B`, then
`closure S` and `closure T` have the same points in `B`, since near `x ∈ B` the neighbourhoods
within `S` and within `T` are those within `B ∩ S = B ∩ T` (Mathlib's
`mem_closure_iff_nhdsWithin_neBot`, `nhdsWithin_restrict`). -/
theorem mem_closure_iff_of_inter_eq {V : Type*} [TopologicalSpace V] {S T B : Set V}
    (hB : IsOpen B) (h : B ∩ S = B ∩ T) {x : V} (hx : x ∈ B) :
    x ∈ closure S ↔ x ∈ closure T := by
  rw [mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhdsWithin_neBot,
    nhdsWithin_restrict S hx hB, nhdsWithin_restrict T hx hB, inter_comm S, inter_comm T, h]

/-! ### Smooth domains and their straighteners -/

/-- A **smooth bounded domain** in `ℝ^n`: a bounded Lipschitz domain whose graph functions are
smooth. It carries its charts as data; every bounded open set with smooth local graphs
(`Rd.IsBoundedSmoothDomain`) is the carrier of one (`Rd.SmoothDomain.ofIsBoundedSmoothDomain`,
`Rd.isBoundedSmoothDomain_iff_exists`), every open ball among them (`Rd.SmoothDomain.ball`). -/
structure SmoothDomain (n : ℕ) [NeZero n] extends BoundedLipschitzDomain (EuclideanSpace ℝ (Fin n))
    where
  contDiff_phi : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (graph j).phi

namespace SmoothDomain

variable (Ω : SmoothDomain n)

/-- A **straightener** of the closure of `Ω`: a smooth, measure-preserving bijection `σ` of `ℝ^n`
with smooth inverse `τ`, and an open set `B` on which `closure Ω = {0 ≤ σ(x)_0}`, with a base point
of `closure Ω ∩ B`. -/
structure Straightener where
  /-- The straightening map. -/
  sigma : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  /-- Its inverse. -/
  tau : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  contDiff_sigma : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sigma
  contDiff_tau : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) tau
  sigma_tau : ∀ y, sigma (tau y) = y
  tau_sigma : ∀ x, tau (sigma x) = x
  measurePreserving_sigma : MeasurePreserving sigma volume volume
  /-- The open set where the straightener describes the closure. -/
  B : Set (EuclideanSpace ℝ (Fin n))
  isOpen_B : IsOpen B
  isBounded_B : Bornology.IsBounded B
  mem_closure_iff : ∀ x ∈ B, x ∈ closure Ω.carrier ↔ 0 ≤ sigma x 0
  mem_iff : ∀ x ∈ B, x ∈ Ω.carrier ↔ 0 < sigma x 0
  /-- A base point. -/
  base : EuclideanSpace ℝ (Fin n)
  base_mem : base ∈ closure Ω.carrier

namespace Straightener

variable {Ω} (S : Straightener Ω)

/-- The inverse of a straightener stays in the closure on the half-space part of `σ(B)`. -/
theorem tau_mem_closure {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) (hyB : S.tau y ∈ S.B) :
    S.tau y ∈ closure Ω.carrier :=
  (S.mem_closure_iff _ hyB).2 (by rwa [S.sigma_tau])

/-- The chart map `x ↦ σ(x)`, with values in the half-space. -/
noncomputable def toMap (x : closure Ω.carrier) : EuclideanHalfSpace n := (𝓡∂ n).symm (S.sigma x)

/-- On `B` the chart map is `σ`, read in `ℝ^n`. -/
theorem coe_toMap {x : closure Ω.carrier} (hx : (x : EuclideanSpace ℝ (Fin n)) ∈ S.B) :
    (𝓡∂ n) (S.toMap x) = S.sigma x := by
  have h0 : 0 ≤ S.sigma x 0 := (S.mem_closure_iff _ hx).1 x.2
  rw [toMap, modelWithCornersEuclideanHalfSpace_symm_apply_of_le h0,
    modelWithCornersEuclideanHalfSpace_apply]

open Classical in
/-- The inverse chart map `y ↦ τ(y)`, with values in the closure (the base point elsewhere). -/
noncomputable def invMap (y : EuclideanHalfSpace n) : closure Ω.carrier :=
  if h : S.tau ((𝓡∂ n) y) ∈ closure Ω.carrier then ⟨S.tau ((𝓡∂ n) y), h⟩ else ⟨S.base, S.base_mem⟩

/-- On the half-space part of `σ(B)` the inverse chart map is `τ`. -/
theorem coe_invMap {y : EuclideanHalfSpace n} (hy : S.tau ((𝓡∂ n) y) ∈ S.B) :
    (S.invMap y : EuclideanSpace ℝ (Fin n)) = S.tau ((𝓡∂ n) y) := by
  have hcl : S.tau ((𝓡∂ n) y) ∈ closure Ω.carrier := S.tau_mem_closure y.2 hy
  rw [invMap, dite_eq_left hcl]

/-- The **chart** of the closure given by a straightener: `x ↦ σ(x)` on `closure Ω ∩ B`, with
values in the half-space. -/
noncomputable def chart :
    OpenPartialHomeomorph (closure Ω.carrier) (EuclideanHalfSpace n) where
  toFun := S.toMap
  invFun := S.invMap
  source := {x | (x : EuclideanSpace ℝ (Fin n)) ∈ S.B}
  target := {y | S.tau ((𝓡∂ n) y) ∈ S.B}
  map_source' x hx := by
    change S.tau ((𝓡∂ n) (S.toMap x)) ∈ S.B
    rw [S.coe_toMap hx, S.tau_sigma]
    exact hx
  map_target' y hy := by
    change (S.invMap y : EuclideanSpace ℝ (Fin n)) ∈ S.B
    rw [S.coe_invMap hy]
    exact hy
  left_inv' x hx := by
    apply Subtype.ext
    have hI := S.coe_toMap hx
    rw [S.coe_invMap (by rw [hI, S.tau_sigma]; exact hx), hI, S.tau_sigma]
  right_inv' y hy := by
    have h1 := S.coe_invMap hy
    have hB : (S.invMap y : EuclideanSpace ℝ (Fin n)) ∈ S.B := by rw [h1]; exact hy
    apply (𝓡∂ n).injective
    rw [S.coe_toMap hB, h1, S.sigma_tau]
  open_source := S.isOpen_B.preimage continuous_subtype_val
  open_target := S.isOpen_B.preimage (S.contDiff_tau.continuous.comp (𝓡∂ n).continuous)
  continuousOn_toFun := ((𝓡∂ n).continuous_symm.comp
    (S.contDiff_sigma.continuous.comp continuous_subtype_val)).continuousOn
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (S.contDiff_tau.continuous.comp (𝓡∂ n).continuous).continuousOn.congr fun y hy =>
      S.coe_invMap hy

/-- The source of the chart is `closure Ω ∩ B`. -/
theorem mem_chart_source {x : closure Ω.carrier} :
    x ∈ S.chart.source ↔ (x : EuclideanSpace ℝ (Fin n)) ∈ S.B := Iff.rfl

/-- The target of the chart. -/
theorem mem_chart_target {y : EuclideanHalfSpace n} :
    y ∈ S.chart.target ↔ S.tau ((𝓡∂ n) y) ∈ S.B := Iff.rfl

/-- On its source the chart is `σ`, read in `ℝ^n`. -/
theorem chart_apply_coe {x : closure Ω.carrier} (hx : (x : EuclideanSpace ℝ (Fin n)) ∈ S.B) :
    (𝓡∂ n) (S.chart x) = S.sigma x :=
  S.coe_toMap hx

/-- On its target the inverse chart is `τ`, read in `ℝ^n`. -/
theorem chart_symm_coe {y : EuclideanHalfSpace n} (hy : S.tau ((𝓡∂ n) y) ∈ S.B) :
    ((S.chart.symm y : closure Ω.carrier) : EuclideanSpace ℝ (Fin n)) = S.tau ((𝓡∂ n) y) :=
  S.coe_invMap hy

end Straightener

/-! ### Boundary and interior straighteners -/

/-- The **straightening** of the `j`-th boundary patch: `σ_j(x) = A_j (x - φ_j(x) e_j)`. -/
noncomputable def straighten (j : Fin Ω.N) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  alignTo (Ω.graph j).e ((Ω.graph j).flatten x)

/-- The inverse of the straightening. -/
noncomputable def unstraighten (j : Fin Ω.N) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (Ω.graph j).unflatten ((alignTo (Ω.graph j).e).symm y)

/-- **The first coordinate of the straightening** is the height above the graph:
`σ_j(x)_0 = ⟪x, e_j⟫ - φ_j(x)`. -/
theorem straighten_coord (j : Fin Ω.N) (x : EuclideanSpace ℝ (Fin n)) :
    Ω.straighten j x 0 = inner ℝ x (Ω.graph j).e - (Ω.graph j).phi x := by
  rw [coord_zero_eq_inner, straighten, ← alignTo_apply_self (Ω.graph j).norm_e,
    LinearIsometryEquiv.inner_map_map, LipschitzGraph.inner_flatten]

/-- The straightener of the `j`-th boundary patch, on the `j`-th boundary ball. -/
noncomputable def boundaryStraightener (j : Fin Ω.N) : Ω.Straightener where
  sigma := Ω.straighten j
  tau := Ω.unstraighten j
  contDiff_sigma := (alignTo (Ω.graph j).e).toContinuousLinearEquiv.contDiff.comp
    ((Ω.graph j).contDiff_flatten (Ω.contDiff_phi j))
  contDiff_tau := ((Ω.graph j).contDiff_unflatten (Ω.contDiff_phi j)).comp
    (alignTo (Ω.graph j).e).symm.toContinuousLinearEquiv.contDiff
  sigma_tau y := by
    simp only [straighten, unstraighten, LipschitzGraph.flatten_unflatten,
      LinearIsometryEquiv.apply_symm_apply]
  tau_sigma x := by
    simp only [straighten, unstraighten, LinearIsometryEquiv.symm_apply_apply,
      LipschitzGraph.unflatten_flatten]
  measurePreserving_sigma := (alignTo (Ω.graph j).e).measurePreserving.comp
    (Ω.graph j).measurePreserving_flatten
  B := ball (Ω.center j) (Ω.radius j)
  isOpen_B := isOpen_ball
  isBounded_B := isBounded_ball
  mem_closure_iff x hx := by
    rw [mem_closure_iff_of_inter_eq isOpen_ball (Ω.ball_inter j) hx,
      LipschitzGraph.closure_domain, straighten_coord, sub_nonneg]
    rfl
  mem_iff x hx := by
    have h : x ∈ ball (Ω.center j) (Ω.radius j) ∩ Ω.carrier ↔
        x ∈ ball (Ω.center j) (Ω.radius j) ∩ (Ω.graph j).domain := by rw [Ω.ball_inter j]
    rw [straighten_coord, sub_pos]
    exact ⟨fun h1 => (h.1 ⟨hx, h1⟩).2, fun h1 => (h.2 ⟨hx, h1⟩).2⟩
  base := Ω.center j
  base_mem := frontier_subset_closure (Ω.center_mem j)

/-- A radius `ρ > 0` with `B(x₀, ρ) ⊆ Ω` around a point of `Ω`. -/
noncomputable def interiorRadius {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω.carrier) : ℝ :=
  (Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀).choose

/-- The interior radius is positive. -/
theorem interiorRadius_pos {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω.carrier) :
    0 < Ω.interiorRadius hx₀ :=
  (Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀).choose_spec.1

/-- The ball of the interior radius lies in `Ω`. -/
theorem ball_interiorRadius_subset {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω.carrier) :
    ball x₀ (Ω.interiorRadius hx₀) ⊆ Ω.carrier :=
  (Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀).choose_spec.2

/-- Around an interior point, the translated first coordinate is positive:
`(x - x₀ + 2ρ e₀)_0 > 0` for `‖x - x₀‖ < ρ`. -/
theorem interior_coord_pos {x₀ x : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hx : x ∈ ball x₀ ρ) :
    0 < (x - x₀ + (2 * ρ) • e0 : EuclideanSpace ℝ (Fin n)) 0 := by
  have h1 : |(x - x₀) 0| ≤ ‖x - x₀‖ := by
    have := PiLp.norm_apply_le (x - x₀) 0
    rwa [Real.norm_eq_abs] at this
  have h2 : ‖x - x₀‖ < ρ := by rwa [← dist_eq_norm]
  have he : (e0 : EuclideanSpace ℝ (Fin n)) 0 = 1 := by simp [e0]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he, mul_one]
  linarith [neg_abs_le ((x - x₀) 0), norm_nonneg (x - x₀)]

/-- The straightener at an interior point `x₀`: the translation `x ↦ x - x₀ + 2ρ e₀` on
`B(x₀, ρ) ⊆ Ω`, which lands in the open half-space. -/
noncomputable def interiorStraightener {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω.carrier) :
    Ω.Straightener where
  sigma x := x - x₀ + (2 * Ω.interiorRadius hx₀) • e0
  tau y := y - (2 * Ω.interiorRadius hx₀) • e0 + x₀
  contDiff_sigma := (contDiff_id.sub contDiff_const).add contDiff_const
  contDiff_tau := (contDiff_id.sub contDiff_const).add contDiff_const
  sigma_tau y := by abel
  tau_sigma x := by abel
  measurePreserving_sigma := (measurePreserving_add_right volume _).comp
    (measurePreserving_sub_right volume _)
  B := ball x₀ (Ω.interiorRadius hx₀)
  isOpen_B := isOpen_ball
  isBounded_B := isBounded_ball
  mem_closure_iff x hx :=
    ⟨fun _ => (interior_coord_pos hx).le, fun _ => subset_closure (Ω.ball_interiorRadius_subset
      hx₀ hx)⟩
  mem_iff x hx := ⟨fun _ => interior_coord_pos hx, fun _ => Ω.ball_interiorRadius_subset hx₀ hx⟩
  base := x₀
  base_mem := subset_closure hx₀

/-- A boundary ball containing a point of `closure Ω` outside `Ω`. -/
noncomputable def boundaryIndex {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closure Ω.carrier)
    (hx' : x ∉ Ω.carrier) : Fin Ω.N :=
  (mem_iUnion.1 (Ω.frontier_subset ⟨hx, by rwa [Ω.isOpen.interior_eq]⟩)).choose

/-- The point lies in its boundary ball. -/
theorem mem_ball_boundaryIndex {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closure Ω.carrier)
    (hx' : x ∉ Ω.carrier) :
    x ∈ ball (Ω.center (Ω.boundaryIndex hx hx')) (Ω.radius (Ω.boundaryIndex hx hx')) :=
  (mem_iUnion.1 (Ω.frontier_subset ⟨hx, by rwa [Ω.isOpen.interior_eq]⟩)).choose_spec

open Classical in
/-- The straightener at a point of the closure: interior or boundary. -/
noncomputable def straightenerAt (x : closure Ω.carrier) : Ω.Straightener :=
  if h : (x : EuclideanSpace ℝ (Fin n)) ∈ Ω.carrier then Ω.interiorStraightener h
  else Ω.boundaryStraightener (Ω.boundaryIndex x.2 h)

/-- A point lies in the set of its straightener. -/
theorem mem_straightenerAt (x : closure Ω.carrier) :
    (x : EuclideanSpace ℝ (Fin n)) ∈ (Ω.straightenerAt x).B := by
  by_cases h : (x : EuclideanSpace ℝ (Fin n)) ∈ Ω.carrier
  · rw [straightenerAt, dite_eq_left h]
    exact mem_ball_self (Ω.interiorRadius_pos h)
  · rw [straightenerAt, dite_eq_right h]
    exact Ω.mem_ball_boundaryIndex x.2 h

/-! ### The closure as a manifold with boundary -/

/-- **The closure of a smooth domain is a charted space** over the half-space: its atlas consists
of the charts of all straighteners. -/
noncomputable instance chartedSpace : ChartedSpace (EuclideanHalfSpace n) (closure Ω.carrier) where
  atlas := {e | ∃ S : Ω.Straightener, e = S.chart}
  chartAt x := (Ω.straightenerAt x).chart
  mem_chart_source x := Ω.mem_straightenerAt x
  chart_mem_atlas _ := ⟨_, rfl⟩

/-- **The closure of a smooth domain is a smooth manifold with boundary**: the change of charts
from `S` to `S'` is the restriction of the smooth map `σ' ∘ τ`. -/
instance isManifold : IsManifold (𝓡∂ n) ∞ (closure Ω.carrier) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨S, rfl⟩ ⟨S', rfl⟩
  refine (S'.contDiff_sigma.comp S.contDiff_tau).contDiffOn.congr fun z hz => ?_
  obtain ⟨⟨hz1, hz2⟩, hzI⟩ := hz
  have hzz : (𝓡∂ n) ((𝓡∂ n).symm z) = z := (𝓡∂ n).right_inv hzI
  have hτ : S.tau z ∈ S.B := by
    have h := S.mem_chart_target.1 hz1
    rwa [hzz] at h
  have hsymm := S.chart_symm_coe (y := (𝓡∂ n).symm z) (by rw [hzz]; exact hτ)
  rw [hzz] at hsymm
  have hB' : ((S.chart.symm ((𝓡∂ n).symm z) : closure Ω.carrier) : EuclideanSpace ℝ (Fin n)) ∈
      S'.B := S'.mem_chart_source.1 hz2
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
  rw [S'.chart_apply_coe hB', hsymm]

/-- **The inclusion of the closure into `ℝ^n` is smooth**: in the chart of a straightener it is
`τ`. -/
theorem contMDiff_subtype_val :
    ContMDiff (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (Subtype.val : closure Ω.carrier → EuclideanSpace ℝ (Fin n)) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  set S := Ω.straightenerAt x
  have hev : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) ∘
      Subtype.val ∘ (extChartAt (𝓡∂ n) x).symm) =ᶠ[𝓝[range (𝓡∂ n)] (extChartAt (𝓡∂ n) x x)]
        S.tau := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ n) x] with z hz
    have hzI : z ∈ range (𝓡∂ n) := extChartAt_target_subset_range x hz
    have hzz : (𝓡∂ n) ((𝓡∂ n).symm z) = z := (𝓡∂ n).right_inv hzI
    rw [extChartAt_target] at hz
    have hzt : S.tau ((𝓡∂ n) ((𝓡∂ n).symm z)) ∈ S.B := S.mem_chart_target.1 hz.1
    have hcomp : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) ∘
        Subtype.val ∘ (extChartAt (𝓡∂ n) x).symm) z =
          ((S.chart.symm ((𝓡∂ n).symm z) : closure Ω.carrier) : EuclideanSpace ℝ (Fin n)) := by
      rw [extChartAt_model_space_eq_id]
      rfl
    rw [hcomp, S.chart_symm_coe hzt, hzz]
  exact (S.contDiff_tau.contDiffAt.contDiffWithinAt).congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin (extChartAt_target_subset_range x (mem_extChartAt_target x)))

/-- The closure of a smooth domain is compact. -/
instance compactSpace : CompactSpace (closure Ω.carrier) :=
  isCompact_iff_compactSpace.1 Ω.isCompact_closure

/-! ### The Lebesgue measure as a smooth measure -/

/-- The **Lebesgue measure on the closure** of `Ω`. -/
noncomputable def volumeOn : Measure (closure Ω.carrier) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).comap Subtype.val

/-- The image of the target of the chart of a straightener is `σ(closure Ω ∩ B)`. -/
theorem Straightener.extend_target (S : Ω.Straightener) :
    (S.chart.extend (𝓡∂ n)).target = S.sigma '' (closure Ω.carrier ∩ S.B) := by
  rw [OpenPartialHomeomorph.extend_target']
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hτ : S.tau ((𝓡∂ n) y) ∈ S.B := hy
    exact ⟨S.tau ((𝓡∂ n) y), ⟨S.tau_mem_closure y.2 hτ, hτ⟩, S.sigma_tau _⟩
  · rintro ⟨x, ⟨hxcl, hxB⟩, rfl⟩
    refine ⟨S.chart ⟨x, hxcl⟩, S.chart.map_source hxB, ?_⟩
    exact S.chart_apply_coe (x := ⟨x, hxcl⟩) hxB

/-- **The Lebesgue measure is a smooth measure** on the closure, with density `1` in every chart:
the straighteners preserve the Lebesgue measure. -/
instance isSmoothMeasure_volumeOn : Manifold.IsSmoothMeasure (𝓡∂ n) Ω.volumeOn where
  exists_density e he := by
    obtain ⟨S, rfl⟩ := he
    refine ⟨1, continuousOn_const, fun _ _ => ⟨zero_lt_one, ENNReal.one_lt_top⟩, ?_⟩
    have hcl : MeasurableSet (closure Ω.carrier) := isClosed_closure.measurableSet
    have hemb := MeasurableEmbedding.subtype_coe hcl
    have hσemb : MeasurableEmbedding S.sigma :=
      (Homeomorph.mk ⟨S.sigma, S.tau, S.tau_sigma, S.sigma_tau⟩ S.contDiff_sigma.continuous
        S.contDiff_tau.continuous).measurableEmbedding
    have hsrc : MeasurableSet S.chart.source := S.chart.open_source.measurableSet
    -- the extended chart is `σ` on the source
    have hcongr : Measure.map (S.chart.extend (𝓡∂ n)) (Ω.volumeOn.restrict S.chart.source) =
        Measure.map (S.sigma ∘ Subtype.val) (Ω.volumeOn.restrict S.chart.source) := by
      refine Measure.map_congr ((ae_restrict_iff' hsrc).2 (Eventually.of_forall fun x hx => ?_))
      rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, S.chart_apply_coe hx]
      rfl
    rw [withDensity_one, hcongr, ← Measure.map_map S.contDiff_sigma.continuous.measurable
      measurable_subtype_coe, S.extend_target]
    have hval : Measure.map Subtype.val (Ω.volumeOn.restrict S.chart.source) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S.B ∩ closure Ω.carrier) := by
      rw [show S.chart.source = Subtype.val ⁻¹' S.B from rfl, ← hemb.restrict_map, volumeOn,
        hemb.map_comap, Subtype.range_coe, Measure.restrict_restrict S.isOpen_B.measurableSet]
    rw [hval, inter_comm]
    exact (S.measurePreserving_sigma.restrict_image_emb hσemb _).map_eq

end SmoothDomain

end Rd
