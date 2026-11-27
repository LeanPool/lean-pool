/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Traces.GraphTraceCharts
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Traces on the boundary of bounded Lipschitz domains

Let `Ω` be a bounded Lipschitz domain with boundary `Γ`: finitely many balls `B_j` cover `Γ`, and
`B_j ∩ Ω = B_j ∩ Ω_j` for Lipschitz graph domains `Ω_j` over hyperplanes `H_j`, with graph maps
`γ_j` and projections `P_j` (`Rd.BoundedLipschitzDomain`). In `B_j` the boundary is the graph of
`Ω_j` (`Rd.BoundedLipschitzDomain.mem_frontier_iff`).

* **Almost everywhere on the boundary** (`Rd.BoundedLipschitzDomain.aeBoundary`): a property holds
  almost everywhere on `Γ` if, for every `j`, it holds at `γ_j(x')` for almost every `x' ∈ H_j` with
  `γ_j(x') ∈ B_j`. The exceptional sets are the null sets of the surface measure, described in the
  charts.
* **Besov spaces on the boundary** (`Rd.BoundedLipschitzDomain.MemBoundaryBesov`): the chart
  construction follows Schneider–Vybíral, Definition 3.3, which assumes dimension at least two.
  Here, for a smooth resolution of unity `(ψ_j)` on `Γ` subordinate to
  `(B_j)` (`Rd.BoundedLipschitzDomain.BoundaryPartition`), `g ∈ B^s_{p,q}(Γ)` if every chart piece
  `(ψ_j g) ∘ γ_j` lies in `B^s_{p,q}(H_j)`, with first differences for `0 < s < 1`.
* **The boundary trace** (`Rd.BoundedLipschitzDomain.boundaryTrace`):
  `Tr_Γ F(y) = ∑_k ψ_k(y) Tr_k F(P_k y)` with the traces `Tr_k` of the graph domains. In each chart
  it is the trace of the graph domain (`Rd.BoundedLipschitzDomain.boundaryTrace_graphMap`), by the
  change of chart; hence it does not depend on the resolution of unity, and it is the restriction
  for continuous functions.
* **The trace space via ambient functions.** Schneider–Vybíral, Theorem 4.11, gives the
  corresponding intrinsic equality on bounded Lipschitz domains in dimension at least two.
  Here the equality extends to dimension one and the construction gives an ambient
  representative. For `1 ≤ p < ∞`, `0 < s < 1`,
  `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff `g = Tr_Γ F` almost everywhere on `Γ` for some
  `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_iff`). The chart pieces of `Tr_Γ F` are the
  traces of `ψ_j F` on the graph domains; conversely `F = ∑_j ζ_j E_j G_j` with the extensions `E_j`
  of the graph domains and cut-offs `ζ_j` with `ζ_j ≠ 0` only in `B_j` and `ζ_j = 1` where
  `ψ_j ≠ 0` (`Rd.BoundedLipschitzDomain.boundaryTrace_extensionSum_eventuallyEq`).
* The boundary trace depends only on `F` on `Ω` (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`),
  and the functions with a finite intrinsic norm on `Ω` are the restrictions of such `F`
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_of_modulusOn`): `B^s_{p,q}(Γ)` is the trace
  space of `B^{s+1/p}_{p,q}(Ω)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`); every such function
  has a boundary trace, unique almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_modNormOn_lt_top`,
  `Rd.BoundedLipschitzDomain.IsBoundaryTrace.unique`). In particular
  `B^s_{p,q}(Γ)` does not depend on the resolution of unity
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_of_boundaryPartition`).
* **Boundary traces with a finite intrinsic norm**
  (`Rd.BoundedLipschitzDomain.HasBoundaryTrace`): `f` has the boundary trace `g` if `f` has a
  finite intrinsic norm on `Ω` and `g` is its boundary trace. The trace space, the existence and
  the uniqueness of the trace hold in this form
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_hasBoundaryTrace`,
  `Rd.BoundedLipschitzDomain.HasBoundaryTrace.memBoundaryBesov`,
  `Rd.BoundedLipschitzDomain.exists_hasBoundaryTrace_of_modNormOn_lt_top`,
  `Rd.BoundedLipschitzDomain.HasBoundaryTrace.unique`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

section Auxiliary

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Elements of `L_p` with equal restrictions to `O` agree almost everywhere on `O`
(`Rd.indicatorLp_eq_iff_ae_eq_restrict` and Mathlib's `ae_restrict_iff'`). -/
theorem ae_eq_of_indicatorLp_eq {O : Set α} (hO : MeasurableSet O) {F f : Lp ℂ p μ}
    (h : indicatorLp hO F = indicatorLp hO f) : ∀ᵐ x ∂μ, x ∈ O → F x = f x :=
  (ae_restrict_iff' hO).1 ((indicatorLp_eq_iff_ae_eq_restrict hO).1 h)

end Auxiliary

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Resolutions of unity on the boundary -/

/-- A **resolution of unity on the boundary** subordinate to the boundary balls: smooth `ψ_j` with
`tsupport ψ_j ⊆ B_j` and `∑_j ψ_j = 1` on `Γ`. -/
structure BoundaryPartition (Ω : BoundedLipschitzDomain V) where
  /-- The functions `ψ_j`. -/
  toFun : Fin Ω.N → V → ℝ
  contDiff : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (toFun j)
  tsupport_subset : ∀ j, tsupport (toFun j) ⊆ ball (Ω.center j) (Ω.radius j)
  sum_eq_one : ∀ y ∈ frontier Ω.carrier, ∑ j, toFun j y = 1

namespace BoundaryPartition

variable {Ω : BoundedLipschitzDomain V} (ψ : Ω.BoundaryPartition)

/-- The functions `ψ_j` with complex values. -/
noncomputable def toComplex (j : Fin Ω.N) : V → ℂ := fun y => (ψ.toFun j y : ℂ)

/-- The `ψ_j` are smooth. -/
theorem contDiff_toComplex (j : Fin Ω.N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ.toComplex j) :=
  Complex.ofRealCLM.contDiff.comp (ψ.contDiff j)

/-- `ψ_j ≠ 0` only in `B_j`. -/
theorem mem_ball_of_ne_zero {j : Fin Ω.N} {y : V} (hy : ψ.toFun j y ≠ 0) :
    y ∈ ball (Ω.center j) (Ω.radius j) :=
  ψ.tsupport_subset j (subset_tsupport _ hy)

/-- `ψ_j(y) = 0` gives `ψ_j(y) = 0` in `ℂ`. -/
theorem toComplex_of_eq_zero {j : Fin Ω.N} {y : V} (hy : ψ.toFun j y = 0) :
    ψ.toComplex j y = 0 := by
  simp [toComplex, hy]

/-- `∑_j ψ_j = 1` on `Γ`. -/
theorem sum_toComplex_eq_one {y : V} (hy : y ∈ frontier Ω.carrier) :
    ∑ j, ψ.toComplex j y = 1 := by
  simp only [toComplex]
  rw [← Complex.ofReal_sum, ψ.sum_eq_one y hy, Complex.ofReal_one]

variable [FiniteDimensional ℝ V]

/-- The functions of a resolution of unity on the boundary have compact support: closed supports
inside the bounded balls `B_j`. -/
theorem hasCompactSupport (j : Fin Ω.N) : HasCompactSupport (ψ.toFun j) :=
  isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    (isBounded_ball.subset (ψ.tsupport_subset j))

/-- The `ψ_j` have compact support. -/
theorem hasCompactSupport_toComplex (j : Fin Ω.N) : HasCompactSupport (ψ.toComplex j) :=
  (ψ.hasCompactSupport j).comp_left Complex.ofReal_zero

/-- **Cut-offs for the resolution of unity**: smooth `ζ_j` with compact support, `ζ_j ≠ 0` only in
`B_j` and `ζ_j = 1` where `ψ_j ≠ 0`; a bump function equal to `1` on a ball around `tsupport ψ_j`
inside `B_j` (Mathlib's `exists_lt_subset_ball` and `ContDiffBump`). -/
theorem exists_cutoff (j : Fin Ω.N) :
    ∃ ζ : V → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      (∀ y, ζ y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j)) ∧ ∀ y, ψ.toFun j y ≠ 0 → ζ y = 1 := by
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport _) (ψ.tsupport_subset j)
  have hρ := Ω.radius_pos j
  let β : ContDiffBump (Ω.center j) :=
    ⟨max r (Ω.radius j / 2), Ω.radius j, lt_max_of_lt_right (by positivity),
      max_lt hr (by linarith)⟩
  refine ⟨fun y => ((β y : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp β.contDiff,
    β.hasCompactSupport.comp_left Complex.ofReal_zero, fun y hy => ?_, fun y hy => ?_⟩
  · have hs : y ∈ Function.support β := fun h => hy (by simp [h])
    rwa [β.support_eq] at hs
  · change ((β y : ℝ) : ℂ) = 1
    rw [β.one_of_mem_closedBall, Complex.ofReal_one]
    exact ball_subset_closedBall
      (ball_subset_ball (le_max_left _ _) (hsub (subset_tsupport _ hy)))

end BoundaryPartition

variable (Ω : BoundedLipschitzDomain V)

/-! ### The boundary in the charts -/

/-- **In a boundary ball the boundary is the graph**: for `y ∈ B_j`, `y ∈ Γ` iff `γ_j(P_j y) = y`,
since `Ω` and `Ω_j` agree on the open ball `B_j` (Mathlib's `frontier_inter_open_inter`). -/
theorem mem_frontier_iff (j : Fin Ω.N) {y : V} (hy : y ∈ ball (Ω.center j) (Ω.radius j)) :
    y ∈ frontier Ω.carrier ↔ (Ω.graph j).graphMap ((Ω.graph j).proj y) = y := by
  have h := frontier_inter_open_inter (s := Ω.carrier)
    (isOpen_ball : IsOpen (ball (Ω.center j) (Ω.radius j)))
  rw [Ω.inter_ball_eq j le_rfl, frontier_inter_open_inter isOpen_ball] at h
  rw [← (Ω.graph j).mem_frontier_domain_iff]
  have h' := Set.ext_iff.1 h y
  simp only [Set.mem_inter_iff, and_iff_left hy] at h'
  exact h'.symm

/-- The boundary meets `B_j` in the graph of `Ω_j`. -/
theorem graphMap_mem_frontier (j : Fin Ω.N) {x' : (Ω.graph j).hyperplane}
    (hx : (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j)) :
    (Ω.graph j).graphMap x' ∈ frontier Ω.carrier := by
  rw [Ω.mem_frontier_iff j hx, (Ω.graph j).proj_graphMap]

/-- **Boundary points in two balls lie on both graphs**: if `γ_j(x') ∈ B_j ∩ B_k`, then
`γ_k(P_k γ_j x') = γ_j x'`. -/
theorem graphMap_proj_graphMap (j k : Fin Ω.N) {x' : (Ω.graph j).hyperplane}
    (hj : (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j))
    (hk : (Ω.graph j).graphMap x' ∈ ball (Ω.center k) (Ω.radius k)) :
    (Ω.graph k).graphMap ((Ω.graph k).proj ((Ω.graph j).graphMap x')) =
      (Ω.graph j).graphMap x' :=
  (Ω.mem_frontier_iff k hk).1 (Ω.graphMap_mem_frontier j hj)

/-- **Resolutions of unity on the boundary exist** (`Rd.exists_smooth_partition`). -/
theorem nonempty_boundaryPartition [FiniteDimensional ℝ V] : Nonempty Ω.BoundaryPartition := by
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_frontier
    (fun j => ball (Ω.center j) (Ω.radius j)) (fun _ => isOpen_ball) Ω.frontier_subset
  exact ⟨⟨ψ, hψ, hψU, hψ1⟩⟩

/-- **Nonnegative resolutions of unity on the boundary exist**: smooth `ψ_j ≥ 0` with
`tsupport ψ_j ⊆ B_j`, `∑_j ψ_j = 1` on `Γ` and `∑_j ψ_j ≤ 1` everywhere, a smooth resolution of
unity subordinate to the boundary balls (`Rd.exists_smooth_partition`). -/
theorem exists_boundaryPartition_nonneg [FiniteDimensional ℝ V] :
    ∃ ψ : Ω.BoundaryPartition, (∀ j y, 0 ≤ ψ.toFun j y) ∧ ∀ y, ∑ j, ψ.toFun j y ≤ 1 := by
  obtain ⟨ψ, hψ, hψU, hψ1, hψ0, hψle⟩ := exists_smooth_partition isClosed_frontier
    (fun j => ball (Ω.center j) (Ω.radius j)) (fun _ => isOpen_ball) Ω.frontier_subset
  exact ⟨⟨ψ, hψ, hψU, hψ1⟩, hψ0, hψle⟩

/-- **Resolutions of unity equal to one near the boundary**: there is a resolution of unity `ψ`
on the boundary with `ψ_j ≥ 0`, `∑_j ψ_j ≤ 1` everywhere and `∑_j ψ_j = 1` on a neighbourhood of
`Γ` (`Rd.exists_smooth_partition_nhds` for the compact `Γ`). -/
theorem exists_boundaryPartition_nhds [FiniteDimensional ℝ V] :
    ∃ ψ : Ω.BoundaryPartition, (∀ j y, 0 ≤ ψ.toFun j y) ∧ (∀ y, ∑ j, ψ.toFun j y ≤ 1) ∧
      ∀ᶠ y in 𝓝ˢ (frontier Ω.carrier), ∑ j, ψ.toFun j y = 1 := by
  obtain ⟨ψ, hψ, hψU, hψ1, hψ0, hψle⟩ := exists_smooth_partition_nhds Ω.isCompact_frontier
    (fun j => ball (Ω.center j) (Ω.radius j)) (fun _ => isOpen_ball) Ω.frontier_subset
  exact ⟨⟨ψ, hψ, hψU, hψ1.self_of_nhdsSet⟩, hψ0, hψle, hψ1⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Almost everywhere on the boundary -/

/-- **Almost everywhere on the boundary**: `∀ᶠ y in Ω.aeBoundary, P y` iff for every `j`,
`P(γ_j x')` holds for almost every `x' ∈ H_j` with `γ_j(x') ∈ B_j`
(`Rd.BoundedLipschitzDomain.eventually_aeBoundary_iff`). The exceptional sets are the null sets of
the surface measure on `Γ`, described in the charts. -/
noncomputable def aeBoundary : Filter V :=
  ⨆ j, Filter.map (Ω.graph j).graphMap (ae (volume : Measure (Ω.graph j).hyperplane)) ⊓
    𝓟 (ball (Ω.center j) (Ω.radius j))

/-- The statements that hold almost everywhere on the boundary. -/
theorem eventually_aeBoundary_iff {P : V → Prop} :
    (∀ᶠ y in Ω.aeBoundary, P y) ↔ ∀ j, ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) → P ((Ω.graph j).graphMap x') := by
  simp only [aeBoundary, eventually_iSup, eventually_inf_principal, eventually_map]

/-- **Chart statements hold almost everywhere on the boundary**: if `P(γ_k x')` holds for almost
every `x' ∈ H_k` with `γ_k(x') ∈ B_k`, then `P` holds almost everywhere on `Γ ∩ B_k`, by the change
of chart (`Rd.LipschitzGraph.ae_proj_graphMap`). -/
theorem eventually_aeBoundary_of_chart (k : Fin Ω.N) {P : V → Prop}
    (h : ∀ᵐ x' ∂(volume : Measure (Ω.graph k).hyperplane),
      (Ω.graph k).graphMap x' ∈ ball (Ω.center k) (Ω.radius k) → P ((Ω.graph k).graphMap x')) :
    ∀ᶠ y in Ω.aeBoundary, y ∈ ball (Ω.center k) (Ω.radius k) → P y := by
  rw [eventually_aeBoundary_iff]
  intro j
  filter_upwards [(Ω.graph j).ae_proj_graphMap (Ω.graph k) h] with x' hx hj hk
  have hA := Ω.graphMap_proj_graphMap j k hj hk
  have h' := hx hA
  rw [hA] at h'
  exact h' hk

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Besov spaces on the boundary -/

variable (p) in
/-- **Besov spaces on the boundary**. The charts follow Schneider–Vybíral, Definition 3.3, in
dimension at least two. The construction uses Lebesgue measure and also covers dimension one.
Here `g ∈ B^s_{p,q}(Γ)` if every chart piece `(ψ_j g) ∘ γ_j` agrees almost everywhere
on `H_j` with some `G_j ∈ L_p(H_j)` with `‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q} < ∞`.
First differences suffice for `0 < s < 1`, the range of the trace theorem. -/
def MemBoundaryBesov (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) (g : V → ℂ) : Prop :=
  ∀ j, ∃ G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane),
    (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) ∧
    ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 G k) < ∞

variable {Ω} in
/-- **Chart pieces see `g` only almost everywhere on `Γ`**: if `g = h` almost everywhere on `Γ`,
then `(ψ_j g) ∘ γ_j = (ψ_j h) ∘ γ_j` almost everywhere on `H_j`, since `ψ_j ≠ 0` only in `B_j`. -/
theorem chart_ae_eq_of_eventuallyEq (ψ : Ω.BoundaryPartition) {g h : V → ℂ}
    (hgh : g =ᶠ[Ω.aeBoundary] h) (j : Fin Ω.N) :
    (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * h ((Ω.graph j).graphMap x') := by
  filter_upwards [(Ω.eventually_aeBoundary_iff.1 hgh) j] with x' hx
  by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
  · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, zero_mul]
  · rw [hx (ψ.mem_ball_of_ne_zero hψ)]

variable {Ω} in
/-- `B^s_{p,q}(Γ)` only sees `g` almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.chart_ae_eq_of_eventuallyEq`). -/
theorem MemBoundaryBesov.congr {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} {g h : V → ℂ}
    (hg : Ω.MemBoundaryBesov p ψ s q g) (hgh : g =ᶠ[Ω.aeBoundary] h) :
    Ω.MemBoundaryBesov p ψ s q h := fun j =>
  let ⟨G, hG, hGfin⟩ := hg j
  ⟨G, hG.trans (chart_ae_eq_of_eventuallyEq ψ hgh j), hGfin⟩

/-! ### The boundary trace -/

/-- **The boundary trace** `Tr_Γ F(y) = ∑_k ψ_k(y) Tr_k F(P_k y)`, with the traces `Tr_k` of the
graph domains `Ω_k` (cone bumps, differences of order `L`). -/
noncomputable def boundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) (L : ℕ)
    (F : Lp ℂ p (volume : Measure V)) (y : V) : ℂ :=
  ∑ k, ψ.toComplex k y * (Ω.graph k).trace hp L F ((Ω.graph k).proj y)

/-- **The boundary trace in a chart**: for `F` with a finite `B^{s+1/p}_{p,q}`-norm of order
`L > s + 1/p` on `V`, `Tr_Γ F(γ_j x') = Tr_j F(x')` for almost every `x' ∈ H_j` with
`γ_j(x') ∈ B_j`. If `ψ_k(γ_j x') ≠ 0`, then `γ_j x' ∈ B_k` lies on the graph of `Ω_k` and
`Tr_k F(P_k γ_j x') = Tr_j F(x')` by the change of chart; and `∑_k ψ_k = 1` on `Γ`. -/
theorem boundaryTrace_graphMap (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) (j : Fin Ω.N) :
    ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) →
        Ω.boundaryTrace ψ hp L F ((Ω.graph j).graphMap x') = (Ω.graph j).trace hp L F x' := by
  have hcc := fun k => (Ω.graph j).trace_ae_eq_trace_comp (Ω.graph k) hp hL hs hsL hq hF
  filter_upwards [ae_all_iff.2 hcc] with x' hx hj
  have hterm : ∀ k, ψ.toComplex k ((Ω.graph j).graphMap x') *
      (Ω.graph k).trace hp L F ((Ω.graph k).proj ((Ω.graph j).graphMap x')) =
        ψ.toComplex k ((Ω.graph j).graphMap x') * (Ω.graph j).trace hp L F x' := fun k => by
    by_cases hψ : ψ.toFun k ((Ω.graph j).graphMap x') = 0
    · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, zero_mul]
    · rw [← hx k (Ω.graphMap_proj_graphMap j k hj (ψ.mem_ball_of_ne_zero hψ))]
  rw [boundaryTrace, Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_mul,
    ψ.sum_toComplex_eq_one (Ω.graphMap_mem_frontier j hj), one_mul]

/-- **The boundary trace does not depend on the resolution of unity**: in every chart both are the
trace of the graph domain. -/
theorem boundaryTrace_eventuallyEq (ψ ψ' : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ' hp L F := by
  refine Ω.eventually_aeBoundary_iff.2 fun j => ?_
  filter_upwards [Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF j,
    Ω.boundaryTrace_graphMap ψ' hp hL hs hsL hq hF j] with x' h1 h2 hj
  rw [h1 hj, h2 hj]

/-- **The boundary trace of continuous functions is the restriction**: if `F` has a continuous
representative `G`, then `Tr_Γ F = G` almost everywhere on `Γ`
(`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). -/
theorem boundaryTrace_eventuallyEq_of_continuous (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞)
    {G : V → ℂ} (hG : Continuous G) (hFG : (F : V → ℂ) =ᵐ[volume] G) :
    Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] G := by
  refine Ω.eventually_aeBoundary_iff.2 fun j => ?_
  filter_upwards [Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF j,
    (Ω.graph j).trace_ae_eq_comp_graphMap hp hL hs hq
      ((Ω.graph j).intrinsicNorm_lt_top_of_modNorm hp L hq hF).1 hG hFG] with x' h1 h2 hj
  rw [h1 hj, h2]
  rfl

/-- **The boundary trace depends only on `F` on `Ω`**: if `F₁ = F₂` almost everywhere on `Ω`, then
`Tr_Γ F₁ = Tr_Γ F₂` almost everywhere on `Γ`, since `Ω` agrees with `Ω_j` on `B_j`
(`Rd.LipschitzGraph.trace_ae_eq_of_ae_eq`). -/
theorem boundaryTrace_congr (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F₁ F₂ : Lp ℂ p (volume : Measure V)}
    (hF₁ : ‖F₁‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F₁ k) < ∞)
    (hF₂ : ‖F₂‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F₂ k) < ∞)
    (h : ∀ᵐ x ∂(volume : Measure V), x ∈ Ω.carrier → F₁ x = F₂ x) :
    Ω.boundaryTrace ψ hp L F₁ =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ hp L F₂ := by
  refine Ω.eventually_aeBoundary_iff.2 fun j => ?_
  have hloc := (Ω.graph j).trace_ae_eq_of_ae_eq hp L hs hq
    ((Ω.graph j).intrinsicNorm_lt_top_of_modNorm hp L hq hF₁).2
    ((Ω.graph j).intrinsicNorm_lt_top_of_modNorm hp L hq hF₂).2
    (isOpen_ball : IsOpen (ball (Ω.center j) (Ω.radius j)))
    (h.mono fun x hx hxd hxb => hx (by
      have hx' : x ∈ (Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j) := ⟨hxd, hxb⟩
      rw [← Ω.inter_ball_eq j le_rfl] at hx'
      exact hx'.1))
  filter_upwards [Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF₁ j,
    Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF₂ j, hloc] with x' h1 h2 h3 hj
  rw [h1 hj, h2 hj, h3 hj]

/-! ### The trace space -/

/-- **The chart pieces of the boundary trace are traces**: `(ψ_j Tr_Γ F) ∘ γ_j = Tr_j(ψ_j F)` almost
everywhere on `H_j` (`Rd.LipschitzGraph.trace_mulLp_ae`). -/
theorem trace_mulLp_ae_boundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) (j : Fin Ω.N) {C : ℝ}
    (hC : ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l (ψ.toComplex j) x‖ ≤ C) :
    (Ω.graph j).trace hp L (mulLp (ψ.contDiff_toComplex j).continuous
      (norm_le_of_iteratedFDeriv_le hC) F) =ᵐ[volume] fun x' =>
        ψ.toComplex j ((Ω.graph j).graphMap x') *
          Ω.boundaryTrace ψ hp L F ((Ω.graph j).graphMap x') := by
  filter_upwards [(Ω.graph j).trace_mulLp_ae hp hL hs hsL hq (ψ.contDiff_toComplex j) hC hF,
    Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF j] with x' h1 h2
  rw [h1]
  by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
  · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, zero_mul]
  · rw [h2 (ψ.mem_ball_of_ne_zero hψ)]

/-- **The trace of an ambient Besov function lies in `B^s_{p,q}(Γ)`**. For `1 ≤ p < ∞`, `0 < s <
1`, `1 ≤ q ≤ ∞`, `s + 1/p < L` and `F` with
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. The chart pieces are the traces of `ψ_j F`
on the graph domains (`Rd.LipschitzGraph.modNorm_trace_le`). -/
theorem memBoundaryBesov_boundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    Ω.MemBoundaryBesov p ψ s q (Ω.boundaryTrace ψ hp L F) := by
  intro j
  obtain ⟨C, hC⟩ := exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j)
    (ψ.hasCompactSupport_toComplex j) L
  have hFj := modNorm_mulLp_lt_top hp (ψ.contDiff_toComplex j) hC hsL hq hF
  obtain ⟨K, hK, hle⟩ := (Ω.graph j).modNorm_trace_le hp L hs hs1 hq
  have hX := ((Ω.graph j).intrinsicNorm_lt_top_of_modNorm hp L hq hFj).1
  exact ⟨_, Ω.trace_mulLp_ae_boundaryTrace ψ hp hL hs hsL hq hF j hC,
    (hle _ hX).trans_lt (ENNReal.mul_lt_top hK.lt_top hX)⟩

/-- **The localised extensions have a finite norm**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞`,
`L ≥ 2`, smooth `ζ_j` with derivatives bounded up to order `L` and `G_j ∈ B^s_{p,q}(H_j)`, the sum
`F = ∑_j ζ_j E_j G_j` of the localised extensions has
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Rd.LipschitzGraph.modNorm_graphExtension_lt_top`, `Rd.modNorm_mulLp_lt_top`,
`Rd.modNorm_finsetSum_lt_top`). -/
theorem modNorm_extensionSum_lt_top (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) {ζ : Fin Ω.N → V → ℂ}
    (hζs : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ζ j)) {C : Fin Ω.N → ℝ}
    (hC : ∀ j, ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l (ζ j) x‖ ≤ C j)
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hGfin : ∀ j, ‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k) < ∞) :
    ‖∑ j, mulLp (hζs j).continuous (norm_le_of_iteratedFDeriv_le (hC j))
        ((Ω.graph j).graphExtension hp 1 (G j))‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (∑ j, mulLp (hζs j).continuous
        (norm_le_of_iteratedFDeriv_le (hC j)) ((Ω.graph j).graphExtension hp 1 (G j))) k) < ∞ :=
  modNorm_finsetSum_lt_top Finset.univ _ hq fun j _ =>
    modNorm_mulLp_lt_top hp (hζs j) (hC j) (add_one_div_toReal_lt hp hs1 hL) hq
      ((Ω.graph j).modNorm_graphExtension_lt_top hp hL hs hs1 hq (hGfin j))

/-- **The boundary trace of the sum of the localised extensions**: for `1 ≤ p < ∞`, `0 < s < 1`,
`1 ≤ q ≤ ∞`, `L ≥ 2`, smooth `ζ_j` with derivatives bounded up to order `L`, `ζ_j ≠ 0` only in
`B_j` and `ζ_j = 1` where `ψ_j ≠ 0`, and chart pieces `G_j ∈ B^s_{p,q}(H_j)` of `g`,
`G_j = (ψ_j g) ∘ γ_j` almost everywhere on `H_j`, the function `F = ∑_j ζ_j E_j G_j` has
`Tr_Γ F = g` almost everywhere on `Γ`. In the chart of `Ω_k`,
`Tr_k(ζ_j E_j G_j) = ζ_j ψ_j g = ψ_j g` by the change of chart
(`Rd.LipschitzGraph.trace_mulLp_ae`, `Rd.LipschitzGraph.trace_ae_eq_trace_comp`,
`Rd.LipschitzGraph.trace_graphExtension`), and `∑_j ψ_j = 1` on `Γ`. -/
theorem boundaryTrace_extensionSum_eventuallyEq (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {ζ : Fin Ω.N → V → ℂ} (hζs : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ζ j))
    (hζB : ∀ j y, ζ j y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j))
    (hζ1 : ∀ j y, ψ.toFun j y ≠ 0 → ζ j y = 1) {C : Fin Ω.N → ℝ}
    (hC : ∀ j, ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l (ζ j) x‖ ≤ C j) {g : V → ℂ}
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hG : ∀ j, (G j : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x'))
    (hGfin : ∀ j, ‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k) < ∞) :
    Ω.boundaryTrace ψ hp L (∑ j, mulLp (hζs j).continuous (norm_le_of_iteratedFDeriv_le (hC j))
      ((Ω.graph j).graphExtension hp 1 (G j))) =ᶠ[Ω.aeBoundary] g := by
  have hL1 : 1 ≤ L := le_trans one_le_two hL
  have hsL := add_one_div_toReal_lt hp hs1 hL
  have hEfin := fun j => (Ω.graph j).modNorm_graphExtension_lt_top hp hL hs hs1 hq (hGfin j)
  have hFfin := fun j => modNorm_mulLp_lt_top hp (hζs j) (hC j) hsL hq (hEfin j)
  have hsum := Ω.modNorm_extensionSum_lt_top hp hL hs hs1 hq hζs hC G hGfin
  refine Ω.eventually_aeBoundary_iff.2 fun k => ?_
  -- the trace in the chart of `Ω_k`
  have htr := (Ω.graph k).trace_finsetSum hp L hs hq Finset.univ
    (F := fun j => mulLp (hζs j).continuous (norm_le_of_iteratedFDeriv_le (hC j))
      ((Ω.graph j).graphExtension hp 1 (G j))) fun j _ => hFfin j
  have hmul := fun j => (Ω.graph k).trace_mulLp_ae hp hL1 hs hsL hq (hζs j) (hC j) (hEfin j)
  have hcc := fun j => (Ω.graph k).trace_ae_eq_trace_comp (Ω.graph j) hp hL1 hs hsL hq (hEfin j)
  have hGj := fun j => (Ω.graph k).ae_proj_graphMap (Ω.graph j) (hG j)
  filter_upwards [Ω.boundaryTrace_graphMap ψ hp hL1 hs hsL hq hsum k,
    Lp.coeFn_fun_finsetSum Finset.univ fun j => (Ω.graph k).trace hp L
      (mulLp (hζs j).continuous (norm_le_of_iteratedFDeriv_le (hC j))
        ((Ω.graph j).graphExtension hp 1 (G j))),
    ae_all_iff.2 hmul, ae_all_iff.2 hcc, ae_all_iff.2 hGj] with x' h1 h2 h3 h4 h5 hk
  have hΓ := Ω.graphMap_mem_frontier k hk
  have hterm : ∀ j, (Ω.graph k).trace hp L (mulLp (hζs j).continuous
      (norm_le_of_iteratedFDeriv_le (hC j)) ((Ω.graph j).graphExtension hp 1 (G j))) x' =
        ψ.toComplex j ((Ω.graph k).graphMap x') * g ((Ω.graph k).graphMap x') := fun j => by
    rw [h3 j]
    by_cases hζ : ζ j ((Ω.graph k).graphMap x') = 0
    · have hψ : ψ.toFun j ((Ω.graph k).graphMap x') = 0 := by
        by_contra hψ
        rw [hζ1 j _ hψ] at hζ
        exact one_ne_zero hζ
      rw [hζ, ψ.toComplex_of_eq_zero hψ, zero_mul, zero_mul]
    · have hA := Ω.graphMap_proj_graphMap k j hk (hζB j _ hζ)
      have h5' := h5 j hA
      rw [hA] at h5'
      rw [h4 j hA, (Ω.graph j).trace_graphExtension hp hL hs hs1 hq (hGfin j), h5']
      by_cases hψ : ψ.toFun j ((Ω.graph k).graphMap x') = 0
      · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, mul_zero]
      · rw [hζ1 j _ hψ, one_mul]
  rw [h1 hk, htr, h2, Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul,
    ψ.sum_toComplex_eq_one hΓ, one_mul]

/-- **Every function of `B^s_{p,q}(Γ)` is the trace of an ambient representative**. For `1 ≤ p <
∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, every
`g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for some `F` with
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. With the chart pieces `G_j` of `g`,
`F = ∑_j ζ_j E_j G_j` with the extensions `E_j` of the graph domains
(`Rd.LipschitzGraph.graphExtension`) and the cut-offs `ζ_j`
(`Rd.BoundedLipschitzDomain.BoundaryPartition.exists_cutoff`,
`Rd.BoundedLipschitzDomain.boundaryTrace_extensionSum_eventuallyEq`). -/
theorem exists_boundaryTrace_eq (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov p ψ s q g) :
    ∃ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞ ∧
      Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] g := by
  choose G hG hGfin using hg
  choose ζ hζs hζc hζB hζ1 using ψ.exists_cutoff
  choose C hC using fun j => exists_iteratedFDeriv_bound (hζs j) (hζc j) L
  exact ⟨_, Ω.modNorm_extensionSum_lt_top hp hL hs hs1 hq hζs hC G hGfin,
    Ω.boundaryTrace_extensionSum_eventuallyEq ψ hp hL hs hs1 hq hζs hζB hζ1 hC G hG hGfin⟩

/-- **The trace space of a bounded Lipschitz domain, specified using ambient functions**. For `1
≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff
`g = Tr_Γ F` almost everywhere on `Γ` for some `F` with
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem exists_boundaryTrace_eq_iff (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) (g : V → ℂ) :
    (∃ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞ ∧
      Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] g) ↔ Ω.MemBoundaryBesov p ψ s q g := by
  refine ⟨fun ⟨F, hF, hFg⟩ => ?_, Ω.exists_boundaryTrace_eq ψ hp hL hs hs1 hq⟩
  exact (Ω.memBoundaryBesov_boundaryTrace ψ hp (le_trans one_le_two hL) hs hs1
    (add_one_div_toReal_lt hp hs1 hL) hq hF).congr hFg

/-- **`B^s_{p,q}(Γ)` does not depend on the resolution of unity**: for two resolutions `ψ`, `ψ'`,
both spaces consist of the boundary traces, which agree almost everywhere on `Γ`. -/
theorem memBoundaryBesov_iff_of_boundaryPartition (ψ ψ' : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) (g : V → ℂ) :
    Ω.MemBoundaryBesov p ψ s q g ↔ Ω.MemBoundaryBesov p ψ' s q g := by
  have hsL := add_one_div_toReal_lt hp hs1 (le_refl 2)
  rw [← Ω.exists_boundaryTrace_eq_iff ψ hp le_rfl hs hs1 hq,
    ← Ω.exists_boundaryTrace_eq_iff ψ' hp le_rfl hs hs1 hq]
  exact exists_congr fun F => and_congr_right fun hF =>
    ⟨fun h => (Ω.boundaryTrace_eventuallyEq ψ' ψ hp one_le_two hs hsL hq hF).trans h,
      fun h => (Ω.boundaryTrace_eventuallyEq ψ ψ' hp one_le_two hs hsL hq hF).trans h⟩

/-- `g` is **the boundary trace of `f`**: `Tr_Γ F = g` almost everywhere on `Γ` for every `F` with
`F = f` on `Ω` and `‖F‖_p + ‖(2^(kσ) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. For `f` with a finite
intrinsic norm on `Ω`, `0 < σ < L` and `1 ≤ q` such `F` exist
(`Rd.BoundedLipschitzDomain.exists_besov_extension_of_modulusOn`), and they all have the same
boundary trace (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`). The predicate makes a statement
only when an admissible `F` exists; `Rd.BoundedLipschitzDomain.HasBoundaryTrace` adds the finite
intrinsic norm. -/
def IsBoundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) (L : ℕ) (σ : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) (g : V → ℂ) : Prop :=
  ∀ F : Lp ℂ p (volume : Measure V), indicatorLp Ω.measurableSet F = indicatorLp Ω.measurableSet f →
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulus p L F k) < ∞ →
      Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] g

/-- **The intrinsic trace space of `B^{s+1/p}_{p,q}(Ω)`**. This is the ambient-extension
form of the trace-space equality of Schneider–Vybíral, Theorem 4.11, in the range below.
Their theorem assumes dimension at least two. The Lean result also covers dimension one.
For `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff `g` is the
boundary trace of some `f` with
`‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. -/
theorem memBoundaryBesov_iff_exists_isBoundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : V → ℂ) :
    Ω.MemBoundaryBesov p ψ s q g ↔ ∃ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet L (s + 1 / p.toReal) q f < ∞ ∧
      Ω.IsBoundaryTrace ψ hp L (s + 1 / p.toReal) q f g := by
  have hsL := add_one_div_toReal_lt hp hs1 hL
  have hL1 : 1 ≤ L := le_trans one_le_two hL
  constructor
  · intro hg
    obtain ⟨F, hF, hFg⟩ := Ω.exists_boundaryTrace_eq ψ hp hL hs hs1 hq hg
    refine ⟨F, (modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet L _ q rfl).trans_lt hF,
      fun F' hF'F hF' => ?_⟩
    exact (Ω.boundaryTrace_congr ψ hp hL1 hs hsL hq hF' hF
      (ae_eq_of_indicatorLp_eq Ω.measurableSet hF'F)).trans hFg
  · rintro ⟨f, hf, hfg⟩
    obtain ⟨F, hFf, hF⟩ := Ω.exists_besov_extension_of_modulusOn hp (by positivity) hsL hq hf
    exact (Ω.memBoundaryBesov_boundaryTrace ψ hp hL1 hs hs1 hsL hq hF).congr (hfg F hFf hF)

/-- **Existence of the boundary trace**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`,
every `f` with `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` has a boundary
trace `g ∈ B^s_{p,q}(Γ)`, namely `Tr_Γ F` for an extension `F` of `f`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_of_modulusOn`). -/
theorem exists_isBoundaryTrace_of_modNormOn_lt_top (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet L (s + 1 / p.toReal) q f < ∞) :
    ∃ g : V → ℂ, Ω.MemBoundaryBesov p ψ s q g ∧
      Ω.IsBoundaryTrace ψ hp L (s + 1 / p.toReal) q f g := by
  have hsL := add_one_div_toReal_lt hp hs1 hL
  have hL1 : 1 ≤ L := le_trans one_le_two hL
  obtain ⟨F, hFf, hF⟩ := Ω.exists_besov_extension_of_modulusOn hp (by positivity) hsL hq hf
  refine ⟨Ω.boundaryTrace ψ hp L F, Ω.memBoundaryBesov_boundaryTrace ψ hp hL1 hs hs1 hsL hq hF,
    fun F' hF'f hF' => ?_⟩
  exact Ω.boundaryTrace_congr ψ hp hL1 hs hsL hq hF' hF
    (ae_eq_of_indicatorLp_eq Ω.measurableSet (hF'f.trans hFf.symm))

variable {Ω} in
/-- **Uniqueness of the boundary trace**: for `1 ≤ p < ∞`, `0 < σ < L` and `1 ≤ q ≤ ∞`, two
boundary traces `g`, `g'` of an `f` with
`‖f‖_{L_p(Ω)} + ‖(2^(kσ) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` agree almost everywhere on `Γ`: both
are `Tr_Γ F` for one extension `F` of `f`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_of_modulusOn`). -/
theorem IsBoundaryTrace.unique {ψ : Ω.BoundaryPartition} {hp : p ≠ ∞} {L : ℕ} {σ : ℝ}
    (hσ : 0 < σ) (hσL : σ < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet L σ q f < ∞) {g g' : V → ℂ}
    (hg : Ω.IsBoundaryTrace ψ hp L σ q f g) (hg' : Ω.IsBoundaryTrace ψ hp L σ q f g') :
    g =ᶠ[Ω.aeBoundary] g' := by
  obtain ⟨F, hFf, hF⟩ := Ω.exists_besov_extension_of_modulusOn hp hσ hσL hq hf
  exact (hg F hFf hF).symm.trans (hg' F hFf hF)

/-! ### Boundary traces of functions with a finite intrinsic norm -/

/-- `f` **has the boundary trace `g`**: `f` has a finite intrinsic norm on `Ω`,
`‖f‖_{L_p(Ω)} + ‖(2^(kσ) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, and `g` is the boundary trace of `f`
in the sense of `Rd.BoundedLipschitzDomain.IsBoundaryTrace`: `Tr_Γ F = g` almost everywhere on `Γ`
for every `F` with `F = f` on `Ω` and `‖F‖_p + ‖(2^(kσ) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. For
`0 < σ < L` and `1 ≤ q` the finite intrinsic norm provides such an `F`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_of_modulusOn`), so the trace condition is a
statement about at least one extension. -/
structure HasBoundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) (L : ℕ) (σ : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) (g : V → ℂ) : Prop where
  /-- The intrinsic quasi-norm
  `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(kσ) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}` of `f` on `Ω`
  (`Rd.modNormOn`) is finite, as in the hypotheses of the `IsBoundaryTrace` theorems above. -/
  modNormOn_lt_top : modNormOn Ω.measurableSet L σ q f < ∞
  /-- `g` is the boundary trace of every admissible extension of `f`. -/
  isBoundaryTrace : Ω.IsBoundaryTrace ψ hp L σ q f g

/-- `f` **has the boundary trace `g`** iff the intrinsic norm
`‖f‖_{L_p(Ω)} + ‖(2^(kσ) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}` is finite and `g` is the boundary trace of
`f` in the sense of `Rd.BoundedLipschitzDomain.IsBoundaryTrace`: the two fields of
`Rd.BoundedLipschitzDomain.HasBoundaryTrace`. -/
theorem hasBoundaryTrace_iff {ψ : Ω.BoundaryPartition} {hp : p ≠ ∞} {L : ℕ} {σ : ℝ} {q : ℝ≥0∞}
    {f : Lp ℂ p (volume : Measure V)} {g : V → ℂ} :
    Ω.HasBoundaryTrace ψ hp L σ q f g ↔
      modNormOn Ω.measurableSet L σ q f < ∞ ∧
      Ω.IsBoundaryTrace ψ hp L σ q f g :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The trace space of `B^{s+1/p}_{p,q}(Ω)`**, with `Rd.BoundedLipschitzDomain.HasBoundaryTrace`:
for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff some `f` with a
finite intrinsic norm of order `s + 1/p` on `Ω` has the boundary trace `g`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`). -/
theorem memBoundaryBesov_iff_exists_hasBoundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : V → ℂ) :
    Ω.MemBoundaryBesov p ψ s q g ↔ ∃ f : Lp ℂ p (volume : Measure V),
      Ω.HasBoundaryTrace ψ hp L (s + 1 / p.toReal) q f g := by
  simp only [hasBoundaryTrace_iff]
  exact Ω.memBoundaryBesov_iff_exists_isBoundaryTrace ψ hp hL hs hs1 hq g

/-- **Boundary traces lie in `B^s_{p,q}(Γ)`**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and
`L ≥ 2`, if `f` has the boundary trace `g` for the order `s + 1/p`, then `g ∈ B^s_{p,q}(Γ)`. -/
theorem HasBoundaryTrace.memBoundaryBesov {ψ : Ω.BoundaryPartition} {hp : p ≠ ∞} {L : ℕ}
    (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} {g : V → ℂ}
    (h : Ω.HasBoundaryTrace ψ hp L (s + 1 / p.toReal) q f g) : Ω.MemBoundaryBesov p ψ s q g :=
  (Ω.memBoundaryBesov_iff_exists_hasBoundaryTrace ψ hp hL hs hs1 hq g).2 ⟨f, h⟩

/-- **Existence of the boundary trace**, with `Rd.BoundedLipschitzDomain.HasBoundaryTrace`: for
`1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, every `f` with
`‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` has a boundary trace
`g ∈ B^s_{p,q}(Γ)` (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_modNormOn_lt_top`). -/
theorem exists_hasBoundaryTrace_of_modNormOn_lt_top (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet L (s + 1 / p.toReal) q f < ∞) :
    ∃ g : V → ℂ, Ω.MemBoundaryBesov p ψ s q g ∧
      Ω.HasBoundaryTrace ψ hp L (s + 1 / p.toReal) q f g := by
  obtain ⟨g, hg, hfg⟩ := Ω.exists_isBoundaryTrace_of_modNormOn_lt_top ψ hp hL hs hs1 hq hf
  exact ⟨g, hg, hf, hfg⟩

variable {Ω} in
/-- **Uniqueness of the boundary trace**, with `Rd.BoundedLipschitzDomain.HasBoundaryTrace`: for
`1 ≤ p < ∞`, `0 < σ < L` and `1 ≤ q ≤ ∞`, two boundary traces `g`, `g'` of `f` agree almost
everywhere on `Γ` (`Rd.BoundedLipschitzDomain.IsBoundaryTrace.unique`). -/
theorem HasBoundaryTrace.unique {ψ : Ω.BoundaryPartition} {hp : p ≠ ∞} {L : ℕ} {σ : ℝ}
    (hσ : 0 < σ) (hσL : σ < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    {g g' : V → ℂ} (hg : Ω.HasBoundaryTrace ψ hp L σ q f g)
    (hg' : Ω.HasBoundaryTrace ψ hp L σ q f g') : g =ᶠ[Ω.aeBoundary] g' :=
  hg.isBoundaryTrace.unique hσ hσL hq hg.modNormOn_lt_top hg'.isBoundaryTrace

end BoundedLipschitzDomain

end Rd
