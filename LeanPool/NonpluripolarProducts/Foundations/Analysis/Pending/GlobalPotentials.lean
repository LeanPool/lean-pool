/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothThetaCriterion
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Chart and local-potential compatibility

The quasi-plurisubharmonic germ condition is invariant under a holomorphic chart change.
The complex manifold structure is explicit, with the model space `ℂⁿ` carrying its usual real
scalar action.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

/-- A local quasi-PSH decomposition is invariant under a holomorphic chart
transition. This composition uses the separately named Pending general PSH
pullback input; there is no additional chart-invariance hole. -/
theorem quasiPlurisubharmonicAt_chart_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (u : M → EReal) (e f : ComplexChart n M)
    (x : M) (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    QuasiPlurisubharmonicAt (chartFunction u e) (e.val x) ↔
      QuasiPlurisubharmonicAt (chartFunction u f) (f.val x) := by
  have transport (a b : ComplexChart n M) (ha : x ∈ a.val.source)
      (hb : x ∈ b.val.source)
      (hu : QuasiPlurisubharmonicAt (chartFunction u a) (a.val x)) :
      QuasiPlurisubharmonicAt (chartFunction u b) (b.val x) := by
    let F := FirstPass.HolomorphicMaps.coordinateMap (id : M → M) b a
    let U := FirstPass.HolomorphicMaps.coordinateDomain (id : M → M) b a
    have hU : IsOpen U :=
      FirstPass.HolomorphicMaps.coordinateDomain_isOpen contMDiff_id b a
    have hxU : b.val x ∈ U :=
      FirstPass.HolomorphicMaps.mem_coordinateDomain hb ha
    have huF : QuasiPlurisubharmonicAt (chartFunction u a) (F (b.val x)) := by
      simpa only [F, FirstPass.HolomorphicMaps.coordinateMap_at hb, id_eq] using hu
    have hp := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic hU
      (FirstPass.HolomorphicMaps.coordinateMap_contDiffOn contMDiff_id b a) hxU huF
    apply hp.congr
    filter_upwards [hU.mem_nhds hxU] with y hy
    change u (a.val.symm (a.val (b.val.symm y))) = u (b.val.symm y)
    exact congrArg u (a.val.left_inv hy.2)
  exact ⟨transport e f he hf, transport f e hf he⟩

end SGPT.Foundations.Analysis.Pending
