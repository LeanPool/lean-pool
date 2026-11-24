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

This namespace retains compatibility declarations used by Pending modules.
Chart independence, local-potential independence, and the smooth theta-PSH
criterion are now proved through the checked core.
The complex manifold structure appears explicitly in every signature. The
model space is the concrete finite-dimensional `ℂⁿ` with its standard compatible
real scalar action. No measure or distribution is used by these statements.
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

/-- Two smooth potentials for the same form differ by a
pluriharmonic function on their common open domain. Thus the PSH correction
criterion is independent of the chosen potential, also at poles of `u`. -/
theorem smoothLocalPotential_psh_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (θ : SmoothRealForm n M 2) (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (ρ σ : ComplexModel n → ℝ)
    (hρ : IsSmoothLocalPotential θ e W ρ) (hσ : IsSmoothLocalPotential θ e W σ)
    (u : ComplexModel n → EReal) :
    PlurisubharmonicOn (fun z => u z + (ρ z : EReal)) W ↔
      PlurisubharmonicOn (fun z => u z + (σ z : EReal)) W := by
  exact FirstPass.smoothLocalPotential_psh_iff θ e W ρ σ hρ hσ u

/-- For a form with local potentials and a smooth real function,
the local PSH definition is precisely semipositivity of `θ + ddᶜu` on complex
lines. The local-potential hypothesis is essential and explicit: this does not
assert that arbitrary smooth two-forms have local potentials. -/
theorem thetaPlurisubharmonic_smooth_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (θ : SmoothRealForm n M 2)
    (hθ : HasSmoothLocalPotentials θ) (u : M → ℝ) (hu : ChartSmooth (n := n) u) :
    ThetaPlurisubharmonic θ (fun x => (u x : EReal)) ↔
      ∀ (e : ComplexChart n M) z, z ∈ e.val.target → ∀ v : ComplexModel n,
        0 ≤ θ.coeff e z ![v, Complex.I • v] +
          smoothDDC (fun y => u (e.val.symm y)) z ![v, Complex.I • v] := by
  exact FirstPass.thetaPlurisubharmonic_smooth_iff θ hθ u hu

end SGPT.Foundations.Analysis.Pending
