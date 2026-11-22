/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-! # Complete connected Riemannian manifolds are proper

The connected Riemannian extended metric gives a metric space. Tau Ceti’s Hopf–Rinow theorem
then supplies compact closed balls and sigma compactness for the weighted development.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Proper

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

include F


omit [FiniteDimensional ℝ F] in
/-- On a connected Riemannian manifold the distance is finite. -/
theorem edist_ne_top_of_connected [ConnectedSpace M] (x y : M) : edist x y ≠ ⊤ := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, F)) (n := ∞)
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F))]
  exact TauCeti.Manifold.riemannianEDist_ne_top 𝓘(ℝ, F) x y

/-- The real-valued Riemannian distance on a connected Riemannian manifold (same `edist`,
same uniformity as the given `EMetricSpace`). -/
noncomputable abbrev riemannianMetricSpace [ConnectedSpace M] : MetricSpace M :=
  EMetricSpace.toMetricSpace (edist_ne_top_of_connected F)

/-- **Hopf–Rinow–Cohn-Vossen**: a complete connected Riemannian manifold is proper. -/
theorem properSpace_of_complete_riemannian [ConnectedSpace M] [CompleteSpace M] :
    @ProperSpace M (riemannianMetricSpace F).toPseudoMetricSpace := by
  let : MetricSpace M := riemannianMetricSpace F
  exact TauCeti.Manifold.properSpace_of_completeSpace 𝓘(ℝ, F)

/-- Edist-closed balls of a complete connected Riemannian manifold are compact. -/
theorem isCompact_edist_le [ConnectedSpace M] [CompleteSpace M] (x₀ : M) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact {y : M | edist x₀ y ≤ ENNReal.ofReal r} := by
  let : MetricSpace M := riemannianMetricSpace F
  have := properSpace_of_complete_riemannian (F := F) (M := M)
  have h := isCompact_closedBall x₀ r
  convert h using 1
  ext y
  simp only [mem_ofPred_eq, Metric.mem_closedBall]
  rw [edist_le_ofReal hr, dist_comm]

/-- A complete connected Riemannian manifold is `σ`-compact. -/
theorem sigmaCompactSpace_of_complete_riemannian [ConnectedSpace M] [CompleteSpace M] :
    SigmaCompactSpace M := by
  let : MetricSpace M := riemannianMetricSpace F
  have := properSpace_of_complete_riemannian (F := F) (M := M)
  infer_instance

end Proper

end CutCur
