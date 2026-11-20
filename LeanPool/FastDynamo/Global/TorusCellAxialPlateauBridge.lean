/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusAxialVelocityWeakTransfer

/-!
# The axial plateau on a placed three-quarter buffer

This leaf collects the exact geometry and coefficient identities used when a
placed cell is viewed on the closed Euclidean core of radius
`3 R_m / 4`.  On that core
the axial cutoff is exactly one, its two stored transverse derivatives are
zero, and the descended axial correction is the constant vector
`a_m e₃`.  The statements are given both in Euclidean chart coordinates and
through the canonical `(0,1]²` torus representative.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set WithLp
open scoped ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-! ## Closed three-quarter buffer geometry -/

/-- A point in the closed three-quarter Euclidean core is strictly inside
the open product-metric buffer ball: the product metric is dominated by the
Euclidean one. -/
theorem mem_bufferDisk_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (m : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    x ∈ P.scaleFamily.bufferDisk m := by
  have hd := dist_le_pairEuclideanDist x (P.scaleFamily.cellCenter m)
  rw [ScaleFamily.bufferDisk, mem_ball]
  linarith [P.scaleFamily.bufferRadius_pos m]

/-- Consequently the whole closed three-quarter Euclidean core lies in
the fixed placement chart. -/
theorem mem_placementChart_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (m : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    x ∈ ScaleFamily.placementChart :=
  P.bufferDisk_subset_chart m
    (P.mem_bufferDisk_of_dist_le_three_quarters m hx)

/-- There is no quotient wrap on the closed three-quarter Euclidean core: its
canonical torus representative is the original Euclidean point. -/
theorem transverseIocRepresentative_eq_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (m : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    transverseIocRepresentative (transverseTorusPoint x) = x :=
  transverseIocRepresentative_transverseTorusPoint_of_mem_placementChart
    (P.mem_placementChart_of_dist_le_three_quarters m hx)

/-- The canonical representative version of three-quarter-buffer torus
membership. -/
theorem mem_torusBufferDisk_of_representative_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (m : ℕ)
    {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q)
        (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    q ∈ P.torusBufferDisk m := by
  rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative m q]
  exact P.mem_bufferDisk_of_dist_le_three_quarters m hq

/-! ## Euclidean plateau and derivative identities -/

/-- The fixed plateau has zero Fréchet derivative everywhere on its closed
unit-value core, the Euclidean disc of radius `3 / 4`, boundary included. -/
theorem fderiv_axialPlateau_eq_zero_of_norm_le_three_quarters
    {x : ℝ × ℝ} (hx : ‖pairToWholePlane x‖ ≤ 3 / 4) :
    fderiv ℝ axialPlateauBump x = 0 := by
  have hone : axialPlateauBump x = 1 :=
    axialPlateau_eq_one_of_norm_pairToWholePlane_le hx
  have hmax : IsLocalMax axialPlateauBump x :=
    Filter.Eventually.of_forall (fun y ↦ by
      rw [hone]
      exact axialPlateau_le_one y)
  exact hmax.fderiv_eq_zero

/-- Both coordinate derivatives of the scaled axial cutoff vanish throughout
the closed three-quarter Euclidean core. -/
theorem axialCellCutoffDerivative_eq_zero_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (m : ℕ)
    (j : Fin 2) {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialCellCutoffDerivative m j x = 0 := by
  have hnorm : ‖pairToWholePlane (P.axialBufferCoordinate m x)‖ ≤ 3 / 4 := by
    rw [P.norm_pairToWholePlane_axialBufferCoordinate m x]
    apply (div_le_iff₀ (P.scaleFamily.bufferRadius_pos m)).2
    nlinarith
  rw [axialCellCutoffDerivative,
    fderiv_axialPlateau_eq_zero_of_norm_le_three_quarters hnorm]
  simp

/-- The displayed Euclidean transverse derivative of the axial correction
vanishes on the plateau. -/
theorem axialOffsetEuclideanDerivative_eq_zero_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    (j : Fin 2) {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetEuclideanDerivative tau m j x = 0 := by
  simp [axialOffsetEuclideanDerivative,
    P.axialCellCutoffDerivative_eq_zero_of_dist_le_three_quarters m j hx]

/-! ## Descended cutoff and torus identities -/

/-- The descended axial cell is the constant axial shift of the paper on the closed
three-quarter Euclidean core, stated through the canonical representative. -/
theorem axialOffsetTorus_eq_axialAmplitude_of_representative_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q)
        (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetTorus tau m q =
      P.scaleFamily.axialAmplitude tau m • axialUnitR3 := by
  rw [← transverseTorusPoint_transverseIocRepresentative q]
  exact P.axialOffsetTorus_eq_axialAmplitude_of_core tau m hq

/-- Each descended displayed derivative vanishes on the closed
three-quarter Euclidean core. -/
theorem axialOffsetTorusDerivative_eq_zero_of_dist_le_three_quarters
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    (j : Fin 2) {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetTorusDerivative tau m j (transverseTorusPoint x) = 0 := by
  have hchart := P.mem_placementChart_of_dist_le_three_quarters m hx
  have hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  have hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩
  rw [AxialWeakTransfer.axialOffsetTorusDerivative_transverseTorusPoint_eq_euclidean_of_mem_Ioc
    P tau m j hxzero hxone]
  exact P.axialOffsetEuclideanDerivative_eq_zero_of_dist_le_three_quarters
    tau m j hx

/-- Canonical-representative version of the zero derivative identity. -/
theorem axialOffsetTorusDerivative_eq_zero_of_representative_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    (j : Fin 2) {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q)
        (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetTorusDerivative tau m j q = 0 := by
  rw [← transverseTorusPoint_transverseIocRepresentative q]
  exact P.axialOffsetTorusDerivative_eq_zero_of_dist_le_three_quarters
    tau m j hq

/-! ## Global disjoint sum and stored weak derivatives -/

/-- On the three-quarter core, the global axial sum is exactly the one
constant cell contribution. -/
theorem axialOffsetGlobalTorus_eq_axialAmplitude_of_representative_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q)
        (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetGlobalTorus tau q =
      P.scaleFamily.axialAmplitude tau m • axialUnitR3 := by
  rw [P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau
    (P.mem_torusBufferDisk_of_representative_dist_le_three_quarters m hq)]
  exact P.axialOffsetTorus_eq_axialAmplitude_of_representative_core tau m hq

/-- Each displayed derivative of the global disjoint axial sum vanishes on
the three-quarter core. -/
theorem axialOffsetGlobalTorusDerivative_eq_zero_of_representative_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (m : ℕ)
    (j : Fin 2) {q : TransverseTorus}
    (hq : pairEuclideanDist (transverseIocRepresentative q)
        (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4) :
    P.axialOffsetGlobalTorusDerivative tau j q = 0 := by
  rw [P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau
    (P.mem_torusBufferDisk_of_representative_dist_le_three_quarters m hq) j]
  exact P.axialOffsetTorusDerivative_eq_zero_of_representative_core
    tau m j hq

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
