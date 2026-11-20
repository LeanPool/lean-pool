/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusAxialVelocityChartFields

/-!
# The concrete added axial velocity: descent to the transverse torus

`Global/TorusAxialVelocityChartFields.lean` builds the smooth Euclidean chart fields
`a_n * vartheta (|y - p_n| / R_n) * e_3` of `eq:axial-offset` together with
their constant-core and support statements, their displayed classical derivatives and the
divergence cancellation.

This module descends those fields and their derivative representatives to the transverse torus
through the measurable periodization already supplied by `TorusChartWeakTransfer`, and proves
the pointwise summability and the disjoint-support formulae of the global axial series.  The
final identification of the descended derivative representatives as Fourier weak derivatives
is a quotient integration by parts, carried out downstream in
`Global/TorusAxialVelocityWeakTransfer.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-! ## Measurable descent to the transverse torus -/

/-- The `n`th concrete axial correction on the transverse torus. -/
def axialOffsetTorus
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ) :
    TransverseTorus → R3 :=
  P.torusPeriodizedExtension n (P.axialOffsetEuclidean tau n)

/-- Its descended displayed transverse derivative. -/
def axialOffsetTorusDerivative
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) : TransverseTorus → R3 :=
  P.torusPeriodizedExtension n (P.axialOffsetEuclideanDerivative tau n j)

/-- The descended `n`-th axial correction on the transverse torus is measurable. -/
theorem measurable_axialOffsetTorus
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ) :
    Measurable (P.axialOffsetTorus tau n) :=
  P.measurable_torusPeriodizedExtension n _
    (P.axialOffsetEuclidean_measurable tau n)

/-- The descended `n`-th displayed transverse derivative is measurable. -/
theorem measurable_axialOffsetTorusDerivative
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) : Measurable (P.axialOffsetTorusDerivative tau n j) :=
  P.measurable_torusPeriodizedExtension n _
    (P.axialOffsetEuclideanDerivative_measurable tau n j)

/-- The descended axial correction vanishes outside the placed torus buffer disc of its own
cell. -/
theorem axialOffsetTorus_eq_zero_of_not_mem_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    {q : TransverseTorus} (hq : q ∉ P.torusBufferDisk n) :
    P.axialOffsetTorus tau n q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n _ hq

/-- The descended displayed derivative vanishes outside the placed torus buffer disc of its own
cell. -/
theorem axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (j : Fin 2) {q : TransverseTorus} (hq : q ∉ P.torusBufferDisk n) :
    P.axialOffsetTorusDerivative tau n j q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n _ hq

/-- Disjointness of the placed buffer discs: the `n`-th axial correction vanishes at every point
of the buffer disc of a different cell `m ≠ n`.  This is what makes the global sum a
disjoint-support series. -/
theorem axialOffsetTorus_eq_zero_on_other_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {n m : ℕ} (hnm : n ≠ m) {q : TransverseTorus}
    (hq : q ∈ P.torusBufferDisk m) : P.axialOffsetTorus tau n q = 0 := by
  apply P.axialOffsetTorus_eq_zero_of_not_mem_buffer tau n
  intro hn
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt)) hn hq
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt)) hq hn

/-- Disjointness of the placed buffer discs for the displayed derivatives: the `n`-th derivative
vanishes on the buffer disc of any other cell `m ≠ n`. -/
theorem axialOffsetTorusDerivative_eq_zero_on_other_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {n m : ℕ} (hnm : n ≠ m) (j : Fin 2) {q : TransverseTorus}
    (hq : q ∈ P.torusBufferDisk m) :
    P.axialOffsetTorusDerivative tau n j q = 0 := by
  apply P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau n j
  intro hn
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt)) hn hq
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt)) hq hn

/-- Exact core value after descent, stated through a Euclidean chart point. -/
theorem axialOffsetTorus_eq_axialAmplitude_of_core
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    {x : ℝ × ℝ}
    (hx : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4) :
    P.axialOffsetTorus tau n (transverseTorusPoint x) =
      P.scaleFamily.axialAmplitude tau n • axialUnitR3 := by
  have hbuffer : x ∈ P.scaleFamily.bufferDisk n := by
    have hR := P.scaleFamily.bufferRadius_pos n
    have hd := dist_le_pairEuclideanDist x (P.scaleFamily.cellCenter n)
    simp only [ScaleFamily.bufferDisk, mem_ball]
    linarith
  change P.periodizedExtension n (P.axialOffsetEuclidean tau n) x = _
  rw [P.periodizedExtension_eq_source n (P.axialOffsetEuclidean tau n) hbuffer]
  exact P.axialOffsetEuclidean_eq_axialAmplitude_of_core tau n hx

/-- Uniform pointwise bound on the descended axial correction: `‖u_n^ax‖ ≤ a_n`, the cell's axial
amplitude, for `tau ≥ 0`. -/
theorem norm_axialOffsetTorus_le
    (P : TorusCellPlacement (r := r) supportRadius) {tau : ℝ} (htau : 0 ≤ tau)
    (n : ℕ) (q : TransverseTorus) :
    ‖P.axialOffsetTorus tau n q‖ ≤
      P.scaleFamily.axialAmplitude tau n := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [axialOffsetTorus, torusPeriodizedExtension, dite_eq_left hq]
    exact P.norm_axialOffsetEuclidean_le htau n _
  · rw [P.axialOffsetTorus_eq_zero_of_not_mem_buffer tau n hq, norm_zero]
    unfold ScaleFamily.axialAmplitude
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.ell_pos n).le

/-- Uniform pointwise bound on the descended displayed derivative:
`‖∇u_n^ax‖ ≤ ‖ϑ'‖_∞ (a_n / R_n)`, the paper's gradient estimate for the added axial
velocity (§3.3, after `eq:axial-offset`). -/
theorem norm_axialOffsetTorusDerivative_le
    (P : TorusCellPlacement (r := r) supportRadius) {tau : ℝ} (htau : 0 ≤ tau)
    (n : ℕ) (j : Fin 2) (q : TransverseTorus) :
    ‖P.axialOffsetTorusDerivative tau n j q‖ ≤
      (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [axialOffsetTorusDerivative, torusPeriodizedExtension, dite_eq_left hq]
    exact P.norm_axialOffsetEuclideanDerivative_le htau n j _
  · rw [P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau n j hq,
      norm_zero]
    exact mul_nonneg (NNReal.coe_nonneg _)
      (by rw [P.scaleFamily.axialGradientScale_formula tau n]
          exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
            (P.scaleFamily.bufferRadius_nonneg n))

/-- The descended field is purely axial, so its transverse divergence
`∂_1 (u_n^ax)_1 + ∂_2 (u_n^ax)_2` vanishes pointwise on the torus. -/
theorem axialOffsetTorusDerivative_transverseDivergence
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ) (n : ℕ)
    (q : TransverseTorus) :
    P.axialOffsetTorusDerivative tau n 0 q 0 +
      P.axialOffsetTorusDerivative tau n 1 q 1 = 0 := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · simp only [axialOffsetTorusDerivative, torusPeriodizedExtension,
      dite_eq_left hq]
    exact P.axialOffsetEuclideanDerivative_transverseDivergence tau n _
  · rw [P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau n 0 hq,
      P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau n 1 hq]
    simp

/-! ## Disjoint-support global series -/

/-- The pointwise sum of all added axial velocities. -/
def axialOffsetGlobalTorus
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    (q : TransverseTorus) : R3 :=
  ∑' n : ℕ, P.axialOffsetTorus tau n q

/-- The pointwise sum of one displayed transverse derivative. -/
def axialOffsetGlobalTorusDerivative
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    (j : Fin 2) (q : TransverseTorus) : R3 :=
  ∑' n : ℕ, P.axialOffsetTorusDerivative tau n j q

/-- Inside the buffer disc of cell `n` the global axial sum reduces to the single term of that
cell, since all other terms vanish there. -/
theorem axialOffsetGlobalTorus_eq_cell_of_mem_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {n : ℕ} {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk n) :
    P.axialOffsetGlobalTorus tau q = P.axialOffsetTorus tau n q := by
  unfold axialOffsetGlobalTorus
  exact tsum_eq_single n fun m hmn ↦
    P.axialOffsetTorus_eq_zero_on_other_buffer tau hmn hq

/-- Inside the buffer disc of cell `n` the global displayed-derivative sum reduces to the single
term of that cell. -/
theorem axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {n : ℕ} {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk n)
    (j : Fin 2) :
    P.axialOffsetGlobalTorusDerivative tau j q =
      P.axialOffsetTorusDerivative tau n j q := by
  unfold axialOffsetGlobalTorusDerivative
  exact tsum_eq_single n fun m hmn ↦
    P.axialOffsetTorusDerivative_eq_zero_on_other_buffer tau hmn j hq

/-- At a point lying in no buffer disc the global axial sum vanishes, every term being zero
there. -/
theorem axialOffsetGlobalTorus_eq_zero_of_outside_buffers
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {q : TransverseTorus} (hq : ∀ n, q ∉ P.torusBufferDisk n) :
    P.axialOffsetGlobalTorus tau q = 0 := by
  unfold axialOffsetGlobalTorus
  simp_rw [P.axialOffsetTorus_eq_zero_of_not_mem_buffer tau _ (hq _)]
  exact tsum_zero

/-- At a point lying in no buffer disc the global displayed-derivative sum vanishes. -/
theorem axialOffsetGlobalTorusDerivative_eq_zero_of_outside_buffers
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    {q : TransverseTorus} (hq : ∀ n, q ∉ P.torusBufferDisk n)
    (j : Fin 2) : P.axialOffsetGlobalTorusDerivative tau j q = 0 := by
  unfold axialOffsetGlobalTorusDerivative
  simp_rw [P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau _ j (hq _)]
  exact tsum_zero

/-- The full added axial velocity is transversally divergence free pointwise:
`∂_1 u_1 + ∂_2 u_2 = 0`, by reduction to a single cell inside a buffer disc and to zero
outside all of them. -/
theorem axialOffsetGlobalTorusDerivative_transverseDivergence
    (P : TorusCellPlacement (r := r) supportRadius) (tau : ℝ)
    (q : TransverseTorus) :
    P.axialOffsetGlobalTorusDerivative tau 0 q 0 +
      P.axialOffsetGlobalTorusDerivative tau 1 q 1 = 0 := by
  by_cases hbuffer : ∃ n, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau hn 0,
      P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau hn 1]
    exact P.axialOffsetTorusDerivative_transverseDivergence tau n q
  · push Not at hbuffer
    rw [P.axialOffsetGlobalTorusDerivative_eq_zero_of_outside_buffers tau hbuffer 0,
      P.axialOffsetGlobalTorusDerivative_eq_zero_of_outside_buffers tau hbuffer 1]
    simp

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
