/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusPlacedCutoffVelocity

/-!
# The three parametrix cut-offs at a placed cell of a torus cell placement

`FastDynamo/Global/TorusPlacedCutoffC2.lean` builds the bundle
`ParametrixCutoffs.HorizontalParametrixCutoffs R` for an arbitrary centre `p` and reserved radius
`R`, under the single geometric hypothesis that the closed disc `D(p, R/2)` — the largest of the
three cut-off supports — does not wrap around the transverse torus.

This module discharges that hypothesis at the cell `n` of a
`ScaleFamily.TorusCellPlacement`, where the centre is `p_n = pairToWholePlane (cellCenter n)` and
the reserved radius is `R_n = bufferRadius n`.  The input is the placement's own chart-packing
field: every buffer disc lies in the fixed coordinate square
`placementChart = (0,1/4) × (1/4,3/4)` (by `eq:chart-packing`; the right half of the paper's
square `(-1/4,1/4) × (1/4,3/4)` of §3.3), which is
contained in the half-open unit box `(0,1]²` used by the lattice periodization.  Since
`R_n/2 < R_n`, the closed half-buffer disc sits inside the buffer disc and hence inside the
chart.

The output, `placedParametrixCutoffs P n`, is the `cutoffs` field of
`TorusTwoSummandParametrix.TwoSummandParametrixData` at the selected cell.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric
open scoped ENNReal

namespace ScaleFamily.TorusCellPlacement

open ParametrixCutoffs
open TransverseSmoothBumpPeriodization

variable {seedParameters : LocalSeedParameters} {r : ScaleRatios seedParameters}
  {supportRadius : ℝ}

/-- Reassembling a whole-plane point from its two coordinates returns the original point. -/
theorem pairToWholePlane_coordinatePair' (x : WholePlane) :
    pairToWholePlane (x 0, x 1) = x := by
  ext j
  fin_cases j <;> simp

/-- A whole-plane point within the closed half-buffer distance of the placed centre has its
coordinate pair inside the full Euclidean buffer disc of the cell. -/
theorem coordinatePair_mem_bufferDisk_of_dist_le_half
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) {x : WholePlane}
    (hx : dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
      P.scaleFamily.bufferRadius n / 2) :
    (x 0, x 1) ∈ P.scaleFamily.bufferDisk n := by
  have hpair : dist (x 0, x 1) (P.scaleFamily.cellCenter n) ≤
      dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) := by
    calc
      dist (x 0, x 1) (P.scaleFamily.cellCenter n) ≤
          ‖pairToWholePlane (x 0, x 1) -
            pairToWholePlane (P.scaleFamily.cellCenter n)‖ :=
        dist_le_norm_pairToWholePlane_sub _ _
      _ = ‖x - pairToWholePlane (P.scaleFamily.cellCenter n)‖ := by
        rw [pairToWholePlane_coordinatePair']
      _ = dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) := by rw [dist_eq_norm]
  change dist (x 0, x 1) (P.scaleFamily.cellCenter n) < P.scaleFamily.bufferRadius n
  calc
    dist (x 0, x 1) (P.scaleFamily.cellCenter n) ≤
        dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) := hpair
    _ ≤ P.scaleFamily.bufferRadius n / 2 := hx
    _ < P.scaleFamily.bufferRadius n := by
      linarith [P.scaleFamily.bufferRadius_pos n]

/-- **The no-wrap hypothesis at a placed cell.**  The closed half-buffer disc about the placed
centre lies in the half-open unit box, because it lies in the fixed coordinate square of
`eq:chart-packing`. -/
theorem closedHalfBufferBall_subset_iocFundamentalBox
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    closedBall (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.bufferRadius n / 2) ⊆ wholePlaneIocFundamentalBox := by
  intro x hx
  have hxle : dist x (pairToWholePlane (P.scaleFamily.cellCenter n)) ≤
      P.scaleFamily.bufferRadius n / 2 := by
    simpa [mem_closedBall] using hx
  have hbuffer := coordinatePair_mem_bufferDisk_of_dist_le_half P n hxle
  have hchart := P.bufferDisk_subset_chart n hbuffer
  rcases hchart with ⟨⟨hx0lo, hx0hi⟩, ⟨hx1lo, hx1hi⟩⟩
  have hx0lo' : 0 < x 0 := by simpa using hx0lo
  have hx0hi' : x 0 < 1 / 4 := by simpa using hx0hi
  have hx1lo' : 1 / 4 < x 1 := by simpa using hx1lo
  have hx1hi' : x 1 < 3 / 4 := by simpa using hx1hi
  intro j
  fin_cases j
  · simpa using
      (show x (0 : Fin 2) ∈ Set.Ioc (0 : ℝ) (0 + 1) from ⟨hx0lo', by linarith⟩)
  · simpa using
      (show x (1 : Fin 2) ∈ Set.Ioc (0 : ℝ) (0 + 1) from ⟨by linarith, by linarith⟩)

/-- **The three placed parametrix cut-offs at the cell `n`** (`φ_n`, `ψ_n`, `χ_n` of §7.1,
before `eq:parametrix-cutoff-bounds`): the `cutoffs` field of
`TorusTwoSummandParametrix.TwoSummandParametrixData` at the selected cell, with centre
`p_n = pairToWholePlane (cellCenter n)` and reserved radius `R_n = bufferRadius n`. -/
def placedParametrixCutoffs (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    HorizontalParametrixCutoffs (P.scaleFamily.bufferRadius n) :=
  TorusPlacedCutoffC2.placedCutoffs (pairToWholePlane (P.scaleFamily.cellCenter n))
    (P.scaleFamily.bufferRadius n) (P.scaleFamily.bufferRadius_pos n)
    (closedHalfBufferBall_subset_iocFundamentalBox P n)

/-- The input cut-off of the placed bundle at the cell `n`. -/
@[simp] theorem placedParametrixCutoffs_input
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    (placedParametrixCutoffs P n).input =
      TorusPlacedCutoffC2.inputMul (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.bufferRadius n) (P.scaleFamily.bufferRadius_pos n) :=
  rfl

/-- The output cut-off of the placed bundle at the cell `n`. -/
@[simp] theorem placedParametrixCutoffs_output
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    (placedParametrixCutoffs P n).output =
      TorusPlacedCutoffC2.outputMul (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.bufferRadius n) (P.scaleFamily.bufferRadius_pos n) :=
  rfl

/-- The background cut-off of the placed bundle at the cell `n`. -/
@[simp] theorem placedParametrixCutoffs_background
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    (placedParametrixCutoffs P n).background =
      TorusPlacedCutoffC2.backgroundMul (pairToWholePlane (P.scaleFamily.cellCenter n))
        (P.scaleFamily.bufferRadius n) (P.scaleFamily.bufferRadius_pos n) :=
  rfl

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
