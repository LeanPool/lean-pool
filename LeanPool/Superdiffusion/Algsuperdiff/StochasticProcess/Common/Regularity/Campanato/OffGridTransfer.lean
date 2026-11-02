/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.CubeTelescope
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.TriadicLattice

/-!
# OffGridTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transferring clipped oscillation decay from lattice centres to every centre

A scale-by-scale regularity iteration run on a cube proves its oscillation
estimate on the windows clipped to that cube, and only at the points of a
triadic lattice: at each scale the centre must be a lattice point.  A Hölder
seminorm needs the estimate at **every** centre of the cube.  This file performs
the transfer and prices it exactly.

The mechanism is the only one available.  Round the arbitrary centre `x` toward
the centre of the cube at the spacing of the cube one triadic scale below the
window; the displacement is then strictly below that spacing, so the window at
`x` sits inside the lattice window **one scale up**, and

* the mean over the small window may be replaced by the mean over the large one
  at no cost, because the mean minimizes the deviation, and the two normalized
  `L²` norms then differ by at most `6 ^ (d/2)` — the volume ratio of two
  clipped windows whose radii differ by a factor `3`;
* the `α`-weight of the larger window is `3 ^ α` times that of the smaller.

So the transfer costs the factor `clipScaleStepConstant d α = 6 ^ (d/2) 3 ^ α`
and **one triadic scale**: a lattice family whose smallest available window
index is `j₀` yields an arbitrary-centre family whose smallest available window
index is `j₀ + 1`.  No smaller enclosing lattice window exists at the scale of
the window itself: that would force the centre to be the lattice point.

Because the windows are clipped, there is no second scale loss.  An enclosing
lattice window is automatically inside the cube — it is clipped to it — so the
lattice family may be used at every index it is available at, and the estimate
reaches every centre of the cube, boundary included.  Rounding toward the centre
of the cube keeps the lattice centre inside the cube, which is what makes the
lattice family applicable at it.

## Main definitions

* `HasClipGridOscillationDecay c Rm Grid Rtop α K j₀ f` — the lattice-centred
  hypothesis: the estimate at window index `j ≥ j₀` at every admissible centre
  `z ∈ Grid j`, on the window clipped to the cube.
* `GridApproximatesOn Grid S Rtop j₀` — every centre of `S` has an admissible
  centre one scale up within twice the smaller radius.
* `centredTriadicGrid c Rm Rtop` — the concrete family of lattice centres of the
  cube `B(c, Rm)`.

## Main results

* `hasClipTriadicOscillationDecayOn_of_grid` — the transfer, with its constant
  and its loss of one triadic scale.
* `gridApproximatesOn_centredTriadicGrid` — the concrete family is fine enough,
  and rounding keeps the centre in the cube.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. Iterating the triadic radius -/

/-- Restarting the triadic radii at a radius of the same family shifts the
index.  This is the dictionary that turns a family available from index `j₀`
into a family available from index `0` at the smaller top radius. -/
theorem triadicRadius_triadicRadius (R : ℝ) (k l : ℕ) :
    triadicRadius (triadicRadius R k) l = triadicRadius R (k + l) := by
  unfold triadicRadius
  rw [pow_add]
  ring

/-! ## 2. The lattice-centred hypothesis -/

/-- **Oscillation decay on clipped windows at a scale-indexed family of
admissible centres.**  `Grid j` is the set of centres at which the estimate is
available for the window of index `j`, and the estimate is available only from
the index `j₀` on. -/
def HasClipGridOscillationDecay (c : Vec d) (Rm : ℝ) (Grid : ℕ → Set (Vec d))
    (Rtop alpha K : ℝ) (j0 : ℕ) (f : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, j0 ≤ j → ∀ z ∈ Grid j,
    normalizedL2On (clipBall c Rm z (triadicRadius Rtop j))
      (fun y => f y - volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) f) ≤
      K * triadicRadius Rtop j ^ alpha

/-- **The family is fine enough to carry every centre of `S`.**  Each centre of
`S` admits, at every available index `j`, an admissible centre for the window of
index `j` within twice the radius of the window of index `j + 1`.  That is
exactly the tolerance under which the window of index `j + 1` at the arbitrary
centre is contained in the window of index `j` at the admissible centre. -/
def GridApproximatesOn (Grid : ℕ → Set (Vec d)) (S : Set (Vec d)) (Rtop : ℝ)
    (j0 : ℕ) : Prop :=
  ∀ x ∈ S, ∀ j : ℕ, j0 ≤ j → ∃ z ∈ Grid j, ‖x - z‖ ≤ 2 * triadicRadius Rtop (j + 1)

/-! ## 3. The transfer -/

/-- **The off-grid transfer on clipped windows.**  From oscillation decay at the
admissible centres of a scale-indexed family, available from index `j₀`, one
obtains oscillation decay at **every** centre of `S`, from index `j₀ + 1` on —
that is, with the top radius pushed down by exactly one triadic scale — at the
cost of the factor `clipScaleStepConstant d α` in the constant. -/
theorem hasClipTriadicOscillationDecayOn_of_grid
    {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)} {S : Set (Vec d)}
    {Rtop alpha K : ℝ} {j0 : ℕ} {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm)
    (hS : S ⊆ Metric.ball c Rm) (hGrid : ∀ j : ℕ, Grid j ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f)
    (happ : GridApproximatesOn Grid S Rtop j0) :
    HasClipTriadicOscillationDecayOn c Rm S (triadicRadius Rtop (j0 + 1)) alpha
      (clipScaleStepConstant d alpha * K) f := by
  intro x hx i
  obtain ⟨z, hzG, hdist⟩ := happ x hx (j0 + i) (Nat.le_add_right _ _)
  set j : ℕ := j0 + i with hj
  have hshift : triadicRadius (triadicRadius Rtop (j0 + 1)) i =
      triadicRadius Rtop (j + 1) := by
    rw [triadicRadius_triadicRadius]
    congr 1
    omega
  have hinner : 0 < triadicRadius Rtop (j + 1) := triadicRadius_pos hRtop _
  have houter : 0 < triadicRadius Rtop j := triadicRadius_pos hRtop _
  have houterRm : triadicRadius Rtop j ≤ Rm :=
    (triadicRadius_le hRtop.le j).trans hRtopRm
  have hinnerRm : triadicRadius Rtop (j + 1) ≤ Rm :=
    (triadicRadius_le hRtop.le (j + 1)).trans hRtopRm
  have hthree : triadicRadius Rtop j = 3 * triadicRadius Rtop (j + 1) := by
    rw [triadicRadius_succ]
    ring
  have hsub : clipBall c Rm x (triadicRadius Rtop (j + 1)) ⊆
      clipBall c Rm z (triadicRadius Rtop j) := by
    refine clipBall_subset_clipBall ?_
    rw [hthree]
    linarith only [hdist]
  have hcomp := oscillation_clipBall_le_of_subset (kappa := 6) hinner hinnerRm (hS hx)
    houter houterRm (hGrid j hzG) hsub (by rw [hthree]; linarith only [hinner]) hf
  have hosc := hdec j (Nat.le_add_right _ _) z hzG
  have hsplit : triadicRadius Rtop j ^ alpha =
      (3 : ℝ) ^ alpha * triadicRadius Rtop (j + 1) ^ alpha := by
    rw [hthree, Real.mul_rpow (by norm_num) hinner.le]
  rw [hshift]
  calc normalizedL2On (clipBall c Rm x (triadicRadius Rtop (j + 1)))
        (fun y => f y - volumeAverage (clipBall c Rm x (triadicRadius Rtop (j + 1))) f)
      ≤ ballVolumePrice 6 d *
        normalizedL2On (clipBall c Rm z (triadicRadius Rtop j))
          (fun y => f y - volumeAverage (clipBall c Rm z (triadicRadius Rtop j)) f) := hcomp
    _ ≤ ballVolumePrice 6 d * (K * triadicRadius Rtop j ^ alpha) :=
        mul_le_mul_of_nonneg_left hosc (ballVolumePrice_nonneg 6 d)
    _ = clipScaleStepConstant d alpha * K * triadicRadius Rtop (j + 1) ^ alpha := by
        rw [hsplit, clipScaleStepConstant]
        ring

/-! ## 4. The concrete triadic family on a cube -/

/-- **The concrete family of admissible centres.**  At window index `j` the
admissible centres are the points of the lattice through `c` of spacing
`2 triadicRadius Rtop (j + 1)` — the side of the cube one triadic scale below
the window — that lie in the cube. -/
def centredTriadicGrid (c : Vec d) (Rm Rtop : ℝ) : ℕ → Set (Vec d) := fun j =>
  (triadicLatticeAt c (2 * triadicRadius Rtop (j + 1)) : Set (Vec d)) ∩ Metric.ball c Rm

theorem centredTriadicGrid_subset (c : Vec d) (Rm Rtop : ℝ) (j : ℕ) :
    centredTriadicGrid c Rm Rtop j ⊆ Metric.ball c Rm := Set.inter_subset_right

/-- **The concrete family is fine enough, and rounding keeps the centre in the
cube.**  Rounding toward the centre of the cube is what supplies the second
half: the rounded centre never leaves the cube, so the lattice family applies at
it. -/
theorem gridApproximatesOn_centredTriadicGrid {Rtop : ℝ} (hRtop : 0 < Rtop)
    (c : Vec d) (Rm : ℝ) (j0 : ℕ) :
    GridApproximatesOn (centredTriadicGrid c Rm Rtop) (Metric.ball c Rm) Rtop j0 := by
  intro x hx j _
  have hs : 0 < 2 * triadicRadius Rtop (j + 1) := by
    have := triadicRadius_pos hRtop (j + 1)
    linarith only [this]
  refine ⟨triadicGridPointAt c (2 * triadicRadius Rtop (j + 1)) x,
    ⟨triadicGridPointAt_mem_triadicLatticeAt _ _ x,
      triadicGridPointAt_mem_ball hs hx⟩, ?_⟩
  exact (norm_sub_triadicGridPointAt_lt hs c x).le

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
