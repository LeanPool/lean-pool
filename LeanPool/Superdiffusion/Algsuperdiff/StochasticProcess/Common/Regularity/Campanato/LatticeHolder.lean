/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.OffGridTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.CubeOscillationHolder
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge

/-!
# LatticeHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A Hölder seminorm bound on the whole cube from lattice oscillation decay

This file composes the two halves of the passage from a scale-by-scale
oscillation estimate on a cube to a Hölder seminorm on the same cube:

* the off-grid transfer, which moves the centre from the lattice to an arbitrary
  point of the cube at the price `clipScaleStepConstant d α` and the loss of one
  triadic scale;
* the clipped Campanato telescope and its convex chaining, which turn
  oscillation decay at every centre into a two-point Hölder bound for the
  canonical representative.

Because the windows are clipped to the cube, the conclusion holds up to the
boundary: no interior sub-cube is involved and no boundary term is created.

Every constant is written out.  The composed price is

`clipOffGridHolderConstant d α N
   = N ^ (1 - α) · clipLocalHolderConstant d α · (clipScaleStepConstant d α) ^ 2`,

with `N` the number of chaining steps, and the conclusion is the bound
`clipOffGridHolderConstant d α N · K` on the `C^{0,α}` seminorm of the
representative on the whole cube, where `K` is the constant of the lattice
family.

The concrete instance is the cube `y + □_m` against a lattice family on its own
clipped windows.  One triadic scale is spent — the enclosing lattice window of
an off-lattice centre is one scale up — so the Campanato decay reaches half-side
`3 ^ (m-1) / 2`, the telescope's top radius is `3 ^ (m-2) / 2`, and the chain
length is `N = 18`, both scale constraints being exact equalities.

## Main definitions

* `clipOffGridHolderConstant d α N` — the composed explicit constant.

## Main results

* `holderSeminormBoundOn_cube_of_grid` — the wrapper on an arbitrary cube, with
  `R` and `N` free.
* `holderSeminormBoundOn_cubeSetAt_of_grid` — the concrete two-point instance
  on `y + □_m`, at `N = 18`.
* `continuousOn_campanatoRepresentative_of_grid`,
  `campanatoRepresentative_ae_eq_of_grid` — the representative produced is
  continuous on the cube and agrees with `f` almost everywhere on it.
* `cubeSetAt_eq_ball` — the dictionary between the cube of the underlying scale
  range and the supremum ball.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. The composed constant -/

/-- **The composed explicit constant** of the passage from a lattice oscillation
family on the clipped windows of a cube to a Hölder seminorm on that cube: the
chaining price `N ^ (1 - α)`, the two-point bound, and the two triadic steps —
one for the passage from the discrete scales to all radii, one for the off-grid
transfer. -/
def clipOffGridHolderConstant (d : ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - alpha) *
    (clipLocalHolderConstant d alpha *
      (clipScaleStepConstant d alpha * clipScaleStepConstant d alpha))

theorem clipOffGridHolderConstant_nonneg (d : ℕ) {alpha : ℝ} (halpha : 0 < alpha)
    (N : ℕ) : 0 ≤ clipOffGridHolderConstant d alpha N := by
  refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
  exact mul_nonneg (clipLocalHolderConstant_nonneg d halpha)
    (mul_nonneg (clipScaleStepConstant_nonneg d alpha)
      (clipScaleStepConstant_nonneg d alpha))

/-! ## 2. The wrapper -/

/-- **The Campanato decay at every centre of the cube, from lattice decay.** -/
theorem hasClipCampanatoDecayOn_of_grid
    {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)} {Rtop alpha K : ℝ} {j0 : ℕ}
    {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 ≤ alpha) (hK : 0 ≤ K)
    (hGrid : ∀ j : ℕ, Grid j ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f)
    (happ : GridApproximatesOn Grid (Metric.ball c Rm) Rtop j0) :
    HasClipCampanatoDecayOn c Rm (Metric.ball c Rm) (triadicRadius Rtop (j0 + 1))
      alpha (clipScaleStepConstant d alpha * (clipScaleStepConstant d alpha * K)) f := by
  have htri := hasClipTriadicOscillationDecayOn_of_grid hRtop hRtopRm
    (subset_refl (Metric.ball c Rm)) hGrid hf hdec happ
  refine hasClipCampanatoDecayOn_of_triadic (triadicRadius_pos hRtop _) ?_ halpha
    (mul_nonneg (clipScaleStepConstant_nonneg d alpha) hK)
    (subset_refl (Metric.ball c Rm)) hf htri
  exact (triadicRadius_le hRtop.le (j0 + 1)).trans hRtopRm

/-- **The Hölder seminorm bound on the whole cube, from lattice decay.**  The
lattice family is available at the admissible centres from index `j₀` on; the
off-grid transfer then supplies every centre of the cube from index `j₀ + 1` on,
and the telescope of top radius `R` — constrained by
`3 R ≤ triadicRadius Rtop (j₀ + 1)` — is chained across the cube in `N` steps,
where `N` is constrained by `2 Rm ≤ N R`. -/
theorem holderSeminormBoundOn_cube_of_grid
    {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)} {Rtop alpha K R : ℝ} {j0 N : ℕ}
    {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hR : 0 < R) (hRle : 3 * R ≤ triadicRadius Rtop (j0 + 1))
    (hN : 0 < N) (hchain : 2 * Rm ≤ (N : ℝ) * R)
    (hGrid : ∀ j : ℕ, Grid j ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f)
    (happ : GridApproximatesOn Grid (Metric.ball c Rm) Rtop j0) :
    HolderSeminormBoundOn (Metric.ball c Rm) alpha
      (clipOffGridHolderConstant d alpha N * K) (campanatoRepresentative f R) := by
  have hcamp := hasClipCampanatoDecayOn_of_grid hRtop hRtopRm halpha.le hK hGrid hf
    hdec happ
  have hK2 : 0 ≤ clipScaleStepConstant d alpha * (clipScaleStepConstant d alpha * K) :=
    mul_nonneg (clipScaleStepConstant_nonneg d alpha)
      (mul_nonneg (clipScaleStepConstant_nonneg d alpha) hK)
  have key := holderSeminormBoundOn_cube_campanatoRepresentative hR hRle
    ((triadicRadius_le hRtop.le (j0 + 1)).trans hRtopRm) halpha hK2 hN hchain hf hcamp
  have hconst : (N : ℝ) ^ (1 - alpha) *
      (clipLocalHolderConstant d alpha *
        (clipScaleStepConstant d alpha * (clipScaleStepConstant d alpha * K))) =
      clipOffGridHolderConstant d alpha N * K := by
    rw [clipOffGridHolderConstant]
    ring
  rwa [hconst] at key

/-- The representative produced by the wrapper is continuous on the cube. -/
theorem continuousOn_campanatoRepresentative_of_grid
    {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)} {Rtop alpha K R : ℝ} {j0 N : ℕ}
    {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hR : 0 < R) (hRle : 3 * R ≤ triadicRadius Rtop (j0 + 1))
    (hN : 0 < N) (hchain : 2 * Rm ≤ (N : ℝ) * R)
    (hGrid : ∀ j : ℕ, Grid j ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f)
    (happ : GridApproximatesOn Grid (Metric.ball c Rm) Rtop j0) :
    ContinuousOn (campanatoRepresentative f R) (Metric.ball c Rm) := by
  have hbound := holderSeminormBoundOn_cube_of_grid hRtop hRtopRm halpha hK hR hRle
    hN hchain hGrid hf hdec happ
  refine continuousOn_of_holderBound halpha
    (mul_nonneg (clipOffGridHolderConstant_nonneg d halpha N) hK) ?_
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using hbound x hx y hy

/-- The representative produced by the wrapper is a representative of `f`. -/
theorem campanatoRepresentative_ae_eq_of_grid [NeZero d]
    {c : Vec d} {Rm : ℝ} {Grid : ℕ → Set (Vec d)} {Rtop alpha K R : ℝ} {j0 : ℕ}
    {f : Vec d → ℝ}
    (hRtop : 0 < Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hR : 0 < R) (hRle : R ≤ triadicRadius Rtop (j0 + 1))
    (hGrid : ∀ j : ℕ, Grid j ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hint : LocallyIntegrable f volume)
    (hdec : HasClipGridOscillationDecay c Rm Grid Rtop alpha K j0 f)
    (happ : GridApproximatesOn Grid (Metric.ball c Rm) Rtop j0) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ Metric.ball c Rm → campanatoRepresentative f R x = f x := by
  have hcamp := hasClipCampanatoDecayOn_of_grid hRtop hRtopRm halpha.le hK hGrid hf
    hdec happ
  exact campanatoRepresentative_ae_eq_of_clip hR hRle
    ((triadicRadius_le hRtop.le (j0 + 1)).trans hRtopRm) halpha
    (subset_refl (Metric.ball c Rm)) hf hcamp hint

/-! ## 3. The cube of the underlying scale range -/

/-- The cube `y + □_n` is the supremum ball of radius `3 ^ n / 2` at `y`. -/
theorem cubeSetAt_eq_ball (y : Vec d) (n : ℤ) :
    Algsuperdiff.Section5.Support.cubeSetAt y n = Metric.ball y ((3 : ℝ) ^ n / 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n / 2 := by linarith only [h3]
  ext x
  rw [Algsuperdiff.Section5.Support.mem_cubeSetAt_iff_forall_coord, Metric.mem_ball,
    dist_eq_norm, pi_norm_lt_iff hpos]
  constructor
  · intro h i
    have hi := h i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
  · intro h i
    have hi := h i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt] at hi
    exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩

/-! ## 4. The concrete instance -/

private theorem zpow_three_sub (m : ℤ) {k : ℤ} {b : ℝ} (hb : (3 : ℝ) ^ k = b) :
    (3 : ℝ) ^ (m - k) = (3 : ℝ) ^ m / b := by
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), hb]

/-- **The concrete instance on `y + □_m`.**  The lattice family lives on the
windows clipped to `y + □_m` itself, so no scale is spent on fitting a lattice
window inside the cube; the single triadic scale spent is the one the off-grid
transfer costs.  Both scale constraints are exact equalities:
`3 R = 3 ^ (m-1) / 2` is the top radius of the transferred Campanato family, and
`18 R = 3 ^ m` is the diameter of the cube. -/
theorem holderSeminormBoundOn_cubeSetAt_of_grid
    {y : Vec d} {Grid : ℕ → Set (Vec d)} {alpha K : ℝ} {m : ℤ} {f : Vec d → ℝ}
    (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hGrid : ∀ j : ℕ, Grid j ⊆ Algsuperdiff.Section5.Support.cubeSetAt y m)
    (hf : MemLp f 2 (volume.restrict (Algsuperdiff.Section5.Support.cubeSetAt y m)))
    (hdec : HasClipGridOscillationDecay y ((3 : ℝ) ^ m / 2) Grid ((3 : ℝ) ^ m / 2)
      alpha K 0 f)
    (happ : GridApproximatesOn Grid (Algsuperdiff.Section5.Support.cubeSetAt y m)
      ((3 : ℝ) ^ m / 2) 0) :
    HolderSeminormBoundOn (Algsuperdiff.Section5.Support.cubeSetAt y m) alpha
      (clipOffGridHolderConstant d alpha 18 * K)
      (campanatoRepresentative f ((3 : ℝ) ^ (m - 2) / 2)) := by
  rw [cubeSetAt_eq_ball] at hGrid hf happ ⊢
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have e1 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := zpow_three_sub m (by norm_num)
  have e2 : (3 : ℝ) ^ (m - 2) = (3 : ℝ) ^ m / 9 := zpow_three_sub m (by norm_num)
  have htop : triadicRadius ((3 : ℝ) ^ m / 2) (0 + 1) = (3 : ℝ) ^ (m - 1) / 2 := by
    rw [triadicRadius_half_zpow]
    norm_num
  have hR : (0 : ℝ) < (3 : ℝ) ^ (m - 2) / 2 := by
    rw [e2]; linarith only [h3]
  have hRle : 3 * ((3 : ℝ) ^ (m - 2) / 2) ≤ triadicRadius ((3 : ℝ) ^ m / 2) (0 + 1) := by
    rw [htop, e1, e2]
    linarith only [h3]
  have hchain : 2 * ((3 : ℝ) ^ m / 2) ≤ (18 : ℕ) * ((3 : ℝ) ^ (m - 2) / 2) := by
    rw [e2]
    push_cast
    linarith only []
  exact holderSeminormBoundOn_cube_of_grid (by linarith only [h3]) le_rfl halpha hK hR
    hRle (by norm_num) hchain hGrid hf hdec happ

/-- **The concrete instance at the concrete family of lattice centres.**  The
approximation hypothesis is discharged by rounding toward the centre of the
cube, so the only remaining inputs are the oscillation estimate at the lattice
centres and square integrability on the cube. -/
theorem holderSeminormBoundOn_cubeSetAt_of_centredTriadicGrid
    {y : Vec d} {alpha K : ℝ} {m : ℤ} {f : Vec d → ℝ}
    (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hf : MemLp f 2 (volume.restrict (Algsuperdiff.Section5.Support.cubeSetAt y m)))
    (hdec : HasClipGridOscillationDecay y ((3 : ℝ) ^ m / 2)
      (centredTriadicGrid y ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2))
      ((3 : ℝ) ^ m / 2) alpha K 0 f) :
    HolderSeminormBoundOn (Algsuperdiff.Section5.Support.cubeSetAt y m) alpha
      (clipOffGridHolderConstant d alpha 18 * K)
      (campanatoRepresentative f ((3 : ℝ) ^ (m - 2) / 2)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine holderSeminormBoundOn_cubeSetAt_of_grid halpha hK ?_ hf hdec ?_
  · intro j
    rw [cubeSetAt_eq_ball]
    exact centredTriadicGrid_subset y _ _ j
  · rw [cubeSetAt_eq_ball]
    exact gridApproximatesOn_centredTriadicGrid (by linarith only [h3]) y _ 0

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
