/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.CubeEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.DeltaOsc
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl

/-!
# Definitions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The bad events of ABK26, Section 3.3

This module defines local implementations of the named events of
`sss.bad.cubes` (ABK26) as measurable subsets of the cutoff sample space, at an
arbitrary triadic cube.  The manuscript indexes them by an integer scale `j` and
a centre `z` in `3^j Z^d`; the pair `(j, z)` is exactly a `Q : TriadicCube d`
with `Q.scale = j` and `Q.index i = z_i / 3^j`, and `cubeSet Q = z + square_j`.

## The four displays

* `e.Bosc.def`.  The oscillation event at threshold `delta_osc
  c_star^{1/2} gamma^{-1/2} 3^{gamma j}` — here `oscThreshold`.
* `e.BoscL.def`.  The scale-resolved oscillation event at
  threshold `(1/5) delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j}
  3^{-(L-j)/5}` — here `oscThresholdAt` — for the single shell `j_L`, measured
  in the volume-normalized norm `3^{2j} ||grad j_L||_{W^{1,infinity}(z+square_j)}`,
  which at `p = infinity` is
  `max { 3^{2j} ||grad^2 j_L||_{L^infinity}, 3^j ||grad j_L||_{L^infinity} }`
  (ABK26, the definition of the volume-normalized Sobolev norm; the
  `|U|^{-1/d}` factor of a cube of side `3^j` is `3^{-j}`).
* `e.Bloc.def`.  The local coarse-grained ellipticity failure at `q = 2`, `s
  = 1/4`, threshold `10`.
* `e.B.def` and `e.Bext.def`.  The union, and its extension over nine
  generations of triadic descendants.

## Reading conventions (recorded)

* `badOsc` is defined as the manuscript's own scale decomposition
  `e.Bosc.decomp`, i.e. as `union_{L > j} B_{osc,L}(z+square_j)`.  The
  manuscript's `B_osc` is contained in this set by `e.Bosc.decomp`, so `badOsc`
  is the *larger* event: its probability bound is the manuscript's union bound
  verbatim, and its complement gives *at least* the oscillation control the
  manuscript's complement gives.  The reason for the choice is that the literal
  `B_osc` needs the sup norm of the derivative of the stream increment `k_L -
  k_j`, which requires a finite-sum carrier on `ShellField` that this
  repository does not have; `oscGaugeSum_le_oscThreshold` below proves the
  deterministic content of `e.Bosc.decomp` that does not need it.
* The `L^infinity` gauges `localCubeDerivNorm` / `localCubeSecondDerivNorm` are
  taken over the *open* cube, matching the proved Section 3 stream convention.

## Main definitions

* `cubeBasePoint`: the corner-free base point `z` of a triadic cube.
* `oscThreshold`, `oscThresholdAt`: the two displayed thresholds.
* `shellOscGauge`: `3^{2j} ||grad j_L||_{W^{1,infinity}(z+square_j)}`.
* `badOscAt`, `badOsc`, `badLoc`, `bad`, `badExtended`.

## Main results

* `measurable*` / `measurableSet_*` for every gauge and event.
* `oscThresholdAt_geometric_sum_le_oscThreshold`: the manuscript's arithmetic
  `(1/5) sum_{n >= 1} 3^{-n/5} <= 1` behind `e.Bosc.decomp`.
* `oscGaugeSum_le_oscThreshold`: on the complement of `badOsc`, the shell-wise
  majorant of `3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z+square_j)}` is
  below the `e.Bosc.def` threshold, for every `L >= j`.

## References

* ABK26, `sss.bad.cubes`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## The base point of a triadic cube -/

/-- The manuscript's centre `z` in `3^j Z^d` of the cube `z + square_j`.  With
this vector, `cubeSet Q` is the translate by `cubeBasePoint Q` of the centered
cube of scale `Q.scale`. -/
def cubeBasePoint (Q : TriadicCube d) : Vec d :=
  fun i => (Q.index i : ℝ) * (3 : ℝ) ^ Q.scale

/-! ## The two oscillation thresholds -/

/-- The right side of `e.Bosc.def`:
`delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j}`. -/
def oscThreshold (M : ABKModel d) (j : ℤ) : ℝ :=
  deltaOsc d * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
    (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (j : ℝ))

/-- The right side of `e.BoscL.def`:
`(1/5) delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j} 3^{-(L-j)/5}`. -/
def oscThresholdAt (M : ABKModel d) (j L : ℤ) : ℝ :=
  (1 / 5 : ℝ) * oscThreshold M j *
    (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((L : ℝ) - (j : ℝ)))

theorem oscThreshold_pos (M : ABKModel d) (j : ℤ) : 0 < oscThreshold M j := by
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have h1 : 0 < Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) :=
    Real.sqrt_pos.2 hc
  have h2 : 0 < (Real.sqrt M.gamma)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hg)
  have h3 : 0 < (3 : ℝ) ^ (M.gamma * (j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h0 : 0 < deltaOsc d := deltaOsc_pos d
  unfold oscThreshold
  positivity

/-! ## The single-shell oscillation gauge -/

/-- The manuscript's `3^{2j} ||grad j_L||_{W^{1,infinity}(z+square_j)}` of
`e.BoscL.def`, at the cube `Q` of scale `j = Q.scale` and shell index `L`.

At `p = infinity` the volume-normalized Sobolev norm of ABK26 is the maximum of
the gradient sup norm and `|U|^{-1/d}` times the value sup norm; for `U = z +
square_j` the factor `|U|^{-1/d}` is `3^{-j}`, so the displayed quantity is `max
{ 3^{2j} ||grad^2 j_L||_{L^infinity(U)}, 3^j ||grad j_L||_{L^infinity(U)} }`. -/
def shellOscGauge (Q : TriadicCube d) (L : ℤ) :
    CutoffSample d → ℝ :=
  fun omega =>
    max
      ((3 : ℝ) ^ (2 * Q.scale) *
        localCubeSecondDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q) (omega.1 L)))
      ((3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q) (omega.1 L)))

/-- The single-shell oscillation gauge is dominated by `3^j` times the proved shell
derivative gauge `||grad j_L|| + 3^j ||grad^2 j_L||` on the same cube, which is
the object controlled by `e.nabla.jk.O`. -/
theorem shellOscGauge_le_shellDerivGauge (Q : TriadicCube d)
    (L : ℤ) (omega : CutoffSample d) :
    shellOscGauge Q L omega ≤
      (3 : ℝ) ^ Q.scale *
        (localCubeDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q) (omega.1 L)) +
          (3 : ℝ) ^ Q.scale *
            localCubeSecondDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (omega.1 L))) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hd := localCubeDerivNorm_nonneg Q.scale
    (ShellField.translate (cubeBasePoint Q) (omega.1 L))
  have hs := localCubeSecondDerivNorm_nonneg Q.scale
    (ShellField.translate (cubeBasePoint Q) (omega.1 L))
  have hsq : (3 : ℝ) ^ (2 * Q.scale) = (3 : ℝ) ^ Q.scale * (3 : ℝ) ^ Q.scale := by
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  refine max_le ?_ ?_
  · rw [hsq]
    nlinarith [h3, hd, hs]
  · nlinarith [h3, hd, hs]

theorem measurable_shellOscGauge (Q : TriadicCube d) (L : ℤ) :
    Measurable (shellOscGauge (d := d) Q L) := by
  have hbase : Measurable
      (fun omega : CutoffSample d =>
        ShellField.translate (cubeBasePoint Q) (omega.1 L)) :=
    (ShellField.measurable_translate (cubeBasePoint Q)).comp
      ((measurable_pi_apply L).comp measurable_subtype_coe)
  exact
    (((measurable_localCubeSecondDerivNorm Q.scale).comp hbase).const_mul _).max
      (((measurable_localCubeDerivNorm Q.scale).comp hbase).const_mul _)

/-! ## The scale-resolved oscillation event `e.BoscL.def` -/

/-- `B_{osc,L}(z + square_j)` of `e.BoscL.def` (ABK26). -/
def badOscAt (M : ABKModel d) (Q : TriadicCube d) (L : ℤ) :
    Set (CutoffSample d) :=
  {omega | oscThresholdAt M Q.scale L < shellOscGauge Q L omega}

theorem measurableSet_badOscAt (M : ABKModel d) (Q : TriadicCube d) (L : ℤ) :
    MeasurableSet (badOscAt M Q L) :=
  measurableSet_lt measurable_const (measurable_shellOscGauge Q L)

/-- The oscillation event `B_osc(z + square_j)`, defined as the manuscript's
own scale decomposition `e.Bosc.decomp` (ABK26). -/
def badOsc (M : ABKModel d) (Q : TriadicCube d) : Set (CutoffSample d) :=
  ⋃ (L : ℤ) (_ : Q.scale < L), badOscAt M Q L

theorem measurableSet_badOsc (M : ABKModel d) (Q : TriadicCube d) :
    MeasurableSet (badOsc M Q) := by
  refine MeasurableSet.iUnion fun L => ?_
  exact MeasurableSet.iUnion fun _ => measurableSet_badOscAt M Q L

theorem badOscAt_subset_badOsc (M : ABKModel d) (Q : TriadicCube d) {L : ℤ}
    (hL : Q.scale < L) : badOscAt M Q L ⊆ badOsc M Q := by
  intro omega homega
  exact Set.mem_iUnion.2 ⟨L, Set.mem_iUnion.2 ⟨hL, homega⟩⟩

/-- On the complement of `badOsc`, every single shell above the cube scale
obeys the `e.BoscL.def` threshold. -/
theorem shellOscGauge_le_of_notMem_badOsc (M : ABKModel d) (Q : TriadicCube d)
    {omega : CutoffSample d} (homega : omega ∉ badOsc M Q) {L : ℤ}
    (hL : Q.scale < L) :
    shellOscGauge Q L omega ≤ oscThresholdAt M Q.scale L := by
  by_contra hcon
  exact homega (badOscAt_subset_badOsc M Q hL (not_le.1 hcon))

/-! ## The local coarse-grained ellipticity event `e.Bloc.def` -/

/-- The exponent `q = 2` at which `e.Bloc.def` is stated. -/
def exponentTwo : Algsuperdiff.Section3.CoarseEllipticityExponent :=
  Algsuperdiff.Section3.CoarseEllipticityExponent.finite ⟨2, by norm_num⟩

/-- `B_loc(z + square_j)` of `e.Bloc.def` (ABK26): the union of `{
lambda^{-1}_{1/4,2}(z+square_j; a_j) > 10 sigma_j^{-1} }` and `{
Lambda_{1/4,2}(z+square_j; a_j) > 10 sigma_j }`. -/
def badLoc (M : ABKModel d) (Q : TriadicCube d) : Set (CutoffSample d) :=
  {omega | 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ <
      cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega} ∪
    {omega | 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) <
      cubeUpperEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega}

theorem measurableSet_badLoc (M : ABKModel d) (Q : TriadicCube d) :
    MeasurableSet (badLoc M Q) :=
  (measurableSet_lt measurable_const
      (measurable_cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num)
        exponentTwo)).union
    (measurableSet_lt measurable_const
      (measurable_cubeUpperEllipticity M Q Q.scale (1 / 4) (by norm_num)
        exponentTwo))

/-! ## The combined and extended bad events -/

/-- `B(z + square_j)` of `e.B.def` (ABK26). -/
def bad (M : ABKModel d) (Q : TriadicCube d) : Set (CutoffSample d) :=
  badOsc M Q ∪ badLoc M Q

theorem measurableSet_bad (M : ABKModel d) (Q : TriadicCube d) :
    MeasurableSet (bad M Q) :=
  (measurableSet_badOsc M Q).union (measurableSet_badLoc M Q)

/-- The literal nine-generation extension `B^*(z + square_j)` of `e.Bext.def`
(ABK26): the union of `B(z' + square_{j-i})` over `i in {0, ..., 9}` and all
triadic descendants `z' + square_{j-i}` of `z + square_j` at depth `i`. -/
def badExtended (M : ABKModel d) (Q : TriadicCube d) : Set (CutoffSample d) :=
  ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
    bad M R

theorem measurableSet_badExtended (M : ABKModel d) (Q : TriadicCube d) :
    MeasurableSet (badExtended M Q) := by
  refine Finset.measurableSet_biUnion _ fun i _ => ?_
  exact Finset.measurableSet_biUnion _ fun R _ => measurableSet_bad M R

theorem bad_subset_badExtended (M : ABKModel d) (Q : TriadicCube d) :
    bad M Q ⊆ badExtended M Q := by
  intro omega homega
  refine Set.mem_biUnion (Finset.mem_range.2 (by norm_num : (0 : ℕ) < 10)) ?_
  refine Set.mem_biUnion ?_ (by simpa using homega)
  have hz : Q.scale - ((0 : ℕ) : ℤ) = Q.scale := by simp
  rw [hz, descendantsAtScale_self]
  exact Finset.mem_singleton_self Q

/-! ## The arithmetic behind `e.Bosc.decomp` -/

/-- The geometric ratio `3^{-1/5}` of the scale decomposition. -/
private theorem rpow_three_neg_fifth_lt_one :
    (3 : ℝ) ^ (-(1 / 5 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

private theorem rpow_three_neg_fifth_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 5 : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- `3^{-1/5} <= 5/6`, the numerical fact behind
`(1/5) sum_{n >= 1} 3^{-n/5} <= 1`. -/
private theorem rpow_three_neg_fifth_le : (3 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 5 / 6 := by
  have hbase : (0 : ℝ) ≤ (6 : ℝ) / 5 := by norm_num
  have hpow : ((6 : ℝ) / 5) ^ (5 : ℕ) ≤ 3 := by norm_num
  have hmono : (((6 : ℝ) / 5) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) ≤ (3 : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hpow (by norm_num)
  have hleft : (((6 : ℝ) / 5) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) = (6 : ℝ) / 5 := by
    rw [← Real.rpow_natCast ((6 : ℝ) / 5) 5, ← Real.rpow_mul hbase]
    norm_num
  rw [hleft] at hmono
  have hposr : (0 : ℝ) < (3 : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (3 : ℝ) ^ (-(1 / 5 : ℝ)) = ((3 : ℝ) ^ (1 / 5 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hinv, inv_le_iff_one_le_mul₀ hposr]
  nlinarith [hmono, hposr]

/-- The manuscript's arithmetic
`(1/5) sum_{n = 1}^{N} 3^{-n/5} <= 1` (ABK26, `e.Bosc.decomp`), in the form of
the scale-resolved thresholds: the sum of the `e.BoscL.def` thresholds over any
finite initial block of scales above `j` is below the `e.Bosc.def` threshold. -/
theorem oscThresholdAt_geometric_sum_le_oscThreshold (M : ABKModel d) (j : ℤ)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, oscThresholdAt M j (j + 1 + (n : ℤ)) ≤
      oscThreshold M j := by
  set r : ℝ := (3 : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 < r := rpow_three_neg_fifth_pos
  have hr1 : r < 1 := rpow_three_neg_fifth_lt_one
  have hrle : r ≤ 5 / 6 := rpow_three_neg_fifth_le
  have hT : 0 < oscThreshold M j := oscThreshold_pos M j
  have hterm : ∀ n : ℕ, oscThresholdAt M j (j + 1 + (n : ℤ)) =
      (1 / 5 : ℝ) * oscThreshold M j * (r * r ^ n) := by
    intro n
    have hexp : ((((j + 1 + (n : ℤ)) : ℤ) : ℝ) - (j : ℝ)) = 1 + (n : ℝ) := by
      push_cast
      ring
    have hpow : r ^ n = (3 : ℝ) ^ (-(1 / 5 : ℝ) * (n : ℝ)) := by
      rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 5 : ℝ))) n,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hmul : r * r ^ n = (3 : ℝ) ^ (-(1 / 5 : ℝ) * (1 + (n : ℝ))) := by
      rw [hpow, hr, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    rw [oscThresholdAt, hexp, hmul]
  have hsum : ∑ n ∈ Finset.range N, oscThresholdAt M j (j + 1 + (n : ℤ)) =
      (1 / 5 : ℝ) * oscThreshold M j * r * ∑ n ∈ Finset.range N, r ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hterm n]
    ring
  have hgeom : ∑ n ∈ Finset.range N, r ^ n ≤ (1 - r)⁻¹ := by
    have hsummable : Summable fun n : ℕ => r ^ n :=
      summable_geometric_of_lt_one hr0.le hr1
    have := hsummable.sum_le_tsum (Finset.range N)
      (fun n _ => pow_nonneg hr0.le n)
    rwa [tsum_geometric_of_lt_one hr0.le hr1] at this
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hcoef : (1 / 5 : ℝ) * r * (1 - r)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpos]
    nlinarith [hrle, hr0]
  calc ∑ n ∈ Finset.range N, oscThresholdAt M j (j + 1 + (n : ℤ))
      = (1 / 5 : ℝ) * oscThreshold M j * r * ∑ n ∈ Finset.range N, r ^ n := hsum
    _ ≤ (1 / 5 : ℝ) * oscThreshold M j * r * (1 - r)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        positivity
    _ = oscThreshold M j * ((1 / 5 : ℝ) * r * (1 - r)⁻¹) := by ring
    _ ≤ oscThreshold M j * 1 := mul_le_mul_of_nonneg_left hcoef hT.le
    _ = oscThreshold M j := mul_one _

/-- The deterministic content of `e.Bosc.decomp` available without a
finite-sum carrier on `ShellField`: on the complement of `badOsc`, the
shell-wise majorant of
`3^{2j} ||grad (k_{j+N} - k_j)||_{W^{1,infinity}(z+square_j)}` stays below the
`e.Bosc.def` threshold, for every finite block of scales above `j`. -/
theorem oscGaugeSum_le_oscThreshold (M : ABKModel d) (Q : TriadicCube d)
    {omega : CutoffSample d} (homega : omega ∉ badOsc M Q) (N : ℕ) :
    ∑ n ∈ Finset.range N, shellOscGauge Q (Q.scale + 1 + (n : ℤ)) omega ≤
      oscThreshold M Q.scale := by
  refine le_trans (Finset.sum_le_sum fun n _ => ?_)
    (oscThresholdAt_geometric_sum_le_oscThreshold M Q.scale N)
  exact shellOscGauge_le_of_notMem_badOsc M Q homega (by omega)

end

end Algsuperdiff.Section3.Provider.BadEvents
