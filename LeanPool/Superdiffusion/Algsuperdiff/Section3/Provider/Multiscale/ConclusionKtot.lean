/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveTermTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum

/-!
# ConclusionKtot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The layer constant `Ktot`: pricing the Step-1 increment gauge over a Whitney layer

`Provider/Multiscale/ConclusionCompetitor.lean` leaves ONE analytic datum of
the good leg of `p.bfA.multiscalebound`'s conclusion open, and names it exactly: the
binder `hgood` of `toReal_tsum_simplexPartition_cutoff_two_leg_le_payload` asks
for a layer-uniform bound

```
g_good 𝔰  ≤  Ktot . 3^{γ (k + h_k)}
```

and that module's docstring records why it cannot supply it: every factor of
the Step-1 majorant `M = stepOneLayerMajorant` depends on `□` only through
`□.scale`, which is constant on a layer the increment gauge `‖k_L −
k_{□.scale}‖²_{W^{1,∞}(□)}`, represented by `(incrementUnitCube₂ □ □.scale L
ω).w1Infinity ^ 2`.

This module prices that gauge.  It has three parts.

## 1. The missing deterministic bridge

Before this module NOTHING in the repository bounded `w1Infinity` ABOVE: the
proved `UnitCubeSkewW2Infinity` A (`toReal_eLpNorm_..._le_w1Infinity`,
`ae_abs_..._le_w1Infinity`, `w1Infinity_nonneg`) only lets `w1Infinity`
DOMINATE things, and the proved cube-level bridge
`gradientW1Infinity_incrementUnitCube₂_le` controls `gradientW1Infinity` — the
max of the S derivative gauges — which is a different quantity.

```
w1Infinity(incrementUnitCube₂ □ n L ω)
    ≤ max { 3^{2j} ‖∇(k_L − k_n)‖_{W^{1,∞}(□)} ,  ‖k_L − k_n‖_{L^∞(□)} } .
```

`w1Infinity_incrementUnitCube₂_le` is exactly this, with the first entry the
proved `incrementOscGauge₂` and the second the T per-cube uniform gauge
`Stream.cubeSupBound` of `Provider/Stream/WaveTranslation.lean` — the object
`e.km.kn.Linfty` prices at every triadic cube.  The value half is where the new
transport machinery enters: `cubeSupBound □ n L` dominates the increment
pointwise on `□` (`matrixOperatorNorm_finiteShellIncrement_le_cubeSupBound`),
and the rescaling `y ↦ 3^{j} y + z_□` carries the open unit cube into the open
cube `□` (`mem_openCubeSet_of_mem_unitOpenCube`).

## 2. The two halves, priced

* **The oscillation half is S on good cubes.**  On the complement of `B_osc(□)`
  the proved `incrementOscGauge_le_oscThreshold` (whose geometric series
  `(1/5)Σ_{n≥1}3^{-n/5} ≤ 1` is settled in `BadEvents/Definitions.lean`) gives
  `3^{2j}‖∇(k_L−k_j)‖_{W^{1,∞}(□)} ≤ δ_osc c⋆^{1/2} γ^{-1/2} 3^{γ j}`, and
  `rpow_mul_oscThreshold_sq` records the design identity behind the whole step:
  ```
  3^{−2γ j} . oscThreshold(j)²  =  δ_osc² c⋆ / γ ,      for EVERY scale j.
  ```
  So the oscillation half contributes a constant to `Ktot` with no `j`- and no
  layer-dependence at all.  `oscThreshold_mono` makes the layer-to-root
  comparison `oscThreshold(□.scale) ≤ oscThreshold(m)` for a layer cube.
* **The value half is the wave gauge**, and it is priced distributionally.
  `isBigOWith_gammaSigma_two_layerSup_cubeSupBound_cutoffLaw` prices the
  MAXIMUM over one Whitney layer at `Γ₂`: `□.scale` is constant on the layer
  (`scale_eq_of_mem_whitneyLayer`), so the transported per-cube amplitude of
  `Stream.isBigOWith_gammaSigma_cubeSupBound_cutoffLaw` is the SAME for every
  cube of the layer, and the proved finite-max estimate
  `Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty` pays exactly one `(3
  max{1, log #𝒲(□_m,k)})^{1/2}` for the whole layer.  Each cube's estimate is
  the O estimate at the translated sample; no same-sample identification is
  made anywhere.

## 3. The pricing itself

`stepOneLayerMajorant_le_ktotConst_mul` is the deterministic layer arithmetic:
with `□.scale = m − k − h_k`,

```
3^{−2γ □.scale} = 3^{−2γ m} . 3^{2γ(k+h_k)} ,
3^{ γ(i − □.scale)} = 3^{γ(i−m)} . 3^{γ(k+h_k)} ≤ 3^{γ(i−m)} . 3^{2γ(k+h_k)} ,
```

so the whole majorant is at most `ktotConst . 3^{2γ(k+h_k)}` as soon as the
gauge and the descendant weight are bounded uniformly over the layers.

```
Ktot := ktotConst M m i Cw (max (oscThreshold M m) Swave) p q ,
γ    := 2 M.gamma ,
```

at the framed loads `(σ_i^{-1/2} p, σ_i^{1/2} q)` at which Step 1 is stated.

## What is not proved in this file

* **`Swave` is not produced in this file.**  The remaining datum of the two
  a.e. theorems is a single real `Swave` dominating `cubeSupBound □ □.scale L
  ω` over ALL layers simultaneously.  `ConclusionKtotEnvelope.lean` later
  supplies the countable wave-envelope route; the declarations here retain
  `Swave` as an antecedent.
* The re-basing is not performed for the Step-2 `b_L` branch, which is a
  different display.
* **`Cw` is carried, not computed in this file.**  The descendant weight
  `multiscaleDescendantWeight □ (simplexScale m h k) (1/4) = 3^{(1 + h_{k+1} −
  h_k)/2}` is layer-dependent through the profile only; bounding it uniformly
  is an arithmetic property of `h` (for the Whitney sequence, of
  `⌈b(1−b)^{-1}k⌉`), and it is left as the caller's datum `Cw` rather than
  derived.  The gap lemma in the needed direction is proved and
  `ConclusionData` supplies the concrete choice `Cw = 3`; that downstream
  producer does not change this theorem's conditional interface.  `h_k ≤
  h_{k+1} + 1`.
* **No `3^{-3k/4}` per-layer weight** is produced or approached: blocks it
  independently, and the exponent produced here is the payload's own
  `3^{γ(k+h_k)}` growth, not a weight.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.ktotConst`

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.w1Infinity_incrementUnitCube₂_le`
* `Algsuperdiff.Section3.Provider.Multiscale.rpow_mul_oscThreshold_sq`
* `Algsuperdiff.Section3.Provider.Multiscale.w1Infinity_incrementUnitCube₂_le_max_oscThreshold`
*
`isBigOWith_gammaSigma_two_layerSup_cubeSupBound_cutoffLaw`
* `Algsuperdiff.Section3.Provider.Multiscale.stepOneLayerMajorant_le_ktotConst_mul`
* `Algsuperdiff.Section3.Provider.Multiscale.ktotConst_nonneg`

## References

* ABK26, `p.bfA.multiscalebound`, Step 1 (majorant) and Step 3; `e.Bosc.def` /
  `e.BoscL.def` / `e.Bosc.decomp`; `e.good.local.events`; `e.km.kn.Linfty`;
  `l.maximums.Gamma.s`; the normalized Sobolev norms.
* `Provider/Multiscale/ConclusionCompetitor.lean` (the consumer),
  `Provider/Stream/WaveTranslation.lean` (the transported gauge),
  `Provider/Orlicz/Maximum.lean` (the finite maximum),
  `Provider/BadEvents/IncrementOscillation.lean` (the oscillation half).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The rescaling map on the unit cube -/

private theorem toReal_eLpNorm_le' {f : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C) :
    (eLpNorm f ∞
      (volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ C := by
  by_cases hf : AEStronglyMeasurable f
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact hC
  rw [eLpNorm_exponent_top hf]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  exact eLpNormEssSup_le_of_ae_bound
    (ae_restrict_of_forall_mem
      (isOpen_openCubeSet (originCube d 0)).measurableSet hbound)

/-- The dilation `y ↦ 3^j y` carries the open unit cube into the open origin
cube of scale `j`. -/
theorem smul_mem_openCubeSet_originCube_scale {j : ℤ} {y : Vec d}
    (hy : y ∈ openCubeSet (originCube d 0)) :
    ((3 : ℝ) ^ j) • y ∈ openCubeSet (originCube d j) := by
  rw [mem_openCubeSet_originCube_iff] at hy ⊢
  intro i
  have h := hy i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hval : (((3 : ℝ) ^ j) • y) i = (3 : ℝ) ^ j * y i := rfl
  rw [hval]
  constructor
  · nlinarith [h.1, h3]
  · nlinarith [h.2, h3]

/-- **The rescaling of `cubeUnitCube` proves in the cube.**  The map `y ↦ 3^{j} y +
z_Q` of `IncrementGaugeTwoIndex.cubeUnitCube` carries the open unit cube into
the open cube `Q`, so a pointwise bound on `Q` is a pointwise bound for the
rescaled unit-cube object. -/
theorem mem_openCubeSet_of_mem_unitOpenCube (Q : TriadicCube d) {y : Vec d}
    (hy : y ∈ openCubeSet (originCube d 0)) :
    ((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q ∈ openCubeSet Q := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    mem_translateSet_iff_sub_mem, cubeBasePoint_eq_triadicCubeShift,
    add_sub_cancel_right]
  exact smul_mem_openCubeSet_originCube_scale hy

/-! ## The bridge -/

/-- **The missing upper bound on the Step-1 increment gauge.**  The frozen Section
2.4 quantity `w1Infinity` of the rescaled literal increment `k_L - k_n` on `Q`
is at most the maximum of the two halves of the manuscript's normalized
`W^{1,∞}` norm (reading):

```
w1Infinity(incrementUnitCube₂ Q n L ω)
    ≤ max { 3^{2j}‖∇(k_L−k_n)‖_{W^{1,∞}(Q)} , ‖k_L−k_n‖_{L^∞(Q)} } ,
```

the first entry the proved `incrementOscGauge₂`, the second the T per-cube
uniform gauge `Stream.cubeSupBound` of `e.km.kn.Linfty`.  No hypothesis at all:
the comparison is a pointwise statement about one shell field. -/
theorem w1Infinity_incrementUnitCube₂_le (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    (incrementUnitCube₂ Q n L omega).w1Infinity ≤
      max (incrementOscGauge₂ Q n L omega) (cubeSupBound Q n L omega.1) := by
  rw [UnitCubeSkewW2Infinity.w1Infinity]
  refine max_le ?_ ?_
  · refine le_trans ?_ (le_max_left _ _)
    refine toReal_eLpNorm_le' (cubeOscGauge_nonneg Q _) fun y hy => ?_
    have hval : Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
        ((incrementUnitCube₂ Q n L omega).firstDeriv y) =
        ShellField.matrixDerivativeNorm
          (ShellField.deriv
            (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
              (ShellField.translate (cubeBasePoint Q)
                (shellIncrement omega.1 n L))) y) := by
      rw [frozen_matrixDerivativeNorm_eq]
      rfl
    rw [Real.norm_eq_abs, hval,
      abs_of_nonneg (ShellField.matrixDerivativeNorm_nonneg _)]
    refine le_trans (matrixDerivativeNorm_deriv_le_unitCubeDerivNorm _ hy) ?_
    have hgoal : incrementOscGauge₂ Q n L omega =
        cubeOscGauge Q (shellIncrement omega.1 n L) := rfl
    rw [hgoal, ← max_unitCubeDerivNorm_cube Q (shellIncrement omega.1 n L)]
    exact le_max_right _ _
  · refine le_trans ?_ (le_max_right _ _)
    refine toReal_eLpNorm_le' (cubeSupBound_nonneg Q n L omega.1) fun y hy => ?_
    have hval : (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn.1.1 y =
        shellIncrement omega.1 n L (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q) := rfl
    rw [Real.norm_eq_abs, hval, abs_of_nonneg (matrixNorm_nonneg _),
      matrixNorm_eq_matrixOperatorNorm, shellIncrement_apply]
    exact matrixOperatorNorm_finiteShellIncrement_le_cubeSupBound omega.1 Q n L
      (mem_openCubeSet_of_mem_unitOpenCube Q hy)

/-! ## The oscillation half on good cubes -/

/-- **The `e.Bosc.def` threshold is exactly scale-invariant in the Step-1
combination.**  For every scale `j`,
`3^{-2γj} . oscThreshold(j)² = δ_osc² c⋆ / γ`.  This is why the oscillation half
of the increment gauge contributes a constant to `Ktot` with no layer
dependence whatsoever. -/
theorem rpow_mul_oscThreshold_sq (M : ABKModel d) (j : ℤ) :
    (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * oscThreshold M j ^ 2 =
      deltaOsc d ^ 2 * Algsuperdiff.Section3.Disorder.cstar M / M.gamma := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hsq : ((3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2 = (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [sq, ← Real.rpow_add (by norm_num)]
    ring_nf
  have hcancel : (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
      = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have hsc : Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 =
      Algsuperdiff.Section3.Disorder.cstar M := Real.sq_sqrt hc.le
  have hsg : (Real.sqrt M.gamma)⁻¹ ^ 2 = M.gamma⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hg.le]
  rw [oscThreshold]
  calc (3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
        (deltaOsc d * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
          (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2
      = deltaOsc d ^ 2 * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 *
          (Real.sqrt M.gamma)⁻¹ ^ 2 *
          ((3 : ℝ) ^ (-(2 * M.gamma * (j : ℝ))) *
            ((3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2) := by ring
    _ = deltaOsc d ^ 2 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ * 1 := by
        rw [hsc, hsg, hsq, hcancel]
    _ = deltaOsc d ^ 2 * Algsuperdiff.Section3.Disorder.cstar M / M.gamma := by
        field_simp

/-- The `e.Bosc.def` threshold is nondecreasing in the scale; a layer cube has
`□.scale ≤ m`, so its threshold is below the root threshold. -/
theorem oscThreshold_mono (M : ABKModel d) {j m : ℤ} (h : j ≤ m) :
    oscThreshold M j ≤ oscThreshold M m := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  have hexp : M.gamma * (j : ℝ) ≤ M.gamma * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hjm hg.le
  have hrpow : (3 : ℝ) ^ (M.gamma * (j : ℝ)) ≤ (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num)).2 hexp
  have hpre : (0 : ℝ) ≤ deltaOsc d * Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
      (Real.sqrt M.gamma)⁻¹ := by
    have h1 : (0 : ℝ) ≤ deltaOsc d := (deltaOsc_pos d).le
    have h2 : (0 : ℝ) ≤ Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) :=
      Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ (Real.sqrt M.gamma)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  rw [oscThreshold, oscThreshold]
  exact mul_le_mul_of_nonneg_left hrpow hpre

/-- **The increment gauge on a good cube.**  Off `B_osc(Q)` the oscillation half of
the bridge is the deterministic `e.Bosc.def` threshold (proved
`incrementOscGauge_le_oscThreshold`, whose geometric series is settled in
`BadEvents/Definitions.lean`), so only the wave half remains random. -/
theorem w1Infinity_incrementUnitCube₂_le_max_oscThreshold (M : ABKModel d)
    (Q : TriadicCube d) {omega : CutoffSample d} (homega : omega ∉ badOsc M Q)
    {L : ℤ} (hL : Q.scale ≤ L) :
    (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ≤
      max (oscThreshold M Q.scale) (cubeSupBound Q Q.scale L omega.1) :=
  le_trans (w1Infinity_incrementUnitCube₂_le Q Q.scale L omega)
    (max_le_max (incrementOscGauge_le_oscThreshold M Q homega hL) le_rfl)

/-! ## The layer maximum -/

/-- **The wave half, priced over a whole Whitney layer.**  `□.scale` is constant on
`𝒲(□_m,k)`, so the transported per-cube amplitude of `e.km.kn.Linfty` is the
same for every cube of the layer and the proved finite maximum estimate
`l.maximums.Gamma.s` pays exactly one log-cardinality factor for the entire
layer.  Every per-cube estimate is the O estimate at the translated sample; no
same-sample identification and no independence across cubes is used. -/
theorem isBigOWith_gammaSigma_two_layerSup_cubeSupBound_cutoffLaw (hd : 2 ≤ d)
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) {n : ℕ}
    (hne : (whitneyLayer (d := d) m hn n).Nonempty) {L : ℤ}
    (hL : m - (n : ℤ) - (hn n : ℤ) < L) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d =>
        (whitneyLayer (d := d) m hn n).sup' hne fun Q =>
          cubeSupBound Q (m - (n : ℤ) - (hn n : ℤ)) L omega.1)
      ((3 * max 1 (Real.log (((whitneyLayer (d := d) m hn n).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        ((3 * max 1 (Real.log (((subcubeShifts d (m - (n : ℤ) - (hn n : ℤ))
              (m - (n : ℤ) - (hn n : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
          (streamLinftyConst d *
            min (Real.sqrt M.gamma⁻¹)
              (Real.sqrt ((L : ℝ) - ((m - (n : ℤ) - (hn n : ℤ) : ℤ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (L : ℝ))))) := by
  have hC : (0 : ℝ) ≤ streamLinftyConst d :=
    (streamLinftyConst_pos (lt_of_lt_of_le Nat.zero_lt_one (by omega))).le
  have hmin : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹)
      (Real.sqrt ((L : ℝ) - ((m - (n : ℤ) - (hn n : ℤ) : ℤ) : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpen : (0 : ℝ) ≤ (3 * max 1 (Real.log (((subcubeShifts d (m - (n : ℤ) - (hn n : ℤ))
      (m - (n : ℤ) - (hn n : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  refine Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty _ hne (by norm_num) ?_ ?_
  · refine mul_nonneg hpen ?_
    exact mul_nonneg (mul_nonneg hC hmin) (Real.rpow_nonneg (by norm_num) _)
  · intro Q hQ
    have hscale : Q.scale = m - (n : ℤ) - (hn n : ℤ) := scale_eq_of_mem_whitneyLayer hQ
    have hbase := isBigOWith_gammaSigma_cubeSupBound_cutoffLaw M hL Q
    rw [hscale] at hbase
    exact hbase

/-! ## The layer constant -/

/-- Both `Cw` (a bound for the descendant weight along the layers) and `Sup` are
the caller's data. -/
def ktotConst (M : ABKModel d) (m i : ℤ) (Cw Sup : ℝ) (p q : Vec d) : ℝ :=
  640 * simplexCrudeConst d (1 / 4) * Cw *
      (1 + 8 * bigLambdaSensitivityConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) * Sup ^ 2) * vecNormSq p +
    320 * simplexCrudeConst d (1 / 4) * Cw *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) * vecNormSq q

/-- **The layer arithmetic.**  On `𝒲(□_m,k)` one has `□.scale = m − k − h_k`,
hence `3^{-2γ□.scale} = 3^{-2γm}3^{2γ(k+h_k)}` and
`3^{γ(i−□.scale)} = 3^{γ(i−m)}3^{γ(k+h_k)} ≤ 3^{γ(i−m)}3^{2γ(k+h_k)}`, so the
Step-1 majorant is at most `ktotConst . 3^{2γ(k+h_k)}` once the increment gauge
and the descendant weight are bounded. -/
theorem stepOneLayerMajorant_le_ktotConst_mul (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ)
    (hn : ℕ → ℕ) (n : ℕ) (i L : ℤ) (omega : CutoffSample d) {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer (d := d) m hn n) (p q : Vec d) {Cw Sup : ℝ}
    (hW : Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) ≤ Cw)
    (hSup0 : 0 ≤ Sup)
    (hw : (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ≤ Sup) :
    stepOneLayerMajorant M m hn n i L omega Q p q ≤
      ktotConst M m i Cw Sup p q *
        (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (hn n : ℝ))) := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hnh : (0 : ℝ) ≤ (n : ℝ) + (hn n : ℝ) := by positivity
  have hscale : ((Q.scale : ℤ) : ℝ) = (m : ℝ) - ((n : ℝ) + (hn n : ℝ)) := by
    rw [scale_eq_of_mem_whitneyLayer hQ]
    push_cast
    ring
  have hX : (3 : ℝ) ^ (-(2 * M.gamma * ((Q.scale : ℤ) : ℝ))) =
      (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) *
        (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (hn n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num), hscale]
    ring_nf
  have hY : (3 : ℝ) ^ (M.gamma * ((i : ℝ) - ((Q.scale : ℤ) : ℝ))) =
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) *
        (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (hn n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num), hscale]
    ring_nf
  have hw0 : (0 : ℝ) ≤ (incrementUnitCube₂ Q Q.scale L omega).w1Infinity := by
    rw [UnitCubeSkewW2Infinity.w1Infinity]
    exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)
  rw [stepOneLayerMajorant, ktotConst, hX, hY]
  set A : ℝ := simplexCrudeConst d (1 / 4) with hAdef
  set W : ℝ := Ch02.multiscaleDescendantWeight Q (simplexScale m hn n) (1 / 4) with hWdef
  set Z : ℝ := (3 : ℝ) ^ (2 * M.gamma * ((n : ℝ) + (hn n : ℝ))) with hZdef
  set Y1 : ℝ := (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (hn n : ℝ))) with hY1def
  set X0 : ℝ := (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) with hX0def
  set Y0 : ℝ := (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) with hY0def
  set w : ℝ := (incrementUnitCube₂ Q Q.scale L omega).w1Infinity with hwdef
  set K : ℝ := 8 * bigLambdaSensitivityConst d *
    (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma with hKdef
  have hA : (0 : ℝ) ≤ A := simplexCrudeConst_nonneg d (by norm_num)
  have hWnn : (0 : ℝ) ≤ W := multiscaleDescendantWeight_nonneg Q (simplexScale m hn n) (1 / 4)
  have hCw : (0 : ℝ) ≤ Cw := le_trans hWnn hW
  have hK : (0 : ℝ) ≤ K := by
    have h1 : (0 : ℝ) ≤ 8 * bigLambdaSensitivityConst d := by
      have := (bigLambdaSensitivityConst_pos hd).le
      linarith
    have h2 : (0 : ℝ) ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
      inv_nonneg.2 (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
    rw [hKdef]
    exact mul_nonneg (mul_nonneg h1 h2) hg.le
  have hZ1 : (1 : ℝ) ≤ Z := by
    rw [hZdef]
    refine Real.one_le_rpow (by norm_num) ?_
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le) hnh
    linarith
  have hZ0 : (0 : ℝ) ≤ Z := le_trans zero_le_one hZ1
  have hX0 : (0 : ℝ) ≤ X0 := Real.rpow_nonneg (by norm_num) _
  have hY0 : (0 : ℝ) ≤ Y0 := Real.rpow_nonneg (by norm_num) _
  have hY1nn : (0 : ℝ) ≤ Y1 := Real.rpow_nonneg (by norm_num) _
  have hY1Z : Y1 ≤ Z := by
    rw [hY1def, hZdef]
    refine (Real.rpow_le_rpow_left_iff (by norm_num)).2 ?_
    have h := mul_nonneg hg.le hnh
    linarith
  have hw2 : w ^ 2 ≤ Sup ^ 2 := by
    have hww : w * w ≤ Sup * Sup := mul_le_mul hw hw hw0 hSup0
    calc w ^ 2 = w * w := by ring
      _ ≤ Sup * Sup := hww
      _ = Sup ^ 2 := by ring
  have hP : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hR : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hs2 : K * X0 * w ^ 2 ≤ K * X0 * Sup ^ 2 :=
    mul_le_mul_of_nonneg_left hw2 (mul_nonneg hK hX0)
  have hinner : 1 + Z * (K * X0 * w ^ 2) ≤ Z * (1 + K * X0 * Sup ^ 2) := by
    have h1 : Z * (K * X0 * w ^ 2) ≤ Z * (K * X0 * Sup ^ 2) :=
      mul_le_mul_of_nonneg_left hs2 hZ0
    nlinarith [h1, hZ1]
  have hinner0 : (0 : ℝ) ≤ 1 + Z * (K * X0 * w ^ 2) := by
    have h0 : (0 : ℝ) ≤ Z * (K * X0 * w ^ 2) :=
      mul_nonneg hZ0 (mul_nonneg (mul_nonneg hK hX0) (sq_nonneg w))
    linarith
  have hleg1 : W * (1 + Z * (K * X0 * w ^ 2)) ≤ Cw * (Z * (1 + K * X0 * Sup ^ 2)) :=
    mul_le_mul hW hinner hinner0 hCw
  have hleg2 : W * Y1 ≤ Cw * Z := mul_le_mul hW hY1Z hY1nn hCw
  have hc1 : (0 : ℝ) ≤ 640 * A * vecNormSq p := by positivity
  have hc2 : (0 : ℝ) ≤ 320 * A * Y0 * vecNormSq q := by positivity
  have h1 : 640 * A * W * (1 + K * (X0 * Z) * w ^ 2) * vecNormSq p ≤
      640 * A * Cw * (1 + K * X0 * Sup ^ 2) * vecNormSq p * Z := by
    calc 640 * A * W * (1 + K * (X0 * Z) * w ^ 2) * vecNormSq p
        = (640 * A * vecNormSq p) * (W * (1 + Z * (K * X0 * w ^ 2))) := by ring
      _ ≤ (640 * A * vecNormSq p) * (Cw * (Z * (1 + K * X0 * Sup ^ 2))) :=
          mul_le_mul_of_nonneg_left hleg1 hc1
      _ = 640 * A * Cw * (1 + K * X0 * Sup ^ 2) * vecNormSq p * Z := by ring
  have h2 : 320 * A * W * (Y0 * Y1) * vecNormSq q ≤
      320 * A * Cw * Y0 * vecNormSq q * Z := by
    calc 320 * A * W * (Y0 * Y1) * vecNormSq q
        = (320 * A * Y0 * vecNormSq q) * (W * Y1) := by ring
      _ ≤ (320 * A * Y0 * vecNormSq q) * (Cw * Z) :=
          mul_le_mul_of_nonneg_left hleg2 hc2
      _ = 320 * A * Cw * Y0 * vecNormSq q * Z := by ring
  linarith [h1, h2]


/-! ## The good-leg pricing, a.e. -/

/-- The layer constant is nonnegative, which is what the bad-cube branch of the
good leg needs. -/
theorem ktotConst_nonneg (hd : 2 ≤ d) (M : ABKModel d) (m i : ℤ) {Cw : ℝ}
    (hCw : 0 ≤ Cw) (Sup : ℝ) (p q : Vec d) : 0 ≤ ktotConst M m i Cw Sup p q := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hA : (0 : ℝ) ≤ simplexCrudeConst d (1 / 4) :=
    simplexCrudeConst_nonneg d (by norm_num)
  have hL : (0 : ℝ) ≤ bigLambdaSensitivityConst d := (bigLambdaSensitivityConst_pos hd).le
  have hc : (0 : ℝ) ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    inv_nonneg.2 (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
  have hX : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hY : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hP : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hR : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hinner : (0 : ℝ) ≤ 1 + 8 * bigLambdaSensitivityConst d *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
      (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) * Sup ^ 2 := by
    have h0 : (0 : ℝ) ≤ 8 * bigLambdaSensitivityConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) * Sup ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hc) hg.le) hX)
        (sq_nonneg _)
    linarith
  rw [ktotConst]
  have h1 : (0 : ℝ) ≤ 640 * simplexCrudeConst d (1 / 4) * Cw *
      (1 + 8 * bigLambdaSensitivityConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) * Sup ^ 2) * vecNormSq p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCw) hinner) hP
  have h2 : (0 : ℝ) ≤ 320 * simplexCrudeConst d (1 / 4) * Cw *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (m : ℝ))) * vecNormSq q :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCw) hY) hR
  linarith


end

end Algsuperdiff.Section3.Provider.Multiscale
