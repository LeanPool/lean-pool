/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.GradNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ValueBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MajorantSlots

/-!
# ShellSlotBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two gauge slots, resolved into a head block and an `L`-carrying tail

Nothing here imports that file, and nothing here claims the anchor.

## The shell-sum route

`MajorantSlots.lean` isolates the whole `L`-dependence of Step 3's display in
the two gauges of the recentered shell `h = k_L − k_{j−2} − (k_L − k_m)_{□_m}`.
This module resolves both gauges into

```
(an L-FREE head block over the layers k ∈ (j−2, m])  +  (a tail over k ∈ (m, L]) ,
```

using only proved material:

* the gradient slot -- `Annular.gradientW1Infinity_centeredShellUnitCube_le`
  (the cube-scale normalization: the centering constant is invisible to a
  gradient gauge) followed by `Support.shellW1InfGradNorm_translate_shellIncrement_split`
  (the manuscript's `∇(k_L − k_{j−2}) = Σ ∇j_k` plus the triangle inequality,
  split at `m`);
* the value slot -- `Annular.valueL2_centeredShellUnitCube_le` (the
  manuscript's own split: the `L^∞` content of `k_m − k_{j−2}` on `3^j v + □_j`
  plus the mean-value bound for `k_L − k_m − (k_L − k_m)_{□_m}` on `□_m`)
  followed by the same layer expansion at the origin cube of scale `m`.

Both tails are values of ONE functional of the shell stream, the
`(m, L]`-layer gauge sum

```
tailLayerSum k v ω L = Σ_{i ∈ (m, L]} ‖∇ j_i‖_{W^{1,∞}(3^k v + □_k)} ,
```

which is nondecreasing in `L`.  An `L`-free bound for it is therefore the ONLY
`L`-uniformity input the whole majorant needs; it is a parameter here
(`hT`), disclosed below.

## The disclosed obligation `hT`, and why it is not discharged here

`hT` asks for a real `T k v ω` dominating the tail sums for every `L ≥ m`, i.e.
for the convergence of the upper shell series with an explicit bound.  This is a
genuine mathematical input about the stream, not a source premise and not a
proof step in disguise:

* it holds almost surely (each layer gauge is `O_{Γ₂}(3^{(γ−1)k})` by
  `Stream.isBigOWith_gammaSigma_shellDerivGauge_cube`, and `γ < 1`), but
* it hold for every `ω` in the carrier: `Cutoff.CutoffSample` constrains only
  the *lower* tails (`Cutoff.LowerTailGood`), so the upper shell series
  diverges on a (null, nonempty) set of sequences.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 3); (`e.ugly.estimate.for.J.pre`, the
  gradient slot); (the layer expansion); (`e.jk.O`, `e.nabla.jk.O`).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## The layer gauge sums -/

/-- The head block of the layer expansion at the cube `3^k v + □_k`: the layers
`i ∈ (k−2, m]`, which is the block the Step-3 display resums.  `L`-free. -/
def headLayerSum (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ i ∈ Finset.Ioc (k - 2) m,
    Support.shellW1InfGradNorm k
      (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 i))

/-- The tail block of the layer expansion at the cube `3^k v + □_k`: the layers
`i ∈ (m, L]`, i.e. the `k > m` block.  This is the ONLY carrier of `L` in the
whole majorant. -/
def tailLayerSum (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) (L : ℤ) : ℝ :=
  ∑ i ∈ Finset.Ioc m L,
    Support.shellW1InfGradNorm k
      (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 i))

theorem headLayerSum_nonneg (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ headLayerSum m k v omega :=
  Finset.sum_nonneg fun _ _ => Support.shellW1InfGradNorm_nonneg _ _

/-- The layer gauge extended by zero below the recentering scale: the canonical
`ℤ`-indexed summand of the upper shell series. -/
def tailLayerTerm (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) (i : ℤ) : ℝ :=
  if m < i then
    Support.shellW1InfGradNorm k
      (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 i))
  else 0

theorem tailLayerTerm_nonneg (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d)
    (i : ℤ) : 0 ≤ tailLayerTerm m k v omega i := by
  unfold tailLayerTerm
  split
  · exact Support.shellW1InfGradNorm_nonneg _ _
  · exact le_rfl

/-- **The canonical tail gauge**: the value of the upper shell series. -/
def tailSeriesGauge (m k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑' i : ℤ, tailLayerTerm m k v omega i

/-- **The obligation `hT`, reduced to summability.**

If the upper shell series converges at `ω`, its value is an `L`-uniform bound for
every tail block.  This is the exact bridge from a probabilistic
summability statement to the `L`-freeness input used below: no other property of
the stream is needed. -/
theorem tailLayerSum_le_tailSeriesGauge (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (hsum : Summable (tailLayerTerm m k v omega))
    (L : ℤ) : tailLayerSum m k v omega L ≤ tailSeriesGauge m k v omega := by
  have hcongr : tailLayerSum m k v omega L =
      ∑ i ∈ Finset.Ioc m L, tailLayerTerm m k v omega i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmi : m < i := (Finset.mem_Ioc.mp hi).1
    unfold tailLayerTerm
    rw [ite_eq_left hmi]
  rw [hcongr]
  exact hsum.sum_le_tsum (Finset.Ioc m L)
    (fun i _ => tailLayerTerm_nonneg m k v omega i)

/-! ## The gradient slot -/

/-- **The gradient gauge of the recentered shell, split at `m`.**

The cube-scale normalization of `Annular.GradNormalization` followed by the
layer expansion of `Support.shellW1InfGradNorm_translate_shellIncrement_split`.
The head block is `L`-free; the tail block is the `k > m` layer sum. -/
theorem gradientW1Infinity_step3Shell_le_head_add_tail (M : ABKModel d) {L m : ℤ}
    (R : TriadicCube d) (hle : R.scale - 2 ≤ L) (h2m : R.scale - 2 ≤ m) (hmL : m ≤ L)
    (omega : Cutoff.CutoffSample d) :
    (step3Shell M L m R hle omega).gradientW1Infinity ≤
      (3 : ℝ) ^ (2 * (R.scale : ℝ)) *
        (headLayerSum m R.scale R.index omega + tailLayerSum m R.scale R.index omega L) := by
  refine le_trans (gradientW1Infinity_centeredShellUnitCube_le M R.scale R.index hle omega
    (Support.fluxIncrementAverage M L m (originCube d m) omega)
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  exact Support.shellW1InfGradNorm_translate_shellIncrement_split R.scale R.index omega.1
    h2m hmL

/-- **The `L`-free gradient slot**, at a caller-supplied tail gauge `T`. -/
def lFreeGradSlot (m : ℤ) (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  (3 : ℝ) ^ (2 * (R.scale : ℝ)) *
    (headLayerSum m R.scale R.index omega + T R.scale R.index omega)

/-- **The gradient slot bound, `L`-free.**  Every `L ≥ m` obeys the same bound
once the tail gauge is `L`-uniform. -/
theorem gradientW1Infinity_step3Shell_le_lFreeGradSlot (M : ABKModel d) {m : ℤ}
    (R : TriadicCube d) (h2m : R.scale - 2 ≤ m)
    (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d)
    (hT : ∀ L : ℤ, m ≤ L → tailLayerSum m R.scale R.index omega L ≤
      T R.scale R.index omega)
    (L : ℤ) (hle : R.scale - 2 ≤ L) (hmL : m ≤ L) :
    (step3Shell M L m R hle omega).gradientW1Infinity ≤ lFreeGradSlot m T R omega := by
  refine le_trans (gradientW1Infinity_step3Shell_le_head_add_tail M R hle h2m hmL omega) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  have := hT L hmL
  linarith only [this]

/-! ## The value slot -/

/-- The frozen centered shell depends on its centering constant only through the
constant's value.  (Re-derivation of the `private` helper of
`Annular/ValueBridge.lean`.) -/
private theorem centeredShellUnitCube_congr_const (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : Cutoff.CutoffSample d) {C₁ C₂ : Mat d}
    (h₁ : matTranspose C₁ = -C₁) (h₂ : matTranspose C₂ = -C₂) (hC : C₁ = C₂) :
    centeredShellUnitCube M Q hle omega C₁ h₁ =
      centeredShellUnitCube M Q hle omega C₂ h₂ := by
  subst hC
  rfl

/-- The scale-`k` lattice point at index `0` is the origin. -/
private theorem triadicLatticePoint_zero (k : ℤ) :
    Support.triadicLatticePoint k (0 : Fin d → ℤ) = (0 : Vec d) := by
  funext i
  change (3 : ℝ) ^ k * (((0 : Fin d → ℤ) i : ℤ) : ℝ) = 0
  rw [Pi.zero_apply, Int.cast_zero, mul_zero]

/-- **The mean-value tail of the value slot, expanded into layers.**

`3^{2m} ‖∇(k_L − k_m)‖_{W^{1,∞}(□_m)}` is at most the `(m, L]` layer sum at the
origin cube of scale `m`, by the same triangle inequality. -/
theorem shellW1InfGradNorm_shellIncrement_le_tailLayerSum (omega : Cutoff.CutoffSample d)
    (m L : ℤ) :
    Support.shellW1InfGradNorm m (shellIncrement omega.1 m L) ≤
      tailLayerSum m m (0 : Fin d → ℤ) omega L := by
  have hbase := Support.shellW1InfGradNorm_translate_shellIncrement_le m
    (0 : Fin d → ℤ) omega.1 m L
  rw [triadicLatticePoint_zero, shellField_translate_zero] at hbase
  refine le_trans hbase (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [triadicLatticePoint_zero, shellField_translate_zero]

/-- **The `L²` gauge of the recentered shell, split at `m`.**

`Annular.valueL2_centeredShellUnitCube_le` at the manuscript's own centering
constant `(k_L − k_m)_{□_m}`, with the mean-value tail expanded into layers.
The first summand is `L`-free. -/
theorem valueL2_step3Shell_le_head_add_tail (M : ABKModel d) {L m : ℤ}
    (R : TriadicCube d) (hle : R.scale - 2 ≤ L) (hnm : R.scale ≤ m) (hmL : m ≤ L)
    (hv : R.index ∈ Support.latticeCubeSet d R.scale m) (omega : Cutoff.CutoffSample d) :
    (step3Shell M L m R hle omega).valueL2 ≤
      Cutoff.localCubeControl R.scale
          (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
            (shellIncrement omega.1 (R.scale - 2) m)) +
        centeringConst d *
          ((3 : ℝ) ^ (2 * m) * tailLayerSum m m (0 : Fin d → ℤ) omega L) := by
  have hCeq := fluxIncrementAverage_eq_cubeAverageMat M hmL (originCube d m) omega
  have hkey := valueL2_centeredShellUnitCube_le M hnm hmL hle hv omega
    (matTranspose_cubeAverageMat_shellIncrement M hmL omega)
  have hstep : (step3Shell M L m R hle omega).valueL2 ≤
      Cutoff.localCubeControl R.scale
          (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
            (shellIncrement omega.1 (R.scale - 2) m)) +
        centeringConst d *
          ((3 : ℝ) ^ (2 * m) * Support.shellW1InfGradNorm m (shellIncrement omega.1 m L)) := by
    rw [step3Shell, centeredShellUnitCube_congr_const M R hle omega
      (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
      (matTranspose_cubeAverageMat_shellIncrement M hmL omega) hCeq]
    exact hkey
  refine le_trans hstep (add_le_add le_rfl ?_)
  have hcc : (0 : ℝ) ≤ centeringConst d := by
    rw [centeringConst]; positivity
  refine mul_le_mul_of_nonneg_left ?_ hcc
  exact mul_le_mul_of_nonneg_left
    (shellW1InfGradNorm_shellIncrement_le_tailLayerSum omega m L) (by positivity)

/-- **The `L`-free value slot**, at a caller-supplied tail gauge `T`. -/
def lFreeValueSlot (m : ℤ) (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  Cutoff.localCubeControl R.scale
      (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
        (shellIncrement omega.1 (R.scale - 2) m)) +
    centeringConst d * ((3 : ℝ) ^ (2 * m) * T m (0 : Fin d → ℤ) omega)

/-- **The value slot bound, `L`-free.** -/
theorem valueL2_step3Shell_le_lFreeValueSlot (M : ABKModel d) {m : ℤ}
    (R : TriadicCube d) (hnm : R.scale ≤ m)
    (hv : R.index ∈ Support.latticeCubeSet d R.scale m)
    (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (omega : Cutoff.CutoffSample d)
    (hT : ∀ L : ℤ, m ≤ L → tailLayerSum m m (0 : Fin d → ℤ) omega L ≤
      T m (0 : Fin d → ℤ) omega)
    (L : ℤ) (hle : R.scale - 2 ≤ L) (hmL : m ≤ L) :
    (step3Shell M L m R hle omega).valueL2 ≤ lFreeValueSlot m T R omega := by
  refine le_trans (valueL2_step3Shell_le_head_add_tail M R hle hnm hmL hv omega) ?_
  refine add_le_add le_rfl ?_
  have hcc : (0 : ℝ) ≤ centeringConst d := by
    rw [centeringConst]; positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hT L hmL) (by positivity)) hcc

end

end Algsuperdiff.Section4.Provider.BoundsEaL
