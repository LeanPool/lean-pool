/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderProducer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepConditional

/-!
# OneStepSchauderChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The excess-decay one-step contraction with the Schauder gradient-Hölder estimate
discharged (interior branch)

`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` carries **two** open inputs:
`hharm` (the harmonic-approximation anchor, transcribed) and the four-slot package `hint /
hgrad / hhol / hschauder`, i.e. the Schauder gradient-Hölder estimate.
`OneStepSchauderProducer.exists_gradientHolder_interior` proves the second one on the
**interior branch**.

The Schauder constant is now a definite closed-form dimensional constant,

```text
  Csch = schauderWindowConst d = 48 · 3^{3/2} · schauderConst d · √((12(d+1))^d) ,
  schauderConst d = d · C_native(d) ,
```

and the boundary-datum leg is `K_h = 0`.

## What is still assumed about the competitor

`hharmclass`: the competitor `v` is **classically** harmonic on the replacement
window `(x + □_{n-2}) ∩ □_m` (Mathlib's `InnerProductSpace.HarmonicOnNhd`,
transported across `toEuc`).  The producer of the competitor
(`ResidualCorrectorExistence`) delivers the *variational*
`Support.IsWeaklyHarmonicOn`; `OneStepSchauderWeyl` bridges variational to
classical **for the CoarseGraining convex smoothings** of the competitor, at
the full radius.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction on the interior branch, with the
gradient-Hölder Schauder estimate discharged.**

Identical to `excessDecay_oneStep_of_harmonicApprox` except that the four
Schauder slots are replaced by classical harmonicity of the
competitor on the replacement window; the constant is
`Csch = schauderWindowConst d` and the boundary-datum leg is `K_h = 0`. -/
theorem excessDecay_oneStep_interior_of_harmonicApprox [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    (hharmclass : HarmonicOnNhd (v ∘ Schauder.toEuc.symm)
      ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)))
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (schauderWindowConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * 0 := by
  -- the competitor is `L²` on the enveloping window
  have hsub : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega : n - 2 ≤ n)
  have hvsub : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hv.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (v y - affineEval c g y) ^ 2)
        (truncatedWindow x m (n - 2)) volume :=
    fun c g => integrableOn_sub_affineEval_sq_truncatedWindow x hvsub c g
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    Schauder.exists_gradientHolder_interior hd hx (by omega : n - 3 ≤ m) hcube hharmclass hintsq
  exact excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv huv hmem hB
    hharm hK (schauderWindowConst_nonneg d) hint hgrad hhol hschauder

end

end Algsuperdiff.Section4.Provider.ExcessDecay
