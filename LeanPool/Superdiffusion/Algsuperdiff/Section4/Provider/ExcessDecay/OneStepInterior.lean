/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# OneStepInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior one-step consumers, re-gated at the clause event

**Strict additions.**  Nothing proved is edited: each theorem here is a new
`_regated` sibling of a proved one-step consumer, stating the SAME conclusion from
the SAME hypotheses except that the anchor display `hharm` is read on the
frozen good event `𝒢(n-2+3, z; s/8, Cv⁻¹ s⁴)` instead of the
literal `𝒢(n-2+3, z; s/8, 1/2)`.

## Why the re-gating is free

Every one of these consumers already carries `hmem`: the sample `ω` is *in* the
printed good-scale event `𝒢(n-2+3, z; s/8, (s/8)√δ)`.  As soon as that supply
threshold sits below the display's threshold — the hypothesis `hrep`, priced by
`RebaseEpsilon.excessDecayDelta_repriced` at `δ ≤ 64 Cv⁻² s⁶` — both
indicators collapse to the same value at `ω`, so a `Cv⁻¹ s⁴`-gated display and a
`(1/2)`-gated one are interchangeable *at that `ω`*
(`indicator_goodEventAt_transfer`).  No analysis, no measurability, no constant
moves.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The re-gated sibling of**
`OneStepSchauderComposeInterior.excessDecay_oneStep_interior_of_weaklyHarmonic`.

Statement transcribed byte-for-byte from the proved theorem, with the `hharm`
display re-gated at the frozen threshold `Cv⁻¹ s⁴` and the reachability
hypothesis `hrep` inserted.  The printed supply event `𝒢(n-2+3, z; s/8,
(s/8)√δ)` sits below both thresholds, so the two indicators agree at the
witnessed `ω` and the re-gating is free.
-/
theorem excessDecay_oneStep_interior_of_weaklyHarmonic_regated [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    {w : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)))}
    (hw : IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) w)
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    {Cv : ℝ}
    (hrep : s / 8 * Real.sqrt delta ≤ Cv⁻¹ * s ^ (4 : ℕ))
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (Cv⁻¹ * s ^ (4 : ℕ)))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - w.toFun y) 2
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
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  refine excessDecay_oneStep_interior_of_weaklyHarmonic hd hk hs hs1 hdelta1 hx hnm hcube hu hw hmem hB ?_
  exact indicator_goodEventAt_transfer hep0 hrep hhalf hmem hharm

end

end Algsuperdiff.Section4.Provider.ExcessDecay
