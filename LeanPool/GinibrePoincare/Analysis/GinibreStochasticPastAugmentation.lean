/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticPastAugmentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyFiltration

/-! Genuine null augmentation of the actual joint Brownian past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The augmentation of the σ-algebra `m` by all `P`-null sets. -/
@[instance_reducible]
def ginibreNullAugmentation {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω :=
  m ⊔ MeasurableSpace.generateFrom {s : Set Ω | P s = 0}

theorem ginibreNullAugmentation_base_le {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : m ≤ ginibreNullAugmentation (mAmbient := mAmbient) P m := le_sup_left

theorem ginibreNullAugmentation_null_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P :
    Measure Ω)
    (m : MeasurableSpace Ω) (s : Set Ω) (hs : P s = 0) :
    @MeasurableSet Ω (ginibreNullAugmentation (mAmbient := mAmbient) P m) s :=
  (show MeasurableSpace.generateFrom {s : Set Ω | P s = 0} ≤ ginibreNullAugmentation (mAmbient :=
      mAmbient) P m from le_sup_right) _ (MeasurableSpace.GenerateMeasurable.basic s hs)

theorem ginibreNullAugmentation_le {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) :
    ginibreNullAugmentation (mAmbient := mAmbient) P m ≤ mAmbient := by
  apply sup_le hm
  exact MeasurableSpace.generateFrom_le (fun s hs => measurableSet_of_null hs)

theorem ginibreNullAugmentation_trim_complete {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P :
    Measure Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) :
    (P.trim (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm)).IsComplete := by
  constructor
  intro s hs
  exact ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m s
    (measure_eq_zero_of_trim_eq_zero (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm) hs)

theorem ginibreNullAugmentation_ae_transfer {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure
    Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) (p : Ω → Prop)
    (hp : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂P.trim (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm), p
        ω := by
  rw [ae_iff] at hp ⊢
  rw [trim_measurableSet_eq _ (ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _
      hp)]
  exact hp

/-- The natural filtration of a family of real pre-Brownian motions, augmented by the `P`-null
sets. -/
def ginibreBrownianAugmentedFiltration {Ω ι : Type*} [mAmbient : MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Filtration ℝ≥0 mAmbient where
  seq s := ginibreNullAugmentation (mAmbient := mAmbient) P (ginibreBrownianFamilyPastSpace B s)
  mono' _ _ hst := sup_le_sup_right (ginibreBrownianFamilyPastSpace_mono B hst) _
  le' s := ginibreNullAugmentation_le (mAmbient := mAmbient) P _ (ginibreBrownianFamilyPastSpace_le
      B P hB s)

end
end GinibrePoincare
