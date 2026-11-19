/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticIndependentBlocks.lean.
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

public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Recombining independent past/innovation blocks -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_product_middle_swap {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  let h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  let h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm MeasurableEquiv.prodAssoc)
  let h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  let h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  let h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem ginibre_independent_blocks_recombine {Ω α β γ δ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    [IsProbabilityMeasure μc] [IsProbabilityMeasure μd]
    (hA : HasLaw A μa P) (hB : HasLaw B μb P)
    (hC : HasLaw C μc P) (hD : HasLaw D μd P)
    (hAB : IndepFun A B P) (hCD : IndepFun C D P)
    (hblocks : IndepFun (fun ω => (A ω, B ω)) (fun ω => (C ω, D ω)) P) :
    IndepFun (fun ω => (A ω, C ω)) (fun ω => (B ω, D ω)) P := by
  have hAC : IndepFun A C P := hblocks.comp measurable_fst measurable_fst
  have hBD : IndepFun B D P := hblocks.comp measurable_snd measurable_snd
  apply (indepFun_iff_hasLaw_prodMk_prod (hAC.hasLaw_prod hA hC)
    (hBD.hasLaw_prod hB hD)).mpr
  have h := hblocks.hasLaw_prod (hAB.hasLaw_prod hA hB) (hCD.hasLaw_prod hC hD)
  exact (ginibre_product_middle_swap μa μb μc μd).hasLaw.comp h

end
end GinibrePoincare
