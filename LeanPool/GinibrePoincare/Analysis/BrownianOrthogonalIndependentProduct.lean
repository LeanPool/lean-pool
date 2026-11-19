/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalIndependentProduct.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalFactorization

/-!
# Brownian orthogonal independent product

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `independent_pairs_on_product_measure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- Reordering two actual product pairs preserves their genuine product measure. -/
theorem measurePreserving_four_product_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (A×B)×(C×D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd)
  have h3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have h4 := measurePreserving_prodAssoc μc μb μd
  have hinner := h4.comp (h3.comp h2)
  have h5 := (MeasurePreserving.id μa).prod hinner
  have h6 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μa μc (μb.prod μd))
  convert h6.comp (h5.comp h1) using 1
  funext p
  rfl

/-- Two independent pairs, sampled independently from each other, remain
independent after grouping the first coordinates and the second coordinates. -/
theorem independent_pairs_on_product_measure {Ω Ξ A B C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → A) (Y : Ω → B) (U : Ξ → C) (V : Ξ → D)
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable U) (hV : Measurable V)
    (hXY : IndepFun X Y μ) (hUV : IndepFun U V ν) :
    IndepFun (fun p : Ω×Ξ => (X p.1, U p.2)) (fun p : Ω×Ξ => (Y p.1, V p.2)) (μ.prod ν) := by
  have hXm : Measurable (fun p : Ω×Ξ => (X p.1, U p.2)) :=
    (hX.comp measurable_fst).prodMk (hU.comp measurable_snd)
  have hYm : Measurable (fun p : Ω×Ξ => (Y p.1, V p.2)) :=
    (hY.comp measurable_fst).prodMk (hV.comp measurable_snd)
  apply (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).mpr
  have hXYm := hX.prodMk hY
  have hUVm := hU.prodMk hV
  let f := fun p : Ω×Ξ => ((X p.1, Y p.1), (U p.2, V p.2))
  let g := fun p : (A×B)×(C×D) => ((p.1.1, p.2.1), (p.1.2, p.2.2))
  have hg : Measurable g := by fun_prop
  have hf : Measurable f := hXYm.prodMap hUVm
  have hpair : (μ.prod ν).map f = ((μ.map X).prod (μ.map Y)).prod ((ν.map U).prod (ν.map V)) := by
    change (μ.prod ν).map (Prod.map (fun a => (X a, Y a)) (fun b => (U b, V b))) = _
    rw [← Measure.map_prod_map μ ν hXYm hUVm,
      hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      hUV.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
  have hshuffle := measurePreserving_four_product_shuffle (μ.map X) (μ.map Y) (ν.map U) (ν.map V)
  change (μ.prod ν).map (g ∘ f) = _
  rw [← Measure.map_map hg hf, hpair, hshuffle.map_eq]
  congr 1
  · exact Measure.map_prod_map μ ν hX hU
  · exact Measure.map_prod_map μ ν hY hV

end
end GinibrePoincare
