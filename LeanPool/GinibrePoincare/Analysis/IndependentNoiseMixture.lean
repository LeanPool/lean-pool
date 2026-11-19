/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/IndependentNoiseMixture.lean.
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

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Independent noise mixture

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `independentNoiseMixture_joint_law`, `independentNoiseMixture_joint_law_ae`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare
noncomputable section

/-- Mixing arbitrary initial parameters preserves independence from a fixed
noise marginal when the true fiber joint laws factor for almost every parameter. -/
theorem independentNoiseMixture_joint_law_ae
    {A Ω E F : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure A) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (X : A × Ω → E) (N : Ω → F) (hX : Measurable X) (hN : Measurable N)
    (hfiber : ∀ᵐ a ∂μ, P.map (fun x => (X (a, x), N x)) =
      (P.map (fun x => X (a, x))).prod (P.map N)) :
    (μ.prod P).map (fun p => (X p, N p.2))=((μ.prod P).map X).prod (P.map N) := by
  have hJ : Measurable (fun p : A×Ω => (X p, N p.2)) := hX.prodMk (hN.comp measurable_snd)
  apply Measure.ext_prod
  intro s t hs ht
  have hXs (a : A) : Measurable (fun x => X (a, x)) := hX.comp measurable_prodMk_left
  have hpair : ∀ᵐ a ∂μ,
      P {x | X (a, x)∈s ∧ N x∈t}=(P {x | X (a, x)∈s})*((P.map N) t) := by
    filter_upwards [hfiber] with a ha
    have h := congrArg (fun ν : Measure (E×F) => ν (s×ˢt)) ha
    rw [Measure.map_apply ((hXs a).prodMk hN) (hs.prod ht), Measure.prod_prod,
      Measure.map_apply (hXs a) hs] at h
    exact h
  rw [Measure.map_apply hJ (hs.prod ht), Measure.prod_apply (hJ (hs.prod ht)), Measure.prod_prod,
    Measure.map_apply hX hs, Measure.prod_apply (hX hs)]
  change (∫⁻ a, P {x | X (a, x)∈s ∧ N x∈t} ∂μ)=
    (∫⁻ a, P {x | X (a, x)∈s} ∂μ)*((P.map N) t)
  calc
    _ = ∫⁻ a, (P {x | X (a, x)∈s})*((P.map N) t) ∂μ := lintegral_congr_ae hpair
    _ = _ := lintegral_mul_const _ (measurable_measure_prodMk_left (hX hs))

/-- Mixing arbitrary initial parameters preserves independence from a fixed
noise marginal when the true fiber joint laws factor. -/
theorem independentNoiseMixture_joint_law
    {A Ω E F : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure A) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (X : A × Ω → E) (N : Ω → F) (hX : Measurable X) (hN : Measurable N)
    (hfiber : ∀ a, P.map (fun x => (X (a, x), N x)) =
      (P.map (fun x => X (a, x))).prod (P.map N)) :
    (μ.prod P).map (fun p => (X p, N p.2))=((μ.prod P).map X).prod (P.map N) :=
  independentNoiseMixture_joint_law_ae μ P X N hX hN (Filter.Eventually.of_forall hfiber)

end
end GinibrePoincare
