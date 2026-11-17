/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MeasureTransport.lean.
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

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Transporting densities through measure-preserving equivalences -/


@[expose] public section


open MeasureTheory

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- A density pulled back along a measure-preserving measurable equivalence
pushes forward to the original density. -/
theorem MeasurePreserving.map_withDensity_comp
    (e : α ≃ᵐ β) (h : MeasurePreserving e μ ν)
    {f : β → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity (f ∘ e)) = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  exact h.setLIntegral_comp_preimage hs hf

/-- Specialization to the standard real-coordinate representation of `ℂ`. -/
theorem map_complexPi_withDensity
    {f : ℂ → ENNReal} (hf : Measurable f) :
    Measure.map Complex.measurableEquivPi.symm
        ((volume : Measure (Fin 2 → ℝ)).withDensity
          (f ∘ Complex.measurableEquivPi.symm)) =
      (volume : Measure ℂ).withDensity f := by
  exact MeasurePreserving.map_withDensity_comp _
    Complex.volume_preserving_equiv_pi.symm hf

end MeasureTheory
