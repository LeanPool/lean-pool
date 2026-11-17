/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreLebesgueL2Transfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDensityBound

/-! # Continuous transfer from Lebesgue L² to Ginibre L² -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The canonical continuous linear map induced by the finite density bound. -/
def ginibreL2OfLebesgue (n : ℕ) (hn : 0 < n) :
    Lp V 2 (volume : Measure (Configuration n)) →L[ℝ] Lp V 2 (ginibreMeasure n) :=
  Lp.LpToLpOfMeasureLeSMul
    (Classical.choose_spec (ginibreMeasure_le_finite_smul_volume n hn)).1
    (Classical.choose_spec (ginibreMeasure_le_finite_smul_volume n hn)).2

/-- The transfer preserves the underlying representative almost everywhere. -/
theorem ginibreL2OfLebesgue_ae (n : ℕ) (hn : 0 < n)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    (ginibreL2OfLebesgue n hn u : Configuration n → V) =ᵐ[ginibreMeasure n] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

/-- Transfer of an actual L² representative is its Ginibre L² class. -/
theorem ginibreL2OfLebesgue_toLp (n : ℕ) (hn : 0 < n)
    (f : Configuration n → V) (hf : MemLp f 2 volume) :
    ginibreL2OfLebesgue n hn (hf.toLp f) =
      (memLp_ginibre_of_volume n hn f hf).toLp f := by
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  have hac : ginibreMeasure n ≪ (volume : Measure (Configuration n)) :=
    Measure.absolutelyContinuous_of_le_smul hm
  apply Lp.ext
  exact (ginibreL2OfLebesgue_ae n hn (hf.toLp f)).trans
    ((hac.ae_eq hf.coeFn_toLp).trans (memLp_ginibre_of_volume n hn f hf).coeFn_toLp.symm)

/-- Ordinary L² convergence of actual representatives implies Ginibre L² convergence. -/
theorem ginibre_toLp_tendsto_of_volume (n : ℕ) (hn : 0 < n)
    (f : ℕ → Configuration n → V) (hf : ∀ m, MemLp (f m) 2 volume)
    (g : Configuration n → V) (hg : MemLp g 2 volume)
    (ht : Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun m => (memLp_ginibre_of_volume n hn (f m) (hf m)).toLp (f m))
      atTop (𝓝 ((memLp_ginibre_of_volume n hn g hg).toLp g)) := by
  have hmap := (ginibreL2OfLebesgue n hn (V := V)).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ginibreL2OfLebesgue_toLp] using hmap

end
end GinibrePoincare
