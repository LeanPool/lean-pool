/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSymmetry
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorGraph

/-! # The differential pregenerator belongs to the full operator graph -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory

/-- The value of a smooth collision-free core function in the symmetric L² space. -/
def ginibreFullCoreSymmetricValue {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricValues n :=
  ⟨ginibreFullCoreValue hn f hf, fun σ => ((ginibreFullCorePair hn f hf).property.2 σ).1⟩

/-- The pregenerator of a smooth core function in the symmetric L² space. -/
def ginibreFullCoreSymmetricPregenerator {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricValues n :=
  ⟨ginibreFullCorePregenerator hn f hf, ginibreFullCorePregenerator_symmetric hn f hf⟩

theorem ginibreFullGenerator_real_core_resolvent {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricResolvent n hn
      (ginibreFullCoreSymmetricValue hn f hf - ginibreFullCoreSymmetricPregenerator hn f hf) =
      ginibreFullCoreSymmetricValue hn f hf := by
  apply Subtype.ext
  exact ginibreFullGenerator_resolvent_core hn f hf

/-- Every concrete smooth collision-free symmetric core function lies in the
actual full symmetric generator graph, with its original pregenerator image. -/
theorem ginibreFullGenerator_core_graph {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricValue hn f hf),
      ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricPregenerator hn f hf)) ∈
      (ginibreFullGenerator n hn).graph := by
  rw [ginibreFullGenerator_graph_iff]
  rw [← map_sub, ginibreFullComplexResolvent_ofReal,
    ginibreFullGenerator_real_core_resolvent]

end GinibrePoincare
