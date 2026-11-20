/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEOrderedDensity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEMarginalIntegrals
/-!
# Correspondence GUE ordered density

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueOrderedRawDensity_eq_chamber_density`.
-/

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
/-- Classical decidability of every proposition, used locally in this file. -/
local instance instDecidableCorrespondenceGUEOrderedDensity (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem gueOrderedRawDensity_eq_chamber_density (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gueOrderedRawDensity n x=if x∈gueStrictChamber n then gueRawDensity n x else 0 := by
  by_cases hx : x∈gueStrictChamber n
  · rw [ite_eq_left hx]
    unfold gueOrderedRawDensity gueRawDensity
    congr 1
    · rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    · apply Finset.prod_congr rfl
      intro p hp
      have hij := (Finset.mem_filter.mp hp).2
      exact ite_eq_left (sub_pos.mpr (hx _ _ hij))
  · rw [ite_eq_right hx]
    unfold gueOrderedRawDensity
    have he : ∃p∈guePairs n, ¬(0<x p.2-x p.1) := by
      simp only [gueStrictChamber, mem_ofPred_eq, not_forall] at hx
      obtain ⟨i, j, hij, hgap⟩ := hx
      exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        fun h => hgap (sub_pos.mp h)⟩
    obtain ⟨p, hp, hgap⟩ := he
    have hz : gueOrderedPairWeight (x p.2-x p.1)=0 := ite_eq_right hgap
    rw [Finset.prod_eq_zero hp hz, mul_zero]

end
end GinibrePoincare
