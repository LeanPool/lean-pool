/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESplitVolume.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESplitDensity
/-!
# Correspondence GUE split volume

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueSplitMeasurableEquiv_apply`, `gueSplit_volume_preserving`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The equivalence `Fin n ⊕ Fin n ≃ Fin n × Fin 2` sending `inl i` to `(i, 0)` and `inr i` to
`(i, 1)`. -/
def gueSplitIndex (n : ℕ) : Fin n⊕Fin n ≃ Fin n×Fin 2 where
  toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  invFun p := if p.2=0 then Sum.inl p.1 else Sum.inr p.1
  left_inv s := by cases s <;> simp
  right_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp

/-- The measurable equivalence `x ↦ (gueRealProjection n x, gueAuxProjection n x)` from
`EuclideanSpace ℝ (Fin n × Fin 2)` to a product of two copies of `EuclideanSpace ℝ (Fin n)`. -/
def gueSplitMeasurableEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n×Fin 2) ≃ᵐ
    EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Fin n×Fin 2→ℝ)).symm |>.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n⊕Fin n => ℝ) (gueSplitIndex n).symm).trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin n => ℝ)).trans
        ((MeasurableEquiv.toLp 2 (Fin n→ℝ)).prodCongr (MeasurableEquiv.toLp 2 (Fin n→ℝ)))))

theorem gueSplitMeasurableEquiv_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    gueSplitMeasurableEquiv n x=(gueRealProjection n x, gueAuxProjection n x) := by
  rfl

theorem gueSplit_volume_preserving (n : ℕ) :
    MeasurePreserving (gueSplitMeasurableEquiv n) volume (volume.prod volume) := by
  have h₁ := (PiLp.volume_preserving_toLp (Fin n×Fin 2)).symm
    (MeasurableEquiv.toLp 2 (Fin n×Fin 2→ℝ))
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n⊕Fin n => ℝ) (gueSplitIndex n).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n⊕Fin n => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin n)).prod (PiLp.volume_preserving_toLp (Fin n))
  exact h₄.comp (h₃.comp (h₂.comp h₁))

end
end GinibrePoincare
