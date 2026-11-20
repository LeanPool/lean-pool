/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff

/-!
# Correspondence collision coordinates

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollisionSplit_apply`, `correspondenceCollisionSplit_volume`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal

/-- Split off one genuine complex particle coordinate from product Lebesgue measure. -/
def correspondenceCollisionSplit {n : ℕ} (j : Fin n) :
    Configuration n ≃ᵐ ℂ × ({k : Fin n // k ≠ j} → ℂ) := by
  classical
  letI : Unique {k : Fin n // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k => Subtype.ext k.property⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℂ) (fun k => k = j)).trans
    ((MeasurableEquiv.piUnique (fun _ : {k : Fin n // k = j} => ℂ)).prodCongr
      (MeasurableEquiv.refl _))

theorem correspondenceCollisionSplit_apply {n : ℕ} (j : Fin n) (z : Configuration n) :
    correspondenceCollisionSplit j z = (z j, fun k => z k.val) := by
  rfl

theorem correspondenceCollisionSplit_volume {n : ℕ} (j : Fin n) :
    MeasurePreserving (correspondenceCollisionSplit j)
      (volume : Measure (Configuration n)) volume := by
  classical
  let : Unique {k : Fin n // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k => Subtype.ext k.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => (volume : Measure ℂ)) (fun k => k = j)
  rw [show Subtype.fintype (fun k : Fin n => k = j) = Fintype.subtypeEq j
    from Subsingleton.elim _ _] at hs
  have h := ((measurePreserving_piUnique (fun _ : {k : Fin n // k = j} =>
      (volume : Measure ℂ))).prod
    (MeasurePreserving.id (Measure.pi fun _ : {k : Fin n // k ≠ j} =>
      (volume : Measure ℂ)))).comp
    hs
  simp only [Measure.volume_eq_prod, volume_pi] at h ⊢
  convert h using 1
  funext z
  rfl

end
end GinibrePoincare

