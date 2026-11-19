/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevReindex.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialTests
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialImagTests

/-! # Moving an arbitrary entry derivative to the actual first coordinate -/

@[expose] public section
open MeasureTheory MvPolynomial
namespace GinibrePoincare
noncomputable section

/-- The relabelling of configurations swapping particles `0` and `j`. -/
def configurationFirstReindex {d : ℕ} (j : Fin (d + 1)) :
    Configuration (d + 1) ≃L[ℝ] Configuration (d + 1) :=
  { toFun := fun z i => z (Equiv.swap 0 j i)
    invFun := fun z i => z (Equiv.swap 0 j i)
    left_inv := by intro z; funext i; simp
    right_inv := by intro z; funext i; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

theorem configurationFirstReindex_direction {d : ℕ} (j : Fin (d + 1)) (a : ℂ) :
    configurationFirstReindex j (Fin.cons a 0) = coordinateDirection j a := by
  classical
  have he : (Fin.cons a 0 : Configuration (d + 1)) = Pi.single 0 a := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  rw [he]
  funext i
  change (Pi.single 0 a : Configuration (d + 1)) (Equiv.swap 0 j i) = coordinateDirection j a i
  simp only [coordinateDirection, Pi.single_apply]
  have hi : Equiv.swap 0 j i = 0 ↔ i = j := by
    rw [← Equiv.eq_symm_apply]
    simp
  simp [hi]

theorem configurationFirstReindex_volume_preserving {d : ℕ} (j : Fin (d + 1)) :
    MeasurePreserving (configurationFirstReindex j) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) => ℂ) (Equiv.swap 0 j)
  convert h using 1
  funext z i
  change z (Equiv.swap 0 j i) = (Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℂ) (Equiv.swap 0 j)) z i
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

theorem configurationFirstReindex_locallyIntegrable {d : ℕ} (j : Fin (d + 1))
    (f : Configuration (d + 1) → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ configurationFirstReindex j) volume := by
  apply (locallyIntegrable_map_homeomorph (configurationFirstReindex j).toHomeomorph).mp
  change LocallyIntegrable f (Measure.map (configurationFirstReindex j) volume)
  rw [(configurationFirstReindex_volume_preserving j).map_eq]
  exact hf

end
end GinibrePoincare
