/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevRealSplit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLocalSlices
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Actual real-line coordinate splitting, including ordinary volume -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The equivalence `(a, b, w) ↦ (a + b i) :: w`, splitting off the first particle with its real
part first. -/
def configurationRealFirstSplit (d : ℕ) :
    (ℝ × (ℝ × Configuration d)) ≃L[ℝ] Configuration (d + 1) where
  toFun q := Fin.cons (Complex.equivRealProdCLM.symm (q.1, q.2.1)) q.2.2
  invFun z := ((z 0).re, (z 0).im, Fin.tail z)
  left_inv q := by cases q; rfl
  right_inv z := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' q r := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (Complex.equivRealProdCLM.symm.map_smul r (q.1, q.2.1))
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem configurationRealFirstSplit_volume_preserving (d : ℕ) :
    MeasurePreserving (configurationRealFirstSplit d)
      (volume : Measure (ℝ × (ℝ × Configuration d))) volume := by
  have h₁ := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ)
    (γ₁ := Configuration d)).symm MeasurableEquiv.prodAssoc
  have h₂ := ((Complex.volume_preserving_equiv_real_prod).symm
    Complex.measurableEquivRealProd).prod (MeasurePreserving.id (volume : Measure (Configuration
        d)))
  have h₃ := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0)
  convert h₃.comp (h₂.comp h₁) using 1
  funext q i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [configurationRealFirstSplit, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc, Complex.measurableEquivRealProd]

theorem configurationRealFirstSplit_locallyIntegrable (d : ℕ)
    (f : Configuration (d + 1) → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ configurationRealFirstSplit d) volume := by
  apply (locallyIntegrable_map_homeomorph (configurationRealFirstSplit d).toHomeomorph).mp
  change LocallyIntegrable f (Measure.map (configurationRealFirstSplit d) volume)
  rw [(configurationRealFirstSplit_volume_preserving d).map_eq]
  exact hf

theorem configurationRealFirstSplit_line_hasDerivAt (d : ℕ)
    (y : ℝ × Configuration d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => configurationRealFirstSplit d (s, y))
      (Fin.cons (1 : ℂ) 0) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change HasDerivAt (fun s : ℝ => Complex.equivRealProdCLM.symm (s, y.1)) 1 t
    convert Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y.1)) using 1 <;> rfl
  · simpa [configurationRealFirstSplit] using hasDerivAt_const t (y.2 j)

end
end GinibrePoincare
