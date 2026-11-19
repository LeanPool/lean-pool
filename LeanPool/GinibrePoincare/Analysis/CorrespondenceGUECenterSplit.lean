/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUECenterSplit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUECenterGeometry
public import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# Correspondence GUE center split

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueCenterSplit_volume_preserving`, `gueCenterSplitEquiv_symm_apply`,
`gueCenter_orthogonal`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The line spanned by `gueCenterUnit n`. -/
def gueCenterLine (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {gueCenterUnit n}

/-- The linear isometry equivalence `t ↦ t • gueCenterUnit n` from `ℝ` onto `gueCenterLine n`. -/
def gueCenterLineIsometry (n : ℕ) (hn : 0 < n) : ℝ ≃ₗᵢ[ℝ] gueCenterLine n where
  toFun t := ⟨t • gueCenterUnit n, by unfold gueCenterLine; exact Submodule.mem_span_singleton.mpr
                                        ⟨t, rfl⟩⟩
  invFun v := inner ℝ (gueCenterUnit n) (v : EuclideanSpace ℝ (Fin n))
  left_inv t := by
    change inner ℝ (gueCenterUnit n) (t • gueCenterUnit n)=t
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, gueCenterUnit_norm hn]
    simp
  right_inv v := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp v.property
    apply Subtype.ext
    change (inner ℝ (gueCenterUnit n) (v : EuclideanSpace ℝ (Fin n))) • gueCenterUnit n=v
    rw [← ht, real_inner_smul_right, real_inner_self_eq_norm_sq, gueCenterUnit_norm hn]
    simp
  map_add' a b := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' a b := by apply Subtype.ext; exact mul_smul _ _ _
  norm_map' t := by
    change ‖t • gueCenterUnit n‖=‖t‖
    rw [norm_smul, gueCenterUnit_norm hn, mul_one]

/-- The measurable equivalence `EuclideanSpace ℝ (Fin n) ≃ᵐ ℝ × (gueCenterLine n)ᗮ` splitting off
the center coordinate via the orthogonal decomposition along `gueCenterLine n`. -/
def gueCenterSplitEquiv (n : ℕ) (hn : 0 < n) : EuclideanSpace ℝ (Fin n) ≃ᵐ
    ℝ×(gueCenterLine n)ᗮ :=
  (gueCenterLine n).orthogonalDecomposition.toMeasurableEquiv.trans
    ((MeasurableEquiv.toLp 2 (gueCenterLine n×(gueCenterLine n)ᗮ)).symm.trans
      ((gueCenterLineIsometry n hn).symm.toMeasurableEquiv.prodCongr (.refl _)))

theorem gueCenterSplit_volume_preserving (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (gueCenterSplitEquiv n hn) volume (volume.prod volume) := by
  exact ((gueCenterLineIsometry n hn).symm.measurePreserving.prod (MeasurePreserving.id _)).comp
    ((WithLp.volume_preserving_ofLp (gueCenterLine n) (gueCenterLine n)ᗮ).comp
      (gueCenterLine n).orthogonalDecomposition.measurePreserving)

theorem gueCenterSplitEquiv_symm_apply (n : ℕ) (hn : 0<n) (t : ℝ)
    (y : (gueCenterLine n)ᗮ) :
    (gueCenterSplitEquiv n hn).symm (t, y)=t • gueCenterUnit n+y := rfl

theorem gueCenter_orthogonal (n : ℕ) (y : (gueCenterLine n)ᗮ) :
    inner ℝ (gueCenterUnit n) (y : EuclideanSpace ℝ (Fin n))=0 := by
  exact (Submodule.mem_orthogonal (gueCenterLine n) y).mp y.property (gueCenterUnit n)
    (Submodule.subset_span (by simp))

end
end GinibrePoincare
