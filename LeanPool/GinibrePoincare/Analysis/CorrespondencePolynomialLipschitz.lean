/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialLipschitz.lean.
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
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
/-!
# Correspondence polynomial lipschitz

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_lipschitz_norm_eq`.
-/

@[expose] public section
open Set
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- The set of difference quotients `‖g z - g w‖ / ‖z - w‖` over pairs `z ≠ w`. -/
def correspondenceDifferenceQuotients (g : ℂ → ℂ) : Set ℝ :=
  {r | ∃z w : ℂ, z≠w ∧ r=‖g z-g w‖/‖z-w‖}

/-- Equation (1.13): the finite optimal difference-quotient bound equals the
supremum of the ordinary real derivative's operator norm. -/
theorem correspondencePolynomial_lipschitz_norm_eq (g : ℂ → ℂ)
    (hg : ContDiff ℝ 1 g) (K : ℝ≥0) (hK : LipschitzWith K g) :
    BddAbove (correspondenceDifferenceQuotients g) ∧
    BddAbove (range (fun z => ‖fderiv ℝ g z‖)) ∧
    sSup (correspondenceDifferenceQuotients g)=sSup (range (fun z => ‖fderiv ℝ g z‖)) := by
  have hq : (correspondenceDifferenceQuotients g).Nonempty :=
    ⟨‖g 0-g 1‖/‖(0 : ℂ)-1‖, 0, 1, by norm_num, rfl⟩
  have hbq : BddAbove (correspondenceDifferenceQuotients g) := by
    refine ⟨K,?_⟩
    rintro r ⟨z, w, hzw, rfl⟩
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))).mpr (hK.norm_sub_le z w)
  have hbd : BddAbove (range (fun z => ‖fderiv ℝ g z‖)) :=
    ⟨K, by rintro r ⟨z, rfl⟩; exact norm_fderiv_le_of_lipschitz ℝ hK⟩
  have hqn : 0≤sSup (correspondenceDifferenceQuotients g) :=
    (div_nonneg (norm_nonneg (g 0-g 1)) (norm_nonneg ((0 : ℂ)-1))).trans
      (le_csSup hbq ⟨0, 1, by norm_num, rfl⟩)
  have hdn : 0≤sSup (range (fun z => ‖fderiv ℝ g z‖)) :=
    (norm_nonneg _).trans (le_csSup hbd (mem_range_self (0 : ℂ)))
  have hLd : LipschitzWith ⟨sSup (range (fun z => ‖fderiv ℝ g z‖)), hdn⟩ g :=
    lipschitzWith_of_nnNorm_fderiv_le (hg.differentiable (by norm_num)) (fun z => by
      exact_mod_cast le_csSup hbd (mem_range_self z))
  have hLq : LipschitzWith ⟨sSup (correspondenceDifferenceQuotients g), hqn⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    by_cases hzw : z=w
    · simp [hzw]
    · exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))).mp
        (le_csSup hbq ⟨z, w, hzw, rfl⟩)
  refine ⟨hbq, hbd, le_antisymm ?_ ?_⟩
  · apply csSup_le hq
    rintro r ⟨z, w, hzw, rfl⟩
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))).mpr (hLd.norm_sub_le z w)
  · apply csSup_le (range_nonempty _)
    rintro r ⟨z, rfl⟩
    exact norm_fderiv_le_of_lipschitz ℝ hLq

end
end GinibrePoincare
