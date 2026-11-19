/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultBoundary.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultHomotopy
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultIteration

/-!
# Correspondence auxiliary local Dolbeault boundary

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `planarDbar_tsupport_subset`, `configurationCauchyGreenPotential_congr_on_support`,
`dolbeaultCylinder_replace`, `smoothDolbeaultPrimitive_contDiff`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

theorem planarDbar_contDiff_infty (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (planarDbar χ) := finiteComplexDbar_contDiff χ hχ 1 Complex.I

theorem planarDbar_tsupport_subset (χ : ℂ → ℂ) : tsupport (planarDbar χ) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra h
  apply hz
  simp [planarDbar, fderiv_of_notMem_tsupport ℝ h]

/-- The coordinate-`j` Cauchy–Green potential of `a` localized by `planarDbar χ` instead of `χ`;
this is the boundary term of the Dolbeault homotopy. -/
def configurationCauchyGreenBoundary {n : ℕ} (j : Fin n) (χ : ℂ → ℂ)
    (a : Configuration n → ℂ) : Configuration n → ℂ :=
  configurationCauchyGreenPotential j (planarDbar χ) a

theorem configurationCauchyGreenBoundary_contDiff {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (configurationCauchyGreenBoundary j χ a) :=
  configurationCauchyGreenPotential_contDiff j _ a (planarDbar_contDiff_infty χ hχ)
    (planarDbar_compact χ hc) ha

theorem configurationCauchyGreenPotential_congr_on_support {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a b : Configuration n → ℂ) (p : Configuration n)
    (he : ∀ z ∈ tsupport χ, a (dolbeaultReplaceCoordinate j (p, z)) =
      b (dolbeaultReplaceCoordinate j (p, z))) :
    configurationCauchyGreenPotential j χ a p = configurationCauchyGreenPotential j χ b p := by
  change (∫ y : ℂ, cauchyGreenKernel y *
      (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y)))) =
    ∫ y : ℂ, cauchyGreenKernel y * (χ (p j-y)*b (dolbeaultReplaceCoordinate j (p, p j-y)))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change cauchyGreenKernel y * (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y))) =
      cauchyGreenKernel y * (χ (p j-y)*b (dolbeaultReplaceCoordinate j (p, p j-y)))
    by_cases hy : p j-y ∈ tsupport χ
    · rw [he _ hy]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul])

theorem dolbeaultCylinder_replace {n : ℕ} (W V : Fin n → Set ℂ)
    (s : Finset (Fin n)) (j : Fin n) (hjs : j ∉ s) (p : Configuration n)
    (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s)
    (z : ℂ) (hz : z ∈ W j) :
    dolbeaultReplaceCoordinate j (p, z) ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s :=
        by
  constructor
  · intro k _
    by_cases hk : k = j
    · subst k; simpa [dolbeaultReplaceCoordinate_apply] using hz
    · simpa only [dolbeaultReplaceCoordinate_apply, ite_eq_right hk] using hp.1 k (Finset.mem_univ
        k)
  · intro k hk
    have hkj : k ≠ j := by intro he; subst k; exact hjs hk
    simpa only [dolbeaultReplaceCoordinate_apply, ite_eq_right hkj] using hp.2 k hk

/-- The composition of the boundary operators `configurationCauchyGreenBoundary j (χ j)` along a
list of coordinates, applied to `a`. -/
def smoothDolbeaultBoundaryComposition {n : ℕ} (χ : Fin n → ℂ → ℂ) :
    List (Fin n) → (Configuration n → ℂ) → Configuration n → ℂ
  | [], a => a
  | j::l, a => configurationCauchyGreenBoundary j (χ j) (smoothDolbeaultBoundaryComposition χ l a)

/-- The smooth Dolbeault primitive along a list of coordinates: for `j :: l`, the primitive for
`l` plus the coordinate-`j` Cauchy–Green potential (with cutoff `χ j`) of the boundary
composition along `l` applied to `α j`. -/
def smoothDolbeaultPrimitive {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (α : Fin n → Configuration n → ℂ) : List (Fin n) → Configuration n → ℂ
  | [] => 0
  | j::l => smoothDolbeaultPrimitive χ α l + configurationCauchyGreenPotential j (χ j)
      (smoothDolbeaultBoundaryComposition χ l (α j))

theorem smoothDolbeaultBoundaryComposition_contDiff {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (l : List (Fin n)) (a : Configuration n → ℂ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (smoothDolbeaultBoundaryComposition χ l a) := by
  induction l with
  | nil => exact ha
  | cons j l ih => exact configurationCauchyGreenBoundary_contDiff j _ _ (hχ j) (hc j) ih

theorem smoothDolbeaultPrimitive_contDiff {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (l : List (Fin n)) : ContDiff ℝ ∞ (smoothDolbeaultPrimitive χ α l) := by
  induction l with
  | nil => exact contDiff_const
  | cons j l ih => exact ih.add (configurationCauchyGreenPotential_contDiff j _ _
      (hχ j) (hc j) (smoothDolbeaultBoundaryComposition_contDiff χ hχ hc l _ (hα j)))

end
end GinibrePoincare
