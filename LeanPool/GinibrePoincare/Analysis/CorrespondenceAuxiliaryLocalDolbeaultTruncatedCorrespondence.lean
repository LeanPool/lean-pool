/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultTruncatedCorrespondence.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultTruncatedIteration

/-!
# Correspondence auxiliary local Dolbeault truncated correspondence

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `truncatedDolbeaultPrimitive_solves`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem dolbeaultWholeCylinder_replace {n : ℕ} (W : Fin n → Set ℂ)
    (j : Fin n) (p : Configuration n) (hp : p ∈ dolbeaultCylinder W Finset.univ)
    (z : ℂ) (hz : z ∈ W j) :
    dolbeaultReplaceCoordinate j (p, z) ∈ dolbeaultCylinder W Finset.univ := by
  intro k _
  by_cases hk : k = j
  · subst k; simpa [dolbeaultReplaceCoordinate_apply] using hz
  · simpa only [dolbeaultReplaceCoordinate_apply, ite_eq_right hk] using hp k (Finset.mem_univ k)

theorem truncatedDolbeaultBoundaryComposition_eq_on {n : ℕ} (R : ℝ)
    (W : Fin n → Set ℂ) (χ : Fin n → ℂ → ℂ)
    (hs : ∀ j, tsupport (χ j) ⊆ W j)
    (hR : ∀ j p, p ∈ dolbeaultCylinder W Finset.univ → ∀ z ∈ tsupport (χ j), ‖p j - z‖ ≤ R)
    (l : List (Fin n)) (a : Configuration n → ℂ) (p : Configuration n)
    (hp : p ∈ dolbeaultCylinder W Finset.univ) :
    truncatedDolbeaultBoundaryComposition R χ l a p = smoothDolbeaultBoundaryComposition χ l a p :=
        by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    change dolbeaultTruncatedCutoff j R (planarDbar (χ j)) _ p = _
    rw [dolbeaultTruncatedCutoff_eq j R _ _ p
      (fun z hz => hR j p hp z (planarDbar_tsupport_subset _ hz))]
    apply configurationCauchyGreenPotential_congr_on_support
    intro z hz
    exact ih _ (dolbeaultWholeCylinder_replace W j p hp z (hs j (planarDbar_tsupport_subset _ hz)))

theorem truncatedDolbeaultPrimitive_eq_on {n : ℕ} (R : ℝ)
    (W : Fin n → Set ℂ) (χ : Fin n → ℂ → ℂ)
    (hs : ∀ j, tsupport (χ j) ⊆ W j)
    (hR : ∀ j p, p ∈ dolbeaultCylinder W Finset.univ → ∀ z ∈ tsupport (χ j), ‖p j - z‖ ≤ R)
    (α : Fin n → Configuration n → ℂ) (l : List (Fin n)) (p : Configuration n)
    (hp : p ∈ dolbeaultCylinder W Finset.univ) :
    truncatedDolbeaultPrimitive R χ α l p = smoothDolbeaultPrimitive χ α l p := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change truncatedDolbeaultPrimitive R χ α l p + dolbeaultTruncatedCutoff j R (χ j) _ p =
      smoothDolbeaultPrimitive χ α l p + configurationCauchyGreenPotential j (χ j) _ p
    rw [ih, dolbeaultTruncatedCutoff_eq j R _ _ p (hR j p hp)]
    congr 1
    apply configurationCauchyGreenPotential_congr_on_support
    intro z hz
    exact truncatedDolbeaultBoundaryComposition_eq_on R W χ hs hR l _ _
      (dolbeaultWholeCylinder_replace W j p hp z (hs j hz))

/-- The actual compact smooth representatives of bounded L² homotopy
operators solve the same local equation as the singular smooth homotopy. -/
theorem truncatedDolbeaultPrimitive_solves {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (W V : Fin n → Set ℂ) (hW : ∀ j, IsOpen (W j)) (hV : ∀ j, IsOpen (V j))
    (hclosed : ∀ j k p, p ∈ dolbeaultCylinder W Finset.univ →
      dbarComponent (α j) k p = dbarComponent (α k) j p)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j)) (hχone : ∀ j z, z ∈ V j → χ j z = 1)
    (hχW : ∀ j, tsupport (χ j) ⊆ W j) (R : ℝ)
    (hR : ∀ j p, p ∈ dolbeaultCylinder W Finset.univ → ∀ z ∈ tsupport (χ j), ‖p j - z‖ ≤ R)
    (l : List (Fin n)) (hl : l.Nodup) (p : Configuration n)
    (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset)
    (j : Fin n) (hj : j ∈ l) :
    dbarComponent (truncatedDolbeaultPrimitive R χ α l) j p = α j p := by
  have he : truncatedDolbeaultPrimitive R χ α l =ᶠ[𝓝 p] smoothDolbeaultPrimitive χ α l := by
    filter_upwards [(dolbeaultCylinder_isOpen W hW Finset.univ).mem_nhds hp.1] with q hq
    exact truncatedDolbeaultPrimitive_eq_on R W χ hχW hR α l q hq
  have hd : dbarComponent (truncatedDolbeaultPrimitive R χ α l) j p =
      dbarComponent (smoothDolbeaultPrimitive χ α l) j p :=
    finiteComplexDbar_congr_of_eventuallyEq he
  rw [hd]
  exact (smoothDolbeaultPrimitive_solves_and_residual α hα W V hW hV hclosed χ hχ hc
    hχone hχW l hl p hp).1 j hj

end
end GinibrePoincare
