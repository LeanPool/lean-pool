/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Algebra.GridPointInterpolation
import LeanPool.CCDN.Algebra.ProjectiveFiniteFibers

/-! A coordinate ring with constant filtered Hilbert polynomial has
finitely many rational affine zeros. Its projective zero locus is empty,
since every nonzero representative would produce arbitrarily many affine
zeros by scaling. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem finite_point_bound_of_hilbert_dimension_zero
    {σ : Type*} [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ ℚ)) (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ M : ℕ, ∀ s : Finset (σ → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) → s.card ≤ M := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  refine ⟨Module.finrank ℚ (filteredCoordinateSpace I N₀), ?_⟩
  intro s hs
  let S : Finset ℚ := s.biUnion (fun x => Finset.univ.image x)
  let N := max N₀ (Fintype.card σ * (S.card - 1))
  have hdimN : Module.finrank ℚ (filteredCoordinateSpace I N) =
      Module.finrank ℚ (filteredCoordinateSpace I N₀) := by
    have h₁ := hN₀ N (le_max_left _ _)
    have h₂ := hN₀ N₀ le_rfl
    rw [hP, Polynomial.eval_C] at h₁ h₂
    exact_mod_cast h₁.symm.trans h₂
  have hh := grid_points_filtered_lower I S (fun x : s => x.val)
    Subtype.val_injective (fun x j => by
      apply Finset.mem_biUnion.mpr
      exact ⟨x.val, x.property, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    (fun x f hf => hs x.val x.property f hf) (le_max_right _ _ : _ ≤ N)
  have hh' : s.card ≤ Module.finrank ℚ (filteredCoordinateSpace I N) := by
    simpa only [Fintype.card_coe] using hh
  exact hh'.trans_eq hdimN

/-- An ideal of `ℚ[X₀, …, Xₙ]` whose filtered Hilbert polynomial is constant has empty projective
zero locus. -/
theorem projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ := by
  obtain ⟨M, hM⟩ := finite_point_bound_of_hilbert_dimension_zero I hdim
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := projective_linear_image_ne_zero_of_finite_zero_fiber I
    (0 : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) M
    (fun s hs _ => hM s hs) x hx
  exact hh rfl

end
end CCDN
