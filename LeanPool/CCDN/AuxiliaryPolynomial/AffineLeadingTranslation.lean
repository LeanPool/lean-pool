/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.AffineTranslation
public import LeanPool.CCDN.Algebra.HomogeneousSlice
import LeanPool.CCDN.AuxiliaryPolynomial.AffineTranslationCount
import LeanPool.CCDN.Height.MultivariateGridHeight

/-! Translation preserves the leading homogeneous equation exactly. Bounded
integer translations make the constant coefficient nonzero in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma scaledHomogenize_one_affineTranslation {R : Type*} [CommRing R] [Nontrivial R]
    {n d : ℕ} (a : Fin n → R) (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    scaledHomogenize d 1 (affineTranslation R a f) =
      homogeneousTranslation R a (scaledHomogenize d 1 f) := by
  have ht : (affineTranslation R a f).totalDegree ≤ d := by
    rwa [affineTranslation_totalDegree]
  apply affineChart_injective_on_homogeneous
    (scaledHomogenize_homogeneous _ _ ht)
    (homogeneousTranslation_homogeneous _ (scaledHomogenize_homogeneous _ _ hd))
  rw [affineChart_scaledHomogenize_one, affineChart_homogeneousTranslation,
    affineChart_scaledHomogenize_one]

private lemma homogeneousSlice_zero_translation {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    homogeneousSlice n 0 (homogeneousTranslation R a f) = homogeneousSlice n 0 f := by
  have he : (homogeneousSlice n (0 : R)).comp (homogeneousTranslation R a).toRingHom =
      homogeneousSlice n 0 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [homogeneousSlice, homogeneousTranslation, homogeneousTranslationHom]
  exact RingHom.congr_fun he f

private lemma homogeneousSlice_zero_scaledHomogenize_one {R : Type*} [CommRing R]
    {n d : ℕ} (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    homogeneousSlice n 0 (scaledHomogenize d 1 f) = homogeneousComponent d f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [homogeneousSlice_monomial, chartExponent_homogenizedExponent]
  have hmd : m.sum (fun _ e => e) ≤ d := (le_totalDegree hm).trans hd
  by_cases he : m.sum (fun _ e => e) = d
  · have hhom := isHomogeneous_monomial (f.coeff m) he
    rw [homogeneousComponent_eq_self hhom]
    simp [homogenizedExponent, he]
  · have hlt : m.sum (fun _ e => e) < d := lt_of_le_of_ne hmd he
    rw [homogeneousComponent_eq_zero d _ ((totalDegree_monomial_le m (f.coeff m)).trans_lt hlt)]
    simp [homogenizedExponent, Nat.sub_ne_zero_of_lt hlt]

/-- Affine translation of the variables does not change the leading form: the top-degree
homogeneous component of `affineTranslation R a f` equals that of `f`. -/
theorem affineTranslation_leading_homogeneousComponent {R : Type*}
    [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    homogeneousComponent (affineTranslation R a f).totalDegree (affineTranslation R a f) =
      homogeneousComponent f.totalDegree f := by
  rw [affineTranslation_totalDegree]
  rw [← homogeneousSlice_zero_scaledHomogenize_one _ (affineTranslation_totalDegree_le a f),
    scaledHomogenize_one_affineTranslation a f le_rfl, homogeneousSlice_zero_translation,
    homogeneousSlice_zero_scaledHomogenize_one f le_rfl]

/-- A nonzero integral polynomial `f` in `n` variables has an integral translate with nonzero
constant coefficient by a vector whose entries lie in `[0, deg f]`. -/
theorem exists_bounded_affine_translation_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
  obtain ⟨a, ha, he, _⟩ := exists_integer_multivariate_grid_height_witness f hf le_rfl
  exact ⟨a, ha, by rwa [affineTranslation_constantCoeff]⟩

end
end CCDN
