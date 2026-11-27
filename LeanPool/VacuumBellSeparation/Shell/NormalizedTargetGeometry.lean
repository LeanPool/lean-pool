/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzFrameMatching

/-!
# Real and imaginary Minkowski geometry of the normalized target

These are identities of the original complex shell and the literal
normalizedTarget, including its zero-mass boundary. They supply the
strict negative pair used by the explicit Lorentz frame construction.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem minkowskiForm_complexSpacetimeRe (z : ComplexSpacetime) :
    minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) = reLorentzSq z := by
  simp only [minkowskiForm, real_inner_self_eq_norm_sq, complexSpacetimeRe]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [reLorentzSq, reSpatialSq, pow_two]

theorem complexMinkowskiForm_square_re (z : ComplexSpacetime) :
    (complexMinkowskiForm z z).re =
      minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) -
        minkowskiForm (complexSpacetimeIm z) (complexSpacetimeIm z) := by
  simp only [complexMinkowskiForm, spatialDot_eq, Complex.sub_re, Complex.add_re,
    Complex.mul_re, minkowskiForm, real_inner_self_eq_norm_sq, complexSpacetimeRe,
    complexSpacetimeIm, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three]
  ring

theorem complexMinkowskiForm_square_im (z : ComplexSpacetime) :
    (complexMinkowskiForm z z).im =
      2 * minkowskiForm (complexSpacetimeRe z) (complexSpacetimeIm z) := by
  simp only [complexMinkowskiForm, spatialDot_eq, Complex.sub_im, Complex.add_im,
    Complex.mul_im, minkowskiForm, complexSpacetimeRe, complexSpacetimeIm,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, Fin.sum_univ_three]
  ring

theorem complexShell_real_imaginary_pair {t : ℝ} {z : ComplexSpacetime}
    (hz : z ∈ complexShell t) :
    minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) -
        minkowskiForm (complexSpacetimeIm z) (complexSpacetimeIm z) = t ^ 2 ∧
      minkowskiForm (complexSpacetimeRe z) (complexSpacetimeIm z) = 0 := by
  have h : complexMinkowskiForm z z = (t : ℂ) ^ 2 := by
    simpa only [complexShell, Set.mem_ofPred_eq, complexMinkowskiForm, pow_two] using hz
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  rw [complexMinkowskiForm_square_re] at hr
  rw [complexMinkowskiForm_square_im] at hi
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] at hr hi
  exact ⟨hr, by linarith⟩

theorem euclidSq_real_imaginary (z : ComplexSpacetime) :
    euclidSq z =
      (complexSpacetimeRe z).1 ^ 2 + (complexSpacetimeIm z).1 ^ 2 +
        ‖(complexSpacetimeRe z).2‖ ^ 2 + ‖(complexSpacetimeIm z).2‖ ^ 2 := by
  simp only [euclidSq, norm_sq_eq_re_im, complexSpacetimeRe, complexSpacetimeIm,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

theorem complexShell_euclidSq_identity {t : ℝ} {z : ComplexSpacetime}
    (hz : z ∈ complexShell t) :
    euclidSq z = 2 * ((complexSpacetimeRe z).1 ^ 2 + (complexSpacetimeIm z).1 ^ 2) -
      2 * minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) + t ^ 2 := by
  have h := (complexShell_real_imaginary_pair hz).1
  simp only [minkowskiForm, real_inner_self_eq_norm_sq, ← pow_two] at h ⊢
  rw [euclidSq_real_imaginary]
  linarith

theorem normalizedTarget_real_negative {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) < 0 := by
  rw [minkowskiForm_complexSpacetimeRe]
  have h := hz.2.2.2.2
  linarith

theorem normalizedTarget_imaginary_negative {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    minkowskiForm (complexSpacetimeIm z) (complexSpacetimeIm z) < 0 := by
  have h := (complexShell_real_imaginary_pair hz.2.2.1).1
  have hn := normalizedTarget_real_negative hz
  nlinarith [sq_nonneg t]

theorem normalizedTarget_pair_orthogonal {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    minkowskiForm (complexSpacetimeRe z) (complexSpacetimeIm z) = 0 :=
  (complexShell_real_imaginary_pair hz.2.2.1).2

theorem normalizedTarget_real_length_bounds {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    4 ≤ negativeMinkowskiLength (complexSpacetimeRe z) ∧
      negativeMinkowskiLength (complexSpacetimeRe z) ≤ 16 := by
  have hs := negativeMinkowskiLength_sq (normalizedTarget_real_negative hz)
  have hn := (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)).le
  have hlow := hz.2.2.2.2
  rw [← minkowskiForm_complexSpacetimeRe] at hlow
  have he := complexShell_euclidSq_identity hz.2.2.1
  have hb := hz.2.2.2.1
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (complexSpacetimeRe z).1, sq_nonneg (complexSpacetimeIm z).1,
      sq_nonneg t]

theorem normalizedTarget_time_squares_le {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    (complexSpacetimeRe z).1 ^ 2 + (complexSpacetimeIm z).1 ^ 2 ≤ 128 := by
  have he := complexShell_euclidSq_identity hz.2.2.1
  have hb := hz.2.2.2.1
  have hn := normalizedTarget_real_negative hz
  nlinarith [sq_nonneg t]

/-- Continuous linear equivalence for the normalized target frame, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def normalizedTargetFrame {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) : Spacetime ≃L[ℝ] Spacetime :=
  lorentzNegativePairFrame (normalizedTarget_real_negative hz)
    (normalizedTarget_imaginary_negative hz) (normalizedTarget_pair_orthogonal hz)

theorem normalizedTargetFrame_gamma_le_three {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) : (normalizedTargetFrame hz (1, 0)).1 ≤ 3 := by
  have hr : 16 ≤ -minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) := by
    have h := hz.2.2.2.2
    rw [← minkowskiForm_complexSpacetimeRe] at h
    linarith
  have hi : 16 ≤ -minkowskiForm (complexSpacetimeIm z) (complexSpacetimeIm z) := by
    have h := (complexShell_real_imaginary_pair hz.2.2.1).1
    nlinarith [sq_nonneg t]
  have h₁ := div_le_div_of_nonneg_left (sq_nonneg (complexSpacetimeRe z).1)
    (by norm_num : (0 : ℝ) < 16) hr
  have h₂ := div_le_div_of_nonneg_left (sq_nonneg (complexSpacetimeIm z).1)
    (by norm_num : (0 : ℝ) < 16) hi
  have hg := lorentzNegativePairFrame_gamma_sq (normalizedTarget_real_negative hz)
    (normalizedTarget_imaginary_negative hz) (normalizedTarget_pair_orthogonal hz)
  change (normalizedTargetFrame hz (1, 0)).1 ^ 2 = _ at hg
  have ht := normalizedTarget_time_squares_le hz
  nlinarith

end VacuumBellSeparation
