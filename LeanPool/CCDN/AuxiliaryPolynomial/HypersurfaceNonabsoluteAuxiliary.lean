/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.Algebra.HomogeneousLinearDescent
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! A degree-d auxiliary equation for nonabsolute irreducible hypersurfaces.
Linear descent of the two homogeneous factors suffices over any extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Over an arbitrary field extension, descent of a proper factorization
produces a degree-d nonmultiple vanishing at all base-field zeros. -/
private theorem nonabsolute_homogeneous_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧ q.IsHomogeneous d ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    exact fun he => hir.ne_zero ((map_injective (algebraMap k K) (algebraMap k K).injective)
      (by simpa using he))
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [(hf.map _).totalDegree hmap0] at he
    omega
  obtain ⟨g, h, hgu, hhu, hfac⟩ := (irreducible_or_factor hmapu).resolve_left hred
  have hg0 : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh0 : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  obtain ⟨hdegrees, htop⟩ := homogeneous_factorization_top (hf.map _) hmap0 hg0 hh0 hfac
  obtain ⟨g₀, hg₀, hg₀hom, hgz⟩ := exists_nonzero_homogeneous_linear_descent (k := k)
    (homogeneousComponent g.totalDegree g) (homogeneousComponent_totalDegree_ne_zero hg0)
    (homogeneousComponent_isHomogeneous _ _)
  obtain ⟨h₀, hh₀, hh₀hom, hhz⟩ := exists_nonzero_homogeneous_linear_descent (k := k)
    (homogeneousComponent h.totalDegree h) (homogeneousComponent_totalDegree_ne_zero hh0)
    (homogeneousComponent_isHomogeneous _ _)
  refine ⟨g₀ * h₀, mul_ne_zero hg₀ hh₀, hdegrees ▸ hg₀hom.mul hh₀hom, ?_, ?_⟩
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      rw [hf.totalDegree hir.ne_zero, hg₀hom.totalDegree hg₀] at he
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      rw [hf.totalDegree hir.ne_zero, hh₀hom.totalDegree hh₀] at he
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, htop, eval_mul, map_zero] at he
    rw [eval_mul]
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · rw [hgz x hgzero, zero_mul]
    · rw [hhz x hhzero, mul_zero]

/-- Integer denominator clearing preserves the exact degree and all rational
zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
theorem integer_nonabsolute_homogeneous_auxiliary {K : Type*}
    [Field K] [Algebra ℚ K] {n d : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin n) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      ∀ x : Fin n → ℚ, eval x (map (Int.castRingHom ℚ) f) = 0 →
        eval x (map (Int.castRingHom ℚ) g) = 0 := by
  obtain ⟨q, hq0, hqh, hqnd, hqzero⟩ := nonabsolute_homogeneous_auxiliary
    (map (Int.castRingHom ℚ) f) (hf.map _) hd hir hred
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model q hq0
  have hg0 : g ≠ 0 := by
    intro hz
    have hh := mul_ne_zero (C_eq_zero.not.mpr ha) hq0
    apply hh
    simpa only [hz, map_zero] using he.symm
  refine ⟨g, hg0, rational_scalar_model_homogeneous he hqh, ?_, ?_⟩
  · intro hdiv
    apply hqnd
    have hh := dvd_mul_of_dvd_right (map_dvd (map (Int.castRingHom ℚ)) hdiv) (C a⁻¹)
    simpa only [he, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using hh
  · intro x hx
    exact (rational_scalar_model_zero_iff ha he x).mpr (hqzero x hx)

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary {K : Type*}
    [Field K] [Algebra ℚ K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (map (Int.castRingHom ℚ) f) ⊆
        projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  obtain ⟨g, hg0, hgh, hgnd, hz⟩ := integer_nonabsolute_homogeneous_auxiliary f hf hd hir hred
  exact ⟨g, hg0, hgh, hgnd, fun x hx => hz x.rep hx⟩

end
end CCDN
