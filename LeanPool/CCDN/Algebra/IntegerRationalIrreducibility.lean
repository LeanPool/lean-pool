/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Positive-degree irreducible integer equations remain irreducible over Q.
Primitive denominator-cleared divisors give an elementary Gauss argument. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An irreducible integer polynomial of positive total degree remains irreducible over `ℚ`. -/
theorem rational_map_irreducible_of_integer {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hir : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (map (Int.castRingHom ℚ) f) := by
  have hdegree : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hf0 : map (Int.castRingHom ℚ) f ≠ 0 := by
    intro he
    exact hir.ne_zero ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using he))
  have hunit : ¬ IsUnit (map (Int.castRingHom ℚ) f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hdegree] at he
    omega
  refine ⟨hunit, ?_⟩
  intro q r he
  by_cases hqu : IsUnit q
  · exact Or.inl hqu
  by_cases hru : IsUnit r
  · exact Or.inr hru
  have hq0 : q ≠ 0 := fun hh => hf0 (by simp [he, hh])
  have hr0 : r ≠ 0 := fun hh => hf0 (by simp [he, hh])
  have hqd := totalDegree_pos_of_ne_zero_of_not_isUnit hq0 hqu
  have hrd := totalDegree_pos_of_ne_zero_of_not_isUnit hr0 hru
  have hsum : q.totalDegree + r.totalDegree = f.totalDegree := by
    rw [← totalDegree_mul_of_isDomain hq0 hr0, ← he, hdegree]
  obtain ⟨g, a, hgprim, ha, hmodel⟩ := exists_primitive_integer_model q hq0
  have hgdegree := rational_scalar_model_degree ha hq0 hmodel
  have hdivQ : map (Int.castRingHom ℚ) g ∣ map (Int.castRingHom ℚ) f := by
    refine ⟨C a⁻¹ * r, ?_⟩
    rw [hmodel, mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    exact he
  obtain ⟨u, hu⟩ := hgprim.rational_map_dvd_iff.mp hdivQ
  have hg0 : g ≠ 0 := fun hh => hir.ne_zero (by simp [hu, hh])
  have hu0 : u ≠ 0 := fun hh => hir.ne_zero (by simp [hu, hh])
  rcases hir.isUnit_or_isUnit hu with hgu | huu
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp hgu).2
    rw [hgdegree] at hh
    omega
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp huu).2
    have hedeg : f.totalDegree = g.totalDegree + u.totalDegree := by
      rw [hu, totalDegree_mul_of_isDomain hg0 hu0]
    rw [hgdegree, hh, add_zero] at hedeg
    omega

end
end CCDN
