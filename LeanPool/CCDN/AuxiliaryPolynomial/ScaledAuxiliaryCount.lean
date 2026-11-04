/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousSlice
import LeanPool.CCDN.Algebra.ScaledHomogenizationPrimitive
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Plane.Bezout

/-! Proper affine sections and Bézout counts from prime-scaled homogeneous
models. The coordinate slice is x₀=p, and the original points stay integral. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Let `p` be a prime not dividing the constant coefficient of the primitive integer polynomial
`f`. If a form `g` is not divisible by the `p`-scaled homogenization of `f`, then over `ℚ` its
slice at `x₀ = p` is not divisible by `f`. -/
theorem scaled_auxiliary_rational_not_dvd {n M : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ scaledHomogenize f.totalDegree (p : ℤ) f ∣ g) :
    ¬ MvPolynomial.map (Int.castRingHom ℚ) f ∣
      MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice n (p : ℤ) g) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdegree :
      (homogeneousSlice n (p : ℤ) (scaledHomogenize f.totalDegree (p : ℤ) f)).totalDegree =
        f.totalDegree := by
    rw [homogeneousSlice_scaledHomogenize _ _ le_rfl,
      totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ hpZ)) hf0, totalDegree_C,
      zero_add]
  have h := rational_homogeneousSlice_not_dvd hpZ (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hpZ hf0) hg (hprim.scaledHomogenize _ hp hp0) hdegree hnd
  intro hdiv
  apply h
  rw [homogeneousSlice_scaledHomogenize _ _ le_rfl, map_mul, map_C]
  simp only [Int.coe_castRingHom, Int.cast_pow]
  have hunit : IsUnit (C ((p : ℚ) ^ f.totalDegree) : MvPolynomial (Fin n) ℚ) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hpQ)).map C
  exact hunit.mul_left_dvd.mpr hdiv

/-- Once a homogeneous auxiliary nonmultiple has been constructed on the
prime-scaled model, its degree gives the original-plane point bound. -/
theorem scaled_plane_points_card_le_auxiliary_degree {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (g : MvPolynomial (Fin 3) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ scaledHomogenize f.totalDegree (p : ℤ) f ∣ g)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (Fin.cons (p : ℤ) (z i)) g = 0) : t ≤ f.totalDegree * M := by
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  have hndQ := scaled_auxiliary_rational_not_dvd f hf0 hprim hp hp0 g hg hnd
  let zQ : Fin t → Fin 2 → ℚ := fun i j => (z i j : ℚ)
  have hiQ : Function.Injective zQ := by
    intro i j he
    apply hinj
    funext k
    exact Int.cast_injective (congrFun he k)
  have hfQ : ∀ i, eval (zQ i) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hz i)
    rw [map_eval, map_zero] at h
    exact h
  have hgQ : ∀ i, eval (zQ i)
      (MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice 2 (p : ℤ) g)) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzg i)
    rw [← homogeneousSlice_eval] at h
    rw [map_eval, map_zero] at h
    exact h
  have h := plane_common_zeros_card_le _ _ hir hndQ zQ hiQ hfQ hgQ
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree] at h
  exact h.trans (Nat.mul_le_mul_left _ (homogeneousSlice_degree_le _ hg))

end
end CCDN
