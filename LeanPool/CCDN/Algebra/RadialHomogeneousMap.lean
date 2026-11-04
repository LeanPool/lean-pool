/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.RadialMap
public import LeanPool.CCDN.Hilbert.InfinitySection

/-! Radial scaling records the homogeneous components as coefficients of a
single polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The `K`-algebra map sending `f` to `∑ n, [f_n] T ^ n`, where `f_n` is the degree-`n`
homogeneous component of `f` and `[·]` its class modulo `I`; it lands in the homogeneous
coordinate algebra `projectiveCoordinateAlgebra I`. -/
def quotientRadialMap {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ K →ₐ[K] projectiveCoordinateAlgebra I where
  toFun f := ⟨Polynomial.map (Ideal.Quotient.mk I) (radialMap f), by
    intro n
    rw [Polynomial.coeff_map, radialMap_coeff]
    exact ⟨homogeneousComponent n f,
      (mem_restrictTotalDegree _ _ _).mpr
        (homogeneousComponent_isHomogeneous n f).totalDegree_le, rfl⟩⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  map_mul' f g := by apply Subtype.ext; simp
  commutes' c := by
    apply Subtype.ext
    simp only [algebraMap_eq, radialMap_C, Polynomial.map_C, SubalgebraClass.coe_algebraMap,
      Polynomial.algebraMap_apply, Polynomial.C_inj]
    exact (Ideal.Quotient.mkₐ K I).commutes c

/-- The coefficient of `T ^ n` in the radial image of `f` is the class modulo `I` of the
degree-`n` homogeneous component of `f`. -/
lemma quotientRadialMap_coeff {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (n : ℕ) :
    ((quotientRadialMap I f : projectiveCoordinateAlgebra I) :
      Polynomial (MvPolynomial σ K ⧸ I)).coeff n =
      (Ideal.Quotient.mk I) (homogeneousComponent n f) := by
  change (Polynomial.map (Ideal.Quotient.mk I) (radialMap f)).coeff n = _
  rw [Polynomial.coeff_map, radialMap_coeff]

/-- The radial image of a homogeneous polynomial `f` of degree `n` is the class of `f`
placed in degree `n` of the homogeneous coordinate algebra. -/
lemma quotientRadialMap_homogeneous {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (n : ℕ) (hf : f.IsHomogeneous n) :
    quotientRadialMap I f = projectiveMonomialMap I n
      ⟨(Ideal.Quotient.mk I) f,
        ⟨f, (mem_restrictTotalDegree _ _ _).mpr hf.totalDegree_le, rfl⟩⟩ := by
  apply Subtype.ext
  ext m
  rw [quotientRadialMap_coeff, projectiveMonomialMap_val, Polynomial.coeff_monomial,
    homogeneousComponent_of_mem hf]
  split_ifs <;> simp_all

end
end CCDN
