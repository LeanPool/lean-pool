/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Jacobian
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# Base change of the coordinate ring and the Jacobian

`ChabautyColeman.HypRing.baseChange` is the ring homomorphism
`A_R → A_{R'}` induced by a ring homomorphism `R → R'` of the bases (componentwise on
the coefficients). For a field extension `K ⊆ K'` this makes `A_{K'}` an `A_K`-algebra,
and `ChabautyColeman.HypJac.map : J(K) →* J(K')` is the induced homomorphism of
Jacobians, obtained from Mathlib's `ClassGroup.extendedHom` (extension of fractional
ideals). It sends the Abel–Jacobi class of a point to the class of the base-changed
point (`ChabautyColeman.HypJac.map_aj`).

(Injectivity of `ChabautyColeman.HypJac.map` for every field extension
(`ChabautyColeman.hypJac_map_injective`) is formalized in
`upstream HyperellipticCurves.Archive.BaseChangeInjectivity`, and its finite-Galois case via Hilbert
90 —
the principality-descent criterion and the contraction identity — in
`upstream HyperellipticCurves.Archive.BaseChangeContraction` and `upstream
HyperellipticCurves.Archive.GaloisAction`;
the main theorems do not depend on them.)

Blueprint node: `def:basechange`.
-/

@[expose] public section

open Polynomial
open scoped nonZeroDivisors

namespace ChabautyColeman

namespace HypRing

section ringHom

variable {R R' : Type*} [CommRing R] [CommRing R'] (f : R[X]) (φ : R →+* R')

/-- Base change of the coordinate ring along a ring homomorphism of the base. -/
noncomputable def baseChange : HypRing R f →+* HypRing R' (f.map φ) :=
  QuadraticAlgebra.mapRingHomTo (Polynomial.mapRingHom φ) rfl (map_zero _)

@[simp]
theorem re_baseChange (z : HypRing R f) : (baseChange f φ z).re = z.re.map φ := rfl

@[simp]
theorem im_baseChange (z : HypRing R f) : (baseChange f φ z).im = z.im.map φ := rfl

theorem baseChange_injective (hφ : Function.Injective φ) :
    Function.Injective (baseChange f φ) :=
  QuadraticAlgebra.mapRingHomTo_injective (Polynomial.map_injective φ hφ) rfl (map_zero _)

end ringHom

section field

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (f : K[X])

noncomputable instance instAlgebraBaseChange :
    Algebra (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) :=
  (baseChange f (algebraMap K K')).toAlgebra

theorem algebraMap_eq_baseChange :
    algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))
      = baseChange f (algebraMap K K') := rfl

theorem algebraMap_baseChange_injective :
    Function.Injective
      (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))) :=
  baseChange_injective f (algebraMap K K') (algebraMap K K').injective

instance instFaithfulSMulBaseChange :
    FaithfulSMul (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_baseChange_injective f)

instance instFactOddMap [Fact (Odd f.natDegree)] :
    Fact (Odd (f.map (algebraMap K K')).natDegree) :=
  ⟨by rw [natDegree_map]; exact Fact.out⟩

end field

end HypRing

section jac

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (f : K[X])

/-- Base change maps Mumford ideals to Mumford ideals. -/
theorem mumfordIdeal_map (u v : K[X]) :
    (mumfordIdeal f u v).map
        (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))
      = mumfordIdeal (f.map (algebraMap K K'))
          (u.map (algebraMap K K')) (v.map (algebraMap K K')) := by
  have h1 : algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))
      (algebraMap K[X] _ u) = algebraMap K'[X] _ (u.map (algebraMap K K')) := by
    ext <;> simp [HypRing.algebraMap_eq_baseChange]
  have h2 : algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))
      (HypRing.y f - algebraMap K[X] _ v)
        = HypRing.y (f.map (algebraMap K K'))
          - algebraMap K'[X] _ (v.map (algebraMap K K')) := by
    ext <;> simp [HypRing.algebraMap_eq_baseChange]
  rw [mumfordIdeal_eq_span, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, h1, h2,
    ← mumfordIdeal_eq_span]

/-- Point ideals extend to point ideals under base change. -/
theorem pointIdeal_map (x₀ y₀ : K) :
    (pointIdeal f x₀ y₀).map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))
      = pointIdeal (f.map (algebraMap K K')) (algebraMap K K' x₀) (algebraMap K K' y₀) := by
  rw [pointIdeal_eq_mumfordIdeal, pointIdeal_eq_mumfordIdeal, mumfordIdeal_map]
  simp

variable [Fact (Odd f.natDegree)]

/-- Base change of the Jacobian along a field extension `K ⊆ K'`:
the homomorphism `J(K) →* J(K')` induced by ideal extension. -/
noncomputable def HypJac.map : HypJac K f →* HypJac K' (f.map (algebraMap K K')) :=
  ClassGroup.extendedHom _ _

variable [NeZero (2 : K)] [Fact (Squarefree f)] [NeZero (2 : K')]
  [Fact (Squarefree (f.map (algebraMap K K')))]

theorem HypJac.map_mk0 (I : (Ideal (HypRing K f))⁰) :
    HypJac.map f (ClassGroup.mk0 I)
      = ClassGroup.mk0 (ClassGroup.extendedIdeal (HypRing K f)
        (HypRing K' (f.map (algebraMap K K'))) I) := by
  rw [HypJac.map, ClassGroup.extendedHom_mk0]

/-- Base change is compatible with the Abel--Jacobi map. -/
theorem HypJac.map_aj (x₀ y₀ : K) :
    HypJac.map f (aj f x₀ y₀)
      = aj (f.map (algebraMap K K')) (algebraMap K K' x₀) (algebraMap K K' y₀) := by
  rw [aj, aj, HypJac.map_mk0]
  exact congrArg ClassGroup.mk0 (Subtype.ext (pointIdeal_map f x₀ y₀))

end jac

end ChabautyColeman

end
