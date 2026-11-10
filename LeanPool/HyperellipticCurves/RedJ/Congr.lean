/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.MumfordReduction
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# The coordinate ring and the Jacobian along a base-field isomorphism

An isomorphism `σ : K ≃+* K'` of base fields with `f.map σ = g` induces an isomorphism
`ChabautyColeman.HypRing.congr : A_K ≃+* A_{K'}` of coordinate rings and (via
`ClassGroup.mulEquiv`) an isomorphism `ChabautyColeman.HypJac.congr : J(K) ≃* J(K')` of
Jacobians, mapping Mumford classes to Mumford classes
(`ChabautyColeman.HypJac.congr_mk0_mumfordIdeal`), point ideals to point ideals
(`ChabautyColeman.pointIdeal_congr`), and hence Abel--Jacobi classes to Abel--Jacobi
classes (`ChabautyColeman.HypJac.congr_aj`).

This transport is what identifies the Jacobian over `K₀[X]/(f₀)`-data with the Jacobian over the
completed field in `ChabautyColeman.mapBase`; the Frobenius-equivariance results built on it
(`lem:frobfix-finite`, `thm:J1-index`) are formalized in `upstream
HyperellipticCurves.Archive.Equivariance`
and `upstream HyperellipticCurves.Archive.J1FiniteIndex`, and the main theorems do not depend on
them.

NOTE (coercion discipline): all statements spell the ring homomorphism underlying `σ` as
the ascription `(σ : K →+* K')`. Mixing this with the elaborator-inserted coercion in
`p.map σ` produces syntactically different coercion terms whose unification inside
`mumfordIdeal`/`mk0` terms does not terminate in reasonable time.
-/

@[expose] public section

open Polynomial nonZeroDivisors

namespace ChabautyColeman

/-! ### The coordinate ring and the Jacobian along an isomorphism of the base field -/

section congr

variable {R R' : Type*} [CommRing R] [CommRing R'] (f : R[X]) {g : R'[X]}

/-- The isomorphism of coordinate rings induced by an isomorphism of the base rings,
with a prescribed (equal) target polynomial. -/
noncomputable def HypRing.congr (σ : R ≃+* R') (hg : f.map (σ : R →+* R') = g) :
    HypRing R f ≃+* HypRing R' g :=
  RingEquiv.ofRingHom
    (QuadraticAlgebra.mapRingHomTo (Polynomial.mapRingHom (σ : R →+* R'))
      (by rwa [coe_mapRingHom]) (map_zero _))
    (QuadraticAlgebra.mapRingHomTo (Polynomial.mapRingHom (σ.symm : R' →+* R))
      (by rw [coe_mapRingHom, ← hg, map_map, RingEquiv.symm_comp, map_id])
      (map_zero _))
    (by ext z <;> simp [map_map, RingEquiv.comp_symm])
    (by ext z <;> simp [map_map, RingEquiv.symm_comp])

variable (σ : R ≃+* R') (hg : f.map (σ : R →+* R') = g)

@[simp]
theorem HypRing.re_congr (z : HypRing R f) :
    (HypRing.congr f σ hg z).re = z.re.map (σ : R →+* R') := rfl

@[simp]
theorem HypRing.im_congr (z : HypRing R f) :
    (HypRing.congr f σ hg z).im = z.im.map (σ : R →+* R') := rfl

end congr

section mumford

variable {K K' : Type*} [Field K] [Field K'] (f : K[X]) {g : K'[X]} (σ : K ≃+* K')
  (hg : f.map (σ : K →+* K') = g)

/-- The coordinate-ring isomorphism induced by a base-field isomorphism maps Mumford
ideals to Mumford ideals. -/
theorem mumfordIdeal_congr (u v : K[X]) :
    (mumfordIdeal f u v).map (HypRing.congr f σ hg : HypRing K f →+* HypRing K' g)
      = mumfordIdeal g (u.map (σ : K →+* K')) (v.map (σ : K →+* K')) := by
  have h1 : (HypRing.congr f σ hg : HypRing K f →+* HypRing K' g) (algebraMap K[X] _ u)
      = algebraMap K'[X] _ (u.map (σ : K →+* K')) := by
    ext <;> simp
  have h2 : (HypRing.congr f σ hg : HypRing K f →+* HypRing K' g)
        (HypRing.y f - algebraMap K[X] _ v)
      = HypRing.y g - algebraMap K'[X] _ (v.map (σ : K →+* K')) := by
    ext <;> simp [HypRing.y]
  rw [mumfordIdeal_eq_span, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, h1, h2,
    mumfordIdeal]

variable [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
  [NeZero (2 : K')] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

/-- The isomorphism of Jacobians induced by an isomorphism of the base fields. -/
noncomputable def HypJac.congr : HypJac K f ≃* HypJac K' g :=
  ClassGroup.mulEquiv (HypRing.congr f σ hg)

/-- The Jacobian isomorphism induced by a base-field isomorphism maps Mumford classes
to Mumford classes. -/
theorem HypJac.congr_mk0_mumfordIdeal {u : K[X]} (hm : u.Monic) (v : K[X]) :
    HypJac.congr f σ hg (ClassGroup.mk0
        ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal g (u.map (σ : K →+* K')) (v.map (σ : K →+* K')),
          mumfordIdeal_mem_nonZeroDivisors g (hm.map (σ : K →+* K')).ne_zero
            (v.map (σ : K →+* K'))⟩ :=
  (ClassGroup.mulEquiv_mk0 (HypRing.congr f σ hg) _).trans
    (congrArg ClassGroup.mk0 (Subtype.ext (mumfordIdeal_congr f σ hg u v)))

end mumford

/-! ### Point ideals and the Abel--Jacobi map along a base-field isomorphism -/

/-- The coordinate-ring isomorphism induced by a base-field isomorphism `σ` maps the point ideal
of `(x, y)` to that of `(σ x, σ y)`. -/
theorem pointIdeal_congr {K K' : Type*} [Field K] [Field K'] (g : K[X]) {g' : K'[X]}
    (σ : K ≃+* K') (hg : g.map (σ : K →+* K') = g') (x y : K) :
    (pointIdeal g x y).map (HypRing.congr g σ hg : HypRing K g →+* HypRing K' g')
      = pointIdeal g' (σ x) (σ y) := by
  have h1 : (HypRing.congr g σ hg : HypRing K g →+* HypRing K' g')
        (algebraMap K[X] _ (X - C x))
      = algebraMap K'[X] _ (X - C (σ x)) := by ext <;> simp
  have h2 : (HypRing.congr g σ hg : HypRing K g →+* HypRing K' g')
        (HypRing.y g - algebraMap K _ y)
      = HypRing.y g' - algebraMap K' _ (σ y) := by ext <;> simp [HypRing.y]
  rw [pointIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, h1, h2, pointIdeal]

/-- **The Abel--Jacobi map is natural in the base field**: an isomorphism of base fields
carrying `g` to `g'` carries the class of the point `(x, y)` to the class of its image. -/
theorem HypJac.congr_aj {K K' : Type*} [Field K] [Field K'] [NeZero (2 : K)] [NeZero (2 : K')]
    (g : K[X]) {g' : K'[X]} [Fact (Odd g.natDegree)] [Fact (Squarefree g)]
    [Fact (Odd g'.natDegree)] [Fact (Squarefree g')] (σ : K ≃+* K')
    (hg : g.map (σ : K →+* K') = g') (x y : K) :
    HypJac.congr g σ hg (aj g x y) = aj g' (σ x) (σ y) :=
  (ClassGroup.mulEquiv_mk0 (HypRing.congr g σ hg) _).trans
    (congrArg ClassGroup.mk0 (Subtype.ext (pointIdeal_congr g σ hg x y)))

end ChabautyColeman

end
