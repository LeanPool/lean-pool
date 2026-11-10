/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Mumford
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The class-group Jacobian and the Abel–Jacobi map

We define `ChabautyColeman.HypJac K f`, the Jacobian of the hyperelliptic curve
`y² = f(x)` in its class-group incarnation `Cl(A_K)` (Mathlib's `ClassGroup`, written
multiplicatively), and the Abel–Jacobi map `ChabautyColeman.aj` sending an affine point
`(x₀, y₀)` to the class of its maximal ideal `(x - x₀, y - y₀)`; the base point `∞`
corresponds to the trivial class.

The class of a general `K`-rational divisor supported on affine points is obtained via
`ClassGroup.mk0` (products/quotients of the ideals involved), so no separate definition
is needed.

We also prove `m_P · m_{ιP} = (x - x₀)` (`ChabautyColeman.pointIdeal_mul_pointIdeal_neg`)
and deduce that the involution inverts Abel–Jacobi classes (`ChabautyColeman.aj_inv`).

Blueprint nodes: `def:hypjac`, `lem:aj-inverse`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X])

/-- The class-group Jacobian of the hyperelliptic curve `y² = f(x)`:
`J(K) := Cl(A_K)`, written multiplicatively (as is Mathlib's `ClassGroup`). -/
abbrev HypJac (K : Type*) [Field K] (f : K[X]) [Fact (Odd f.natDegree)] : Type _ :=
  ClassGroup (HypRing K f)

/-- The ideal `(x - x₀, y - y₀)` of the coordinate ring attached to an affine point
`(x₀, y₀)`; for a point on the curve it is the maximal ideal of the point. -/
noncomputable def pointIdeal (x₀ y₀ : K) : Ideal (HypRing K f) :=
  Ideal.span {algebraMap K[X] _ (X - C x₀), HypRing.y f - algebraMap K _ y₀}

theorem X_sub_C_mem_pointIdeal (x₀ y₀ : K) :
    algebraMap K[X] (HypRing K f) (X - C x₀) ∈ pointIdeal f x₀ y₀ :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem y_sub_mem_pointIdeal (x₀ y₀ : K) :
    HypRing.y f - algebraMap K (HypRing K f) y₀ ∈ pointIdeal f x₀ y₀ :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem pointIdeal_ne_bot (x₀ y₀ : K) : pointIdeal f x₀ y₀ ≠ ⊥ := by
  intro h
  have hx := X_sub_C_mem_pointIdeal f x₀ y₀
  rw [h, Ideal.mem_bot] at hx
  exact X_sub_C_ne_zero x₀
    ((map_eq_zero_iff _ QuadraticAlgebra.algebraMap_injective).mp hx)

/-- The `≠ 0` form of `ChabautyColeman.pointIdeal_ne_bot`, in the currency the
`nonZeroDivisors` consumers spend. -/
theorem pointIdeal_ne_zero (x₀ y₀ : K) : pointIdeal f x₀ y₀ ≠ 0 := by
  simpa [Submodule.zero_eq_bot] using pointIdeal_ne_bot f x₀ y₀

/-! ### The divisor of `x - x₀` (blueprint node `lem:aj-inverse`)

For a point `(x₀, y₀)` on the curve, `m_P · m_{ιP} = (x - x₀)` as ideals of `A_K`;
consequently the Abel–Jacobi classes of `P` and `ιP` are mutually inverse.
-/

namespace HypRing

theorem algebraMap_eq_C (r : K) :
    algebraMap K (HypRing K f) r = algebraMap K[X] _ (C r) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (HypRing K f), Polynomial.algebraMap_eq]

end HypRing

/-- The point ideal of `(x₀, y₀)` is the Mumford ideal of `(x - x₀, y₀)`. -/
theorem pointIdeal_eq_mumfordIdeal (x₀ y₀ : K) :
    pointIdeal f x₀ y₀ = mumfordIdeal f (X - C x₀) (C y₀) := by
  rw [pointIdeal, mumfordIdeal_eq_span, HypRing.algebraMap_eq_C]

/-- `div(x - x₀)` is `m_P · m_{ιP}`: the product of the point ideals of `(x₀, ±y₀)` is
the principal ideal `(x - x₀)`; the special case `u = x - x₀, v = y₀` of the Mumford
norm identity. -/
theorem pointIdeal_mul_pointIdeal_neg (hsf : Squarefree f) (h2 : (2 : K) ≠ 0) {x₀ y₀ : K}
    (h : y₀ ^ 2 = f.eval x₀) :
    pointIdeal f x₀ y₀ * pointIdeal f x₀ (-y₀) =
      Ideal.span {algebraMap K[X] (HypRing K f) (X - C x₀)} := by
  have hdvd : X - C x₀ ∣ C y₀ ^ 2 - f := by
    refine dvd_iff_isRoot.mpr ?_
    simp [IsRoot, h]
  rw [pointIdeal_eq_mumfordIdeal, pointIdeal_eq_mumfordIdeal, map_neg,
    ← map_star_mumfordIdeal, mumfordIdeal_mul_map_star f hsf h2 hdvd]

variable [Fact (Odd f.natDegree)]

open nonZeroDivisors in
theorem pointIdeal_mem_nonZeroDivisors (x₀ y₀ : K) :
    pointIdeal f x₀ y₀ ∈ (Ideal (HypRing K f))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (pointIdeal_ne_zero f x₀ y₀)

variable [NeZero (2 : K)] [Fact (Squarefree f)]

/-- The Abel--Jacobi map on affine points: `aj (x₀, y₀)` is the ideal class of
`(x - x₀, y - y₀)` in `J(K) = Cl(A_K)`. The base point `∞` maps to the trivial
class `1` by convention (`ClassGroup` is written multiplicatively). -/
noncomputable def aj (x₀ y₀ : K) : HypJac K f :=
  ClassGroup.mk0 ⟨pointIdeal f x₀ y₀, pointIdeal_mem_nonZeroDivisors f x₀ y₀⟩

/-- The involution acts as inversion under the Abel--Jacobi map: `aj (ιP) = (aj P)⁻¹`. -/
theorem aj_inv {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    aj f x₀ (-y₀) = (aj f x₀ y₀)⁻¹ := by
  refine ClassGroup.mk0_eq_mk0_inv_iff.mpr
    ⟨algebraMap K[X] _ (X - C x₀),
     (map_ne_zero_iff _ QuadraticAlgebra.algebraMap_injective).mpr (X_sub_C_ne_zero x₀), ?_⟩
  change pointIdeal f x₀ (-y₀) * pointIdeal f x₀ y₀ = _
  rw [mul_comm]
  exact pointIdeal_mul_pointIdeal_neg f Fact.out two_ne_zero h

/-- Cantor's reduction step at the level of ideal classes: if `v² - f = u·w`, the
classes of `(u, y - v)` and `(w, y - v)` are mutually inverse in `J(K)`. -/
theorem classGroup_mk0_mumfordIdeal_cofactor {u v w : K[X]} (hvw : v ^ 2 - f = u * w)
    (hu : u ≠ 0) (hw : w ≠ 0) :
    ClassGroup.mk0 ⟨mumfordIdeal f u v,
        mem_nonZeroDivisors_of_ne_zero (mumfordIdeal_ne_zero f hu v)⟩
      = (ClassGroup.mk0 ⟨mumfordIdeal f w v,
        mem_nonZeroDivisors_of_ne_zero (mumfordIdeal_ne_zero f hw v)⟩)⁻¹ := by
  refine ClassGroup.mk0_eq_mk0_inv_iff.mpr
    ⟨HypRing.y f - algebraMap K[X] _ v, fun hc ↦ ?_, ?_⟩
  · exact absurd (congrArg QuadraticAlgebra.im hc) (by simp)
  · change mumfordIdeal f u v * mumfordIdeal f w v = _
    exact mumfordIdeal_mul_cofactor f Fact.out two_ne_zero hvw

open nonZeroDivisors in
/-- Every nonzero ideal class of `A_K` is the class of a Mumford ideal
(semi-reduction at the level of `J(K)`). -/
theorem exists_mk0_eq_mk0_mumfordIdeal (𝔞 : Ideal (HypRing K f))
    (h𝔞 : 𝔞 ∈ (Ideal (HypRing K f))⁰) :
    ∃ (u v : K[X]) (hu : u ≠ 0), u ∣ v ^ 2 - f ∧
      ClassGroup.mk0 ⟨𝔞, h𝔞⟩ = ClassGroup.mk0 ⟨mumfordIdeal f u v,
        mem_nonZeroDivisors_of_ne_zero (mumfordIdeal_ne_zero f hu v)⟩ := by
  obtain ⟨c, u, v, hc, hu, hdvd, heq⟩ := exists_span_singleton_mul_mumfordIdeal f 𝔞 (by
    simpa [Submodule.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp h𝔞)
  refine ⟨u, v, hu, hdvd, ?_⟩
  have hcne : Ideal.span {algebraMap K[X] (HypRing K f) c} ∈ (Ideal (HypRing K f))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (span_singleton_algebraMap_ne_zero f hc)
  have hmne : mumfordIdeal f u v ∈ (Ideal (HypRing K f))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (mumfordIdeal_ne_zero f hu v)
  have h1 : (⟨𝔞, h𝔞⟩ : (Ideal (HypRing K f))⁰)
      = ⟨Ideal.span {algebraMap K[X] (HypRing K f) c}, hcne⟩ * ⟨mumfordIdeal f u v, hmne⟩ :=
    Subtype.ext heq
  rw [h1, map_mul, (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨_, rfl⟩⟩, one_mul]

end ChabautyColeman

end
