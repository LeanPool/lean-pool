/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Finiteness.Prod

/-! An explicit parameter space for Euler-constrained polynomial pairs.
For degree d=k+2, its dimension is d^2-1: two polynomials of degree at most
k and one homogeneous polynomial of degree k. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The parameter space of Euler-constrained pairs: triples `(A, B, Q)` with `A` and `B` bivariate
polynomials of total degree at most `k` and `Q` homogeneous of degree `k`. -/
abbrev EulerPairSpace (R : Type*) [CommRing R] (k : ℕ) :=
  (restrictTotalDegree (Fin 2) R k) × (restrictTotalDegree (Fin 2) R k) ×
    (homogeneousSubmodule (Fin 2) R k)

/-- `(A,B,Q)` gives `(A+yQ,B-xQ)`, so the two top-degree radial terms cancel. -/
def eulerPairCoordinates (R : Type*) [CommRing R] (k : ℕ) :
    EulerPairSpace R k →ₗ[R] MvPolynomial (Fin 2) R × MvPolynomial (Fin 2) R where
  toFun u := (u.1.val + X 1 * u.2.2.val, u.2.1.val - X 0 * u.2.2.val)
  map_add' u v := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, mul_add] <;> ring
  map_smul' a u := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      mul_smul_comm, smul_add, smul_sub, RingHom.id_apply]

/-- The first polynomial `A + y * Q` of an Euler pair has total degree at most `k + 1`. -/
lemma eulerPairCoordinates_fst_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) : (eulerPairCoordinates R k u).1.totalDegree ≤ k + 1 := by
  have hA := (mem_restrictTotalDegree _ _ _).mp u.1.property
  have hQ := u.2.2.property.totalDegree_le
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact hA.trans (by omega)
  · exact (totalDegree_mul _ _).trans (by
      have hx := (isHomogeneous_X R (1 : Fin 2)).totalDegree_le
      omega)

/-- The second polynomial `B - x * Q` of an Euler pair has total degree at most `k + 1`. -/
lemma eulerPairCoordinates_snd_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) : (eulerPairCoordinates R k u).2.totalDegree ≤ k + 1 := by
  have hB := (mem_restrictTotalDegree _ _ _).mp u.2.1.property
  have hQ := u.2.2.property.totalDegree_le
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact hB.trans (by omega)
  · exact (totalDegree_mul _ _).trans (by
      have hx := (isHomogeneous_X R (0 : Fin 2)).totalDegree_le
      omega)

private lemma eulerPairCoordinates_contraction {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) :
    X 0 * (eulerPairCoordinates R k u).1 + X 1 * (eulerPairCoordinates R k u).2 =
      X 0 * u.1.val + X 1 * u.2.1.val := by
  change X 0 * (u.1.val + X 1 * u.2.2.val) + X 1 * (u.2.1.val - X 0 * u.2.2.val) = _
  ring

/-- The radial contraction `x * P + y * Q` of the pair `(P, Q)` attached to an element of
`EulerPairSpace R k` has total degree at most `k + 1`. -/
lemma eulerPairCoordinates_contraction_degree {R : Type*} [CommRing R] (k : ℕ)
    (u : EulerPairSpace R k) :
    (X 0 * (eulerPairCoordinates R k u).1 + X 1 * (eulerPairCoordinates R k u).2).totalDegree ≤
      k + 1 := by
  rw [eulerPairCoordinates_contraction]
  apply (totalDegree_add _ _).trans
  apply max_le
  · have ha := (mem_restrictTotalDegree _ _ _).mp u.1.property
    have hx := (isHomogeneous_X R (0 : Fin 2)).totalDegree_le
    exact (totalDegree_mul _ _).trans (by omega)
  · have hb := (mem_restrictTotalDegree _ _ _).mp u.2.1.property
    have hx := (isHomogeneous_X R (1 : Fin 2)).totalDegree_le
    exact (totalDegree_mul _ _).trans (by omega)

private lemma eulerPairCoordinates_eq_zero {F : Type*} [Field F] (k : ℕ)
    (u : EulerPairSpace F k) (hu : eulerPairCoordinates F k u = 0) : u = 0 := by
  have hp := congrArg Prod.fst hu
  have hq := congrArg Prod.snd hu
  change u.1.val + X 1 * u.2.2.val = 0 at hp
  change u.2.1.val - X 0 * u.2.2.val = 0 at hq
  have hA : homogeneousComponent (k + 1) u.1.val = 0 :=
    homogeneousComponent_eq_zero _ _ (by
      have hh := (mem_restrictTotalDegree _ _ _).mp u.1.property
      omega)
  have hYQ : (X (1 : Fin 2) * u.2.2.val).IsHomogeneous (k + 1) := by
    simpa only [Nat.add_comm 1 k] using (isHomogeneous_X F (1 : Fin 2)).mul u.2.2.property
  have hh := congrArg (homogeneousComponent (k + 1)) hp
  rw [map_add, hA, homogeneousComponent_of_mem hYQ, ite_eq_left rfl, map_zero, zero_add] at hh
  have hQ0 : u.2.2.val = 0 := (mul_eq_zero.mp hh).resolve_left (X_ne_zero _)
  rw [hQ0, mul_zero, add_zero] at hp
  rw [hQ0, mul_zero, sub_zero] at hq
  exact Prod.ext (Subtype.ext hp) (Prod.ext (Subtype.ext hq) (Subtype.ext hQ0))

/-- Over a field, the map `(A, B, Q) ↦ (A + y * Q, B - x * Q)` is injective. -/
theorem eulerPairCoordinates_injective {F : Type*} [Field F] (k : ℕ) :
    Function.Injective (eulerPairCoordinates F k) := by
  intro u v huv
  have hh : eulerPairCoordinates F k (u - v) = 0 := by rw [map_sub, huv, sub_self]
  exact sub_eq_zero.mp (eulerPairCoordinates_eq_zero k (u - v) hh)

/-- The number of unknowns is exactly the desired Noether-form degree. -/
theorem finrank_eulerPairSpace {F : Type*} [Field F] (k : ℕ) :
    Module.finrank F (EulerPairSpace F k) = (k + 2) ^ 2 - 1 := by
  let : Module.Finite F (homogeneousSubmodule (Fin 2) F k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  unfold EulerPairSpace
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_restrictTotalDegree, finrank_homogeneousSubmodule_fin (n := 1)]
  simp only [Fintype.card_fin]
  have hchoose : 2 * (k + 2).choose k = (k + 2) * (k + 1) := by
    have hh := Nat.choose_mul_succ_eq (k + 1) k
    rw [Nat.choose_succ_self_right, show k + 1 + 1 = k + 2 by omega,
      show k + 2 - k = 2 by omega] at hh
    nlinarith
  rw [show 1 + k = k + 1 by omega, Nat.choose_succ_self_right]
  have he : 2 + k = k + 2 := by omega
  rw [he]
  have hh : (k + 2).choose k + ((k + 2).choose k + (k + 1)) + 1 = (k + 2) ^ 2 := by
    nlinarith
  omega

end
end CCDN
