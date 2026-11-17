/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The Mumford datum of a tuple of curve points, with denominators cleared

The Mumford datum interpolating a tuple of points `(xᵢ, yᵢ)` of the curve `y² = f(x)` — the
support `u = ∏ (X - xᵢ)`, the interpolant `v` with `v(xᵢ) = yᵢ` and its cofactor
`w = (v² - f) / u` — involves division by the interpolation denominators. This file
constructs the **denominator-cleared** versions, which are polynomial in the coordinates
of the tuple and therefore commute with ring homomorphisms (`ChabautyColeman.map_tupleU`
and friends); the honest datum over a field is recovered in
`LeanPool.HyperellipticCurves.Log.Witness.TupleSeed`.

## Main definitions

* `ChabautyColeman.tupleU`: the support `∏ (X - xᵢ)`.
* `ChabautyColeman.tupleInterp`: the interpolant of prescribed values, cleared by the common
  denominator `ChabautyColeman.nodeDen` (so its value at `xᵢ` is `cᵢ · nodeDen x`).
* `ChabautyColeman.tupleWNum`: the cleared cofactor, with denominator `nodeDen x ^ 2`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Nodes

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The product of the differences of the node `x i` from all other nodes. -/
def nodeDiff (x : Fin m → R) (i : Fin m) : R := ∏ j ∈ {i}ᶜ, (x i - x j)

/-- The product of all node-difference products: the common denominator of the Lagrange
interpolation at the nodes. -/
def nodeDen (x : Fin m → R) : R := ∏ i, nodeDiff x i

/-- The product of the node-difference products at all nodes other than `i`. -/
def nodeCoDen (x : Fin m → R) (i : Fin m) : R := ∏ k ∈ {i}ᶜ, nodeDiff x k

/-- The monic polynomial with the nodes as its roots. -/
noncomputable def tupleU (x : Fin m → R) : R[X] := Lagrange.nodal Finset.univ x

theorem tupleU_eq_prod (x : Fin m → R) : tupleU x = ∏ i, (X - C (x i)) := rfl

/-- The `i`-th Lagrange numerator: the nodal polynomial with the node `x i` removed. -/
noncomputable def nodeLag (x : Fin m → R) (i : Fin m) : R[X] := Lagrange.nodal {i}ᶜ x

theorem nodeLag_eq_prod (x : Fin m → R) (i : Fin m) :
    nodeLag x i = ∏ j ∈ {i}ᶜ, (X - C (x j)) := rfl

/-- The denominator-cleared Lagrange interpolant of the values `c` at the nodes `x`: a
polynomial of degree less than the number of nodes taking the value `c i * nodeDen x` at
`x i`. -/
noncomputable def tupleInterp (x : Fin m → R) (c : Fin m → R) : R[X] :=
  ∑ i, C (c i * nodeCoDen x i) * nodeLag x i

theorem nodeDen_eq_mul (x : Fin m → R) (i : Fin m) :
    nodeDen x = nodeDiff x i * nodeCoDen x i :=
  Fintype.prod_eq_mul_prod_compl i _

theorem eval_nodeLag_self (x : Fin m → R) (i : Fin m) :
    (nodeLag x i).eval (x i) = nodeDiff x i :=
  Lagrange.eval_nodal

theorem eval_nodeLag_of_ne {x : Fin m → R} {i j : Fin m} (h : j ≠ i) :
    (nodeLag x i).eval (x j) = 0 :=
  Lagrange.eval_nodal_at_node (Finset.mem_compl.mpr (by simpa using h))

theorem monic_nodeLag (x : Fin m → R) (i : Fin m) : (nodeLag x i).Monic :=
  Lagrange.nodal_monic

theorem monic_tupleU (x : Fin m → R) : (tupleU x).Monic :=
  Lagrange.nodal_monic

theorem natDegree_tupleU [Nontrivial R] (x : Fin m → R) : (tupleU x).natDegree = m := by
  rw [tupleU, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]

theorem natDegree_nodeLag [Nontrivial R] (x : Fin m → R) (i : Fin m) :
    (nodeLag x i).natDegree = m - 1 := by
  rw [nodeLag, Lagrange.natDegree_nodal, Finset.card_compl]
  simp

theorem eval_tupleU (x : Fin m → R) (a : R) : (tupleU x).eval a = ∏ i, (a - x i) :=
  Lagrange.eval_nodal

theorem eval_tupleU_self (x : Fin m → R) (i : Fin m) : (tupleU x).eval (x i) = 0 :=
  Lagrange.eval_nodal_at_node (Finset.mem_univ i)

/-- The derivative of the nodal polynomial at a node is the node-difference product. -/
theorem derivative_tupleU_eval (x : Fin m → R) (i : Fin m) :
    (tupleU x).derivative.eval (x i) = nodeDiff x i := by
  rw [tupleU, Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i),
    ← Finset.compl_singleton]
  exact Lagrange.eval_nodal

/-- Unit-separated nodes have unit node-difference products — the nodal polynomial is
transversal at each node, which is what Hensel lifting at the nodes needs. -/
theorem isUnit_nodeDiff {x : Fin m → R} (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (i : Fin m) :
    IsUnit (nodeDiff x i) :=
  Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun j hj ↦
    hx i j fun h ↦ Finset.mem_compl.mp hj (Finset.mem_singleton.mpr h.symm)

theorem eval_tupleInterp (x c : Fin m → R) (j : Fin m) :
    (tupleInterp x c).eval (x j) = c j * nodeDen x := by
  rw [tupleInterp, eval_finsetSum, Finset.sum_eq_single j]
  · rw [eval_mul, eval_C, eval_nodeLag_self, nodeDen_eq_mul x j]
    ring
  · intro i _ hij
    rw [eval_mul, eval_nodeLag_of_ne (Ne.symm hij), mul_zero]
  · simp

theorem degree_tupleInterp_lt [Nontrivial R] (x c : Fin m → R) :
    (tupleInterp x c).degree < (m : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (mod_cast WithBot.bot_lt_coe m)).mpr fun i _ ↦ ?_
  refine lt_of_le_of_lt ((degree_mul_le _ _).trans (add_le_add degree_C_le le_rfl)) ?_
  rw [zero_add, degree_eq_natDegree (monic_nodeLag x i).ne_zero, natDegree_nodeLag]
  exact_mod_cast Nat.sub_lt i.pos one_pos

end Nodes

section Datum

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The denominator-cleared cofactor of the tuple datum: `nodeDen x ^ 2` times the cofactor
`(v ^ 2 - f) / u` of the Mumford datum interpolating the tuple. -/
noncomputable def tupleWNum (f : R[X]) (x y : Fin m → R) : R[X] :=
  (tupleInterp x y ^ 2 - C (nodeDen x ^ 2) * f) /ₘ tupleU x

end Datum

section Map

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)

theorem map_nodeDiff (x : Fin m → R) (i : Fin m) :
    φ (nodeDiff x i) = nodeDiff (fun j ↦ φ (x j)) i := by
  simp [nodeDiff, map_prod]

theorem map_nodeDen (x : Fin m → R) : φ (nodeDen x) = nodeDen fun j ↦ φ (x j) := by
  simp [nodeDen, map_prod, map_nodeDiff]

theorem map_nodeCoDen (x : Fin m → R) (i : Fin m) :
    φ (nodeCoDen x i) = nodeCoDen (fun j ↦ φ (x j)) i := by
  simp [nodeCoDen, map_prod, map_nodeDiff]

theorem map_tupleU (x : Fin m → R) : (tupleU x).map φ = tupleU fun j ↦ φ (x j) := by
  simp [tupleU_eq_prod, Polynomial.map_prod]

theorem map_nodeLag (x : Fin m → R) (i : Fin m) :
    (nodeLag x i).map φ = nodeLag (fun j ↦ φ (x j)) i := by
  simp [nodeLag_eq_prod, Polynomial.map_prod]

theorem map_tupleInterp (x c : Fin m → R) :
    (tupleInterp x c).map φ = tupleInterp (fun j ↦ φ (x j)) fun j ↦ φ (c j) := by
  rw [tupleInterp, Polynomial.map_sum, tupleInterp]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Polynomial.map_mul, Polynomial.map_C, map_mul, map_nodeCoDen, map_nodeLag]

theorem map_tupleWNum (f : R[X]) (x y : Fin m → R) :
    (tupleWNum f x y).map φ = tupleWNum (f.map φ) (fun j ↦ φ (x j)) fun j ↦ φ (y j) := by
  rw [tupleWNum, map_divByMonic φ (monic_tupleU x), tupleWNum, map_tupleU, Polynomial.map_sub,
    Polynomial.map_pow, map_tupleInterp, Polynomial.map_mul, Polynomial.map_C, map_pow,
    map_nodeDen]

end Map

end ChabautyColeman

end
