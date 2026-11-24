/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import LeanPool.SuzukiCancellation.Algebra.Lie.IteratedCommutator
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Norm bounds for commutators and iterated adjoints

The bounds cover a single commutator, an adjoint power, a sequence of adjoints, and
nested commutators indexed by lists or finite tuples. They apply to BCH estimates and
product-formula error bounds.

## Main results

* `TrotterError.norm_commutator_le` bounds the commutator norm by twice the product of the argument
  norms.
* `TrotterError.norm_adSequence_le` bounds a sequence of iterated adjoint actions by a product of
  norm estimates.
* `FQFP.BCH.norm_nestedComm_le` bounds a nested commutator with `p` brackets by `2 ^ p` times the
  product of the argument norms.
-/

@[expose] public section

namespace TrotterError

open Finset LieAlgebra
open scoped algebraMap

attribute [local instance] LieRing.ofAssociativeRing

/-- The norm of a commutator is bounded by `2 * ‖A‖ * ‖B‖`. -/
theorem norm_commutator_le {𝔸 : Type*} [NormedRing 𝔸] (A B : 𝔸) :
    ‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  rw [Ring.lie_def]
  calc
    ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le (A * B) (B * A)
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le A B) (norm_mul_le B A)
    _ = 2 * ‖A‖ * ‖B‖ := by ring

/-- The norm of the `k`-fold iterated commutator is bounded by `(2 * ‖A‖)^k * ‖B‖`. -/
theorem norm_adPow_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) :
    ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ‖adPow A (k + 1) B‖ = ‖⁅A, adPow A k B⁆‖ := by rw [ad_pow_succ]
        _ ≤ 2 * ‖A‖ * ‖adPow A k B‖ := norm_commutator_le A (adPow A k B)
        _ ≤ 2 * ‖A‖ * ((2 * ‖A‖) ^ k * ‖B‖) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖A‖) ^ (k + 1) * ‖B‖ := by rw [pow_succ]; ring

/-- The norm of an iterated `ad` over a sequence is bounded by the product of the
per-step bounds `(2 * ‖A i‖) ^ (q i)`. -/
theorem norm_adSequence_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    ‖adSequence A q B‖ ≤ (∏ i : Fin s, (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
  induction s with
  | zero => simp
  | succ s ih =>
      calc
        ‖adSequence A q B‖
            = ‖adPow (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)‖ := by
                rw [adSequence_succ]
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ‖adSequence (fun i : Fin s => A i.castSucc)
                (fun i : Fin s => q i.castSucc) B‖ :=
              norm_adPow_le (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ((∏ i : Fin s, (2 * ‖A i.castSucc‖) ^ (q i.castSucc)) * ‖B‖) :=
              mul_le_mul_of_nonneg_left
                (ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc))
                (by positivity)
        _ = (∏ i : Fin (s + 1), (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
              rw [Fin.prod_univ_castSucc]
              ring

end TrotterError

open Finset

namespace FQFP.BCH

open TrotterError

attribute [local instance] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The norm of `nestedCommOfList b L` is bounded by `2 ^ L.length` times the product of the
norms of the seed and the list entries. -/
theorem norm_nestedCommOfList_le (b : 𝔸) (L : List 𝔸) :
    ‖nestedCommOfList b L‖ ≤ 2 ^ L.length * (‖b‖ * (L.map norm).prod) := by
  induction L generalizing b with
  | nil => simp [nestedCommOfList]
  | cons x L ih =>
      rw [show nestedCommOfList b (x :: L) = nestedCommOfList ⁅x, b⁆ L from rfl,
        List.length_cons, List.map_cons, List.prod_cons, pow_succ']
      calc ‖nestedCommOfList ⁅x, b⁆ L‖
          ≤ 2 ^ L.length * (‖⁅x, b⁆‖ * (L.map norm).prod) := ih ⁅x, b⁆
        _ ≤ 2 ^ L.length * ((2 * ‖x‖ * ‖b‖) * (L.map norm).prod) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (norm_commutator_le x b)
                (List.prod_nonneg fun a ha => by
                  obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
                  exact norm_nonneg x))
              (by positivity)
        _ = 2 ^ L.length * 2 * (‖x‖ * (‖b‖ * (L.map norm).prod)) := by ring
        _ = 2 * 2 ^ L.length * (‖b‖ * (‖x‖ * (L.map norm).prod)) := by ring

/-- The norm of a `p`-fold nested commutator is bounded by `2 ^ p` times the product of the
norms of its arguments. For `p = 1` this is `norm_commutator_le`. -/
theorem norm_nestedComm_le {p : ℕ} (H : Fin (p + 1) → 𝔸) :
    ‖nestedComm H‖ ≤ 2 ^ p * ∏ i : Fin (p + 1), ‖H i‖ := by
  induction p with
  | zero =>
      rw [nestedComm]; simp
  | succ p ih =>
      rw [nestedComm]
      have hprod : (∏ i : Fin (p + 2), ‖H i‖)
          = (∏ i : Fin (p + 1), ‖H i.castSucc‖) * ‖H (Fin.last (p + 1))‖ := by
        rw [Fin.prod_univ_castSucc]
      calc ‖⁅H (Fin.last (p + 1)), nestedComm (fun i : Fin (p + 1) => H i.castSucc)⁆‖
          ≤ 2 * ‖H (Fin.last (p + 1))‖ *
              ‖nestedComm (fun i : Fin (p + 1) => H i.castSucc)‖ := norm_commutator_le _ _
        _ ≤ 2 * ‖H (Fin.last (p + 1))‖ *
              (2 ^ p * ∏ i : Fin (p + 1), ‖(fun i : Fin (p + 1) => H i.castSucc) i‖) :=
            mul_le_mul_of_nonneg_left (ih _) (by positivity)
        _ = 2 ^ (p + 1) * ∏ i : Fin (p + 2), ‖H i‖ := by
            rw [hprod]; ring

end FQFP.BCH
