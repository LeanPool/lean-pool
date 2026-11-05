/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! # Absolute convergence from summable local Euler tails -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem summable_multiplicative_of_local_tails {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => f (p ^ k)))
    (htail : Summable (fun p : ℕ => if p.Prime then ∑' k : ℕ, f (p ^ (k + 1)) else 0)) :
    Summable f := by
  classical
  let t : ℕ → ℝ := fun p => if p.Prime then ∑' k : ℕ, f (p ^ (k + 1)) else 0
  have ht0 (p : ℕ) : 0 ≤ t p := by
    dsimp [t]
    split_ifs
    · exact tsum_nonneg (fun _ => hf _)
    · exact le_rfl
  apply (summable_nat_add_iff 1).mp
  apply summable_of_sum_le (fun n => hf (n + 1)) (c := exp (∑' p, t p))
  intro U
  let S := U.biUnion (fun n => (n + 1).primeFactors)
  obtain ⟨hSsum, hSprod⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf1 hmul (fun {p} hp => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hlocal p hp) S
  have hSsum' : Summable (fun n : Nat.factoredNumbers S => f n) := hSsum.of_norm
  let e : U → Nat.factoredNumbers S := fun n => ⟨n.1 + 1, Nat.mem_factoredNumbers.mpr
    ⟨Nat.succ_ne_zero _, fun p hp => mem_biUnion.mpr
      ⟨n.1, n.2, by simpa only [Nat.primeFactors, List.mem_toFinset] using hp⟩⟩⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have H : a.1 + 1 = b.1 + 1 := congrArg Subtype.val hab
    omega
  have HU : (∑ n ∈ U, f (n + 1)) ≤ ∑' n : Nat.factoredNumbers S, f n := by
    have H := (hasSum_fintype (fun n : U => f (n.1 + 1))).summable.tsum_le_tsum_of_inj e he
      (fun n _ => hf n) (fun _ => le_rfl) hSsum'
    simp only [e, tsum_fintype] at H
    rw [sum_coe_sort U (fun n => f (n + 1))] at H
    exact H
  apply HU.trans
  rw [hSprod.tsum_eq]
  calc
    _ ≤ ∏ p ∈ S.filter Nat.Prime, exp (t p) := by
      apply prod_le_prod₀
      · intro p _
        exact tsum_nonneg (fun _ => hf _)
      · intro p hp
        have hp' := (mem_filter.mp hp).2
        rw [(hlocal p hp').tsum_eq_zero_add, pow_zero, hf1]
        simpa only [t, hp', ite_true, add_comm] using add_one_le_exp (∑' k : ℕ, f (p ^ (k + 1)))
    _ = exp (∑ p ∈ S.filter Nat.Prime, t p) := (exp_sum _ _).symm
    _ ≤ exp (∑' p : ℕ, t p) := exp_le_exp.mpr (htail.sum_le_tsum _ (fun p _ => ht0 p))

end NairTenenbaum
