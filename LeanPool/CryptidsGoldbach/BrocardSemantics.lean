/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Veljjanoski
-/

-- Modified for Lean Pool.

module

public import LeanPool.CryptidsGoldbach.Brocard28
public import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring

/-!
# Semantics of `brocard_28`

`Halts brocard28 ↔ ∃ n, 7 < n ∧ IsSquare (n ! + 1)`: the machine's triangular test of
`n! / 8` is equivalent to `n! + 1` being a perfect square, since `n! + 1 = m ^ 2` forces `m` odd,
`m = 2k + 1`, and then `n! / 8 = k (k + 1) / 2 = tri k`.
-/

@[expose] public section

namespace ConjectureMachines

/-- Brocard's conjecture says that no natural number beyond `7` has square `n! + 1`. -/
def BrocardConjecture : Prop := ∀ n : ℕ, 7 < n → ¬ IsSquare (n.factorial + 1)

end ConjectureMachines

namespace ConjectureMachines.Brocard28

/-- `tri k = k * (k + 1) / 2`. -/
theorem two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [tri_succ, Nat.mul_add, ih]; ring

/-- For `n ≥ 4`, `n! + 1` is a square if and only if `n! / 8` is triangular. -/
theorem isSquare_iff_isTri {n : ℕ} (hn : 4 ≤ n) : IsSquare (n.factorial + 1) ↔ IsTri (V n) := by
  obtain ⟨c, hc⟩ := eight_dvd_factorial hn
  have hV : V n = c := by rw [V, hc, Nat.mul_div_cancel_left _ (by decide)]
  rw [hV, hc]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk | hk⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
    · -- `m` even: `m * m` is even, but `8 c + 1` is odd
      exfalso
      rw [hk] at hm
      have : 8 * c + 1 = 4 * (k * k) := by rw [hm]; ring
      omega
    · refine ⟨k, ?_⟩
      rw [hk] at hm
      have h1 : 8 * c + 1 = 4 * (k * k) + 4 * k + 1 := by rw [hm]; ring
      have h2 := two_mul_tri k
      rw [Nat.mul_succ] at h2
      omega
  · rintro ⟨k, hk⟩
    refine ⟨2 * k + 1, ?_⟩
    have h2 := two_mul_tri k
    rw [Nat.mul_succ] at h2
    have h3 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k) + 4 * k + 1 := by ring
    omega

/-- The 28-state machine halts on the blank tape if and only if Brocard's problem has a
solution beyond `n = 4, 5, 7`. -/
theorem halts_brocard28_iff_exists_square :
    ConjectureMachines.Halts brocard28 ↔ ∃ n, 7 < n ∧ IsSquare (n.factorial + 1) := by
  rw [halts_brocard28_iff_exists_tri]
  constructor
  · rintro ⟨n, h8, hn⟩
    exact ⟨n, by omega, (isSquare_iff_isTri (by omega)).mpr hn⟩
  · rintro ⟨n, h7, hn⟩
    exact ⟨n, by omega, (isSquare_iff_isTri (by omega)).mp hn⟩

/-- The 28-state machine halts if and only if Brocard's conjecture is false. -/
theorem halts_brocard28_iff_not_brocard :
    ConjectureMachines.Halts brocard28 ↔ ¬ BrocardConjecture := by
  rw [halts_brocard28_iff_exists_square]
  exact ⟨fun ⟨n, h7, hn⟩ hB => hB n h7 hn,
    fun h => by_contra fun hne => h fun n h7 hn => hne ⟨n, h7, hn⟩⟩

end ConjectureMachines.Brocard28
