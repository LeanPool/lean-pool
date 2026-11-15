/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Duality between packings and rows: the finite core

* `sum_mul_sum_mem` — double counting `∑_S κ_S a(S) = ∑_i a_i ∑_{S ∋ i} κ_S`;
* `no_separator`    — if every fractional packing has value at most `K`, then no `κ ≥ 0` has
                      `∑_S κ_S (a(S) - t_S) < 0` for all `a ≥ 0` of mass at most `K`.

In `no_separator`, write `c = ∑_S κ_S t_S` and `M_i = ∑_{S ∋ i} κ_S`. The hypothesis reads
`∑_i a_i M_i < c` for all admissible `a`; `a = 0` gives `c > 0`.
Case A (no `M_i` is positive): `((K+1)/c) κ` is a packing of value `K + 1 > K`.
Case B (`M_j = max_i M_i > 0`): `κ / M_j` is a packing, so `c ≤ K M_j`, while `a = K e_j` gives
`K M_j < c`.

This is the part of the proof of Proposition 6.7 (Duality) of the paper which follows the
separation step; there `c` and `M_i` are written `ϑ` and `σ_i`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_mul_sum_mem (κ : Finset ι → ℝ) (a : ι → ℝ) :
    ∑ S, κ S * ∑ i ∈ S, a i
      = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
  have h1 : ∀ S : Finset ι, κ S * ∑ i ∈ S, a i = ∑ i, if i ∈ S then a i * κ S else 0 := by
    intro S
    rw [Fintype.sum_ite_mem, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∀ i : ι, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S
      = ∑ S : Finset ι, if i ∈ S then a i * κ S else 0 := by
    intro i
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun S _ => h1 S, Finset.sum_congr rfl fun i _ => h2 i]
  exact Finset.sum_comm

theorem no_separator (t : Finset ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hsep : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ≤ K →
        ∑ S, κ S * (∑ i ∈ S, a i - t S) < 0) : False := by
  -- `c = ∑_S κ_S t_S` and `M_i = ∑_{S ∋ i} κ_S`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ S, κ S * t S := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ι → ℝ,
      ∀ i, M i = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := ⟨_, fun _ => rfl⟩
  -- the separation hypothesis in the form `∑_i a_i M_i < c`
  have hsep' : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ≤ K → ∑ i, a i * M i < c := by
    intro a ha0 haK
    have h := hsep a ha0 haK
    have h1 : ∑ i, a i * M i = ∑ S, κ S * ∑ i ∈ S, a i := by
      rw [sum_mul_sum_mem κ a]
      exact Finset.sum_congr rfl fun i _ => by rw [hM i]
    have h2 : ∑ S, κ S * (∑ i ∈ S, a i - t S)
        = ∑ S, κ S * ∑ i ∈ S, a i - ∑ S, κ S * t S := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun S _ => mul_sub _ _ _
    rw [h2, ← h1, ← hc] at h
    linarith
  -- `a = 0` gives `c > 0`
  have hcpos : 0 < c := by
    have h := hsep' 0 (fun _ => le_rfl) (by simpa using hK)
    simpa using h
  by_cases hex : ∃ i, 0 < M i
  · -- Case B: the largest load `M j` is positive
    obtain ⟨i0, hi0⟩ := hex
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ M ⟨i0, Finset.mem_univ i0⟩
    have hMj : 0 < M j := lt_of_lt_of_le hi0 (hj i0 (Finset.mem_univ i0))
    -- `κ / M j` is a packing
    have h1 := hpack (fun S => κ S / M j) (fun S => div_nonneg (hκ S) hMj.le)
      (fun i => by
        rw [← Finset.sum_div, ← hM i]
        exact (div_le_one hMj).mpr (hj i (Finset.mem_univ i)))
    have h2 : c ≤ K * M j := by
      have h3 : ∑ S, κ S / M j * t S = c / M j := by
        rw [hc, Finset.sum_div]
        exact Finset.sum_congr rfl fun S _ => by ring
      rw [h3, div_le_iff₀ hMj] at h1
      exact h1
    -- `a = K e_j` is admissible
    have hsum : ∑ i, (Pi.single j K : ι → ℝ) i = K := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h4 := hsep' (Pi.single j K)
      (fun i => by
        rw [Pi.single_apply]
        split_ifs
        · exact hK
        · exact le_rfl)
      hsum.le
    have h5 : ∑ i, (Pi.single j K : ι → ℝ) i * M i = K * M j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [h5] at h4
    linarith
  · -- Case A: no load is positive, so every nonnegative multiple of `κ` is a packing
    have hM0 : ∀ i, M i ≤ 0 := fun i => not_lt.mp fun h => hex ⟨i, h⟩
    have hs : 0 ≤ (K + 1) / c := div_nonneg (by linarith) hcpos.le
    have h1 := hpack (fun S => (K + 1) / c * κ S) (fun S => mul_nonneg hs (hκ S))
      (fun i => by
        rw [← Finset.mul_sum, ← hM i]
        have h6 : (K + 1) / c * M i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs (hM0 i)
        linarith)
    have h2 : ∑ S, (K + 1) / c * κ S * t S = K + 1 := by
      have h3 : ∑ S, (K + 1) / c * κ S * t S = (K + 1) / c * c := by
        rw [hc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring
      rw [h3, div_mul_cancel₀ _ hcpos.ne']
    rw [h2] at h1
    linarith

end Dual
end AaronsonAmbainis
