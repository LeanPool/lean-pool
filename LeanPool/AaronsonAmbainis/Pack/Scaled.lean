/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Pack.Gate
public import LeanPool.AaronsonAmbainis.Pack.Blocks

/-!
# The packing bound before the limit

`scaled_bound`: from the block inequality, for a fractional packing `κ` and every natural number
`M ≥ 1`,
`M² ∑_S κ_S |f x - f (x^S)| ≤ d² (π M + 2)² + ∑_S |f x - f (x^S)|`.
This is the inequality `M² Λ ≤ d² (π M + 2)² + C₀` in the proof of the packing bound (Lemma 6.5 of
the paper).

Proof: `N = M²`, `k S = ⌊N κ S⌋₊`, block family `Σ S, Fin (k S)`, `m = ⌈π M / 2⌉₊`.
-/

@[expose] public section

namespace AaronsonAmbainis.Pack

open Finset

/-- For `k S = ⌊N κ S⌋₊` and a fractional packing `κ`, every coordinate lies in at most `N`
blocks of the family `Σ S, Fin (k S)`. -/
theorem card_blocks_le {ι : Type} [Fintype ι] [DecidableEq ι] (κ : Finset ι → ℝ)
    (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) (N : ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin ⌊(N : ℝ) * κ S⌋₊) => i ∈ b.1).card ≤ N := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [card_blocks (fun S : Finset ι => ⌊(N : ℝ) * κ S⌋₊) i]
  have hreal : ((∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
      ≤ (N : ℝ) := by
    rw [Nat.cast_sum]
    calc ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ((⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), (N : ℝ) * κ S :=
          Finset.sum_le_sum fun S _ => Nat.floor_le (mul_nonneg hN (hκ S))
      _ = (N : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (hpack i) hN
      _ = (N : ℝ) := mul_one _
  exact Nat.cast_le.mp hreal

/-- The packing bound before the limit, from the block inequality with `N = M ^ 2` and
`m = ⌈π M / 2⌉₊`. -/
theorem scaled_bound (hB : BlockInequality) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hd : HasDegreeLE f d) (x : Cube ι)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| := by
  -- the block inequality for the family `Σ S, Fin ⌊M² κ S⌋₊` and `m = ⌈π M / 2⌉₊`
  have hblock := hB ι d f hf hd x (Σ S : Finset ι, Fin ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun b => b.1) (M ^ 2) ⌈Real.pi * (M : ℝ) / 2⌉₊ (gate_pos M hM)
    (card_blocks_le κ hκ hpack (M ^ 2)) (gate_cos M hM)
  rw [sum_blocks (fun S : Finset ι => ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun S : Finset ι => |f x - f (flipSet x S)|)] at hblock
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- the right side of the block inequality
  have hright : 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 := by
    calc 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
        = (d : ℝ) ^ 2 * (4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (gate_sq M) hd2
  -- termwise: `M² κ S < ⌊M² κ S⌋₊ + 1`
  have hterm : ∀ S : Finset ι, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
      ≤ ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
        + |f x - f (flipSet x S)| := by
    intro S
    have hlt : ((M ^ 2 : ℕ) : ℝ) * κ S < ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have habs : (0 : ℝ) ≤ |f x - f (flipSet x S)| := abs_nonneg _
    calc (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
        = (((M ^ 2 : ℕ) : ℝ) * κ S) * |f x - f (flipSet x S)| := by rw [hcast]; ring
      _ ≤ (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1) * |f x - f (flipSet x S)| :=
          mul_le_mul_of_nonneg_right hlt.le habs
      _ = ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
            + |f x - f (flipSet x S)| := by ring
  calc (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      = ∑ S, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|) := by rw [Finset.mul_sum]
    _ ≤ ∑ S, (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + |f x - f (flipSet x S)|) := Finset.sum_le_sum fun S _ => hterm S
    _ = ∑ S, ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + ∑ S, |f x - f (flipSet x S)| := Finset.sum_add_distrib
    _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| :=
        add_le_add (hblock.trans hright) le_rfl

end AaronsonAmbainis.Pack
