/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Partition
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Śliwa's basis and the operator on finite sequences

Śliwa (p. 629) works in the polynomials `ℂ[x]` with the basis

* `f₀ = 1`,
* `fᵢ = α^{((2r - 1)aₙ - 2i)/√(4aₙ)} xⁱ` on `Jₙ,ᵣ`, and the same with `bₙ` on `Lₙ,ᵣ`,
* `fᵢ = aₙ₋ᵣ (xⁱ - x^{i - aₙ})` on `Iₙ,ᵣ`,
* `fᵢ = xⁱ - bₙ x^{i - bₙ}` on `Kₙ,ᵣ`,

puts `‖∑ cᵢ fᵢ‖ = ∑ |cᵢ|`, and lets `T` multiply by `x`.

We work directly with coordinates in the basis `(fᵢ)`, as finitely supported sequences
`ℕ →₀ ℂ`, so `fᵢ` is the unit vector `δᵢ`. Solving each line above for `xⁱ` gives `xⁱ` in
coordinates by a recursion that only looks at smaller indices (`ReadL1.xPow`):

* `x⁰ = δ₀`; `xⁱ = δᵢ / cᵢ` on `J` and `L` blocks (`cᵢ` the weight);
* `xⁱ = δᵢ / aₙ₋ᵣ + x^{i - aₙ}` on `Iₙ,ᵣ`; `xⁱ = δᵢ + bₙ x^{i - bₙ}` on `Kₙ,ᵣ`.

Multiplying each `fᵢ` by `x` gives where the operator sends `δᵢ` (`ReadL1.shiftImage`), and the
operator on finite sequences is the linear extension (`ReadL1.T₀`). The point of the file is
`ReadL1.T₀_xPow`: the operator sends `xⁱ` to `xⁱ⁺¹`, i.e. it really is multiplication by `x`.
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- Śliwa's constant `α`. He allows any `α ≥ 8` (p. 628, "Let α ≥ 8"); we fix `α = 8`. -/
def alpha : ℝ := 8

lemma alpha_pos : 0 < alpha := by norm_num [alpha]

/-- The weight `α^{((2r - 1)c - 2i)/√(4c)}` of `xⁱ` in `fᵢ`, on a `J` block (`c = aₙ`) or an `L`
block (`c = bₙ`). -/
noncomputable def weight (c r i : ℕ) : ℝ :=
  alpha ^ (((2 * (r : ℝ) - 1) * c - 2 * i) / Real.sqrt (4 * c))

lemma weight_pos (c r i : ℕ) : 0 < weight c r i := Real.rpow_pos_of_pos alpha_pos _

lemma weight_ne_zero (c r i : ℕ) : (weight c r i : ℂ) ≠ 0 := by
  exact_mod_cast (weight_pos c r i).ne'

open Classical in
/-- The block containing `i` (an arbitrary block if there is none, which only happens at `0`). -/
noncomputable def block (d : ℕ → ℕ) (i : ℕ) : Block :=
  if h : ∃ B : Block, B.Mem d i then h.choose else ⟨0, 0, .J⟩

lemma Block.one_le_of_mem (h : PartitionHyp d) {B : Block} {i : ℕ} (hB : B.Mem d i) : 1 ≤ i := by
  have := (B.mem_level h hB).1; omega

lemma block_mem (h : PartitionHyp d) {i : ℕ} (hi : 1 ≤ i) : (block d i).Mem d i := by
  have hex := exists_block h hi
  rw [block, dite_eq_left hex]
  exact hex.choose_spec

/-- Any block containing `i` is `block d i`. -/
lemma block_eq (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) : block d i = B :=
  block_unique h (block_mem h (Block.one_le_of_mem h hB)) hB

/-- **`xⁱ` in the coordinates of Śliwa's basis.** -/
noncomputable def xPow (d : ℕ → ℕ) : ℕ → (ℕ →₀ ℂ)
  | 0 => single 0 1
  | i + 1 =>
    match (block d (i + 1)).kind with
    | .J => (weight (seqA d (block d (i + 1)).n) (block d (i + 1)).r (i + 1) : ℂ)⁻¹ •
        single (i + 1) 1
    | .I => (seqA d ((block d (i + 1)).n - (block d (i + 1)).r) : ℂ)⁻¹ • single (i + 1) 1 +
        if _h : seqA d (block d (i + 1)).n ≠ 0 then xPow d (i + 1 - seqA d (block d (i + 1)).n)
        else 0
    | .L => (weight (seqB d (block d (i + 1)).n) (block d (i + 1)).r (i + 1) : ℂ)⁻¹ •
        single (i + 1) 1
    | .K => single (i + 1) 1 +
        if _h : seqB d (block d (i + 1)).n ≠ 0 then
          (seqB d (block d (i + 1)).n : ℂ) • xPow d (i + 1 - seqB d (block d (i + 1)).n)
        else 0
  termination_by i => i
  decreasing_by all_goals omega

/-- **Where the operator sends `δᵢ = fᵢ`**: the coordinates of `x fᵢ`. -/
noncomputable def shiftImage (d : ℕ → ℕ) (i : ℕ) : ℕ →₀ ℂ :=
  if i = 0 then xPow d 1 else
    match (block d i).kind with
    | .J => (weight (seqA d (block d i).n) (block d i).r i : ℂ) • xPow d (i + 1)
    | .I => (seqA d ((block d i).n - (block d i).r) : ℂ) •
        (xPow d (i + 1) - xPow d (i + 1 - seqA d (block d i).n))
    | .L => (weight (seqB d (block d i).n) (block d i).r i : ℂ) • xPow d (i + 1)
    | .K => xPow d (i + 1) - (seqB d (block d i).n : ℂ) • xPow d (i + 1 - seqB d (block d i).n)

/-- The operator on finitely supported sequences: the linear extension of `δᵢ ↦ shiftImage i`. -/
noncomputable def T₀ (d : ℕ → ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  linearCombination ℂ (shiftImage d)

lemma T₀_single (i : ℕ) (c : ℂ) : T₀ d (single i c) = c • shiftImage d i := by
  simp [T₀]

/-- **The operator multiplies by `x`: it sends `xⁱ` to `xⁱ⁺¹`.** Each case undoes the recursion
defining `xⁱ`, using the claim for the smaller power it refers to. -/
theorem T₀_xPow (h : PartitionHyp d) (i : ℕ) : T₀ d (xPow d i) = xPow d (i + 1) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases i with _ | i
  · simp [xPow, T₀_single, shiftImage]
  · have hB := block_mem h (i := i + 1) (by omega)
    obtain ⟨hr1, hrn, hk⟩ := hB
    have ha := h.one_le_a (block d (i + 1)).n
    have hb : 0 < seqB d (block d (i + 1)).n :=
      lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b _)
    rw [xPow]
    rcases hkind : (block d (i + 1)).kind with _ | _ | _ | _ <;>
      simp only [hkind] at hk ⊢
    · -- `J`: `xⁱ = δᵢ / cᵢ` and `δᵢ ↦ cᵢ xⁱ⁺¹`.
      rw [map_smul, T₀_single]
      simp only [shiftImage, Nat.add_one_ne_zero, ite_false, hkind]
      rw [one_smul, smul_smul, inv_mul_cancel₀ (weight_ne_zero _ _ _), one_smul]
    · -- `I`: `xⁱ = δᵢ / aₙ₋ᵣ + x^{i - aₙ}` and `δᵢ ↦ aₙ₋ᵣ (xⁱ⁺¹ - x^{i + 1 - aₙ})`.
      have ha' : (seqA d ((block d (i + 1)).n - (block d (i + 1)).r) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h.one_le_a _))
      have hle : seqA d (block d (i + 1)).n ≤ i + 1 := by
        have := Nat.le_mul_of_pos_left (seqA d (block d (i + 1)).n) hr1; omega
      rw [dite_eq_left (by omega), map_add, map_smul, T₀_single, ih _ (by omega)]
      simp only [shiftImage, Nat.add_one_ne_zero, ite_false, hkind]
      rw [one_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
      rw [show i + 1 - seqA d (block d (i + 1)).n + 1 = i + 1 + 1 - seqA d (block d (i + 1)).n
        by omega]
      abel
    · -- `L`: as for `J`, with `bₙ`.
      rw [map_smul, T₀_single]
      simp only [shiftImage, Nat.add_one_ne_zero, ite_false, hkind]
      rw [one_smul, smul_smul, inv_mul_cancel₀ (weight_ne_zero _ _ _), one_smul]
    · -- `K`: `xⁱ = δᵢ + bₙ x^{i - bₙ}` and `δᵢ ↦ xⁱ⁺¹ - bₙ x^{i + 1 - bₙ}`.
      have hle : seqB d (block d (i + 1)).n ≤ i + 1 := by
        have := Nat.le_mul_of_pos_left (seqA d (block d (i + 1)).n + seqB d (block d (i + 1)).n)
          hr1
        omega
      rw [dite_eq_left (by omega), map_add, map_smul, T₀_single, one_smul, ih _ (by omega)]
      simp only [shiftImage, Nat.add_one_ne_zero, ite_false, hkind]
      rw [show i + 1 - seqB d (block d (i + 1)).n + 1 = i + 1 + 1 - seqB d (block d (i + 1)).n
        by omega]
      abel

end ReadL1
