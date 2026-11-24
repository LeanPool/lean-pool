/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestProjectedFar
public import LeanPool.ShellsortMean.HarvestMenuSieve

/-! Average the genuine one-ring diagonal energies on the actual gap menu. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestNearMean
open Finset RoughGapEndpoint HarvestActualRings RoughGapDenominatorAverage Actual214
open HarvestProjectedFar

private theorem ring_support {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : Fin (n + 1)) (i : Fin n) (nz : ringVec ht hp p k i ≠ 0) :
    start T (rad H k.val) ≤ i.val ∧ i.val < start T (rad H k.val) + 2 * rad H k.val := by
  have eq : k = band ht hp i := by
    by_contra ne
    simp [ringVec, ne] at nz
  exact merged_support ht hp i (by rw [eq])

private theorem ring_norm_square {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : Fin (n + 1)) (i : Fin n) :
    ‖(ringVec ht hp p k i : ℂ)‖ ^ 2 = |(ringVec ht hp p k i : ℝ)| := by
  unfold ringVec slotError
  split_ifs <;> norm_num

private theorem ring_mean {n T D : ℕ} (j : ℕ) (hc : 9400 ≤ gap j) (hd : 0 < D) (ht : T ≤ n)
    (p : RankPlacement n) (k : Fin (n + 1)) :
    let G := window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))
    let hp := gap_pos j
    (∑ h ∈ G, ∑ b ∈ highGrid h D,
      energy 0 (fun i => (ringVec ht hp p k i : ℂ)) (b, h)) / (G.card : ℝ) ≤
      18800 * (32 * (gap j : ℝ) + (4 * Real.pi / D) * (2 * rad (gap j) k.val : ℕ)) *
        ∑ i, |(ringVec ht hp p k i : ℝ)| := by
  intro G hp
  let a := start T (rad (gap j) k.val)
  let L := 2 * rad (gap j) k.val
  let u (i : Fin n) := (ringVec ht hp p k i : ℝ)
  have hs (i : Fin n) (nz : u i ≠ 0) : a ≤ i.val ∧ i.val < a + L := by
    apply ring_support ht hp p k i
    dsimp [u] at nz
    exact_mod_cast nz
  let v (i : Fin L) := (pad a u i : ℂ)
  have matchE (h b : ℕ) (pos : 0 < h) :
      energy 0 (fun i => (ringVec ht hp p k i : ℂ)) (b, h) = energy a v (b, h) := by
    let : NeZero h := ⟨pos.ne'⟩
    have eq := coeff_pad a u hs (b : ZMod h)
    rw [coeff_exp, coeff_exp] at eq
    dsimp [u] at eq
    unfold energy
    simp only [Int.cast_zero, zero_add, Int.cast_natCast]
    dsimp [v]
    push_cast at eq
    simp only [neg_mul, u]
    simp only [neg_mul] at eq
    rw [eq]
  have energy_sum :
      (∑ h ∈ G, ∑ b ∈ highGrid h D,
        energy 0 (fun i => (ringVec ht hp p k i : ℂ)) (b, h)) =
      (∑ h ∈ G, ∑ b ∈ highGrid h D, energy a v (b, h)) := by
    apply sum_congr rfl
    intro h _
    apply sum_congr rfl
    intro b hb
    exact matchE h b (Nat.zero_lt_of_lt (mem_range.mp (mem_filter.mp hb).1))
  have hsAbs (i : Fin n) (nz : |u i| ≠ 0) := hs i (fun z => nz (by simp [z]))
  have ev (t : Fin L) : ‖v t‖ ^ 2 = pad a (fun i => |u i|) t := by
    by_cases h : a + t.val < n
    · simpa [v, pad, h, u] using ring_norm_square ht hp p k ⟨a + t.val, h⟩
    · simp [v, pad, h]
  have normsum : (∑ t, ‖v t‖ ^ 2) = ∑ i, |u i| := by
    simp_rw [ev]
    exact (pad_sum a (fun i => |u i|) hsAbs).symm
  rw [energy_sum]
  have bnd := actual_menu_short_mean j hc hd (a : ℤ) v
  simp only at bnd
  rw [normsum] at bnd
  convert bnd using 1; dsimp [L, u]; ring

/-- The diagonal part of the high-frequency energy, averaged by menu then
summed over every annulus of the genuine rank cut. The near-bandwidth factor
from the cross-term decomposition is applied by the caller. -/
theorem actual_menu_ring_energy {n T D : ℕ} (j : ℕ) (hc : 9400 ≤ gap j) (hd : 0 < D)
    (ht : T ≤ n) (p : RankPlacement n) :
    let G := window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))
    let hp := gap_pos j
    let s := ∑ i, |(slotError p T i : ℝ)|
    ∑ k : Fin (n + 1), (∑ h ∈ G, ∑ b ∈ highGrid h D,
      energy 0 (fun i => (ringVec ht hp p k i : ℂ)) (b, h)) / (G.card : ℝ) ≤
      18800 * (32 * (gap j : ℝ) * s + (4 * Real.pi / D) * (2 * (gap j : ℝ) * s + 4 * (cutMoment p
        T : ℝ))) := by
  intro G hp s
  let M (k : Fin (n + 1)) := ∑ i, |(ringVec ht hp p k i : ℝ)|
  let L (k : Fin (n + 1)) := ((2 * rad (gap j) k.val : ℕ) : ℝ)
  let f := 4 * Real.pi / D
  have mass : ∑ k, M k = s := by
    dsimp [M, s]
    rw [sum_comm]
    simp_rw [real_slot_mass]
  have totalLength : ∑ k, L k * M k ≤ 2 * (gap j : ℝ) * s + 4 * (cutMoment p T : ℝ) := by
    dsimp [L, M, s]
    exact_mod_cast length_mass ht hp p
  calc
    _ ≤ ∑ k, 18800 * (32 * (gap j : ℝ) + f * L k) * M k :=
      sum_le_sum fun k _ => ring_mean j hc hd ht p k
    _ = 18800 * (32 * (gap j : ℝ) * s + f*∑ k, L k * M k) := by
      rw [←mass]
      simp only [mul_sum, sum_add_distrib, mul_add, add_mul]
      ring_nf
    _ ≤ _ := by
      have fn : 0 ≤ f := by dsimp [f]; positivity
      gcongr

end Shellsort.HarvestNearMean
