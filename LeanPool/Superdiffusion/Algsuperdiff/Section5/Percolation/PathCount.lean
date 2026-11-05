/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Lattice
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Pi
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Parity

/-!
# PathCount

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Counting finite lattice paths

This file gives explicit finite enumerations of centered-cube starting sites,
sup-neighbor offsets, and lattice paths of a prescribed vertex length.  The
enumeration deliberately includes an extra factor of `3^d`, matching the
dimension-only overcount used in the percolation union bound.
-/

namespace Algsuperdiff.Section5.Percolation

open scoped BigOperators

private theorem odd_three_pow (k : ℕ) : Odd (3 ^ k) := by
  exact (show Odd 3 by norm_num).pow

private theorem exists_centered_index {q : ℕ} (hq : Odd q) {z : ℤ}
    (hz : 2 * z.natAbs < q) :
    ∃ j : Fin q, (j : ℤ) - (q / 2 : ℕ) = z := by
  have hhalf : 2 * (q / 2) + 1 = q := Nat.two_mul_div_two_add_one_of_odd hq
  have habs : z.natAbs ≤ q / 2 := by omega
  by_cases hz0 : 0 ≤ z
  · have hcast : (z.natAbs : ℤ) = z := by
      rw [Int.natCast_natAbs, abs_of_nonneg hz0]
    let j : Fin q := ⟨q / 2 + z.natAbs, by omega⟩
    refine ⟨j, ?_⟩
    change ((q / 2 + z.natAbs : ℕ) : ℤ) - (q / 2 : ℕ) = z
    calc
      ((q / 2 + z.natAbs : ℕ) : ℤ) - (q / 2 : ℕ) = (z.natAbs : ℤ) := by
        push_cast
        ring
      _ = z := hcast
  · have hzneg : z < 0 := lt_of_not_ge hz0
    have hcast : (z.natAbs : ℤ) = -z := by
      rw [Int.natCast_natAbs, abs_of_neg hzneg]
    let j : Fin q := ⟨q / 2 - z.natAbs, by omega⟩
    refine ⟨j, ?_⟩
    change ((q / 2 - z.natAbs : ℕ) : ℤ) - (q / 2 : ℕ) = z
    calc
      ((q / 2 - z.natAbs : ℕ) : ℤ) - (q / 2 : ℕ) = -(z.natAbs : ℤ) := by
        rw [Nat.cast_sub habs]
        push_cast
        ring
      _ = z := by rw [hcast, neg_neg]

/-- The site encoded by one coordinate in `Fin (3^k)` in every direction,
centered around the origin. -/
def cubeSiteOfIndex {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Site d :=
  fun i => ((j i : ℕ) : ℤ) - (((3 ^ k) / 2 : ℕ) : ℤ)

private theorem cubeSiteOfIndex_injective {d k : ℕ} :
    Function.Injective (cubeSiteOfIndex (d := d) k) := by
  intro j j' h
  funext i
  apply Fin.ext
  have hi := congr_fun h i
  change ((j i : ℕ) : ℤ) - ((3 ^ k) / 2 : ℕ) =
    ((j' i : ℕ) : ℤ) - ((3 ^ k) / 2 : ℕ) at hi
  omega

/-- The finite set of lattice sites in the centered scale-`k` cube. -/
def cubeSites (d k : ℕ) : Finset (Site d) :=
  Finset.univ.image (cubeSiteOfIndex (d := d) k)

/-- Every explicitly encoded cube site satisfies the strict cube inequalities. -/
theorem cubeSiteOfIndex_inCube {d k : ℕ} (j : Fin d → Fin (3 ^ k)) :
    inCube k (cubeSiteOfIndex k j) := by
  intro i
  let q := 3 ^ k
  have hhalf : 2 * (q / 2) + 1 = q :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow k)
  change 2 * (((j i : ℕ) : ℤ) - (q / 2 : ℕ)).natAbs < q
  by_cases hji : (j i : ℕ) ≤ q / 2
  · have hnonpos : ((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ) ≤ 0 := by
      omega
    have habsEq :
        (((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ)).natAbs =
          q / 2 - (j i : ℕ) := by
      apply Int.ofNat_injective
      calc
        Int.ofNat (((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ)).natAbs =
            -(((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ)) :=
          Int.ofNat_natAbs_of_nonpos hnonpos
        _ = ((q / 2 : ℕ) : ℤ) - ((j i : ℕ) : ℤ) := by ring
        _ = Int.ofNat (q / 2 - (j i : ℕ)) := (Int.ofNat_sub hji).symm
    rw [habsEq]
    omega
  · have hle : q / 2 ≤ (j i : ℕ) := Nat.le_of_lt (lt_of_not_ge hji)
    have hnonneg : 0 ≤ ((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ) := by omega
    have habsEq :
        (((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ)).natAbs =
          (j i : ℕ) - q / 2 := by
      apply Int.ofNat_injective
      calc
        Int.ofNat (((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ)).natAbs =
            ((j i : ℕ) : ℤ) - ((q / 2 : ℕ) : ℤ) :=
          Int.natAbs_of_nonneg hnonneg
        _ = Int.ofNat ((j i : ℕ) - q / 2) := (Int.ofNat_sub hle).symm
    rw [habsEq]
    have hjlt := (j i).isLt
    omega

/-- The explicit cube-site enumeration contains every site in the cube. -/
theorem mem_cubeSites_of_inCube {d k : ℕ} {x : Site d} (hx : inCube k x) :
    x ∈ cubeSites d k := by
  have hex : ∀ i : Fin d, ∃ j : Fin (3 ^ k),
      (j : ℤ) - ((3 ^ k) / 2 : ℕ) = x i := by
    intro i
    exact exists_centered_index (odd_three_pow k) (hx i)
  choose j hj using hex
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  funext i
  exact hj i

/-- The scale-`k` cube contains exactly `3^(d*k)` lattice sites. -/
theorem card_cubeSites (d k : ℕ) :
    (cubeSites d k).card = 3 ^ (d * k) := by
  rw [cubeSites, Finset.card_image_of_injective _ cubeSiteOfIndex_injective,
    Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  calc
    (3 ^ k) ^ d = 3 ^ (k * d) := (pow_mul 3 k d).symm
    _ = 3 ^ (d * k) := by rw [Nat.mul_comm k d]

/-- The sup-neighbor offset encoded by one coordinate in `Fin 3` in every
direction. -/
def offsetOfIndex {d : ℕ} (j : Fin d → Fin 3) : Site d :=
  fun i => (j i : ℤ) - 1

private theorem offsetOfIndex_injective {d : ℕ} :
    Function.Injective (offsetOfIndex (d := d)) := by
  intro j j' h
  funext i
  apply Fin.ext
  have hi := congr_fun h i
  change ((j i : ℕ) : ℤ) - 1 = ((j' i : ℕ) : ℤ) - 1 at hi
  omega

/-- The finite palette of all `3^d` sup-neighbor offsets, including zero. -/
def neighborOffsets (d : ℕ) : Finset (Site d) :=
  Finset.univ.image offsetOfIndex

/-- The neighbor-offset palette has cardinality `3^d`. -/
theorem card_neighborOffsets (d : ℕ) :
    (neighborOffsets d).card = 3 ^ d := by
  rw [neighborOffsets, Finset.card_image_of_injective _ offsetOfIndex_injective,
    Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]

/-- Every adjacent step is represented by the neighbor-offset palette. -/
theorem exists_neighborOffset_of_adj {d : ℕ} {x y : Site d} (hxy : Adj x y) :
    ∃ δ ∈ neighborOffsets d, y = x + δ := by
  have hcoord : ∀ i : Fin d, 2 * (y i - x i).natAbs < 3 := by
    intro i
    have hi := natAbs_sub_le_siteDist y x i
    rw [siteDist_comm, hxy] at hi
    omega
  have hex : ∀ i : Fin d, ∃ j : Fin 3, (j : ℤ) - 1 = y i - x i := by
    intro i
    simpa only [show (3 / 2 : ℕ) = 1 by norm_num] using!
      (exists_centered_index (show Odd 3 by norm_num) (hcoord i))
  choose j hj using hex
  let δ := offsetOfIndex j
  refine ⟨δ, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, ?_⟩
  funext i
  change y i = x i + ((j i : ℤ) - 1)
  rw [hj i]
  ring

/-- All walks with `n` steps starting at `x`. -/
def walksFrom {d : ℕ} (x : Site d) : ℕ → Finset (List (Site d))
  | 0 => {[x]}
  | n + 1 => (neighborOffsets d).biUnion fun δ =>
      (walksFrom (x + δ) n).image (List.cons x)

/-- A path belongs to the finite walk enumeration determined by its first
vertex and number of remaining vertices. -/
theorem mem_walksFrom_of_isPath {d : ℕ} (x : Site d) :
    ∀ (xs : List (Site d)), IsPath (x :: xs) →
      x :: xs ∈ walksFrom x xs.length
  | [], _ => by
      exact Finset.mem_singleton.mpr rfl
  | y :: ys, hpath => by
      obtain ⟨δ, hδ, hy⟩ := exists_neighborOffset_of_adj hpath.rel
      apply Finset.mem_biUnion.mpr
      refine ⟨δ, hδ, Finset.mem_image.mpr ⟨(x + δ) :: ys, ?_, ?_⟩⟩
      · rw [← hy]
        exact mem_walksFrom_of_isPath y ys hpath.tail
      · rw [← hy]

/-- Every walk in the `n`-step enumeration has exactly `n + 1` vertices. -/
theorem length_eq_succ_of_mem_walksFrom {d : ℕ} (x : Site d) :
    ∀ {n : ℕ} {Γ : List (Site d)}, Γ ∈ walksFrom x n → Γ.length = n + 1
  | 0, Γ, hΓ => by
      rw [walksFrom, Finset.mem_singleton] at hΓ
      rw [hΓ]
      rfl
  | n + 1, Γ, hΓ => by
      rw [walksFrom] at hΓ
      obtain ⟨δ, _hδ, hΓ⟩ := Finset.mem_biUnion.mp hΓ
      obtain ⟨Δ, hΔ, hcons⟩ := Finset.mem_image.mp hΓ
      rw [← hcons, List.length_cons, length_eq_succ_of_mem_walksFrom (x + δ) hΔ]

/-- The number of `n`-step walks from a fixed site is at most `(3^d)^n`. -/
theorem card_walksFrom_le {d : ℕ} (x : Site d) :
    ∀ n, (walksFrom x n).card ≤ (3 ^ d) ^ n
  | 0 => by
      simp only [walksFrom, Finset.card_singleton, pow_zero]
      exact le_rfl
  | n + 1 => by
      calc
        (walksFrom x (n + 1)).card ≤
            ∑ δ ∈ neighborOffsets d,
              ((walksFrom (x + δ) n).image (List.cons x)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _δ ∈ neighborOffsets d, (3 ^ d) ^ n := by
          apply Finset.sum_le_sum
          intro δ _hδ
          exact Finset.card_image_le.trans (card_walksFrom_le (x + δ) n)
        _ = (neighborOffsets d).card * (3 ^ d) ^ n := by
          rw [Finset.sum_const_nat fun _ _ => rfl]
        _ = (3 ^ d) ^ (n + 1) := by
          rw [card_neighborOffsets, pow_succ, Nat.mul_comm]

/-- The finite set of lattice paths of vertex length `n` whose first vertex
lies in the centered scale-`k` cube. -/
def pathsOfLength (d k : ℕ) : ℕ → Finset (List (Site d))
  | 0 => ∅
  | n + 1 => (cubeSites d k).biUnion fun x => walksFrom x n

/-- Every crossing path occurs in the enumeration at its vertex length. -/
theorem IsPathFrom.mem_pathsOfLength {d k : ℕ} {Γ : List (Site d)}
    (hΓ : IsPathFrom k Γ) :
    Γ ∈ pathsOfLength d k Γ.length := by
  cases Γ with
  | nil => exact False.elim hΓ
  | cons x xs =>
      obtain ⟨hpath, hx, _hy⟩ := hΓ
      apply Finset.mem_biUnion.mpr
      exact ⟨x, mem_cubeSites_of_inCube hx, mem_walksFrom_of_isPath x xs hpath⟩

/-- Every path-list in the length-`n` enumeration has exactly `n` vertices. -/
theorem length_eq_of_mem_pathsOfLength {d k n : ℕ} {Γ : List (Site d)}
    (hΓ : Γ ∈ pathsOfLength d k n) : Γ.length = n := by
  cases n with
  | zero =>
      simp only [pathsOfLength, Finset.notMem_empty] at hΓ
  | succ n =>
      obtain ⟨x, _hx, hwalk⟩ := Finset.mem_biUnion.mp hΓ
      exact length_eq_succ_of_mem_walksFrom x hwalk

/-- Path-count bound for the dimension-only union bound. -/
theorem card_pathsOfLength_le (d k n : ℕ) :
    (pathsOfLength d k n).card ≤ 3 ^ (d * k) * (3 ^ d) ^ n := by
  cases n with
  | zero => simp only [pathsOfLength, Finset.card_empty, Nat.zero_le]
  | succ n =>
      calc
        (pathsOfLength d k (n + 1)).card ≤
            ∑ x ∈ cubeSites d k, (walksFrom x n).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ cubeSites d k, (3 ^ d) ^ n := by
          apply Finset.sum_le_sum
          intro x _hx
          exact card_walksFrom_le x n
        _ = 3 ^ (d * k) * (3 ^ d) ^ n := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), card_cubeSites]
        _ ≤ 3 ^ (d * k) * (3 ^ d) ^ (n + 1) := by
          rw [pow_succ]
          exact Nat.mul_le_mul_left _
            (Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) d))

end Algsuperdiff.Section5.Percolation
