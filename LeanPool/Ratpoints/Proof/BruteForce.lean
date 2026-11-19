/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Model.BruteForce
public import LeanPool.Ratpoints.Spec.Basic

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import LeanPool.Ratpoints.Mathlib.Data.Int.Sqrt
import LeanPool.Ratpoints.Mathlib.Data.List.Basic
import LeanPool.Ratpoints.Proof.Containers

/-!
# The brute-force reference finds exactly the points

`Ratpoints.bruteForce c H` lists every normalized point of height at most `H` on
`y ^ 2 = F(x, z)`, and nothing else, each once; comparator certifies this
(`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.mem_bruteForce_iff`: a triple lies in `Ratpoints.bruteForce c H` exactly when it is a
  normalized point of height at most `H`.
* `Ratpoints.nodup_bruteForce`: the list has no duplicates.
* `Ratpoints.toFinset_bruteForce`: its set of elements is `Ratpoints.points c H`.
* `Ratpoints.bruteForce_eq_append`, `Ratpoints.filter_bruteForce_eq_append`: the list is the
  points at infinity followed by those of the denominators `1, …, H`, and its points at infinity and
  those of the denominators `bLow, …, bHigh` are those of these candidates;
  `Ratpoints.filter_bruteForce_eq_self`: its points at infinity and those of the denominators
  `1, …, B` for `B ≥ H` are all its points.
* `Ratpoints.ite_pointsAbove_eq_filter`: the points of one candidate are those that the
  specification of the order lists, `(x, y, z)` before `(x, -y, z)`.

## Proof

The evaluation of the model, Horner's rule on the products `cₖ z^(d - k)` with one more factor `z`
for odd `d`, is `Ratpoints.binaryForm` (`Ratpoints.BruteForce.horner_scaledCoeffs_mul`); `v` is
the square of `y` exactly when the model's test of `⌊√v⌋` succeeds and `y = ±⌊√v⌋`
(`Ratpoints.BruteForce.mem_pointsAbove_iff`); and the candidates are the pairs that the
normalization allows. The triples of different candidates differ in `x` or in `z`, so the list has
no duplicates.
-/

@[expose] public section

namespace Ratpoints

namespace BruteForce

theorem degree_eq (c : List ℤ) : degree c = Ratpoints.degree c := rfl

theorem horner_eq_sum (w : List ℤ) (x : ℤ) :
    horner w x = ∑ k ∈ Finset.range w.length, w.getD k 0 * x ^ k := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [horner, List.foldr_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one] at ih ⊢
    rw [ih, Finset.mul_sum, add_comm]
    exact congrArg (· + a) (Finset.sum_congr rfl fun k _ ↦ by ring)

theorem horner_scaledCoeffs (c : List ℤ) (d : ℕ) (x z : ℤ) :
    horner (scaledCoeffs c d z) x =
      ∑ k ∈ Finset.range (d + 1), c.getD k 0 * z ^ (d - k) * x ^ k := by
  rw [horner_eq_sum, scaledCoeffs, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (Finset.mem_range.mp hk)]

theorem horner_scaledCoeffs_mul (c : List ℤ) (x z : ℤ) :
    horner (scaledCoeffs c (degree c) z) x * (if degree c % 2 = 1 then z else 1) =
      binaryForm c x z := by
  rw [horner_scaledCoeffs, binaryForm, Finset.sum_mul, degree_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ Ratpoints.degree c := Finset.mem_range_succ_iff.mp hk
  split_ifs with h
  · rw [h, show Ratpoints.degree c + 1 - k = Ratpoints.degree c - k + 1 by lia, pow_succ]
    ring
  · rw [show Ratpoints.degree c % 2 = 0 by lia, add_zero]
    ring

private theorem sq_eq_iff (b v : ℤ) :
    b ^ 2 = v ↔ Int.sqrt v * Int.sqrt v = v ∧ (b = Int.sqrt v ∨ b = -Int.sqrt v) := by
  constructor
  · rintro rfl
    rw [sq, Int.sqrt_eq]
    exact ⟨Int.natAbs_mul_self' b, Int.natAbs_eq b⟩
  · rintro ⟨h, rfl | rfl⟩ <;> simpa [sq] using h

theorem mem_pointsAbove_iff {x z v : ℤ} {p : ℤ × ℤ × ℤ} :
    p ∈ pointsAbove x z v ↔ p.1 = x ∧ p.2.2 = z ∧ p.2.1 ^ 2 = v := by
  obtain ⟨a, b, e⟩ := p
  rw [sq_eq_iff, Int.sqrt_mul_self_eq_iff]
  simp only [pointsAbove]
  split_ifs with h h0
  · simp only [List.mem_singleton, Prod.mk.injEq, Int.sqrt, h0]
    grind
  · simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, Int.sqrt, h]
    grind
  · simp [h]

theorem mem_pointsOfDen_iff {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ} {p : ℤ × ℤ × ℤ} :
    p ∈ pointsOfDen c d z xs ↔ p.1 ∈ xs ∧ p.2.2 = z ∧ Int.gcd p.1 z = 1 ∧
      p.2.1 ^ 2 = horner (scaledCoeffs c d z) p.1 * (if d % 2 = 1 then z else 1) := by
  simp only [pointsOfDen, List.mem_flatMap]
  constructor
  · intro ⟨x, hx, h⟩
    by_cases hg : Int.gcd x z = 1
    · simp only [hg, ↓reduceIte] at h
      obtain ⟨rfl, rfl, hy⟩ := mem_pointsAbove_iff.mp h
      exact ⟨hx, rfl, hg, hy⟩
    · simp [hg] at h
  · rintro ⟨hx, rfl, hg, hy⟩
    refine ⟨p.1, hx, ?_⟩
    simp only [hg, ↓reduceIte]
    exact mem_pointsAbove_iff.mpr ⟨rfl, rfl, hy⟩

theorem exists_sq_eq_of_pointsOfDen_ne_nil {c : List ℤ} {b : ℕ} {xs : List ℤ}
    (h : pointsOfDen c (degree c) b xs ≠ []) :
    ∃ a ∈ xs, ∃ y : ℤ, Int.gcd a b = 1 ∧ y ^ 2 = binaryForm c a b := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hx, -, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  exact ⟨q.1, hx, q.2.1, hg, hy.trans (horner_scaledCoeffs_mul c _ _)⟩

theorem pointsOfDen_filter_of_ne {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ} {keep : ℤ → Bool}
    (h : ∀ x ∈ xs, pointsOfDen c d z [x] ≠ [] → keep x) :
    pointsOfDen c d z (xs.filter keep) = pointsOfDen c d z xs :=
  List.flatMap_filter_of_ne (by simpa [pointsOfDen] using h)

theorem pointsOfDen_ne_nil_of_mem {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ} {x : ℤ} (hx : x ∈ xs)
    (h : pointsOfDen c d z [x] ≠ []) :
    pointsOfDen c d z xs ≠ [] := by
  simp only [pointsOfDen, ne_eq, List.flatMap_eq_nil_iff, not_forall] at h ⊢
  obtain ⟨y, hy, hne⟩ := h
  exact ⟨y, by simpa [List.mem_singleton.mp hy] using hx, hne⟩

theorem mem_numerators_iff {x : ℤ} {H : ℕ} : x ∈ numerators H ↔ |x| ≤ H := by
  simp only [numerators, List.mem_map, List.mem_range, abs_le]
  exact ⟨fun ⟨i, hi, h⟩ ↦ by lia, fun h ↦ ⟨(x + H).toNat, by lia, by lia⟩⟩

theorem nodup_pointsAbove (x z v : ℤ) : (pointsAbove x z v).Nodup := by
  simp only [pointsAbove]
  split_ifs with h h0
  · simp
  · simp only [List.nodup_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    lia
  · simp

/-- The test of `Ratpoints.BruteForce.pointsAbove` is that `⌊√v⌋ ^ 2 = v`, with `Int.sqrt`. -/
theorem pointsAbove_eq_ite (x z v : ℤ) :
    pointsAbove x z v = if Int.sqrt v ^ 2 = v then
      (if Int.sqrt v = 0 then [(x, 0, z)] else [(x, Int.sqrt v, z), (x, -Int.sqrt v, z)])
    else [] := by
  simp only [pointsAbove, sq, ← Int.sqrt_mul_self_eq_iff, Int.sqrt, Int.natCast_eq_zero]

theorem nodup_numerators (H : ℕ) : (numerators H).Nodup :=
  List.nodup_range.map fun _ _ h ↦ by lia

theorem nodup_pointsOfDen (c : List ℤ) (d : ℕ) (z : ℤ) {xs : List ℤ} (hxs : xs.Nodup) :
    (pointsOfDen c d z xs).Nodup := by
  rw [pointsOfDen, List.nodup_flatMap]
  refine ⟨fun x _ ↦ ?_, hxs.pairwise_of_forall_ne fun a _ b _ hab p ha hb ↦ hab ?_⟩
  · by_cases hg : Int.gcd x z = 1 <;> simp only [hg, ↓reduceIte]
    exacts [nodup_pointsAbove .., List.nodup_nil]
  · have key (x : ℤ) (h : p ∈ if Int.gcd x z = 1 then
        pointsAbove x z (horner (scaledCoeffs c d z) x * if d % 2 = 1 then z else 1) else []) :
        p.1 = x := by
      by_cases hg : Int.gcd x z = 1 <;> simp only [hg, ↓reduceIte] at h
      exacts [(mem_pointsAbove_iff.mp h).1, absurd h List.not_mem_nil]
    rw [← key a ha, ← key b hb]

end BruteForce

open BruteForce in
/-- The brute-force reference lists exactly the normalized points of height at most `H`, for every
coefficient list and every height; comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_bruteForce_iff {c : List ℤ} {H : ℕ} {p : ℤ × ℤ × ℤ} :
    p ∈ bruteForce c H ↔ IsPoint c H p := by
  obtain ⟨x, y, z⟩ := p
  simp only [bruteForce, List.mem_append, List.mem_ite_nil_right, List.mem_flatMap,
    List.mem_range, mem_pointsOfDen_iff, horner_scaledCoeffs_mul, mem_numerators_iff,
    List.mem_singleton, IsPoint, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro (⟨hH, rfl, rfl, -, hy⟩ | ⟨j, hj, hx, rfl, hg, hy⟩)
    · exact ⟨hy, rfl, .inr ⟨rfl, rfl⟩, by simpa using hH, by lia⟩
    · exact ⟨hy, hg, .inl (by lia), hx, by lia⟩
  · rintro ⟨hy, hg, hz | ⟨rfl, rfl⟩, hx, hzH⟩
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, z = j + 1 := ⟨(z - 1).toNat, by lia⟩
      exact .inr ⟨j, by lia, hx, rfl, hg, hy⟩
    · exact .inl ⟨by simpa using hx, rfl, rfl, by simp, hy⟩

open BruteForce in
/-- The brute-force reference lists each point once; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem nodup_bruteForce (c : List ℤ) (H : ℕ) : (bruteForce c H).Nodup := by
  have hz {z : ℤ} {xs : List ℤ} {p : ℤ × ℤ × ℤ} (h : p ∈ pointsOfDen c (degree c) z xs) :
      p.2.2 = z :=
    (mem_pointsOfDen_iff.mp h).2.1
  simp only [bruteForce]
  refine List.Nodup.append ?_ ?_ fun p h1 h2 ↦ ?_
  · split_ifs
    exacts [nodup_pointsOfDen _ _ _ (List.nodup_singleton 1), List.nodup_nil]
  · rw [List.nodup_flatMap]
    refine ⟨fun j _ ↦ nodup_pointsOfDen _ _ _ (nodup_numerators H),
      List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab p ha hb ↦ hab ?_⟩
    lia [(hz ha).symm.trans (hz hb)]
  · split_ifs at h1
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h2
      lia [(hz h1).symm.trans (hz hj)]
    · exact List.not_mem_nil h1

theorem toFinset_bruteForce (c : List ℤ) (H : ℕ) : (bruteForce c H).toFinset = points c H :=
  Finset.ext fun _ ↦ by simp [mem_bruteForce_iff]

open BruteForce in
/-- The reference with its points at infinity apart, for `H ≥ 1`. -/
theorem bruteForce_eq_append (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    bruteForce c H = pointsOfDen c (degree c) 0 [1] ++
      (List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H) := by
  simp [bruteForce, hH, List.range'_eq_map_range, Nat.add_comm, List.flatMap_map,
    BruteForce.degree_eq]

open BruteForce in
/-- The points of the reference with the denominators from `bLow ≥ 1` to `bHigh ≤ H`, and its points
at infinity, are those of these denominators, in increasing order. -/
theorem filter_bruteForce_eq_append (c : List ℤ) {H bLow bHigh : ℕ} (hH : 1 ≤ H) (hbLow : 1 ≤ bLow)
    (hbH : bHigh ≤ H) :
    (bruteForce c H).filter (fun p : ℤ × ℤ × ℤ ↦ p.2.2 = 0 ∨ bLow ≤ p.2.2 ∧ p.2.2 ≤ bHigh) =
      pointsOfDen c (degree c) 0 [1] ++ (List.range' bLow (bHigh + 1 - bLow)).flatMap
        fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H) := by
  rw [bruteForce_eq_append c hH, List.filter_append, List.filter_flatMap,
    ← List.filter_range'_le_and_le (a := 1) (n := H) hbLow (by lia), List.flatMap_filter]
  refine congr($(List.filter_eq_self.mpr fun q hq ↦ by simp [(mem_pointsOfDen_iff.mp hq).2.1]) ++
    $(List.flatMap_congr fun b hb ↦ ?_))
  have hb1 := (List.mem_range'_1.mp hb).1
  split_ifs with h
  · exact List.filter_eq_self.mpr fun q hq ↦ by simp_all [(mem_pointsOfDen_iff.mp hq).2.1]
  · exact List.filter_eq_nil_iff.mpr fun q hq ↦ by
      simp only [(mem_pointsOfDen_iff.mp hq).2.1]
      simp_all
      lia

/-- The points of height at most `H` with a denominator of at most `B ≥ H` are all of them. -/
theorem filter_bruteForce_eq_self (c : List ℤ) {H B : ℕ} (hB : H ≤ B) :
    (bruteForce c H).filter (fun p : ℤ × ℤ × ℤ ↦ p.2.2 = 0 ∨ 1 ≤ p.2.2 ∧ p.2.2 ≤ B) =
      bruteForce c H :=
  List.filter_eq_self.mpr fun p hp ↦ by
    simp only [decide_eq_true_eq]
    lia [(mem_bruteForce_iff.mp hp).2.2]

/-! ### The points of one candidate, as the specification of the order lists them -/

/-- A triple whose `(x, z)` is normalized and of height at most `H` is a point exactly when
`y ^ 2 = F(x, z)` and `gcd(x, z) = 1`. -/
theorem isPoint_iff_of_le {c : List ℤ} {H : ℕ} {x y z : ℤ} (hn : 0 < z ∨ z = 0 ∧ x = 1)
    (hx : |x| ≤ H) (hz : z ≤ H) :
    IsPoint c H (x, y, z) ↔ y ^ 2 = binaryForm c x z ∧ Int.gcd x z = 1 := by
  simp [IsPoint, IsNormalizedPair, hn, hx, hz]

open BruteForce in
/-- The points of the brute-force reference over the candidate `(x, z)`, normalized and of height
at most `H`, are those of the specification of the order (`Ratpoints.pointsWithDen`): `(x, y, z)`
and then `(x, -y, z)` for `y = ⌊√F(x, z)⌋`, as far as they are points, one when `y = 0`. -/
theorem ite_pointsAbove_eq_filter {c : List ℤ} {H : ℕ} {x z : ℤ} (hn : 0 < z ∨ z = 0 ∧ x = 1)
    (hx : |x| ≤ H) (hz : z ≤ H) :
    (if Int.gcd x z = 1 then pointsAbove x z (binaryForm c x z) else []) =
      (if Int.sqrt (binaryForm c x z) = 0 then [(x, 0, z)] else
        [(x, Int.sqrt (binaryForm c x z), z), (x, -Int.sqrt (binaryForm c x z), z)]).filter
          (IsPoint c H) := by
  rw [List.filter_eq_ite_of_forall (P := Int.sqrt (binaryForm c x z) ^ 2 = binaryForm c x z ∧
    Int.gcd x z = 1) fun q hq ↦ ?_, pointsAbove_eq_ite]
  · split_ifs <;> first | rfl | (exfalso; tauto)
  · rw [decide_eq_true_iff]
    split_ifs at hq with h0 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> simp [isPoint_iff_of_le hn hx hz, h0]

end Ratpoints

end
