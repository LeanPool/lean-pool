/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Destutter
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Lattice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Lattice paths for the percolation estimate

This file defines the integer lattice with the sup distance, nearest-neighbor
paths, centered triadic lattice cubes, and paths crossing consecutive cubes.
The main geometric results are the lower bound on the number of vertices in a
crossing path and the passage from the source's notion of a path, whose steps
have sup distance at most one, to a path of strictly adjacent sites.
-/

namespace Algsuperdiff.Section5.Percolation

/-- The integer lattice in dimension `d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The integer-valued sup distance on lattice sites. -/
def siteDist {d : ℕ} (x y : Site d) : ℕ :=
  Finset.univ.sup fun i => (x i - y i).natAbs

/-- A coordinate difference is bounded by the sup distance. -/
theorem natAbs_sub_le_siteDist {d : ℕ} (x y : Site d) (i : Fin d) :
    (x i - y i).natAbs ≤ siteDist x y := by
  exact Finset.le_sup (f := fun j : Fin d => (x j - y j).natAbs)
    (Finset.mem_univ i)

/-- The lattice sup distance vanishes on the diagonal. -/
@[simp] theorem siteDist_self {d : ℕ} (x : Site d) : siteDist x x = 0 := by
  unfold siteDist
  simp only [sub_self, Int.natAbs_zero]
  exact Nat.eq_zero_of_le_zero Finset.sup_const_le

/-- The lattice sup distance vanishes only on the diagonal. -/
theorem siteDist_eq_zero_iff {d : ℕ} {x y : Site d} :
    siteDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := natAbs_sub_le_siteDist x y i
    rw [h] at hi
    omega
  · rintro rfl
    exact siteDist_self x

/-- The lattice sup distance is symmetric. -/
theorem siteDist_comm {d : ℕ} (x y : Site d) : siteDist x y = siteDist y x := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _hi
    have hneg : x i - y i = -(y i - x i) := by ring
    rw [hneg, Int.natAbs_neg]
    exact natAbs_sub_le_siteDist y x i
  · apply Finset.sup_le
    intro i _hi
    have hneg : y i - x i = -(x i - y i) := by ring
    rw [hneg, Int.natAbs_neg]
    exact natAbs_sub_le_siteDist x y i

/-- The lattice sup distance satisfies the triangle inequality. -/
theorem siteDist_triangle {d : ℕ} (x y z : Site d) :
    siteDist x z ≤ siteDist x y + siteDist y z := by
  apply Finset.sup_le
  intro i _hi
  calc
    (x i - z i).natAbs = ((x i - y i) + (y i - z i)).natAbs := by
      congr 1
      ring
    _ ≤ (x i - y i).natAbs + (y i - z i).natAbs := Int.natAbs_add_le _ _
    _ ≤ siteDist x y + siteDist y z :=
      Nat.add_le_add (natAbs_sub_le_siteDist x y i)
        (natAbs_sub_le_siteDist y z i)

/-- Two sites are adjacent when their sup distance is one.  The source allows
a step of sup distance at most one, hence allows a path to repeat a site; the
two readings describe the same events, because deleting the repetitions of a
source path changes neither its endpoints nor its vertex set; that deletion
is `exists_isPathFrom_of_isWeakPath`. -/
def Adj {d : ℕ} (x y : Site d) : Prop :=
  siteDist x y = 1

/-- A lattice path is a finite sequence of adjacent sites. -/
def IsPath {d : ℕ} (Γ : List (Site d)) : Prop :=
  Γ.IsChain Adj

/-- Membership in the centered open triadic cube of scale `k`. -/
def inCube {d : ℕ} (k : ℕ) (x : Site d) : Prop :=
  ∀ i, 2 * (x i).natAbs < 3 ^ k

/-- A path crossing from the scale-`k` cube to the complement of the
scale-`k+1` cube.  The pattern match makes nonemptiness explicit while
recording the source's head and last-vertex conditions. -/
def IsPathFrom {d : ℕ} (k : ℕ) : List (Site d) → Prop
  | [] => False
  | x :: xs => IsPath (x :: xs) ∧ inCube k x ∧
      ¬inCube (k + 1) ((x :: xs).getLast (List.cons_ne_nil x xs))

private theorem siteDist_first_getLast_lt_length {d : ℕ} (x : Site d) :
    ∀ (xs : List (Site d)), IsPath (x :: xs) →
      siteDist x ((x :: xs).getLast (List.cons_ne_nil x xs)) < (x :: xs).length
  | [], _ => by
      simp only [List.getLast_singleton, siteDist_self, List.length_singleton,
        Nat.zero_lt_one]
  | y :: ys, hpath => by
      have hxy : siteDist x y = 1 := hpath.rel
      have htail : IsPath (y :: ys) := hpath.tail
      have hlast := siteDist_first_getLast_lt_length y ys htail
      have htriangle := siteDist_triangle x y
        ((y :: ys).getLast (List.cons_ne_nil y ys))
      have hlastEq :
          (x :: y :: ys).getLast (List.cons_ne_nil x (y :: ys)) =
            (y :: ys).getLast (List.cons_ne_nil y ys) := by
        rfl
      rw [hlastEq]
      rw [hxy] at htriangle
      simp only [List.length_cons] at hlast ⊢
      omega

/-- Any path crossing two consecutive centered triadic cubes has at least
`3^k + 1` vertices. -/
theorem IsPathFrom.length_lower_bound {d : ℕ} {k : ℕ} {Γ : List (Site d)}
    (hΓ : IsPathFrom k Γ) :
    3 ^ k + 1 ≤ Γ.length := by
  cases Γ with
  | nil => exact False.elim hΓ
  | cons x xs =>
      obtain ⟨hpath, hx, hy⟩ := hΓ
      let y := (x :: xs).getLast (List.cons_ne_nil x xs)
      simp only [inCube] at hx hy
      push Not at hy
      obtain ⟨i, hyi⟩ := hy
      have hxi := hx i
      have hcoord : (y i - x i).natAbs ≤ siteDist y x :=
        natAbs_sub_le_siteDist y x i
      have habs : (y i).natAbs ≤ (y i - x i).natAbs + (x i).natAbs := by
        have h := Int.natAbs_add_le (y i - x i) (x i)
        have heq : y i - x i + x i = y i := by ring
        rwa [heq] at h
      have habs' : (y i).natAbs ≤ siteDist y x + (x i).natAbs :=
        habs.trans (Nat.add_le_add_right hcoord (x i).natAbs)
      have hdist : 3 ^ k + 1 ≤ siteDist x y := by
        dsimp only [y] at hyi hcoord habs habs' ⊢
        rw [siteDist_comm]
        rw [pow_succ] at hyi
        omega
      have hlength := siteDist_first_getLast_lt_length x xs hpath
      change siteDist x y < (x :: xs).length at hlength
      exact hdist.trans (Nat.le_of_lt hlength)

/-- The source's notion of a path: a finite sequence of sites whose consecutive
entries are at sup distance at most one, so that a site may be repeated. -/
def IsWeakPath {d : ℕ} (Γ : List (Site d)) : Prop :=
  Γ.IsChain fun x y => siteDist x y ≤ 1

private theorem head?_destutter' {d : ℕ} :
    ∀ (l : List (Site d)) (a : Site d),
      (l.destutter' (· ≠ ·) a).head? = some a
  | [], a => by rw [List.destutter'_nil]; rfl
  | b :: l, a => by
      by_cases hab : a ≠ b
      · rw [List.destutter'_cons_pos _ hab]; rfl
      · rw [List.destutter'_cons_neg _ hab]
        exact head?_destutter' l a

private theorem getLast?_cons_of_ne_nil {α : Type*} (a : α) {u : List α}
    (hu : u ≠ []) : (a :: u).getLast? = u.getLast? := by
  cases u with
  | nil => exact absurd rfl hu
  | cons c t => rw [List.getLast?_cons_cons]

private theorem getLast?_destutter' {d : ℕ} :
    ∀ (l : List (Site d)) (a : Site d),
      (l.destutter' (· ≠ ·) a).getLast? = (a :: l).getLast?
  | [], a => by rw [List.destutter'_nil]
  | b :: l, a => by
      by_cases hab : a ≠ b
      · rw [List.destutter'_cons_pos _ hab,
          getLast?_cons_of_ne_nil a (List.destutter'_ne_nil l _)]
        exact getLast?_destutter' l b
      · have hab' : a = b := not_not.mp hab
        rw [List.destutter'_cons_neg _ hab, getLast?_destutter' l a,
          List.getLast?_cons_cons, hab']

private theorem toFinset_destutter' {d : ℕ} :
    ∀ (l : List (Site d)) (a : Site d),
      (l.destutter' (· ≠ ·) a).toFinset = (a :: l).toFinset
  | [], a => by rw [List.destutter'_nil]
  | b :: l, a => by
      by_cases hab : a ≠ b
      · rw [List.destutter'_cons_pos _ hab, List.toFinset_cons, List.toFinset_cons,
          toFinset_destutter' l b, List.toFinset_cons]
      · have hab' : a = b := not_not.mp hab
        rw [List.destutter'_cons_neg _ hab, toFinset_destutter' l a,
          List.toFinset_cons, List.toFinset_cons, List.toFinset_cons, hab',
          Finset.insert_idem]

private theorem isPath_destutter' {d : ℕ} :
    ∀ (l : List (Site d)) (a : Site d),
      ((a :: l).IsChain fun x y => siteDist x y ≤ 1) →
        IsPath (l.destutter' (· ≠ ·) a)
  | [], a, _ => by
      rw [List.destutter'_nil]
      exact List.isChain_singleton a
  | b :: l, a, h => by
      by_cases hab : a ≠ b
      · rw [List.destutter'_cons_pos _ hab]
        refine List.IsChain.cons (isPath_destutter' l b h.tail) ?_
        intro y hy
        rw [head?_destutter' l b, Option.mem_some_iff] at hy
        have hle : siteDist a b ≤ 1 := h.rel
        have hne : siteDist a b ≠ 0 := fun h0 => hab (siteDist_eq_zero_iff.mp h0)
        have : Adj a b := by
          unfold Adj
          omega
        rw [← hy]
        exact this
      · have hab' : a = b := not_not.mp hab
        rw [List.destutter'_cons_neg _ hab]
        refine isPath_destutter' l a ?_
        rw [hab']
        exact h.tail

theorem exists_isPath_of_isWeakPath {d : ℕ} (Γ : List (Site d))
    (hΓ : IsWeakPath Γ) :
    ∃ Δ : List (Site d), IsPath Δ ∧ Δ.head? = Γ.head? ∧
      Δ.getLast? = Γ.getLast? ∧ Δ.toFinset = Γ.toFinset := by
  cases Γ with
  | nil => exact ⟨[], List.isChain_nil, rfl, rfl, rfl⟩
  | cons x xs =>
      exact ⟨xs.destutter' (· ≠ ·) x, isPath_destutter' xs x hΓ,
        head?_destutter' xs x, getLast?_destutter' xs x,
        toFinset_destutter' xs x⟩

theorem exists_isPathFrom_of_isWeakPath {d k : ℕ} {x y : Site d}
    {Γ : List (Site d)} (hΓ : IsWeakPath Γ)
    (hhead : Γ.head? = some x) (hlast : Γ.getLast? = some y)
    (hx : inCube k x) (hy : ¬ inCube (k + 1) y) :
    ∃ Δ : List (Site d), IsPathFrom k Δ ∧ Δ.toFinset = Γ.toFinset := by
  obtain ⟨Δ, hpath, hΔhead, hΔlast, hΔfinset⟩ := exists_isPath_of_isWeakPath Γ hΓ
  refine ⟨Δ, ?_, hΔfinset⟩
  cases Δ with
  | nil =>
      rw [hhead] at hΔhead
      exact absurd hΔhead (by simp)
  | cons z zs =>
      have hz : z = x := by
        rw [hhead, List.head?_cons, Option.some_inj] at hΔhead
        exact hΔhead
      have hlastEq : (z :: zs).getLast (List.cons_ne_nil z zs) = y := by
        have := List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil z zs)
        rw [this, hlast, Option.some_inj] at hΔlast
        exact hΔlast
      refine ⟨hpath, ?_, ?_⟩
      · rw [hz]; exact hx
      · rw [hlastEq]; exact hy

end Algsuperdiff.Section5.Percolation
