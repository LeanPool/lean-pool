/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import Init

/-!
  Deduplication and monotone fixed-point iteration on finite lists.
  The iteration is a computable function. Its soundness proof (`fixpoint_sound`) is
  choice-free; its convergence proof (`fixpoint_closed`) depends on `Classical.choice`.
-/

@[expose] public section

namespace FormalLinguistics

/-- Deduplicate a finite universe by keeping the last occurrence of each element. -/
def dedupList [DecidableEq α] : List α → List α
  | [] => []
  | a :: t =>
    let r := dedupList t
    if a ∈ r then r else a :: r

theorem mem_dedupList [DecidableEq α] {x : α} {l : List α} :
    x ∈ dedupList l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupList]
  | cons a t ih =>
    simp only [dedupList]
    split
    · next h =>
      rw [ih]
      constructor
      · intro hx; exact List.mem_cons_of_mem a hx
      · intro hx
        rcases List.mem_cons.mp hx with rfl | ht
        · exact ih.mp h
        · exact ht
    · next h =>
      simp [ih]

theorem nodup_dedupList [DecidableEq α] (l : List α) : (dedupList l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [dedupList]
    split
    · exact ih
    · next h => exact List.nodup_cons.mpr ⟨h, ih⟩

/-- If `l1` has no duplicates and every element of `l1` lies in `l2`, then `l1.length ≤ l2.length`. -/
theorem nodup_length_le [DecidableEq α] {l1 l2 : List α}
    (hnd : l1.Nodup) (hsub : ∀ x, x ∈ l1 → x ∈ l2) : l1.length ≤ l2.length := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨ha_not, ht_nd⟩ := hnd
    have ha_in : a ∈ l2 := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x, x ∈ t → x ∈ l2.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => ha_not (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.mpr (hsub x (List.mem_cons_of_mem a hx))
    have hle := ih ht_nd hsub'
    have herase : (l2.erase a).length + 1 = l2.length := by
      rw [List.length_erase_of_mem ha_in]
      have hpos : 0 < l2.length := List.length_pos_of_mem ha_in
      omega
    simp
    omega

/-- Repeatedly apply a function `n` times. -/
def iterN (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterN f n (f x)

section Fixpoint

variable {α : Type}

/-- One step of monotone closure inside a fixed universe `U`. -/
def stepFilter (U : List α) (p : List α → α → Bool) (s : List α) : List α :=
  U.filter (p s)

theorem stepFilter_nodup {U : List α} (hU : U.Nodup) (p : List α → α → Bool) (s : List α) :
    (stepFilter U p s).Nodup :=
  hU.filter _

theorem stepFilter_subset_U {U : List α} (p : List α → α → Bool) (s : List α) :
    ∀ x, x ∈ stepFilter U p s → x ∈ U := by
  intro x hx
  exact (List.mem_filter.mp hx).1

theorem stepFilter_mono {U : List α} {p : List α → α → Bool}
    (hmono : ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, p s1 x = true → p s2 x = true)
    {s1 s2 : List α} (hsub : ∀ x, x ∈ s1 → x ∈ s2) :
    ∀ x, x ∈ stepFilter U p s1 → x ∈ stepFilter U p s2 := by
  intro x hx
  obtain ⟨hxU, hpx⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hxU, hmono s1 s2 hsub x hpx⟩

theorem stepFilter_infl {U : List α} {p : List α → α → Bool}
    (hinfl : ∀ s x, x ∈ s → x ∈ U → p s x = true)
    {s : List α} (hsU : ∀ x, x ∈ s → x ∈ U) :
    ∀ x, x ∈ s → x ∈ stepFilter U p s := by
  intro x hx
  exact List.mem_filter.mpr ⟨hsU x hx, hinfl s x hx (hsU x hx)⟩

theorem iterN_stepFilter_closed_of_closed {U : List α} {p : List α → α → Bool}
    (hmono : ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, p s1 x = true → p s2 x = true)
    (hinfl : ∀ s x, x ∈ s → x ∈ U → p s x = true)
    {s : List α} (hsU : ∀ x, x ∈ s → x ∈ U)
    (hclosed : ∀ x, x ∈ stepFilter U p s → x ∈ s) (k : Nat) :
    (∀ x, x ∈ iterN (stepFilter U p) k s ↔ x ∈ s) := by
  induction k generalizing s with
  | zero => intro x; rfl
  | succ k ih =>
    simp only [iterN]
    have hstep_sub : ∀ x, x ∈ stepFilter U p s → x ∈ s := hclosed
    have hs_sub : ∀ x, x ∈ s → x ∈ stepFilter U p s := stepFilter_infl hinfl hsU
    have hstep_closed : ∀ x, x ∈ stepFilter U p (stepFilter U p s) → x ∈ stepFilter U p s := by
      intro x hx
      exact hs_sub x (hstep_sub x (stepFilter_mono hmono hstep_sub x hx))
    have hstepU : ∀ x, x ∈ stepFilter U p s → x ∈ U := stepFilter_subset_U p s
    intro x
    rw [ih hstepU hstep_closed]
    exact ⟨hstep_sub x, hs_sub x⟩

/-- Constructive search for an element in `l1` not belonging to `l2`. -/
theorem list_subset_or_exists_not_mem [DecidableEq α] (l1 l2 : List α) :
    (∀ y, y ∈ l1 → y ∈ l2) ∨ (∃ y, y ∈ l1 ∧ y ∉ l2) := by
  induction l1 with
  | nil => left; intro _ h; simp at h
  | cons a t ih =>
    if ha : a ∈ l2 then
      rcases ih with hsub | ⟨y, hy1, hy2⟩
      · left
        intro y hy
        rcases List.mem_cons.mp hy with rfl | ht
        · exact ha
        · exact hsub y ht
      · right
        exact ⟨y, List.mem_cons_of_mem a hy1, hy2⟩
    else
      right
      exact ⟨a, List.mem_cons_self .., ha⟩

theorem iterN_stepFilter_fixpoint_aux [DecidableEq α] {U : List α} (hU : U.Nodup)
    {p : List α → α → Bool}
    (hmono : ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, p s1 x = true → p s2 x = true)
    (hinfl : ∀ s x, x ∈ s → x ∈ U → p s x = true) :
    ∀ k (s : List α), s.Nodup → (∀ x, x ∈ s → x ∈ U) → U.length ≤ s.length + k →
      ∀ x, x ∈ stepFilter U p (iterN (stepFilter U p) k s) → x ∈ iterN (stepFilter U p) k s := by
  intro k
  induction k with
  | zero =>
    intro s hsnd hsU hlen x hx
    simp only [iterN] at hx ⊢
    if hxin : x ∈ s then
      exact hxin
    else
      have hnd' : (x :: s).Nodup := List.nodup_cons.mpr ⟨hxin, hsnd⟩
      have hsub' : ∀ y, y ∈ x :: s → y ∈ U := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact stepFilter_subset_U p s y hx
        · exact hsU y hy'
      have hle := nodup_length_le hnd' hsub'
      simp at hle
      omega
  | succ k ih =>
    intro s hsnd hsU hlen
    rcases list_subset_or_exists_not_mem (stepFilter U p s) s with hclosed | ⟨y, hy_in, hy_not⟩
    · intro x hx
      have heq := iterN_stepFilter_closed_of_closed hmono hinfl hsU hclosed (k + 1)
      have hsub1 : ∀ y, y ∈ iterN (stepFilter U p) (k + 1) s → y ∈ s := fun y hy => (heq y).mp hy
      have hx_step_s : x ∈ stepFilter U p s := stepFilter_mono hmono hsub1 x hx
      exact (heq x).mpr (hclosed x hx_step_s)
    · simp only [iterN]
      have hnd_ys : (y :: s).Nodup := List.nodup_cons.mpr ⟨hy_not, hsnd⟩
      have hsub_ys : ∀ z, z ∈ y :: s → z ∈ stepFilter U p s := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hy_in
        · exact stepFilter_infl hinfl hsU z hz'
      have hle := nodup_length_le hnd_ys hsub_ys
      simp at hle
      exact ih (stepFilter U p s) (stepFilter_nodup hU p s) (stepFilter_subset_U p s) (by omega)

/-- Main finite-universe fixpoint theorem: starting from `[]`, after `U.length` steps,
    `iterN (stepFilter U p) U.length []` is a fixpoint of `stepFilter U p`. -/
theorem fixpoint_closed [DecidableEq α] {U : List α} (hU : U.Nodup) {p : List α → α → Bool}
    (hmono : ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, p s1 x = true → p s2 x = true)
    (hinfl : ∀ s x, x ∈ s → x ∈ U → p s x = true) :
    let fp := iterN (stepFilter U p) U.length []
    ∀ x, x ∈ U → p fp x = true → x ∈ fp := by
  intro fp x hxU hpx
  have hcl := iterN_stepFilter_fixpoint_aux hU hmono hinfl U.length []
    List.nodup_nil (fun _ h => by simp at h) (by simp)
  exact hcl x (List.mem_filter.mpr ⟨hxU, hpx⟩)

/-- Least-fixpoint soundness: any predicate `Q` closed under `p` holds on all elements of `fp`. -/
theorem fixpoint_sound {U : List α} {p : List α → α → Bool} {Q : α → Prop}
    (hQ : ∀ s, (∀ y, y ∈ s → Q y) → ∀ x, x ∈ U → p s x = true → Q x) :
    ∀ k (s : List α), (∀ y, y ∈ s → Q y) →
      ∀ x, x ∈ iterN (stepFilter U p) k s → Q x := by
  intro k
  induction k with
  | zero => intro s hs x hx; exact hs x hx
  | succ k ih =>
    intro s hs x hx
    apply ih (stepFilter U p s) _ x hx
    intro y hy
    obtain ⟨hyU, hpy⟩ := List.mem_filter.mp hy
    exact hQ s hs y hyU hpy

end Fixpoint
end FormalLinguistics
