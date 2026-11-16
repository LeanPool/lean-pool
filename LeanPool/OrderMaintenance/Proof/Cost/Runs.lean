/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct


/-!
# Runs as functions of the state

Under INV-S, the run of a group is determined by the element list and the elements' `grp`
fields: it is the sublist of the elements in that group. Likewise for the groups of a chunk.
So the cost invariants can be stated in terms of the element list `L` and the state alone, and
transported along the M2 lemmas, which keep `L` but give the new nesting only existentially.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The run of group `g`: the elements of `L` in `g`, in list order. -/
def runOf (s : Core) (L : List Nat) (g : Nat) : List Nat := L.filter fun e => eG s e = g

/-- The groups of chunk `c`, in list order. -/
def grpsOf (s : Core) (Ls : List Nat) (c : Nat) : List Nat := Ls.filter fun g => gC s g = c

theorem flatten_map_ite {L : List Nat} (hnd : L.Nodup) {g : Nat} (hg : g ∈ L) (X : List Nat) :
    (L.map fun b => if b = g then X else []).flatten = X := by
  induction L with
  | nil => simp at hg
  | cons a t ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.flatten_cons]
    by_cases ha : a = g
    · subst ha
      have : (t.map fun b => if b = a then X else []) = t.map fun _ => [] :=
        List.map_congr_left fun b hb => by rw [ite_eq_right (fun (e : b = a) => hnd.1 (e ▸ hb))]
      simp [this]
    · rw [ite_eq_right ha, ih hnd.2 (by simpa [Ne.symm ha] using hg)]; simp

theorem INV.elts_eq {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    A.elts g = runOf s A.elist g := by
  unfold runOf
  rw [INV.elist_flatten, List.filter_flatten, List.map_map]
  have : (A.glist.map ((List.filter fun e => decide (eG s e = g)) ∘ A.elts)) =
      A.glist.map fun b => if b = g then A.elts g else [] := by
    refine List.map_congr_left fun b hb => ?_
    simp only [Function.comp_apply]
    by_cases hbg : b = g
    · subst hbg
      rw [ite_eq_left rfl, List.filter_eq_self]
      intro e he; simp [h.grp b hb e he]
    · rw [ite_eq_right hbg, List.filter_eq_nil_iff]
      intro e he; simp [h.grp b hb e he, hbg]
  rw [this, flatten_map_ite h.gList.nodup hg]

theorem INV.grps_eq {s : Core} {A : Abs} (h : INV s A) {c : Nat} (hc : c ∈ A.chunks) :
    A.grps c = grpsOf s A.glist c := by
  unfold grpsOf
  rw [INV.glist_flatten, List.filter_flatten, List.map_map]
  have hnd : A.chunks.Nodup := h.cList.nodup
  have : (A.chunks.map ((List.filter fun g => decide (gC s g = c)) ∘ A.grps)) =
      A.chunks.map fun b => if b = c then A.grps c else [] := by
    refine List.map_congr_left fun b hb => ?_
    simp only [Function.comp_apply]
    by_cases hbc : b = c
    · subst hbc
      rw [ite_eq_left rfl, List.filter_eq_self]
      intro g hg; simp [h.chk b hb g hg]
    · rw [ite_eq_right hbc, List.filter_eq_nil_iff]
      intro g hg; simp [h.chk b hb g hg, hbc]
  rw [this, flatten_map_ite hnd hc]

/-- A group's run is empty iff its `first` is `NIL`. -/
theorem INV.first_nil_iff {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gF s g = NIL ↔ runOf s A.elist g = [] := by
  rw [← h.elts_eq hg, (h.gEnds g hg).1]
  constructor
  · intro e
    cases hr : A.elts g with
    | nil => rfl
    | cons a t =>
      rw [hr] at e; simp only [List.headD_cons] at e
      exact absurd (e ▸ A.elts_sub_elist hg (by rw [hr]; simp)) h.eList.nonil
  · intro e; rw [e]; rfl

/-- The groups of the list are the live (alive, allocated, non-`NIL`) groups. -/
theorem INV.mem_glist_iff {s : Core} {A : Abs} (h : INV s A) {g : Nat} :
    g ∈ A.glist ↔ g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true := by
  constructor
  · intro hg
    have h0 : g ≠ NIL := fun e => h.gList.nonil (e ▸ hg)
    have hs := h.gAlloc g hg
    exact ⟨h0, hs, (h.gAlive g (by unfold NIL at h0; omega) hs).mpr hg⟩
  · rintro ⟨h0, hs, ha⟩
    exact (h.gAlive g (by unfold NIL at h0; omega) hs).mp ha

/-- Elements of the list in a group of the list. -/
theorem mem_runOf {s : Core} {L : List Nat} {g e : Nat} :
    e ∈ runOf s L g ↔ e ∈ L ∧ eG s e = g := by
  simp [runOf]

/-- Every element of the list lies in a group of the list. -/
theorem INV.eG_mem {s : Core} {A : Abs} (h : INV s A) {e : Nat} (he : e ∈ A.elist) :
    eG s e ∈ A.glist := (h.mem_elist he).1

/-- The element list is the concatenation of the runs, in group-list order. -/
theorem INV.elist_runs {s : Core} {A : Abs} (h : INV s A) :
    A.elist = (A.glist.map (runOf s A.elist)).flatten := by
  conv_lhs => rw [INV.elist_flatten]
  congr 1
  exact List.map_congr_left fun g hg => h.elts_eq hg

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Lists -/

theorem filter_insertAfterL (p : Nat → Bool) (x y : Nat) (L : List Nat) (hxy : p x = p y) :
    (OrderMaintenance.Spec.insertAfterL x y L).filter p =
      if p x then OrderMaintenance.Spec.insertAfterL x y (L.filter p) else L.filter p := by
  induction L with
  | nil => simp [OrderMaintenance.Spec.insertAfterL]
  | cons a t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    by_cases hax : a = x
    · subst hax
      by_cases hp : p a = true
      · simp [hp, ← hxy, OrderMaintenance.Spec.insertAfterL]
      · simp [hp, ← hxy]
    · rw [ite_eq_right hax]
      by_cases hp : p a = true
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hp, ih]
        split <;> simp [OrderMaintenance.Spec.insertAfterL, hax]
      · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg hp, ih]

/-- `IsChain` survives inserting `y` right after `x`, for any relation. -/
theorem isChain_insert' {R : Nat → Nat → Prop} {l1 l2 : List Nat} {x y : Nat} {f f' : Nat → Nat}
    (hs : ((l1 ++ x :: l2).map f).IsChain R) (hagree : ∀ z ∈ l1 ++ x :: l2, f' z = f z)
    (hxy : R (f x) (f' y)) (hy2 : ∀ w ∈ l2.head?, R (f' y) (f w)) :
    ((l1 ++ x :: y :: l2).map f').IsChain R := by
  have e1 : l1.map f' = l1.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have e2 : l2.map f' = l2.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have ex : f' x = f x := hagree x (by simp)
  simp only [List.map_append, List.map_cons, e1, e2, ex] at hs ⊢
  rw [List.isChain_append] at hs ⊢
  refine ⟨hs.1, ?_, ?_⟩
  · rw [List.isChain_cons_cons]
    refine ⟨hxy, ?_⟩
    rw [List.isChain_cons]
    refine ⟨fun w hw => ?_, (List.isChain_cons.mp hs.2.1).2⟩
    cases l2 with
    | nil => simp at hw
    | cons a t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hw
      subst hw; exact hy2 a (by simp)
  · intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hs.2.2 a ha (f x) (by simp)

/-- In a chain of a reflexive-free gap relation, consecutive members are related. -/
theorem isChain_mid {R : Nat → Nat → Prop} {l1 l2 : List Nat} {x y : Nat} {f : Nat → Nat}
    (hs : ((l1 ++ x :: y :: l2).map f).IsChain R) : R (f x) (f y) := by
  simp only [List.map_append, List.map_cons] at hs
  rw [List.isChain_append] at hs
  exact (List.isChain_cons_cons.mp hs.2.1).1

end OrderMaintenance.Proof
