/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Frame
public import LeanPool.OrderMaintenance.Proof.Correct.Wrapper


/-!
# M5: list facts

* filters whose predicate changes at one element (`filter_erase_of`, `filter_snoc_of`,
  `filter_cons_of`): how a range changes when one chunk moves;
* a convex filter is an infix (`filter_infix_of_convex`): ranges are blocks of the chunk list;
* neighbours in an infix triple `[a, b, c]` (`Infix3.*`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem Array.size_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = if i < a.size then a.size else i + 1 :=
  OrderMaintenance.Proof.Array.size_setX a i v

/-- Two sublists of a list of distinct elements: inclusion is a sublist. -/
theorem sublist_of_subset_common : ∀ {A B L : List Nat}, A.Sublist L → B.Sublist L → L.Nodup → A
  ⊆ B →
    A.Sublist B
  | A, B, [], hA, hB, _, _ => by rw [List.sublist_nil.mp hA]; exact List.nil_sublist _
  | A, B, x :: L, hA, hB, hL, hsub => by
    have hx := List.nodup_cons.mp hL
    rcases List.sublist_cons_iff.mp hA with hA' | ⟨A', rfl, hA'⟩ <;>
      rcases List.sublist_cons_iff.mp hB with hB' | ⟨B', rfl, hB'⟩
    · exact sublist_of_subset_common hA' hB' hx.2 hsub
    · have hxA : x ∉ A := fun h => hx.1 (hA'.subset h)
      have : A ⊆ B' := fun a ha => by
        have := hsub ha; simp only [List.mem_cons] at this
        rcases this with e | e
        · subst e; exact absurd ha hxA
        · exact e
      exact (sublist_of_subset_common hA' hB' hx.2 this).cons x
    · exact absurd (hB'.subset (hsub (by simp))) hx.1
    · have hxA : x ∉ A' := fun h => hx.1 (hA'.subset h)
      have : A' ⊆ B' := fun a ha => by
        have := hsub (List.mem_cons_of_mem _ ha); simp only [List.mem_cons] at this
        rcases this with e | e
        · subst e; exact absurd ha hxA
        · exact e
      exact (sublist_of_subset_common hA' hB' hx.2 this).cons_cons x

/-! ### Filters changed at one element -/

theorem filter_erase_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = false) :
    l.filter p' = (l.filter p).erase c := by
  induction l with
  | nil => simp only [List.filter_nil, List.erase_nil]
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    have ih' := ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc)
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc]
      simp only [Bool.false_eq_true, ite_false, ih']
      by_cases hpx : p x = true
      · rw [List.filter_cons, ite_eq_left hpx, List.erase_cons_head]
        exact List.erase_of_not_mem (fun h => hx.1 (List.mem_of_mem_filter h))
      · rw [List.filter_cons, ite_eq_right hpx]
    · rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, ih']
      split
      · rw [List.erase_cons_tail (by simpa using hxc)]
      · rfl

theorem filter_snoc_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = true) (hpc : p c = false) (hcl : c ∈ l)
    (hbefore : ∀ x ∈ l, p x = true → x ≠ c → Before l x c) :
    l.filter p' = l.filter p ++ [c] := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hcl
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc, ite_eq_left rfl]
      have h1 : t.filter p' = t.filter p := by
        apply List.filter_congr; intro y hy
        exact hpp y (List.mem_cons_of_mem _ hy) (fun e => hx.1 (e ▸ hy))
      have h2 : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy hpy
        have hb := hbefore y (List.mem_cons_of_mem _ hy) hpy (fun e => hx.1 (e ▸ hy))
        rw [before_cons] at hb
        rcases hb with hb | ⟨rfl, -⟩
        · exact hx.1 hb.mem_right
        · exact hx.1 hy
      rw [h1, h2, List.filter_cons, hpc]
      simp only [Bool.false_eq_true, ite_false, h2, List.nil_append]
    · have hct : c ∈ t := by
        rcases List.mem_cons.mp hcl with h | h
        · exact absurd h.symm hxc
        · exact h
      have ih' := ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc) hct (by
        intro y hy hpy hyc
        have hb := hbefore y (List.mem_cons_of_mem _ hy) hpy hyc
        rw [before_cons] at hb
        rcases hb with hb | ⟨rfl, -⟩
        · exact hb
        · exact absurd hy hx.1)
      rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, ih']
      split <;> simp only [List.cons_append]

theorem filter_cons_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = true) (hpc : p c = false) (hcl : c ∈ l)
    (hafter : ∀ x ∈ l, p x = true → x ≠ c → Before l c x) :
    l.filter p' = c :: l.filter p := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hcl
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc, ite_eq_left rfl]
      have h1 : t.filter p' = t.filter p := by
        apply List.filter_congr; intro y hy
        exact hpp y (List.mem_cons_of_mem _ hy) (fun e => hx.1 (e ▸ hy))
      rw [h1, List.filter_cons, hpc]; simp only [Bool.false_eq_true, ↓reduceIte]
    · have hct : c ∈ t := by
        rcases List.mem_cons.mp hcl with h | h
        · exact absurd h.symm hxc
        · exact h
      have hpx : p x = false := by
        by_contra hpx
        have hb := hafter x (by simp) (by simpa using hpx) hxc
        rw [before_cons] at hb
        rcases hb with hb | ⟨e, -⟩
        · exact hx.1 hb.mem_right
        · exact hxc e.symm
      rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, hpx]
      simp only [Bool.false_eq_true, ite_false]
      exact ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc) hct (by
        intro y hy hpy hyc
        have hb := hafter y (List.mem_cons_of_mem _ hy) hpy hyc
        rw [before_cons] at hb
        rcases hb with hb | ⟨e, -⟩
        · exact hb
        · exact absurd e.symm hxc)

/-! ### Convex filters -/

/-- A filter that is convex (closed under betweenness) is a block of the list. -/
theorem filter_infix_of_convex {l : List Nat} (hl : l.Nodup) {p : Nat → Bool}
    (hcv : ∀ a b d, p a = true → p d = true → Before l a b → Before l b d → p b = true) :
    l.filter p <:+: l := by
  induction l with
  | nil => simp only [List.filter_nil, List.infix_rfl]
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    have ih' := ih hx.2 (fun a b d ha hd hab hbd => hcv a b d ha hd (hab.cons x) (hbd.cons x))
    by_cases hpx : p x = true
    · rw [List.filter_cons, ite_eq_left hpx]
      -- the rest of the block is a prefix of `t`
      have hpre : t.filter p <+: t := by
        obtain ⟨u, w, e⟩ := ih'
        cases u with
        | nil => exact ⟨w, by simpa using e⟩
        | cons y u =>
          cases hf : t.filter p with
          | nil => exact List.nil_prefix
          | cons z r =>
            exfalso
            -- `y` lies between `x` and `z`, so it satisfies `p`, so it is in the filter before `z`
            have hzt : z ∈ t := List.mem_of_mem_filter (by rw [hf]; simp)
            have hpz : p z = true := (List.mem_filter.mp (by rw [hf]; simp)).2
            have hyz : Before t y z := by
              rw [← e, hf]
              have : y :: u ++ z :: r ++ w = [y] ++ (u ++ z :: r ++ w) := by
                simp only [List.cons_append, List.append_assoc, List.nil_append]
              rw [this]; exact before_append_mem (by simp) (by simp)
            have hpy : p y = true := hcv x y z hpx hpz (by
              rw [before_cons]; exact Or.inr ⟨rfl, hyz.mem_left⟩) (hyz.cons x)
            have hyf : y ∈ t.filter p := List.mem_filter.mpr ⟨hyz.mem_left, hpy⟩
            rw [hf] at hyf
            have hnd : (y :: u ++ z :: r ++ w).Nodup := by rw [← hf, e]; exact hx.2
            have : y ∉ z :: r := by
              intro hm
              have := List.nodup_append.mp (List.nodup_append.mp hnd).1
              exact this.2.2 y (by simp) y hm rfl
            exact this hyf
      exact (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩).isInfix
    · rw [List.filter_cons, ite_eq_right hpx]
      exact ih'.trans (List.suffix_cons x t).isInfix

/-! ### Ends of a list -/

theorem headD_mem {l : List Nat} (h : l ≠ []) (d : Nat) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      List.mem_cons, true_or]

theorem getLastD_mem {l : List Nat} (h : l ≠ []) (d : Nat) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  simp only [Option.getD_some, List.getLast_mem]

theorem before_headD {l : List Nat} {c d : Nat} (hc : c ∈ l) (hne : c ≠ l.headD d) :
    Before l (l.headD d) c := by
  cases l with
  | nil => simp only [List.not_mem_nil] at hc
  | cons a t =>
    simp only [List.headD_cons] at hne ⊢
    rw [before_cons]
    rcases List.mem_cons.mp hc with h | h
    · exact absurd h hne
    · exact Or.inr ⟨rfl, h⟩

theorem before_getLastD {l : List Nat} {c d : Nat} (hc : c ∈ l) (hne : c ≠ l.getLastD d) :
    Before l c (l.getLastD d) := by
  have hl : l ≠ [] := List.ne_nil_of_mem hc
  obtain ⟨u, a, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hl
  rw [List.concat_eq_append] at hc hne ⊢
  simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.getD_some] at hne ⊢
  rcases List.mem_append.mp hc with h | h
  · exact before_append_mem h (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; exact absurd h hne

/-- In a block `y :: z :: _` of a nodup list, `z` follows `y`. -/
theorem succOf_infix {l r : List Nat} {y z : Nat} (hl : l.Nodup) (h : y :: z :: r <:+: l) :
    succOf l y = z := by
  obtain ⟨u, w, rfl⟩ := h
  have : u ++ y :: z :: r ++ w = u ++ y :: (z :: (r ++ w)) := by
    simp only [List.append_assoc, List.cons_append]
  rw [this] at hl ⊢; rw [succOf_mid hl]; rfl

theorem predOf_infix {l r : List Nat} {y z : Nat} (hl : l.Nodup) (h : r ++ [z, y] <:+: l) :
    predOf l y = z := by
  obtain ⟨u, w, rfl⟩ := h
  have : u ++ (r ++ [z, y]) ++ w = (u ++ r ++ [z]) ++ y :: w := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [this] at hl ⊢; rw [predOf_mid hl]; simp only [List.append_assoc, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.getD_some]

theorem headD_append_cons (L R : List Nat) (a d : Nat) :
    (L ++ a :: R).headD d = if L = [] then a else L.headD d := by
  cases L <;> simp only [List.nil_append, List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some, ↓reduceIte, List.cons_append, reduceCtorEq]

theorem getLastD_append_cons (L R : List Nat) (a d : Nat) :
    (L ++ a :: R).getLastD d = if R = [] then a else R.getLastD d := by
  by_cases hR : R = []
  · subst hR; simp only [List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.getD_some, ↓reduceIte]
  · rw [ite_eq_right hR, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
      List.getLast?_eq_some_getLast hR]
    rw [List.getLast?_eq_some_getLast (by simp)]
    simp only [List.getLast_append_of_ne_nil _ (List.cons_ne_nil a R)]
    rw [List.getLast_cons hR]

theorem headD_ne_nil' {l : List Nat} (hnil : NIL ∉ l) (hl : l ≠ []) : l.headD NIL ≠ NIL :=
  fun e => hnil (e ▸ headD_mem hl NIL)

theorem getLastD_ne_nil' {l : List Nat} (hnil : NIL ∉ l) (hl : l ≠ []) : l.getLastD NIL ≠ NIL :=
  fun e => hnil (e ▸ getLastD_mem hl NIL)

/-! ### Erasing an element -/

theorem before_erase {l : List Nat} (hl : l.Nodup) {a b v : Nat} (ha : a ≠ v) (hb : b ≠ v) :
    Before (l.erase v) a b ↔ Before l a b := by
  constructor
  · intro h; exact h.mono (List.erase_sublist)
  · intro h
    have hm : ∀ x, x ≠ v → (x ∈ l.erase v ↔ x ∈ l) := fun x hx => List.mem_erase_of_ne hx
    exact before_of_sublist (List.erase_sublist) hl ((hm a ha).mpr h.mem_left)
      ((hm b hb).mpr h.mem_right) h

theorem sublist_erase_of_not_mem {l m : List Nat} {v : Nat} (h : l.Sublist m) (hv : v ∉ l) :
    l.Sublist (m.erase v) := by
  have := h.erase v
  rwa [List.erase_of_not_mem hv] at this

theorem infix_erase {l t : List Nat} {v : Nat} (hl : l.Nodup) (h : t <:+: l) (hv : v ∉ t) :
    t <:+: l.erase v := by
  obtain ⟨u, w, rfl⟩ := h
  by_cases hu : v ∈ u
  · rw [List.append_assoc, List.erase_append_left _ hu]
    exact ⟨u.erase v, w, by simp⟩
  · rw [List.append_assoc, List.erase_append_right _ hu, List.erase_append_right _ hv]
    exact ⟨u, w.erase v, by simp⟩

/-! ### Inserting around an element in a list and a superlist -/

theorem sublist_split_mid {A B P Q : List Nat} {x : Nat} (h : (A ++ x :: B).Sublist (P ++ x :: Q))
    (hP : x ∉ P) (hQ : x ∉ Q) : A.Sublist P ∧ B.Sublist Q := by
  induction P generalizing A with
  | nil =>
    simp only [List.nil_append] at h
    cases A with
    | nil =>
      simp only [List.nil_append] at h
      rw [List.cons_sublist_cons] at h
      exact ⟨List.Sublist.slnil, h⟩
    | cons a A' =>
      exfalso
      simp only [List.cons_append] at h
      rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
      · exact hQ (h'.subset (by simp))
      · simp only [List.cons.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact hQ (h'.subset (by simp))
  | cons p P' ih =>
    simp only [List.mem_cons, not_or] at hP
    simp only [List.cons_append] at h
    cases A with
    | nil =>
      simp only [List.nil_append] at h ⊢
      rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
      · exact ⟨List.nil_sublist _, (ih (A := []) (by simpa using h') hP.2).2⟩
      · simp only [List.cons.injEq] at hr; exact absurd hr.1 hP.1
    | cons a A' =>
      simp only [List.cons_append] at h
      rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
      · obtain ⟨h1, h2⟩ := ih (A := a :: A') (by simpa using h') hP.2
        exact ⟨h1.cons p, h2⟩
      · simp only [List.cons.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨h1, h2⟩ := ih h' hP.2
        exact ⟨h1.cons_cons a, h2⟩

theorem sublist_around {A B P Q : List Nat} {x y z : Nat} (h : (A ++ x :: B).Sublist (P ++ x :: Q))
    (hP : x ∉ P) (hQ : x ∉ Q) : (A ++ y :: x :: z :: B).Sublist (P ++ y :: x :: z :: Q) := by
  obtain ⟨h1, h2⟩ := sublist_split_mid h hP hQ
  exact h1.append ((h2.cons_cons z).cons_cons x |>.cons_cons y)

theorem before_dedup {L1 L2 : List Nat} {x a b : Nat} (h : Before (L1 ++ x :: x :: L2) a b)
    (hab : a ≠ b) : Before (L1 ++ x :: L2) a b := by
  unfold Before at *
  induction L1 with
  | nil =>
    simp only [List.nil_append] at h ⊢
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
    · exact h'
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      apply List.Sublist.cons_cons
      rw [List.singleton_sublist] at h' ⊢
      simp only [List.mem_cons] at h'
      rcases h' with e | e
      · exact absurd e.symm hab
      · exact e
  | cons l L1' ih =>
    simp only [List.cons_append] at h ⊢
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
    · exact (ih h').cons l
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      apply List.Sublist.cons_cons
      rw [List.singleton_sublist] at h' ⊢
      simp only [List.mem_append, List.mem_cons] at h' ⊢
      tauto

/-- Collapsing `y` and `z` onto `x` maps the order `A, y, x, z, B` onto `A, x, B`. -/
theorem before_proj {A B : List Nat} {x y z c d : Nat} (hyA : y ∉ A) (hzA : z ∉ A) (hyB : y ∉ B)
    (hzB : z ∉ B) (h : Before (A ++ y :: x :: z :: B) c d) :
    let p := fun e => if e = y ∨ e = z then x else e
    p c = p d ∨ Before (A ++ x :: B) (p c) (p d) := by
  intro p
  by_cases e : p c = p d
  · exact Or.inl e
  right
  have hm : (A ++ y :: x :: z :: B).map p = A ++ x :: x :: x :: B := by
    have hA : A.map p = A := by
      conv_rhs => rw [← List.map_id A]
      apply List.map_congr_left
      intro a ha
      have : ¬(a = y ∨ a = z) := by rintro (rfl | rfl) <;> contradiction
      simp only [p, ite_eq_right this, id]
    have hB : B.map p = B := by
      conv_rhs => rw [← List.map_id B]
      apply List.map_congr_left
      intro a ha
      have : ¬(a = y ∨ a = z) := by rintro (rfl | rfl) <;> contradiction
      simp only [p, ite_eq_right this, id]
    have hx : p x = x := by simp only [p]; split <;> rfl
    simp only [List.map_append, List.map_cons, hA, hB, hx, p, true_or, or_true, ite_true]
  have h1 : Before (A ++ x :: x :: x :: B) (p c) (p d) := by
    rw [← hm]; exact h.map p
  exact before_dedup (before_dedup h1 e) e

/-- Order in `A, x, B` lifts to `A, y, x, z, B` through the collapse of `y`, `z` onto `x`. -/
theorem before_lift {A B : List Nat} {x y z c d : Nat} (hnd : (A ++ y :: x :: z :: B).Nodup)
    (hc : c ∈ A ++ y :: x :: z :: B) (hd : d ∈ A ++ y :: x :: z :: B)
    (hne : (if c = y ∨ c = z then x else c) ≠ (if d = y ∨ d = z then x else d))
    (h : Before (A ++ x :: B) (if c = y ∨ c = z then x else c) (if d = y ∨ d = z then x else d)) :
    Before (A ++ y :: x :: z :: B) c d := by
  have hnd' := List.nodup_append.mp hnd
  have hyA : y ∉ A := fun hy => hnd'.2.2 y hy y (by simp) rfl
  have hzA : z ∉ A := fun hz => hnd'.2.2 z hz z (by simp) rfl
  have h2 := hnd'.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at h2
  have hyB : y ∉ B := h2.1.2.2
  have hzB : z ∉ B := h2.2.2.1
  have hcd : c ≠ d := fun e => hne (by rw [e])
  rcases before_total hc hd hcd with h' | h'
  · exact h'
  · exfalso
    have hsmall : (A ++ x :: B).Nodup :=
      hnd.sublist ((List.Sublist.refl A).append ((((List.Sublist.refl B).cons z).cons_cons
        x).cons y))
    rcases before_proj hyA hzA hyB hzB h' with e | e <;> simp only at e
    · exact hne e.symm
    · exact h.asymm hsmall e

/-! ### Replacing one element -/

theorem mem_replace1_of_ne {l ys : List Nat} {x y : Nat} (hx : x ∈ l) (hxy : x ≠ y) : x ∈
  l.replace1 y ys := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hx
  | cons a t ih =>
    simp only [List.replace1]
    split
    · next hay =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd hay hxy
      · exact List.mem_append_right _ hx
    · simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (ih hx)

theorem mem_replace1_new {l ys : List Nat} {y z : Nat} (hy : y ∈ l) (hz : z ∈ ys) : z ∈
  l.replace1 y ys := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hy
  | cons a t ih =>
    simp only [List.replace1]
    split
    · exact List.mem_append_left _ hz
    · next hay =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd rfl hay
      · exact List.mem_cons_of_mem _ (ih hy)

theorem mem_replace1 {l ys : List Nat} {y z : Nat} (hz : z ∈ l.replace1 y ys) : z ∈ l ∨ z ∈ ys := by
  induction l with
  | nil => simp only [List.replace1, List.not_mem_nil] at hz
  | cons a t ih =>
    simp only [List.replace1] at hz
    split at hz
    · simp only [List.mem_append] at hz
      rcases hz with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

theorem infix_replace1 {T l ys : List Nat} {y : Nat} (h : T <:+: l) (hy : y ∉ T) : T <:+:
  l.replace1 y ys := by
  obtain ⟨u, w, rfl⟩ := h
  rw [replace1_append]
  by_cases hu : y ∈ u
  · rw [ite_eq_left (List.mem_append_left _ hu), replace1_append, ite_eq_left hu]
    exact ⟨u.replace1 y ys, w, by simp⟩
  · rw [ite_eq_right (fun h => by
      rcases List.mem_append.mp h with h | h
      · exact hu h
      · exact hy h)]
    exact ⟨u, w.replace1 y ys, by simp⟩

theorem infix_take {l : List Nat} (hl : l.Nodup) {a b k : Nat} (h : [a, b] <:+: l) (hb : b ∈
  l.take k) :
    [a, b] <:+: l.take k := by
  obtain ⟨u, w, rfl⟩ := h
  have hnd : (u ++ a :: b :: w).Nodup := by simpa using hl
  have h1 := List.nodup_append.mp hnd
  have hbu : b ∉ u := fun hh => h1.2.2 b hh b (by simp) rfl
  have hba : b ≠ a := fun e => by subst e; simp only [List.nodup_cons, List.mem_cons, true_or,
      not_true_eq_false, false_and, or_self_left,
      ne_eq, forall_eq_or_imp, and_false] at h1
  have hk : u.length + 2 ≤ k := by
    by_contra hk
    have e : (u ++ [a, b] ++ w).take k = (u ++ [a]).take k := by
      rw [show u ++ [a, b] ++ w = (u ++ [a]) ++ (b :: w) by simp,
        List.take_append_of_le_length (by
          simp only [List.length_append, List.length_cons, List.length_nil, zero_add]; omega)]
    rw [e] at hb
    have := List.mem_of_mem_take hb
    simp only [List.mem_append, List.mem_singleton] at this
    rcases this with hh | hh
    · exact hbu hh
    · exact hba hh
  rw [List.take_append, List.take_of_length_le (by
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd];
      omega)]
  exact ⟨u, _, rfl⟩

theorem infix_drop {l : List Nat} (hl : l.Nodup) {a b k : Nat} (h : [a, b] <:+: l) (ha : a ∈
  l.drop k) :
    [a, b] <:+: l.drop k := by
  obtain ⟨u, w, rfl⟩ := h
  have hnd : (u ++ a :: b :: w).Nodup := by simpa using hl
  have h1 := List.nodup_append.mp hnd
  have h2 := List.nodup_cons.mp h1.2.1
  have hk : k ≤ u.length := by
    by_contra hk
    have e : (u ++ [a, b] ++ w).drop k = (b :: w).drop (k - (u.length + 1)) := by
      rw [show u ++ [a, b] ++ w = (u ++ [a]) ++ (b :: w) by simp, List.drop_append,
        List.drop_eq_nil_of_le (by
          simp only [List.length_append, List.length_cons, List.length_nil, zero_add]; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
          List.nil_append]
    rw [e] at ha
    exact h2.1 (List.mem_of_mem_drop ha)
  rw [show u ++ [a, b] ++ w = u ++ ([a, b] ++ w) by simp, List.drop_append_of_le_length hk]
  exact ⟨u.drop k, w, by simp⟩

/-! ### Infix triples -/

theorem before_of_infix2 {l : List Nat} {a b : Nat} (h : [a, b] <:+: l) : Before l a b :=
  h.sublist

theorem infix3_left {l : List Nat} {a b c : Nat} (h : [a, b, c] <:+: l) : [a, b] <:+: l :=
  (show [a, b] <:+: [a, b, c] from ⟨[], [c], rfl⟩).trans h

theorem infix3_right {l : List Nat} {a b c : Nat} (h : [a, b, c] <:+: l) : [b, c] <:+: l :=
  (show [b, c] <:+: [a, b, c] from ⟨[a], [], rfl⟩).trans h

/-- What precedes `b` in a nodup list, with `a` right before `b`, is `a` or precedes `a`. -/
theorem before_pred {l : List Nat} (hl : l.Nodup) {a b x : Nat} (h : [a, b] <:+: l)
    (hx : Before l x b) : x = a ∨ Before l x a := by
  obtain ⟨u, w, rfl⟩ := h
  have e : u ++ [a, b] ++ w = (u ++ [a]) ++ b :: w := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e] at hx hl
  have hxm := mem_of_before_split hl hx
  rcases List.mem_append.mp hxm with h1 | h1
  · right
    rw [e]
    have : (u ++ [a]) ++ b :: w = u ++ a :: (b :: w) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [this]; exact before_split h1
  · left; simpa using h1

/-- What follows `b` in a nodup list, with `c` right after `b`, is `c` or follows `c`. -/
theorem before_succ {l : List Nat} (hl : l.Nodup) {b c x : Nat} (h : [b, c] <:+: l)
    (hx : Before l b x) : x = c ∨ Before l c x := by
  obtain ⟨u, w, rfl⟩ := h
  have hm := hx.mem_right
  rcases List.mem_append.mp hm with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exfalso
      -- `x ∈ u` comes before `b`
      have hxb : Before (u ++ [b, c] ++ w) x b := by
        have : u ++ [b, c] ++ w = u ++ b :: (c :: w) := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [this]; exact before_split h2
      exact hx.asymm hl hxb
    · simp only [List.mem_cons,  List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl
      · exact absurd rfl (hx.ne hl)
      · left; rfl
  · right
    have : u ++ [b, c] ++ w = (u ++ [b]) ++ c :: w := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [this]
    have : (u ++ [b]) ++ c :: w = (u ++ [b] ++ [c]) ++ w := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [this]
    exact before_append_mem (by simp) h1

end OrderMaintenance.Proof.Top
