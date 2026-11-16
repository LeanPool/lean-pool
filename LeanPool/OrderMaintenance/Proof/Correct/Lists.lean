/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Inv


/-!
# Linked lists as `succOf` / `predOf`

Lemmas for reading and updating the doubly linked lists of INV-S: successors and predecessors
in appended and flattened lists, and sortedness under a change at one position.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem headD_reverse (l : List Nat) (d : Nat) : l.reverse.headD d = l.getLastD d := by
  rcases l.eq_nil_or_concat with rfl | ⟨l', a, rfl⟩ <;> simp

/-! ### `succOf` -/

@[simp] theorem succOf_nil (x : Nat) : succOf [] x = NIL := rfl
@[simp] theorem succOf_single (a x : Nat) : succOf [a] x = NIL := rfl
theorem succOf_cons_cons (a b : Nat) (t : List Nat) (x : Nat) :
    succOf (a :: b :: t) x = if a = x then b else succOf (b :: t) x := rfl

theorem succOf_cons (a : Nat) (l : List Nat) (x : Nat) :
    succOf (a :: l) x = if a = x then l.headD NIL else succOf l x := by
  cases l with
  | nil => by_cases h : a = x <;> simp [h]
  | cons b t => rfl

theorem succOf_not_mem {l : List Nat} {x : Nat} (h : x ∉ l) : succOf l x = NIL := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [succOf_cons]
    simp only [List.mem_cons, not_or] at h
    rw [ite_eq_right (Ne.symm h.1), ih h.2]

/-- Successors in an append of disjoint lists. -/
theorem succOf_append {l1 l2 : List Nat} (hnd : l1.Nodup) (x : Nat) :
    succOf (l1 ++ l2) x =
      if x ∈ l1 then (if l1.getLast? = some x then l2.headD NIL else succOf l1 x)
      else succOf l2 x := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    rw [List.cons_append, succOf_cons, succOf_cons]
    simp only [List.nodup_cons] at hnd
    by_cases hax : a = x
    · subst hax
      simp only [List.mem_cons, true_or, ite_true]
      cases t with
      | nil => simp
      | cons b u =>
        have : (b :: u).getLast? ≠ some a := by
          intro h; exact hnd.1 (List.mem_of_getLast? h)
        simp [List.getLast?_cons_cons, this]
    · rw [ite_eq_right hax, ite_eq_right hax, ih hnd.2]
      simp only [List.mem_cons, Ne.symm hax, false_or]
      by_cases hxt : x ∈ t
      · simp only [hxt, ite_true]
        cases t with
        | nil => simp at hxt
        | cons b u => simp [List.getLast?_cons_cons]
      · simp [hxt]

theorem succOf_mem_or {l : List Nat} {x : Nat} : succOf l x ∈ l ∨ succOf l x = NIL := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [succOf_cons]
    split
    · cases t with
      | nil => simp
      | cons b u => simp
    · rcases ih with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

/-- In `l1 ++ x :: l2` with `x ∉ l1`, the successor of `x` is the head of `l2`. -/
theorem succOf_mid {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) :
    succOf (l1 ++ x :: l2) x = l2.headD NIL := by
  have h1 : l1.Nodup := (List.nodup_append.mp hnd).1
  have hx : x ∉ l1 := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  rw [succOf_append h1, ite_eq_right hx, succOf_cons, ite_eq_left rfl]

/-! ### `predOf` -/

theorem predOf_append {l1 l2 : List Nat} (hnd : l2.Nodup) (x : Nat) :
    predOf (l1 ++ l2) x =
      if x ∈ l2 then (if l2.head? = some x then l1.getLastD NIL else predOf l2 x)
      else predOf l1 x := by
  unfold predOf
  rw [List.reverse_append, succOf_append (List.nodup_reverse.mpr hnd)]
  simp only [List.mem_reverse, List.getLast?_reverse, headD_reverse]

theorem predOf_mid {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) :
    predOf (l1 ++ x :: l2) x = l1.getLastD NIL := by
  have h2 : (x :: l2).Nodup := (List.nodup_append.mp hnd).2.1
  rw [predOf_append h2]
  simp

theorem predOf_not_mem {l : List Nat} {x : Nat} (h : x ∉ l) : predOf l x = NIL :=
  succOf_not_mem (by simpa using h)

theorem predOf_mem_or {l : List Nat} {x : Nat} : predOf l x ∈ l ∨ predOf l x = NIL := by
  unfold predOf
  rcases succOf_mem_or (l := l.reverse) (x := x) with h | h
  · exact Or.inl (List.mem_reverse.mp h)
  · exact Or.inr h

/-! ### Blocks of a flattened list -/

/-- Inside a block, the successor in the flattened list is the successor in the block, unless
the element is the block's last. -/
theorem succOf_flatten {L : List (List Nat)} (hnd : L.flatten.Nodup) {b : List Nat} (hb : b ∈ L)
    {x : Nat} (hx : x ∈ b) (hlast : b.getLast? ≠ some x) :
    succOf L.flatten x = succOf b x := by
  obtain ⟨L1, L2, rfl⟩ := List.mem_iff_append.mp hb
  rw [List.flatten_append, List.flatten_cons] at hnd ⊢
  have hn1 := (List.nodup_append.mp hnd).1
  have hxL1 : x ∉ L1.flatten := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp [hx]) rfl
  have hn2 := (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
  rw [succOf_append hn1, ite_eq_right hxL1, succOf_append hn2, ite_eq_left hx, ite_eq_right hlast]

theorem predOf_flatten {L : List (List Nat)} (hnd : L.flatten.Nodup) {b : List Nat} (hb : b ∈ L)
    {x : Nat} (hx : x ∈ b) (hfirst : b.head? ≠ some x) :
    predOf L.flatten x = predOf b x := by
  unfold predOf
  rw [List.reverse_flatten]
  have hnd' : (L.map List.reverse).reverse.flatten.Nodup := by
    rw [← List.reverse_flatten]; exact List.nodup_reverse.mpr hnd
  exact succOf_flatten hnd' (List.mem_reverse.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩))
    (by simpa using hx)
    (by simpa [List.getLast?_reverse] using hfirst)

/-- If the successor of a block member lies in the same block, it is the successor in the
block. -/
theorem succOf_flatten_of_mem {L : List (List Nat)} (hnd : L.flatten.Nodup) (hnil : NIL ∉ L.flatten)
    {b : List Nat} (hb : b ∈ L) {x : Nat} (hx : x ∈ b) (hs : succOf L.flatten x ∈ b) :
    succOf L.flatten x = succOf b x := by
  by_cases hlast : b.getLast? = some x
  · exfalso
    obtain ⟨L1, L2, rfl⟩ := List.mem_iff_append.mp hb
    rw [List.flatten_append, List.flatten_cons] at hnd hnil hs
    have hn1 := (List.nodup_append.mp hnd).1
    have hxL1 : x ∉ L1.flatten :=
      fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp [hx]) rfl
    have h23 := (List.nodup_append.mp hnd).2.1
    rw [succOf_append hn1, ite_eq_right hxL1,
      succOf_append (List.nodup_append.mp h23).1, ite_eq_left hx,
      ite_eq_left hlast] at hs
    -- the head of the following blocks is not in `b`
    rcases hL2 : L2.flatten with _ | ⟨y, t⟩
    · rw [hL2] at hs; simp only [List.headD_nil] at hs
      exact hnil (List.mem_append_right _ (List.mem_append_left _ hs))
    · rw [hL2] at hs h23
      simp only [List.headD_cons] at hs
      exact (List.nodup_append.mp h23).2.2 y hs y (by simp) rfl
  · exact succOf_flatten hnd hb hx hlast

/-! ### Sortedness after changing one position -/

/-- Changing the value at one member of a sorted list keeps it sorted when the new value lies
strictly between the values at its neighbours. -/
theorem isChain_update {l : List Nat} (hnd : l.Nodup) {f f' : Nat → Nat}
    (hs : (l.map f).IsChain (· < ·))
    {x : Nat} (hx : x ∈ l) (hother : ∀ y ∈ l, y ≠ x → f' y = f y)
    (hpred : predOf l x ≠ NIL → f (predOf l x) < f' x)
    (hsucc : succOf l x ≠ NIL → f' x < f (succOf l x)) (hnil : NIL ∉ l) :
    (l.map f').IsChain (· < ·) := by
  obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.mp hx
  have hp := predOf_mid hnd
  have hsu := succOf_mid hnd
  have hx1 : x ∉ l1 := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hx2 : x ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have e1 : l1.map f' = l1.map f :=
    List.map_congr_left fun y hy => hother y (by simp [hy]) (fun h => hx1 (h ▸ hy))
  have e2 : l2.map f' = l2.map f :=
    List.map_congr_left fun y hy => hother y (by simp [hy]) (fun h => hx2 (h ▸ hy))
  simp only [List.map_append, List.map_cons, e1, e2] at hs ⊢
  rw [List.isChain_append] at hs ⊢
  rw [List.isChain_cons] at hs ⊢
  refine ⟨hs.1, ⟨?_, hs.2.1.2⟩, ?_⟩
  · intro y hy
    cases l2 with
    | nil => simp at hy
    | cons a t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      have : a ≠ NIL := fun h => hnil (by simp [h])
      have := hsucc (by rw [hsu]; simpa using this)
      rw [hsu] at this; simpa using this
  · intro y hy z hz
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
    subst hz
    rcases l1.eq_nil_or_concat with h | ⟨l1', a, rfl⟩
    · subst h; simp at hy
    · simp only [List.concat_eq_append] at *
      simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Option.mem_def, Option.some.injEq] at hy
      subst hy
      have : a ≠ NIL := fun h => hnil (by simp [h])
      have := hpred (by rw [hp]; simpa using this)
      rw [hp] at this; simpa using this

/-- `IsChain` survives inserting `y` right after `x`, for any relation. -/
theorem isChain_insert_relation {R : Nat → Nat → Prop} {l1 l2 : List Nat} {x y : Nat}
    {f f' : Nat → Nat}
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

end OrderMaintenance.Proof

/-! ### Successors and predecessors after list surgery -/

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem predOf_cons {a : Nat} {l : List Nat} (hnd : (a :: l).Nodup) (z : Nat) :
    predOf (a :: l) z = if z ∈ l then (if l.head? = some z then a else predOf l z) else NIL := by
  have := predOf_append (l1 := [a]) (l2 := l) (List.nodup_cons.mp hnd).2 z
  simp only [List.singleton_append] at this
  rw [this]
  by_cases hz : z ∈ l <;> simp [hz, predOf]

theorem succOf_cons' {a : Nat} {l : List Nat} (z : Nat) :
    succOf (a :: l) z = if z = a then l.headD NIL else succOf l z := by
  rw [succOf_cons]
  by_cases h : z = a
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- Successors after inserting `y` right after `x`. -/
theorem succOf_insert {l1 l2 : List Nat} {x y : Nat} (hnd : (l1 ++ x :: y :: l2).Nodup) (z : Nat) :
    succOf (l1 ++ x :: y :: l2) z =
      if z = x then y else if z = y then l2.headD NIL
      else succOf (l1 ++ x :: l2) z := by
  have h1 : l1.Nodup := (List.nodup_append.mp hnd).1
  have hdis := (List.nodup_append.mp hnd).2.2
  have hx1 : x ∉ l1 := fun h => hdis x h x (by simp) rfl
  have hy1 : y ∉ l1 := fun h => hdis y h y (by simp) rfl
  have h2 := (List.nodup_append.mp hnd).2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at h2
  rw [succOf_append h1, succOf_append h1, succOf_cons', succOf_cons', succOf_cons']
  by_cases hz1 : z ∈ l1
  · have hzx : z ≠ x := fun h => hx1 (h ▸ hz1)
    have hzy : z ≠ y := fun h => hy1 (h ▸ hz1)
    simp [hz1, hzx, hzy]
  · by_cases hzx : z = x
    · subst hzx; simp [hz1]
    · by_cases hzy : z = y
      · subst hzy; simp [hz1, hzx]
      · simp [hz1, hzx, hzy]

/-- Predecessors after inserting `y` right after `x`. -/
theorem predOf_insert {l1 l2 : List Nat} {x y : Nat} (hnd : (l1 ++ x :: y :: l2).Nodup) (z : Nat) :
    predOf (l1 ++ x :: y :: l2) z =
      if z = y then x else if l2.head? = some z then y else predOf (l1 ++ x :: l2) z := by
  have h2 := (List.nodup_append.mp hnd).2.1
  have h2' : (x :: l2).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at h2 ⊢; exact ⟨h2.1.2, h2.2.2⟩
  have h3 : (y :: l2).Nodup := (List.nodup_cons.mp h2).2
  rw [predOf_append h2, predOf_append h2', predOf_cons h2, predOf_cons h2', predOf_cons h3]
  simp only [List.nodup_cons, List.mem_cons, not_or] at h2
  obtain ⟨⟨hxy, hx2⟩, hy2, -⟩ := h2
  have hl2 : ∀ z, l2.head? = some z → z ∈ l2 := fun z h => List.mem_of_mem_head? h
  by_cases hzy : z = y
  · subst hzy; simp [Ne.symm hxy, hy2, hxy]
  · by_cases hzx : z = x
    · subst hzx
      have hh : l2.head? ≠ some z := fun h => hx2 (hl2 _ h)
      simp [hh, hxy]
    · by_cases hz2 : z ∈ l2
      · by_cases hh : l2.head? = some z <;> simp [hz2, hzy, hzx, Ne.symm hzx, Ne.symm hzy, hh]
      · have : l2.head? ≠ some z := fun h => hz2 (hl2 _ h)
        simp [hz2, hzy, hzx, this]

/-- Successors after inserting `a` at the front. -/
theorem succOf_insert_front {l : List Nat} {a : Nat} (_hnd : (a :: l).Nodup) (z : Nat) :
    succOf (a :: l) z = if z = a then l.headD NIL else succOf l z := succOf_cons' z

/-- Predecessors after inserting `a` at the front. -/
theorem predOf_insert_front {l : List Nat} {a : Nat} (hnd : (a :: l).Nodup) (z : Nat) :
    predOf (a :: l) z = if l.head? = some z then a else predOf l z := by
  rw [predOf_cons hnd]
  by_cases hz : z ∈ l
  · simp [hz]
  · have : l.head? ≠ some z := fun h => hz (List.mem_of_mem_head? h)
    simp [hz, this, predOf_not_mem hz]

/-- Successors after removing `x` from `l1 ++ x :: l2`. -/
theorem succOf_erase {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) {z : Nat}
    (hzx : z ≠ x) :
    succOf (l1 ++ l2) z = if l1.getLast? = some z then l2.headD NIL
      else succOf (l1 ++ x :: l2) z := by
  have h1 : l1.Nodup := (List.nodup_append.mp hnd).1
  rw [succOf_append h1, succOf_append h1, succOf_cons' (a := x)]
  have hl1 : ∀ z, l1.getLast? = some z → z ∈ l1 := fun z h => List.mem_of_getLast? h
  by_cases hz1 : z ∈ l1
  · by_cases hl : l1.getLast? = some z <;> simp [hz1, hl]
  · have : l1.getLast? ≠ some z := fun h => hz1 (hl1 _ h)
    simp [hz1, this, hzx]

/-- Predecessors after removing `x` from `l1 ++ x :: l2`. -/
theorem predOf_erase {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) {z : Nat}
    (hzx : z ≠ x) :
    predOf (l1 ++ l2) z = if l2.head? = some z then l1.getLastD NIL
      else predOf (l1 ++ x :: l2) z := by
  have h2 := (List.nodup_append.mp hnd).2.1
  have h2' : l2.Nodup := (List.nodup_cons.mp h2).2
  rw [predOf_append h2', predOf_append h2, predOf_cons h2]
  have hl2 : ∀ z, l2.head? = some z → z ∈ l2 := fun z h => List.mem_of_mem_head? h
  by_cases hz2 : z ∈ l2
  · by_cases hh : l2.head? = some z <;> simp [hz2, hh, hzx, Ne.symm hzx]
  · have : l2.head? ≠ some z := fun h => hz2 (hl2 _ h)
    simp [hz2, this, hzx]

end OrderMaintenance.Proof

/-! ### Linked-list updates -/

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem headD_ne_nil {l : List Nat} {z : Nat} (hz : z ∈ l) (hnil : NIL ∉ l) :
    l.headD NIL ≠ NIL := by
  cases l with
  | nil => simp at hz
  | cons a t => intro h; simp only [List.headD_cons] at h; exact hnil (by simp [h])

theorem head?_eq_iff {l : List Nat} {z : Nat} (hz : z ≠ NIL) :
    l.head? = some z ↔ l.headD NIL = z := by
  cases l with
  | nil => simp only [List.head?_nil, reduceCtorEq, List.headD_eq_head?_getD,
      Option.getD_none, false_iff]; exact fun h => hz h.symm
  | cons a t => simp

theorem getLast?_eq_iff {l : List Nat} {z : Nat} (hz : z ≠ NIL) :
    l.getLast? = some z ↔ l.getLastD NIL = z := by
  rcases l.eq_nil_or_concat with rfl | ⟨l', a, rfl⟩
  · simp only [List.getLast?_nil, reduceCtorEq, List.getLastD_eq_getLast?,
      Option.getD_none, false_iff]; exact fun h => hz h.symm
  · simp

/-- Inserting `y` right after `x`. -/
theorem LList.insert_after {nxt prv nxt' prv' : Nat → Nat} {hd : Nat} {l1 l2 : List Nat}
    {x y : Nat} (h : LList nxt prv hd (l1 ++ x :: l2)) (hy : y ∉ l1 ++ x :: l2) (hy0 : y ≠ NIL)
    (hn : ∀ z ∈ l1 ++ x :: y :: l2, nxt' z = if z = x then y else if z = y then nxt x else nxt z)
    (hp : ∀ z ∈ l1 ++ x :: y :: l2, prv' z = if z = y then x else if z = nxt x then y else prv z) :
    LList nxt' prv' hd (l1 ++ x :: y :: l2) := by
  have hnd : (l1 ++ x :: y :: l2).Nodup := by
    have : l1 ++ x :: y :: l2 = (l1 ++ [x]) ++ y :: l2 := by simp
    rw [this, List.nodup_middle]
    simp only [List.append_assoc, List.singleton_append]
    exact List.nodup_cons.mpr ⟨hy, h.nodup⟩
  have hmem : ∀ z ∈ l1 ++ x :: y :: l2, z ≠ y → z ∈ l1 ++ x :: l2 := by
    intro z hz hzy; simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
  have hsx : nxt x = l2.headD NIL := by rw [h.next x (by simp), succOf_mid h.nodup]
  have hyx : y ≠ x := fun e => hy (e ▸ (by simp : x ∈ l1 ++ x :: l2))
  have hnil : NIL ∉ l1 ++ x :: y :: l2 := by
    intro hm
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm
    · exact h.nonil (by simp [hm])
    · exact h.nonil (by simp [← hm])
    · exact hy0 hm.symm
    · exact h.nonil (by simp [hm])
  refine ⟨hnd, hnil, ?_, ?_, ?_⟩
  · rw [h.head]; cases l1 <;> simp
  · intro z hz
    rw [hn z hz, succOf_insert hnd]
    by_cases hzx : z = x
    · simp [hzx]
    · by_cases hzy : z = y
      · simp [hzy, hyx, hsx]
      · simp [hzx, hzy, h.next z (hmem z hz hzy)]
  · intro z hz
    rw [hp z hz, predOf_insert hnd]
    have hz0 : z ≠ NIL := fun e => hnil (e ▸ hz)
    have key : l2.head? = some z ↔ z = l2.headD NIL := by rw [head?_eq_iff hz0]; exact eq_comm
    by_cases hzy : z = y
    · simp [hzy]
    · rw [ite_eq_right hzy, ite_eq_right hzy, hsx]
      by_cases hzn : z = l2.headD NIL
      · rw [ite_eq_left hzn, ite_eq_left (key.mpr hzn)]
      · rw [ite_eq_right hzn, ite_eq_right (fun e => hzn (key.mp e)), h.prev z (hmem z hz hzy)]

/-- Inserting `a` at the front. -/
theorem LList.insert_front {nxt prv nxt' prv' : Nat → Nat} {hd : Nat} {l : List Nat} {a : Nat}
    (h : LList nxt prv hd l) (ha : a ∉ l) (ha0 : a ≠ NIL)
    (hn : ∀ z ∈ a :: l, nxt' z = if z = a then hd else nxt z)
    (hp : ∀ z ∈ a :: l, prv' z = if z = a then NIL else if z = hd then a else prv z) :
    LList nxt' prv' a (a :: l) := by
  have hnd : (a :: l).Nodup := List.nodup_cons.mpr ⟨ha, h.nodup⟩
  have hnil : NIL ∉ a :: l := by
    simp only [List.mem_cons, not_or]; exact ⟨Ne.symm ha0, h.nonil⟩
  refine ⟨hnd, hnil, rfl, ?_, ?_⟩
  · intro z hz
    rw [hn z hz, succOf_insert_front hnd]
    by_cases hza : z = a
    · simp [hza, h.head]
    · have hzl : z ∈ l := by simpa [hza] using hz
      simp [hza, h.next z hzl]
  · intro z hz
    rw [hp z hz, predOf_insert_front hnd]
    have hz0 : z ≠ NIL := fun e => hnil (e ▸ hz)
    by_cases hza : z = a
    · subst hza
      have : l.head? ≠ some z := fun e => ha (List.mem_of_mem_head? e)
      simp only [ite_true]
      rw [ite_eq_right this]
      exact (predOf_not_mem ha).symm
    · have hzl : z ∈ l := by simpa [hza] using hz
      rw [ite_eq_right hza, h.head]
      have key : l.head? = some z ↔ z = l.headD NIL := by rw [head?_eq_iff hz0]; exact eq_comm
      by_cases hzh : z = l.headD NIL
      · rw [ite_eq_left hzh, ite_eq_left (key.mpr hzh)]
      · rw [ite_eq_right hzh, ite_eq_right (fun e => hzh (key.mp e)), h.prev z hzl]

/-- Removing `x` from `l1 ++ x :: l2`. -/
theorem LList.erase {nxt prv nxt' prv' : Nat → Nat} {hd : Nat} {l1 l2 : List Nat} {x : Nat}
    (h : LList nxt prv hd (l1 ++ x :: l2))
    (hn : ∀ z ∈ l1 ++ l2, nxt' z = if z = prv x then nxt x else nxt z)
    (hp : ∀ z ∈ l1 ++ l2, prv' z = if z = nxt x then prv x else prv z) :
    LList nxt' prv' (if prv x = NIL then nxt x else hd) (l1 ++ l2) := by
  have hnd : (l1 ++ l2).Nodup := by
    have := h.nodup; rw [List.nodup_middle] at this; exact (List.nodup_cons.mp this).2
  have hnil : NIL ∉ l1 ++ l2 := fun hm => h.nonil (by simp at hm ⊢; tauto)
  have hpx : prv x = l1.getLastD NIL := by rw [h.prev x (by simp), predOf_mid h.nodup]
  have hsx : nxt x = l2.headD NIL := by rw [h.next x (by simp), succOf_mid h.nodup]
  have hxz : ∀ z ∈ l1 ++ l2, z ≠ x := by
    intro z hz e; subst e
    have := h.nodup; rw [List.nodup_middle] at this; exact (List.nodup_cons.mp this).1 hz
  have hmem : ∀ z ∈ l1 ++ l2, z ∈ l1 ++ x :: l2 := by
    intro z hz; simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
  refine ⟨hnd, hnil, ?_, ?_, ?_⟩
  · rw [hpx, hsx, h.head]
    rcases l1.eq_nil_or_concat with rfl | ⟨l1', p, rfl⟩
    · simp
    · have hp0 : p ≠ NIL := fun e => h.nonil (by simp [e])
      simp [hp0]
  · intro z hz
    have hz0 : z ≠ NIL := fun e => hnil (e ▸ hz)
    rw [hn z hz, succOf_erase h.nodup (hxz z hz), hpx, hsx]
    have key : l1.getLast? = some z ↔ z = l1.getLastD NIL := by
      rw [getLast?_eq_iff hz0]; exact eq_comm
    by_cases hzp : z = l1.getLastD NIL
    · rw [ite_eq_left hzp, ite_eq_left (key.mpr hzp)]
    · rw [ite_eq_right hzp, ite_eq_right (fun e => hzp (key.mp e)), h.next z (hmem z hz)]
  · intro z hz
    have hz0 : z ≠ NIL := fun e => hnil (e ▸ hz)
    rw [hp z hz, predOf_erase h.nodup (hxz z hz), hpx, hsx]
    have key : l2.head? = some z ↔ z = l2.headD NIL := by rw [head?_eq_iff hz0]; exact eq_comm
    by_cases hzn : z = l2.headD NIL
    · rw [ite_eq_left hzn, ite_eq_left (key.mpr hzn)]
    · rw [ite_eq_right hzn, ite_eq_right (fun e => hzn (key.mp e)), h.prev z (hmem z hz)]

/-- Inserting `a` right before and `b` right after `g`. -/
theorem LList.insert_around {nxt prv nxt' prv' : Nat → Nat} {hd : Nat} {l1 l2 : List Nat}
    {g a b : Nat} (h : LList nxt prv hd (l1 ++ g :: l2)) (ha : a ∉ l1 ++ g :: l2)
    (hb : b ∉ l1 ++ g :: l2) (hab : a ≠ b) (ha0 : a ≠ NIL) (hb0 : b ≠ NIL)
    (hn : ∀ z ∈ l1 ++ a :: g :: b :: l2, nxt' z =
      if z = a then g else if z = g then b else if z = b then nxt g
      else if z = prv g then a else nxt z)
    (hp : ∀ z ∈ l1 ++ a :: g :: b :: l2, prv' z =
      if z = a then prv g else if z = g then a else if z = b then g
      else if z = nxt g then b else prv z) :
    LList nxt' prv' (if prv g = NIL then a else hd) (l1 ++ a :: g :: b :: l2) := by
  have hgm : g ∈ l1 ++ g :: l2 := by simp
  have hag : a ≠ g := fun e => ha (e ▸ hgm)
  have hbg : b ≠ g := fun e => hb (e ▸ hgm)
  have hpx : prv g = l1.getLastD NIL := by rw [h.prev g hgm, predOf_mid h.nodup]
  have hsx : nxt g = l2.headD NIL := by rw [h.next g hgm, succOf_mid h.nodup]
  -- step 1: insert `b` after `g`
  have h1 := LList.insert_after
    (nxt' := fun z => if z = g then b else if z = b then nxt g else nxt z)
    (prv' := fun z => if z = b then g else if z = nxt g then b else prv z) h hb hb0
    (fun z _ => rfl) (fun z _ => rfl)
  have hb1 : (l1 ++ g :: b :: l2).Nodup := h1.nodup
  have ha1 : a ∉ l1 ++ g :: b :: l2 := by
    simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto
  -- members of the final list other than `a` are members of the old list, or `b`
  have hmem : ∀ z ∈ l1 ++ a :: g :: b :: l2, z ≠ a → z ≠ b → z ∈ l1 ++ g :: l2 := by
    intro z hz hza hzb; simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
  have hnb : nxt g ≠ b := by
    rw [hsx]; intro e
    cases l2 with
    | nil => exact hb0 e.symm
    | cons c t => simp only [List.headD_cons] at e; exact hb (by simp [e])
  have hnil : NIL ∉ l1 ++ a :: g :: b :: l2 := by
    intro hm
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm | hm
    · exact h.nonil (by simp [hm])
    · exact ha0 hm.symm
    · exact h.nonil (by simp [← hm])
    · exact hb0 hm.symm
    · exact h.nonil (by simp [hm])
  rcases l1.eq_nil_or_concat with rfl | ⟨l1', p, rfl⟩
  · -- `g` was the head: `a` becomes the new head
    have hpg : prv g = NIL := by rw [hpx]; rfl
    have hhd : hd = g := by rw [h.head]; rfl
    rw [ite_eq_left hpg]
    refine LList.insert_front h1 ha1 ha0 (fun z hz => ?_) (fun z hz => ?_)
    · rw [hn z (by simpa using hz)]
      by_cases hza : z = a
      · simp [hza, hhd]
      · have hz0 : z ≠ NIL := fun e => hnil (by rw [← e]; simpa using hz)
        simp [hza, hpg, hz0]
    · rw [hp z (by simpa using hz)]
      by_cases hza : z = a
      · simp [hza, hpg]
      · rw [ite_eq_right hza, ite_eq_right hza, hhd]
  · -- `g` had a predecessor `p`: insert `a` after `p`
    simp only [List.concat_eq_append] at *
    have hpg : prv g = p := by rw [hpx]; simp
    have hp0 : p ≠ NIL := fun e => h.nonil (by simp [e])
    rw [ite_eq_right (by rw [hpg]; exact hp0)]
    have e1 : l1' ++ [p] ++ g :: b :: l2 = l1' ++ p :: (g :: b :: l2) := by simp
    have e2 : l1' ++ [p] ++ a :: g :: b :: l2 = l1' ++ p :: a :: (g :: b :: l2) := by simp
    rw [e1] at h1 ha1
    rw [e2] at hn hp hmem ⊢
    have hpa : p ≠ a := fun e => ha (by simp [e])
    have hpgn : p ≠ g := fun e => by
      have := h.nodup; rw [show l1' ++ [p] ++ g :: l2 = l1' ++ p :: g :: l2 by simp] at this
      simp [List.nodup_append, e] at this
    have hpb : p ≠ b := fun e => hb (by simp [e])
    have hnp : nxt p = g := by
      have hnd0 := h.nodup
      rw [show l1' ++ [p] ++ g :: l2 = l1' ++ p :: (g :: l2) by simp] at hnd0
      rw [h.next p (by simp), show l1' ++ [p] ++ g :: l2 = l1' ++ p :: (g :: l2) by simp,
        succOf_mid hnd0]
      rfl
    refine LList.insert_after h1 ha1 ha0 (fun z hz => ?_) (fun z hz => ?_)
    · rw [hn z hz]
      by_cases hza : z = a
      · simp [hza, hpgn, hpb, Ne.symm hpa, hnp]
      · by_cases hzp : z = p
        · subst hzp; simp [hpa, hpgn, hpb, hpg]
        · simp only [hza, hzp, ite_false, hpg]
    · rw [hp z hz]
      by_cases hza : z = a
      · simp [hza, hpg]
      · simp only [hza, ite_false]
        by_cases hzg : z = g
        · subst hzg; simp [hpgn,   hnp, hpb]
        · by_cases hzb : z = b
          · subst hzb; simp [hbg, hnp, hpb, hpgn]
          · simp [hzg, hzb, hnp, hpb, hpgn]

theorem getLastD_append_cons (l : List Nat) (a : Nat) (t : List Nat) (d : Nat) :
    (l ++ a :: t).getLastD d = (a :: t).getLastD d := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_append,
    List.getLast?_eq_some_getLast (l := a :: t) (by simp)]
  simp

theorem getLastD_cons_mem (a : Nat) (t : List Nat) (d : Nat) : (a :: t).getLastD d ∈ a :: t := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (l := a :: t) (by simp)]
  simp only [Option.getD_some]
  exact List.getLast_mem _

theorem headD_append_cons (l : List Nat) (a : Nat) (t : List Nat) (d : Nat) :
    (l ++ a :: t).headD d = (l.headD a) := by
  cases l <;> simp

theorem mem_insert_iff {l1 l2 : List Nat} {x y e : Nat} :
    e ∈ l1 ++ x :: y :: l2 ↔ e = y ∨ e ∈ l1 ++ x :: l2 := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

theorem succOf_ne_self {l : List Nat} (hnd : l.Nodup) (x : Nat) (hx : x ≠ NIL) :
    succOf l x ≠ x := by
  by_cases hm : x ∈ l
  · obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.mp hm
    rw [succOf_mid hnd]
    intro e
    cases l2 with
    | nil => exact hx e.symm
    | cons a t =>
      simp only [List.headD_cons] at e; subst e
      exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (by simp)
  · rw [succOf_not_mem hm]; exact Ne.symm hx

theorem predOf_ne_self {l : List Nat} (hnd : l.Nodup) (x : Nat) (hx : x ≠ NIL) :
    predOf l x ≠ x :=
  succOf_ne_self (List.nodup_reverse.mpr hnd) x hx

theorem predOf_ne_succOf {l : List Nat} (hnd : l.Nodup) {x : Nat} (hx : x ∈ l)
    (hp : predOf l x ≠ NIL) : predOf l x ≠ succOf l x := by
  obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.mp hx
  rw [predOf_mid hnd, succOf_mid hnd] at *
  intro e
  rcases l1.eq_nil_or_concat with h | ⟨l1', a, rfl⟩
  · subst h; exact hp rfl
  · simp only [List.concat_eq_append, List.getLastD_concat] at e hp
    cases l2 with
    | nil => exact hp e
    | cons b t =>
      simp only [List.headD_cons] at e; subst e
      have := (List.nodup_append.mp hnd).2.2 a (by simp) a (by simp)
      exact this rfl

theorem mem_around_iff {l1 l2 : List Nat} {g a b z : Nat} :
    z ∈ l1 ++ a :: g :: b :: l2 ↔ z = a ∨ z = b ∨ z ∈ l1 ++ g :: l2 := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem mem_split_of_mem {l1 l2 : List Nat} {g z : Nat} (h : z ∈ l1 ++ l2) : z ∈ l1 ++ g :: l2 := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- In a list without duplicates, `succOf l a = b ≠ NIL` splits `l` around the pair `a, b`. -/
theorem succOf_split {l : List Nat} {a b : Nat} (h : succOf l a = b) (hb : b ≠ NIL) :
    ∃ l1 l2, l = l1 ++ a :: b :: l2 := by
  have ha : a ∈ l := by
    by_contra hm; rw [succOf_not_mem hm] at h; exact hb h.symm
  obtain ⟨l1, r, rfl⟩ := List.mem_iff_append.mp ha
  induction l1 generalizing r with
  | nil =>
    simp only [List.nil_append] at h ⊢
    rw [succOf_cons', ite_eq_left rfl] at h
    cases r with
    | nil => exact absurd h.symm hb
    | cons c t => simp only [List.headD_cons] at h; subst h; exact ⟨[], t, rfl⟩
  | cons d t ih =>
    by_cases hda : d = a
    · subst hda
      simp only [List.cons_append] at h
      rw [succOf_cons', ite_eq_left rfl] at h
      cases ht : t ++ d :: r with
      | nil => simp at ht
      | cons c u =>
        rw [ht] at h; simp only [List.headD_cons] at h; subst h
        exact ⟨[], u, by simp [ht]⟩
    · simp only [List.cons_append] at h
      rw [succOf_cons', ite_eq_right (Ne.symm hda)] at h
      obtain ⟨l1, l2, e⟩ := ih r h (by simp)
      exact ⟨d :: l1, l2, by simp [e]⟩

/-- `predOf l b = a ≠ NIL` splits `l` around the pair `a, b`. -/
theorem predOf_split {l : List Nat} {a b : Nat} (h : predOf l b = a) (ha : a ≠ NIL) :
    ∃ l1 l2, l = l1 ++ a :: b :: l2 := by
  obtain ⟨m1, m2, e⟩ := succOf_split (l := l.reverse) h ha
  refine ⟨m2.reverse, m1.reverse, ?_⟩
  have := congrArg List.reverse e
  simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons] at this
  rw [this]; simp

end OrderMaintenance.Proof
