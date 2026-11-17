/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartViews


/-!
# M5: what `startDrain` computes, under the invariant

The sides (`sidesOf`, `fixSides`), the cut (Lemma T0), and the parts.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### `sidesOf` and `fixSides` -/

theorem lookup_assocSet (l : List (Nat × Side)) (k k' : Nat) (sd : Side) :
    lookup (assocSet l k sd) k' = if k' = k then some sd else lookup l k' := by
  by_cases h : k' = k
  · subst h; rw [ite_eq_left rfl, lookup_assocSet_eq]
  · rw [ite_eq_right h, lookup_assocSet_ne _ _ _ _ h]

/-- The step of `sidesOf`. -/
def sideStep (b : Nat) (acc : List (Nat × Side) × Side) (e : Nat) : List (Nat × Side) × Side :=
  let sd' := if e == b then Side.right else acc.2
  (assocSet acc.1 e sd', sd')

theorem sidesOf_eq (order : List Nat) (b : Nat) : sidesOf order b = (order.foldl (sideStep b)
  ([], .left)).1 := rfl

theorem sideStep_fold {b : Nat} : ∀ (l : List Nat), b ∉ l → ∀ (acc : List (Nat × Side)) (sd : Side),
    (l.foldl (sideStep b) (acc, sd)).2 = sd ∧
      ∀ e, lookup (l.foldl (sideStep b) (acc, sd)).1 e = if e ∈ l then some sd else lookup acc e
  | [], _, acc, sd => ⟨rfl, fun e => by simp⟩
  | x :: l, hb, acc, sd => by
    simp only [List.mem_cons, not_or] at hb
    simp only [List.foldl_cons]
    have hx : (sideStep b (acc, sd) x) = (assocSet acc x sd, sd) := by
      unfold sideStep; simp [Ne.symm hb.1]
    rw [hx]
    obtain ⟨h1, h2⟩ := sideStep_fold l hb.2 (assocSet acc x sd) sd
    refine ⟨h1, fun e => ?_⟩
    rw [h2, lookup_assocSet]
    by_cases he : e ∈ l
    · simp [he]
    · by_cases hex : e = x
      · simp [hex]
      · simp [he, hex]

/-- **`sidesOf`**: left before the boundary, right from it on. -/
theorem sidesOf_spec {P Q : List Nat} {b : Nat} (hnd : (P ++ b :: Q).Nodup) (e : Nat) :
    lookup (sidesOf (P ++ b :: Q) b) e =
      if e ∈ P then some .left else if e = b ∨ e ∈ Q then some .right else none := by
  have h1 := List.nodup_append.mp hnd
  have hbP : b ∉ P := fun h => h1.2.2 b h b (by simp) rfl
  have hbQ : b ∉ Q := (List.nodup_cons.mp h1.2.1).1
  rw [sidesOf_eq, List.foldl_append, List.foldl_cons]
  obtain ⟨p1, p2⟩ := sideStep_fold P hbP [] .left
  have hb : sideStep b (P.foldl (sideStep b) ([], .left)) b =
      (assocSet (P.foldl (sideStep b) ([], .left)).1 b .right, .right) := by
    unfold sideStep; simp
  rw [hb]
  obtain ⟨-, q2⟩ := sideStep_fold Q hbQ (assocSet (P.foldl (sideStep b) ([], .left)).1 b .right)
    .right
  rw [q2, lookup_assocSet, p2]
  by_cases heP : e ∈ P
  · have heQ : e ∉ Q := fun h => h1.2.2 e heP e (by simp [h]) rfl
    have heb : e ≠ b := fun h => hbP (h ▸ heP)
    simp [heP, heQ, heb]
  · by_cases heQ : e ∈ Q
    · simp [heP, heQ]
    · by_cases heb : e = b
      · simp [  heb, hbP]
      · simp [heP, heQ, heb, lookup]

/-- **`fixSides`**: a ghost entry takes the side of its first target (a live node). -/
theorem fixSides_spec (ns : Array Node) : ∀ (es : List Nat) (side : List (Nat × Side)),
    (∀ e ∈ es, (ns.getX e).draining = true → (ns.getX (ns.getX e).t1).draining = false ∧
      (lookup side (ns.getX e).t1).isSome) →
    ∃ side', fixSides ns es side = some side' ∧ ∀ x, lookup side' x =
      if x ∈ es ∧ (ns.getX x).draining = true then lookup side (ns.getX x).t1 else lookup side x
  | [], side, _ => ⟨side, rfl, fun x => by simp⟩
  | e :: es, side, h => by
    by_cases hd : (ns.getX e).draining = true
    · obtain ⟨hl, hs⟩ := h e (by simp) hd
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hs
      have hrest : ∀ e' ∈ es, (ns.getX e').draining = true → (ns.getX (ns.getX e').t1).draining
        = false ∧
          (lookup (assocSet side e st) (ns.getX e').t1).isSome := by
        intro e' he' hd'
        obtain ⟨a, b⟩ := h e' (by simp [he']) hd'
        refine ⟨a, ?_⟩
        rw [lookup_assocSet]
        split
        · rfl
        · exact b
      obtain ⟨side', h1, h2⟩ := fixSides_spec ns es (assocSet side e st) hrest
      refine ⟨side', by simp only [fixSides, hd, ite_true, hst]; exact h1, fun x => ?_⟩
      rw [h2]
      by_cases hx : x ∈ es ∧ (ns.getX x).draining = true
      · rw [ite_eq_left hx, ite_eq_left ⟨by simp [hx.1], hx.2⟩, lookup_assocSet]
        have : (ns.getX x).t1 ≠ e := by
          intro h'
          have := (h x (by simp [hx.1]) hx.2).1
          rw [h', hd] at this; exact absurd this (by simp)
        rw [ite_eq_right this]
      · rw [ite_eq_right hx, lookup_assocSet]
        by_cases hxe : x = e
        · subst hxe; rw [ite_eq_left rfl, ite_eq_left ⟨by simp, hd⟩, hst]
        · rw [ite_eq_right hxe, ite_eq_right]
          rintro ⟨hm, hd'⟩
          simp only [List.mem_cons, hxe, false_or] at hm
          exact hx ⟨hm, hd'⟩
    · have hrest : ∀ e' ∈ es, (ns.getX e').draining = true → (ns.getX (ns.getX e').t1).draining
        = false ∧
          (lookup side (ns.getX e').t1).isSome := fun e' he' hd' => h e' (by simp [he']) hd'
      obtain ⟨side', h1, h2⟩ := fixSides_spec ns es side hrest
      refine ⟨side', by simp only [fixSides, hd]; exact h1, fun x => ?_⟩
      rw [h2]
      by_cases hxe : x = e
      · subst hxe
        have : ¬(x ∈ es ∧ (ns.getX x).draining = true) := fun h' => hd h'.2
        rw [ite_eq_right this, ite_eq_right (fun h' => hd h'.2)]
      · simp only [List.mem_cons, hxe, false_or]

end OrderMaintenance.Proof.Top

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model

/-! ### Side list lengths -/

theorem length_assocSet_of_some {β : Type} {l : List (Nat × β)} {k : Nat} (v : β)
    (h : (lookup l k).isSome) : (assocSet l k v).length = l.length := by
  unfold assocSet
  have : l.any (·.1 == k) = true := by
    unfold lookup at h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨q, hq, -⟩ := hp
    exact List.any_eq_true.mpr ⟨q, List.mem_of_find?_eq_some hq, by simpa using List.find?_some hq⟩
  rw [ite_eq_left this]; simp

theorem length_sideStep_fold (b : Nat) : ∀ (l : List Nat) (acc : List (Nat × Side) × Side),
    (l.foldl (sideStep b) acc).1.length ≤ acc.1.length + l.length
  | [], _ => by simp
  | e :: l, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have := length_sideStep_fold b l (sideStep b acc e)
    have h2 : (sideStep b acc e).1.length ≤ acc.1.length + 1 := by
      unfold sideStep assocSet; split <;> (split <;> simp)
    omega

theorem length_sidesOf (order : List Nat) (b : Nat) : (sidesOf order b).length ≤ order.length := by
  rw [sidesOf_eq]; have := length_sideStep_fold b order ([], .left); simpa using this

theorem length_fixSides (ns : Array Node) : ∀ (es : List Nat) (side side' : List (Nat × Side)),
    (∀ e ∈ es, (lookup side e).isSome) → fixSides ns es side = some side' → side'.length =
      side.length
  | [], side, side', _, h => by simp only [fixSides, Option.some.injEq] at h; rw [h]
  | e :: es, side, side', hk, h => by
    simp only [fixSides] at h
    split at h
    · split at h
      · next st _ =>
        have hk' : ∀ e' ∈ es, (lookup (assocSet side e st) e').isSome := by
          intro e' he'
          rw [lookup_assocSet]; split
          · rfl
          · exact hk e' (List.mem_cons_of_mem _ he')
        rw [length_fixSides ns es _ side' hk' h, length_assocSet_of_some st (hk e (by simp))]
      · simp at h
    · exact length_fixSides ns es side side' (fun e' he' => hk e' (List.mem_cons_of_mem _ he')) h

end OrderMaintenance.Proof.Top
