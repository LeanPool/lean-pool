/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartFrame


/-!
# M5: the sides and the parts at a drain start

Children before the boundary go left, the others right; a ghost entry goes with its targets.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Lists -/

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

theorem mem_left_iff_before {P Q : List Nat} {b e : Nat} (hnd : (P ++ b :: Q).Nodup) :
    e ∈ P ↔ Before (P ++ b :: Q) e b := by
  constructor
  · exact before_split
  · intro h
    have hm := h.mem_left
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | rfl | hm
    · exact hm
    · exact absurd rfl (h.ne hnd)
    · exfalso
      exact h.asymm hnd (before_append_right (before_cons.mpr (Or.inr ⟨rfl, hm⟩)))

/-- A list split at its `k`-th element. -/
theorem split_at {l : List Nat} {k : Nat} (hk : k < l.length) :
    l = l.take k ++ l.getD k 0 :: l.drop (k + 1) := by
  rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- **Before the boundary in a superlist iff before it in the list.** -/
theorem mem_take_iff_left {l o P Q : List Nat} {k e : Nat} (hlo : l.Sublist o) (ho : o.Nodup)
    (hk : k < l.length) (he : e ∈ l) (hsplit : o = P ++ l.getD k 0 :: Q) :
    e ∈ l.take k ↔ e ∈ P := by
  have hl : l.Nodup := ho.sublist hlo
  have hb : l.getD k 0 ∈ l := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hsp := split_at hk
  have hnd' : (l.take k ++ l.getD k 0 :: l.drop (k + 1)).Nodup := hsp ▸ hl
  rw [mem_left_iff_before hnd', ← hsp, mem_left_iff_before (hsplit ▸ ho), ← hsplit]
  constructor
  · intro h; exact h.mono hlo
  · intro h; exact before_of_sublist hlo ho he hb h

/-- The parent of an entry below the root's height is live. -/
theorem Shape.par_liveN {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord) {h
  e : Nat}
    (he : Ent ord h e) (hh : h < s.P.H) : liveN s (par s h e) := by
  by_cases h0 : h = 0
  · subst h0
    unfold Ent at he; rw [S.ord0] at he
    rw [par_live (Or.inl rfl), ite_eq_left rfl]; exact (S.lp e he).1
  · obtain ⟨hn, hht⟩ := (S.ordMem h (by omega) (by omega) e).mp he
    by_cases hd : (nd s e).draining = true
    · obtain ⟨g1, -, g3, -⟩ := S.ghost e ⟨hn, hd⟩
      unfold par; rw [ite_eq_right h0, ite_eq_left hd]
      exact (S.up _ g1 (by rw [g3]; omega)).1
    · have hl : liveN s e := ⟨hn, by simpa using hd⟩
      rw [par_live (Or.inr hl), ite_eq_right h0]
      exact (S.up e hl (by omega)).1

theorem infix_pair_idx {l : List Nat} {a b : Nat} (h : [a, b] <:+: l) :
    ∃ i, i + 1 < l.length ∧ l.getD i 0 = a ∧ l.getD (i + 1) 0 = b := by
  obtain ⟨u, w, rfl⟩ := h
  refine ⟨u.length, by simp, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem getD_mem_take {l : List Nat} {i k : Nat} (hi : i < l.length) (hk : i < k) : l.getD i 0 ∈
  l.take k := by
  rw [List.getD_eq_getElem _ _ hi, ← List.getElem_take (j := k) (h := by simp; omega)]
  exact List.getElem_mem _

theorem getD_not_mem_take {l : List Nat} (hl : l.Nodup) {i k : Nat} (hi : i < l.length) (hk : k
  ≤ i) :
    l.getD i 0 ∉ l.take k := by
  rw [List.getD_eq_getElem _ _ hi]
  intro hm
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at e
  have := (List.Nodup.getElem_inj_iff hl).mp e
  simp at hj; omega

theorem filter_mem_take {l : List Nat} (hl : l.Nodup) (k : Nat) :
    l.filter (fun e => decide (e ∈ l.take k)) = l.take k ∧ l.filter (fun e => !decide (e ∈
      l.take k)) = l.drop k := by
  have hsp : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  have hnd : (l.take k ++ l.drop k).Nodup := hsp ▸ hl
  have hdis := (List.nodup_append.mp hnd).2.2
  constructor
  · conv_lhs => rw [hsp]
    rw [List.filter_append, List.filter_eq_self.mpr (fun e he => by simp [he]),
      List.filter_eq_nil_iff.mpr (fun e he => by
        simp only [List.take_append_drop, decide_eq_true_eq]
        exact fun h => hdis e h e he rfl),
        List.append_nil]
  · conv_lhs => rw [hsp]
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun e he => by simp [he]),
      List.filter_eq_self.mpr (fun e he => by
        simp only [List.take_append_drop, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not]
        exact fun h => hdis e h e he rfl),
        List.nil_append]

/-! ### At a drain start -/

section parts
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
  (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
  (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
include hpc hv0 hI hlp hTP hof hW

/-- The cut is inside. -/
theorem sp_k : 2 ≤ (nd (ts s) v).children.length ∧ 1 ≤ sK (wiC s v) v ∧
    sK (wiC s v) v < (nd (ts s) v).children.length := by
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  by_cases h2 : 2 ≤ ht (ts s) v
  · obtain ⟨a, b, c, -⟩ := sd_cut2 hpc hv0 hI hlp hTP h2 hof hW
    exact ⟨a, b, by omega⟩
  · obtain ⟨a, b, c, -⟩ := sd_cut1 hpc hv0 hI hlp (by omega) hof hW
    exact ⟨a, b, by omega⟩

omit hlp hTP hof hW in
/-- The children, in the order of `v`'s table. -/
theorem sp_kids_sub : (nd (ts s) v).children.Sublist (order (ts s) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨-, hsub, -⟩ := S.kids v hvl
  exact sublist_of_subset_common hsub (S.O1 v hvl.1) (S.ordNodup _)
    (fun e he => S.kid_mem hI.time hvl he)

omit hlp hTP hof hW in
theorem sp_order_nodup : (order (ts s) v).Nodup := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  exact (S.ordNodup _).sublist (S.O1 v hvl.1)

/-- The boundary child. -/
theorem sp_b : (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ∈ (nd (ts s) v).children ∧
    ∃ P Q, order (ts s) v = P ++ (nd (ts s) v).children.getD (sK (wiC s v) v) 0 :: Q := by
  obtain ⟨-, -, hk⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  have hb : (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ∈ (nd (ts s) v).children := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  exact ⟨hb, List.mem_iff_append.mp ((sp_kids_sub hpc hv0 hI).subset hb)⟩

omit hTP hof hW in
/-- An entry of `v`'s table has `v` as its parent. -/
theorem sp_par {e : Nat} (he : e ∈ order (ts s) v) : par (ts s) (ht (ts s) v - 1) e = v := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  have hent := S.tabEnt v hvl.1 e he
  have hT : v ∈ tabs (ts s) (ht (ts s) v - 1) e := by
    have h1 := (sd_ht hpc hv0 hI hlp).1
    exact (S.tabsIff _ e v hent).mpr ⟨hvl.1, by omega, he⟩
  rcases S.Q _ e v hent hT with h | h
  · exact h.symm
  · exfalso
    have hpl := S.par_liveN hent (by have := (sd_ht hpc hv0 hI hlp).2; change _ < s.P.H; omega)
    obtain ⟨hg, -⟩ := S.src _ hpl (by rw [← h]; exact hv0)
    rw [← h] at hg
    exact absurd hg.2 (by rw [hvl.2]; simp)

omit hTP hof hW in
theorem sp_entry {e : Nat} (he : e ∈ order (ts s) v) :
    (ht (ts s) v = 1 → e ∈ (nd (ts s) v).children) ∧
    (2 ≤ ht (ts s) v → isN (ts s) e ∧ ht (ts s) e = ht (ts s) v - 1 ∧
      ((nd (ts s) e).draining = false → e ∈ (nd (ts s) v).children)) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  have hp := sp_par hpc hv0 hI hlp he
  have hent := S.tabEnt v hvl.1 e he
  constructor
  · intro h1
    rw [h1, Nat.sub_self] at hent hp
    unfold Ent at hent; rw [S.ord0] at hent
    exact (S.mem_children hvl).mpr ⟨by rw [ite_eq_left h1]; exact hent, (by
        rw [h1, Nat.sub_self]
        exact hp)⟩
  · intro h2
    obtain ⟨hn, hh⟩ := (S.ordMem _ (by omega) (by
      have := (sd_ht hpc hv0 hI hlp).2
      change _ ≤ s.P.H
      omega) e).mp hent
    refine ⟨hn, hh, fun hd => ?_⟩
    have hl : liveN (ts s) e := ⟨hn, hd⟩
    exact (S.mem_children hvl).mpr ⟨by rw [ite_eq_right (by omega)]; exact ⟨hl, hh⟩, hp⟩

omit hTP hof hW in
theorem sp_ghost (h2 : 2 ≤ ht (ts s) v) {g : Nat} (hg : g ∈ order (ts s) v) (hgd : (nd (ts s)
  g).draining = true) :
    (nd (ts s) g).t1 ∈ (nd (ts s) v).children ∧ (nd (ts s) g).t2 ∈ (nd (ts s) v).children ∧
      [(nd (ts s) g).t1, (nd (ts s) g).t2] <:+: (nd (ts s) v).children ∧
      [(nd (ts s) g).t1, g, (nd (ts s) g).t2] <:+: order (ts s) v := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hn, hh, -⟩ := (sp_entry hpc hv0 hI hlp hg).2 h2
  have hgh : ghostN (ts s) g := ⟨hn, hgd⟩
  have hp := sp_par hpc hv0 hI hlp hg
  unfold par at hp; rw [ite_eq_right (by omega), ite_eq_left hgd] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinf2, hinf3⟩ := S.ghost g hgh
  rw [hp] at hinf2
  have hent : Ent ord (ht (ts s) g) g := (S.ordMem _ (by omega) (by
    have := (sd_ht hpc hv0 hI hlp).2; change _ ≤ s.P.H; omega) g).mpr ⟨hn, rfl⟩
  have hT : v ∈ tabs (ts s) (ht (ts s) g) g := (S.tabsIff _ g v hent).mpr ⟨hvl.1, by omega, hg⟩
  have hw := S.W1 g hgh v hT
  exact ⟨hinf2.subset (by simp), hinf2.subset (by simp), hinf2, hw⟩

/-- The drain's side list is no longer than `v`'s table. -/
theorem sp_side_len {side : List (Nat × Side)} (hs : sSideO (wiC s v) v = some side) :
    side.length ≤ (order (ts s) v).length := by
  obtain ⟨-, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI
  have hord : ((wiC s v).nodes.getX v).order = order (ts s) v := (wiC_sameTree s v).order v
  have hh : ((wiC s v).nodes.getX v).height = ht (ts s) v := (wiC_sameTree s v).height v
  unfold sSideO drainSide sB at hs
  rw [sd_kids_eq, hord, hh] at hs
  have h0 := length_sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)
  split at hs
  · have hk : ∀ e ∈ drainEntries (wiC s v).nodes ((wiC s v).nodes.getX v),
        (lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0))
          e).isSome := by
      intro e he
      have hem : e ∈ order (ts s) v := by rw [← hord]; exact List.mem_of_mem_filter he
      rw [hsp] at hnd hem ⊢
      rw [sidesOf_spec hnd e]
      simp only [List.mem_append, List.mem_cons] at hem
      split
      · rfl
      · split
        · rfl
        · next h1 h2 =>
          exfalso
          rcases hem with h | h | h
          · exact h1 h
          · exact h2 (Or.inl h)
          · exact h2 (Or.inr h)
    rw [length_fixSides _ _ _ _ hk hs]; exact h0
  · cases hs; exact h0

/-- **The sides** `startDrain` computes. -/
theorem sp_side : ∃ side, sSideO (wiC s v) v = some side ∧ ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts
        s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x := by
  have S := hI.shape
  obtain ⟨-, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI
  have hord : ((wiC s v).nodes.getX v).order = order (ts s) v := (wiC_sameTree s v).order v
  have hh : ((wiC s v).nodes.getX v).height = ht (ts s) v := (wiC_sameTree s v).height v
  unfold sSideO drainSide sB
  rw [sd_kids_eq, hord, hh]
  by_cases h2 : 2 ≤ ht (ts s) v
  · rw [ite_eq_left (by omega)]
    obtain ⟨side', h1, h2'⟩ := fixSides_spec (wiC s v).nodes (drainEntries (wiC s v).nodes ((wiC
      s v).nodes.getX v))
      (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (by
        intro e he hd
        have hd' : (nd (ts s) e).draining = true := by
          rw [← (wiC_sameTree s v).draining e]; exact hd
        have hem : e ∈ order (ts s) v := by rw [← hord]; exact List.mem_of_mem_filter he
        obtain ⟨ht1, -⟩ := sp_ghost hpc hv0 hI hlp h2 hem hd'
        obtain ⟨hn, -⟩ := (sp_entry hpc hv0 hI hlp hem).2 h2
        obtain ⟨g1, -⟩ := S.ghost e ⟨hn, hd'⟩
        have et1 : ((wiC s v).nodes.getX e).t1 = (nd (ts s) e).t1 := (wiC_sameTree s v).t1 e
        refine ⟨by rw [et1, show ((wiC s v).nodes.getX (nd (ts s) e).t1).draining = _ from
          (wiC_sameTree s v).draining _]; exact g1.2, ?_⟩
        rw [et1, hsp, sidesOf_spec (hsp ▸ hnd)]
        have hm := (sp_kids_sub hpc hv0 hI).subset ht1
        rw [hsp] at hm
        simp only [List.mem_append, List.mem_cons] at hm
        split_ifs <;> simp_all)
    refine ⟨side', h1, fun x => ?_⟩
    rw [h2']
    have e1 : ((wiC s v).nodes.getX x).draining = (nd (ts s) x).draining := (wiC_sameTree s
      v).draining x
    have e2 : ((wiC s v).nodes.getX x).t1 = (nd (ts s) x).t1 := (wiC_sameTree s v).t1 x
    rw [e1, e2]
    by_cases hx : x ∈ drainEntries (wiC s v).nodes ((wiC s v).nodes.getX v) ∧ (nd (ts s)
      x).draining = true
    · rw [ite_eq_left hx, ite_eq_left ⟨h2, hx⟩]
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx h.2)]
  · rw [ite_eq_right (by omega)]
    exact ⟨_, rfl, fun x => by rw [ite_eq_right (fun h => h2 h.1)]⟩

omit hpc hv0 hI hlp hTP hof hW in
theorem sw_entries {e : Nat} : e ∈ sEntries (wiC s v) v ↔ e ∈ order (ts s) v ∧
    (ht (ts s) v = 1 ∨ e ∈ (nd (ts s) v).children ∨ (nd (ts s) e).first ≠ NIL) := by
  unfold sEntries drainEntries
  rw [show ((wiC s v).nodes.getX v).order = order (ts s) v from (wiC_sameTree s v).order v,
    show ((wiC s v).nodes.getX v).height = ht (ts s) v from (wiC_sameTree s v).height v,
    show ((wiC s v).nodes.getX v).children = (nd (ts s) v).children from (wiC_sameTree s
      v).children v,
    List.mem_filter]
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, bne_iff_ne, ne_eq,
    show ((wiC s v).nodes.getX e).first = (nd (ts s) e).first from wiC_first s v e, or_assoc]

section side
variable {side : List (Nat × Side)} (hside : sSideO (wiC s v) v = some side)
  (hlook : ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts
        s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
include hlook

/-- **A child's side**: left before the boundary. -/
theorem sw_kid {e : Nat} (he : e ∈ (nd (ts s) v).children) :
    lookup side e = some (if e ∈ (nd (ts s) v).children.take (sK (wiC s v) v) then .left else
      .right) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨-, -, hk⟩ := S.kids v hvl
  obtain ⟨-, -, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  obtain ⟨-, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI
  have hsub := sp_kids_sub hpc hv0 hI
  rw [hlook]
  rw [ite_eq_right (fun h => by
    have := (hk e he).2 h.1
    rw [this.2] at h; exact absurd h.2.2 (by simp))]
  have hiff := mem_take_iff_left hsub hnd hkn he hsp
  rw [hsp, sidesOf_spec (hsp ▸ hnd)]
  have hm := hsub.subset he
  rw [hsp] at hm
  simp only [List.mem_append, List.mem_cons] at hm
  by_cases ht : e ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
  · rw [ite_eq_left (hiff.mp ht), ite_eq_left ht]
  · have hP : e ∉ P := fun h => ht (hiff.mpr h)
    rw [ite_eq_right hP, ite_eq_left (by tauto), ite_eq_right ht]

omit hlook in
/-- **A drain's targets among the children are not separated.** -/
theorem sw_nosep' (h2 : 2 ≤ ht (ts s) v) {a b g : Nat} (hinf : [a, b] <:+: (nd (ts s) v).children)
    (hg : g ≠ NIL) (ha : srcOf (ts s) a = g) (hb : srcOf (ts s) b = g) :
    a ∈ (nd (ts s) v).children.take (sK (wiC s v) v) ↔ b ∈ (nd (ts s) v).children.take (sK (wiC
      s v) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, -⟩ := S.kids v hvl
  obtain ⟨-, -, -, hsep, -⟩ := sd_cut2 hpc hv0 hI hlp hTP h2 hof hW
  obtain ⟨i, hi, e1, e2⟩ := infix_pair_idx hinf
  rw [← e1, ← e2]
  set k := sK (wiC s v) v
  by_cases hik : i + 1 < k
  · exact ⟨fun _ => getD_mem_take hi hik, fun _ => getD_mem_take (by omega) (by omega)⟩
  · by_cases hik' : k ≤ i
    · exact ⟨fun h => absurd h (getD_not_mem_take hnd (by omega) hik'),
        fun h => absurd h (getD_not_mem_take hnd hi (by omega))⟩
    · exfalso
      have hk : k = i + 1 := by omega
      have : sPr (wiC s v) v k = true := by
        unfold sPr drainPr sameDrainN
        rw [sd_kids_eq, hk, Nat.add_sub_cancel, e1, e2]
        have o1 : ((wiC s v).nodes.getX a).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX a).overflowOf = _ from (wiC_sameTree s v).overflowOf
            _]; exact ha
        have o2 : ((wiC s v).nodes.getX b).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX b).overflowOf = _ from (wiC_sameTree s v).overflowOf
            _]; exact hb
        rw [o1, o2]; simp [hg]
      rw [hsep] at this; exact absurd this (by simp)

omit hlook in
/-- **Pairs are not separated.** -/
theorem sw_nosep (h2 : 2 ≤ ht (ts s) v) {g : Nat} (hg : g ∈ order (ts s) v)
    (hgd : (nd (ts s) g).draining = true) :
    (nd (ts s) g).t1 ∈ (nd (ts s) v).children.take (sK (wiC s v) v) ↔
      (nd (ts s) g).t2 ∈ (nd (ts s) v).children.take (sK (wiC s v) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, -⟩ := S.kids v hvl
  obtain ⟨-, -, hinf, -⟩ := sp_ghost hpc hv0 hI hlp h2 hg hgd
  obtain ⟨-, -, -, hsep, -⟩ := sd_cut2 hpc hv0 hI hlp hTP h2 hof hW
  obtain ⟨i, hi, e1, e2⟩ := infix_pair_idx hinf
  rw [← e1, ← e2]
  set k := sK (wiC s v) v
  by_cases hik : i + 1 < k
  · exact ⟨fun _ => getD_mem_take hi hik, fun _ => getD_mem_take (by omega) (by omega)⟩
  · by_cases hik' : k ≤ i
    · exact ⟨fun h => absurd h (getD_not_mem_take hnd (by omega) hik'),
        fun h => absurd h (getD_not_mem_take hnd hi (by omega))⟩
    · exfalso
      have hk : k = i + 1 := by omega
      obtain ⟨hn, -⟩ := (sp_entry hpc hv0 hI hlp hg).2 h2
      obtain ⟨-, -, -, -, h5, h6, -⟩ := S.ghost g ⟨hn, hgd⟩
      have : sPr (wiC s v) v k = true := by
        unfold sPr drainPr sameDrainN
        rw [sd_kids_eq, hk, Nat.add_sub_cancel, e1, e2]
        have o1 : ((wiC s v).nodes.getX (nd (ts s) g).t1).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX (nd (ts s) g).t1).overflowOf = _ from (wiC_sameTree s
            v).overflowOf _]
          exact h5
        have o2 : ((wiC s v).nodes.getX (nd (ts s) g).t2).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX (nd (ts s) g).t2).overflowOf = _ from (wiC_sameTree s
            v).overflowOf _]
          exact h6
        rw [o1, o2]; simp [hn.1]
      rw [hsep] at this; exact absurd this (by simp)

/-- **A ghost entry goes with its first target.** -/
theorem sw_ghost (h2 : 2 ≤ ht (ts s) v) {g : Nat} (hg : g ∈ order (ts s) v)
    (hgd : (nd (ts s) g).draining = true) : lookup side g = lookup side (nd (ts s) g).t1 := by
  have S := hI.shape
  obtain ⟨ht1, ht2, -, hinf3⟩ := sp_ghost hpc hv0 hI hlp h2 hg hgd
  obtain ⟨-, -, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  obtain ⟨hbk, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI
  have hsub := sp_kids_sub hpc hv0 hI
  have hns := sw_nosep hpc hv0 hI hlp hTP hof hW h2 hg hgd
  have hk1 := sw_kid hpc hv0 hI hlp hTP hof hW hlook ht1
  rw [hk1, hlook g]
  have hsideT1 : lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0))
      (nd (ts s) g).t1 = some (if (nd (ts s) g).t1 ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
        then .left else .right) := by
    rw [← hk1, hlook, ite_eq_right]
    obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
    obtain ⟨-, -, hk⟩ := S.kids v hvl
    intro h; have := (hk _ ht1).2 h2; rw [this.2] at h; exact absurd h.2.2 (by simp)
  by_cases hge : 2 ≤ ht (ts s) v ∧ g ∈ sEntries (wiC s v) v ∧ (nd (ts s) g).draining = true
  · rw [ite_eq_left hge, hsideT1]
  · rw [ite_eq_right hge]
    -- the position of `g` is that of its targets
    have hiff1 := mem_take_iff_left hsub hnd hkn ht1 hsp
    have hiff2 := mem_take_iff_left hsub hnd hkn ht2 hsp
    have hbg : (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ≠ g := by
      intro e
      obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
      obtain ⟨-, -, hk⟩ := S.kids v hvl
      have := (hk _ hbk).2 h2; rw [e] at this; rw [this.2] at hgd; exact absurd hgd (by simp)
    have hb1 := before_of_infix2 (infix3_left hinf3)
    have hb2 := before_of_infix2 (infix3_right hinf3)
    rw [hsp] at hb1 hb2 hnd
    rw [hsp, sidesOf_spec hnd]
    have hgm := hb1.mem_right
    simp only [List.mem_append, List.mem_cons] at hgm
    by_cases ht : (nd (ts s) g).t1 ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
    · have hP2 : (nd (ts s) g).t2 ∈ P := hiff2.mp (hns.mp ht)
      have hgP : g ∈ P := (mem_left_iff_before hnd).mpr
        (hb2.trans ((mem_left_iff_before hnd).mp hP2) hnd)
      rw [ite_eq_left hgP, ite_eq_left ht]
    · have hP1 : (nd (ts s) g).t1 ∉ P := fun h => ht (hiff1.mpr h)
      have hgP : g ∉ P := fun h => hP1 ((mem_left_iff_before hnd).mpr
        (hb1.trans ((mem_left_iff_before hnd).mp h) hnd))
      have hgQ : g = (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ∨ g ∈ Q := by
        rcases hgm with h | h | h
        · exact absurd h hgP
        · exact absurd h.symm hbg
        · exact Or.inr h
      rw [ite_eq_right hgP, ite_eq_left hgQ, ite_eq_right ht]

/-- **The children of the two new nodes.** -/
theorem sw_ch : sCh1 (wiC s v) v side = (nd (ts s) v).children.take (sK (wiC s v) v) ∧
    sCh2 (wiC s v) v side = (nd (ts s) v).children.drop (sK (wiC s v) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, -⟩ := S.kids v hvl
  obtain ⟨f1, f2⟩ := filter_mem_take hnd (sK (wiC s v) v)
  unfold sCh1 sCh2
  rw [sd_kids_eq]
  constructor
  · rw [← f1]; apply List.filter_congr; intro e he
    rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook he]; split <;> simp_all
  · rw [← f2]; apply List.filter_congr; intro e he
    rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook he]; split <;> simp_all

/-- Children before the boundary and ghosts whose ranges lie between them. -/
theorem sw_left {e : Nat} : e ∈ sLeft (wiC s v) v side ↔
    e ∈ (nd (ts s) v).children.take (sK (wiC s v) v) ∨
      (2 ≤ ht (ts s) v ∧ e ∈ order (ts s) v ∧ (nd (ts s) e).draining = true ∧ (nd (ts s)
        e).first ≠ NIL ∧
        (nd (ts s) e).t1 ∈ (nd (ts s) v).children.take (sK (wiC s v) v)) := by
  have hsub := sp_kids_sub hpc hv0 hI
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  unfold sLeft
  rw [List.mem_filter, sw_entries]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨⟨hm, hcase⟩, hsd⟩
    by_cases hd : 2 ≤ ht (ts s) v ∧ (nd (ts s) e).draining = true
    · right
      rw [sw_ghost hpc hv0 hI hlp hTP hof hW hlook hd.1 hm hd.2] at hsd
      obtain ⟨ht1, -⟩ := sp_ghost hpc hv0 hI hlp hd.1 hm hd.2
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook ht1] at hsd
      refine ⟨hd.1, hm, hd.2, ?_, ?_⟩
      · rcases hcase with h | h | h
        · omega
        · exfalso
          obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
          obtain ⟨-, -, hk⟩ := (hI.shape).kids v hvl
          have := (hk e h).2 hd.1; rw [this.2] at hd; exact absurd hd.2 (by simp)
        · exact h
      · split at hsd
        · assumption
        · exact absurd hsd (by simp)
    · left
      have hk : e ∈ (nd (ts s) v).children := by
        by_cases h2 : 2 ≤ ht (ts s) v
        · apply ((sp_entry hpc hv0 hI hlp hm).2 h2).2.2
          simpa using (fun h => hd ⟨h2, h⟩)
        · exact (sp_entry hpc hv0 hI hlp hm).1 (by omega)
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook hk] at hsd
      split at hsd
      · assumption
      · exact absurd hsd (by simp)
  · rintro (h | ⟨h2, hm, hd, hf, ht1⟩)
    · have hk := List.mem_of_mem_take h
      refine ⟨⟨hsub.subset hk, Or.inr (Or.inl hk)⟩, ?_⟩
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook hk, ite_eq_left h]
    · refine ⟨⟨hm, Or.inr (Or.inr hf)⟩, ?_⟩
      rw [sw_ghost hpc hv0 hI hlp hTP hof hW hlook h2 hm hd]
      obtain ⟨ht1', -⟩ := sp_ghost hpc hv0 hI hlp h2 hm hd
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook ht1', ite_eq_left ht1]

/-- Children from the boundary onward and ghosts whose ranges lie between them. -/
theorem sw_right {e : Nat} : e ∈ sRight (wiC s v) v side ↔
    e ∈ (nd (ts s) v).children.drop (sK (wiC s v) v) ∨
      (2 ≤ ht (ts s) v ∧ e ∈ order (ts s) v ∧ (nd (ts s) e).draining = true ∧ (nd (ts s)
        e).first ≠ NIL ∧
        (nd (ts s) e).t1 ∈ (nd (ts s) v).children.drop (sK (wiC s v) v)) := by
  have hsub := sp_kids_sub hpc hv0 hI
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, hkk⟩ := S.kids v hvl
  have hdis : ∀ x ∈ (nd (ts s) v).children, (x ∈ (nd (ts s) v).children.drop (sK (wiC s v) v) ↔
      x ∉ (nd (ts s) v).children.take (sK (wiC s v) v)) := by
    intro x hx
    have hsp : (nd (ts s) v).children = (nd (ts s) v).children.take (sK (wiC s v) v) ++
        (nd (ts s) v).children.drop (sK (wiC s v) v) := (List.take_append_drop _ _).symm
    have hnd' := hsp ▸ hnd
    have hd := (List.nodup_append.mp hnd').2.2
    constructor
    · intro h h'; exact hd x h' x h rfl
    · intro h
      have := hx; rw [hsp, List.mem_append] at this
      rcases this with h' | h'
      · exact absurd h' h
      · exact h'
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  unfold sRight
  rw [List.mem_filter, sw_entries]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨⟨hm, hcase⟩, hsd⟩
    by_cases hd : 2 ≤ ht (ts s) v ∧ (nd (ts s) e).draining = true
    · right
      rw [sw_ghost hpc hv0 hI hlp hTP hof hW hlook hd.1 hm hd.2] at hsd
      obtain ⟨ht1, -⟩ := sp_ghost hpc hv0 hI hlp hd.1 hm hd.2
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook ht1] at hsd
      refine ⟨hd.1, hm, hd.2, ?_, ?_⟩
      · rcases hcase with h | h | h
        · omega
        · exfalso
          have := (hkk e h).2 hd.1; rw [this.2] at hd; exact absurd hd.2 (by simp)
        · exact h
      · split at hsd
        · exact absurd hsd (by simp)
        · next hn => exact (hdis _ ht1).mpr hn
    · left
      have hk : e ∈ (nd (ts s) v).children := by
        by_cases h2 : 2 ≤ ht (ts s) v
        · apply ((sp_entry hpc hv0 hI hlp hm).2 h2).2.2
          simpa using (fun h => hd ⟨h2, h⟩)
        · exact (sp_entry hpc hv0 hI hlp hm).1 (by omega)
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook hk] at hsd
      split at hsd
      · exact absurd hsd (by simp)
      · next hn => exact (hdis _ hk).mpr hn
  · rintro (h | ⟨h2, hm, hd, hf, ht1⟩)
    · have hk := List.mem_of_mem_drop h
      refine ⟨⟨hsub.subset hk, Or.inr (Or.inl hk)⟩, ?_⟩
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook hk, ite_eq_right ((hdis _ hk).mp h)]
    · refine ⟨⟨hm, Or.inr (Or.inr hf)⟩, ?_⟩
      rw [sw_ghost hpc hv0 hI hlp hTP hof hW hlook h2 hm hd]
      obtain ⟨ht1', -⟩ := sp_ghost hpc hv0 hI hlp h2 hm hd
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook ht1', ite_eq_right ((hdis _ ht1').mp ht1)]

end side

end parts

end OrderMaintenance.Proof.Top
