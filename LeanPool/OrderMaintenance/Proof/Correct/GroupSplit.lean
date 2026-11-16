/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Insert


/-!
# Starting a group split preserves INV-S (Lemma 3.2, `StartSplit`)

`startGroupSplit g` checks that `g` is alive (hence in the group list), computes guarded labels
for two new groups, allocates them (from the free list or fresh) and links them right before and
after `g`, in the group list and in `g`'s chunk. Their runs are empty, so the element list does
not change.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Running the pieces -/

theorem run_require_bind {β : Type} (b : Bool) (msg : String) (k : Unit → CM β) (s : Core) :
    (require b msg >>= k).run s = if b then (k ()).run s else .error (.guard msg) s := by
  unfold require; cases b <;> rfl

theorem labBefore_run (s : Core) (g : Nat) :
    (∃ lab, lab < gL s g ∧ (g ≠ cF s (gC s g) → gL s (gP s g) < lab) ∧
        (labBefore g).run s = .ok lab s) ∨
    (∃ msg, (labBefore g).run s = .error (.guard msg) s) := by
  unfold labBefore
  simp only [run_getP_bind, run_getG_bind, run_getC_bind]
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).first
  · rw [ite_eq_left (beq_iff_eq.mpr hf), run_before]
    by_cases hg : (s.Gs.getX g).lab < s.P.groupSpacing ∨ s.P.groupSpacing = 0
    · right; exact ⟨_, ite_eq_left hg⟩
    · left; refine ⟨(s.Gs.getX g).lab - s.P.groupSpacing, ?_, fun h => (h hf).elim, ite_eq_right hg⟩
      simp only [not_or] at hg; simp only [gL]; omega
  · rw [ite_eq_right (fun h => hf (beq_iff_eq.mp h))]
    simp only [run_getG_bind]
    rw [run_between]
    by_cases hg : (s.Gs.getX (s.Gs.getX g).prev).lab + 1 ≥ (s.Gs.getX g).lab
    · right; exact ⟨_, ite_eq_left hg⟩
    · left
      refine ⟨((s.Gs.getX (s.Gs.getX g).prev).lab + (s.Gs.getX g).lab) / 2, ?_, fun _ => ?_,
        ite_eq_right hg⟩ <;> simp only [gL, gP] <;> omega

theorem labAfter_run (s : Core) (g : Nat) :
    (∃ lab, gL s g < lab ∧ (g ≠ cLs s (gC s g) → lab < gL s (gN s g)) ∧
        (labAfter g).run s = .ok lab s) ∨
    (∃ msg, (labAfter g).run s = .error (.guard msg) s) := by
  unfold labAfter
  simp only [run_getP_bind, run_getG_bind, run_getC_bind]
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).last
  · rw [ite_eq_left (beq_iff_eq.mpr hf), run_after]
    by_cases hg : (s.Gs.getX g).lab + s.P.groupSpacing ≥ 1 <<< s.P.groupBits ∨
        (s.Gs.getX g).lab + s.P.groupSpacing ≤ (s.Gs.getX g).lab
    · right; exact ⟨_, ite_eq_left hg⟩
    · left; refine ⟨(s.Gs.getX g).lab + s.P.groupSpacing, ?_, fun h => (h hf).elim, ite_eq_right hg⟩
      simp only [not_or] at hg; simp only [gL]; omega
  · rw [ite_eq_right (fun h => hf (beq_iff_eq.mp h))]
    simp only [run_getG_bind]
    rw [run_between]
    by_cases hg : (s.Gs.getX g).lab + 1 ≥ (s.Gs.getX (s.Gs.getX g).next).lab
    · right; exact ⟨_, ite_eq_left hg⟩
    · left
      refine ⟨((s.Gs.getX g).lab + (s.Gs.getX (s.Gs.getX g).next).lab) / 2, ?_, fun _ => ?_,
        ite_eq_right hg⟩ <;> simp only [gL, gN] <;> omega

/-- Group allocation, as a pure function. -/
def allocGroup (s : Core) (c : Nat) : Nat × Core :=
  match s.freeG with
  | i :: rest => (i, { s with freeG := rest, Gs := s.Gs.set! i { chk := c } })
  | [] => (s.Gs.size, { s with Gs := s.Gs.push { chk := c } })

theorem newGroup_eq (c : Nat) : newGroup c = modifyGet (allocGroup · c) := rfl

theorem allocGroup_P (s : Core) (c : Nat) : (allocGroup s c).2.P = s.P := by
  unfold allocGroup; split <;> rfl

theorem run_newGroup_bind {β : Type} (c : Nat) (k : Nat → CM β) (s : Core) :
    (newGroup c >>= k).run s = (k (allocGroup s c).1).run (allocGroup s c).2 := rfl

@[simp] theorem run_newGroup (c : Nat) (s : Core) :
    (newGroup c).run s = .ok (allocGroup s c).1 (allocGroup s c).2 := rfl

theorem startGroupSplit_run (s : Core) (g : Nat) :
    (∃ labL labR, g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true ∧
        labL < gL s g ∧ (g ≠ cF s (gC s g) → gL s (gP s g) < labL) ∧
        gL s g < labR ∧ (g ≠ cLs s (gC s g) → labR < gL s (gN s g)) ∧
        (startGroupSplit g).run s =
          .ok () (linkGroupPair (allocGroup (allocGroup s (gC s g)).2 (gC s g)).2 g
            (allocGroup s (gC s g)).1
            (allocGroup (allocGroup s (gC s g)).2 (gC s g)).1 labL labR)) ∨
    (∃ msg, (startGroupSplit g).run s = .error (.guard msg) s) := by
  unfold startGroupSplit
  simp only [run_getG_bind, run_get_bind, run_require_bind]
  by_cases ha : (g != NIL && decide (g < s.Gs.size) && (s.Gs.getX g).alive) = true
  · rw [ite_eq_left ha]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at ha
    rw [run_bind]
    rcases labBefore_run s g with ⟨labL, h1, h2, hr⟩ | ⟨msg, hr⟩
    · rw [hr]
      simp only
      rw [run_bind]
      rcases labAfter_run s g with ⟨labR, h3, h4, hr'⟩ | ⟨msg, hr'⟩
      · rw [hr']
        left
        exact ⟨labL, labR, ha.1.1, ha.1.2, ha.2, h1, h2, h3, h4, by simp [gC]⟩
      · rw [hr']; right; exact ⟨msg, rfl⟩
    · rw [hr]; right; exact ⟨msg, rfl⟩
  · rw [ite_eq_right ha]; right; exact ⟨_, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Allocation -/

/-- What allocation needs: the free list holds unused allocated indices. -/
structure FreeOK (s : Core) (L : List Nat) : Prop where
  pos : 1 ≤ s.Gs.size
  mem : ∀ g ∈ L, g < s.Gs.size
  free : ∀ g ∈ s.freeG, 1 ≤ g ∧ g < s.Gs.size ∧ g ∉ L
  nodup : s.freeG.Nodup

theorem INV.freeOK {s : Core} {A : Abs} (h : INV s A) : FreeOK s A.glist :=
  ⟨h.gPos, h.gAlloc, h.free, h.freeNodup⟩

theorem allocGroup_spec {s : Core} {L : List Nat} (h : FreeOK s L) (c : Nat) :
    let p := allocGroup s c
    p.1 ∉ L ∧ 1 ≤ p.1 ∧ p.1 < p.2.Gs.size ∧ p.2.Gs.getX p.1 = { chk := c } ∧
      (∀ b, b ≠ p.1 → p.2.Gs.getX b = s.Gs.getX b) ∧ p.1 ∉ p.2.freeG ∧
      s.Gs.size ≤ p.2.Gs.size ∧ (∀ b ∈ p.2.freeG, b ∈ s.freeG) ∧ FreeOK p.2 L ∧
      (∀ b, b < s.Gs.size → b ∉ s.freeG → b ≠ p.1) ∧
      p.2.E = s.E ∧ p.2.C = s.C ∧ p.2.head = s.head ∧ p.2.tail = s.tail ∧
      p.2.firstGroup = s.firstGroup ∧ p.2.firstChunk = s.firstChunk ∧
      p.2.Gs.size ≤ s.Gs.size + 1 ∧ (s.Gs.size < p.2.Gs.size → p.1 = s.Gs.size) := by
  unfold allocGroup
  rcases hf : s.freeG with _ | ⟨i, rest⟩
  · simp only
    refine ⟨fun hm => by have := h.mem _ hm; omega, h.pos, by simp, by simp, ?_, by simp,
      by simp, by simp, ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, by simp,
      by simp⟩
    · intro b hb; simp [hb]
    · refine ⟨by simp, fun g hg => by have := h.mem g hg; simp; omega, by simp, by simp⟩
    · intro b hb _; omega
  · simp only
    have hi := h.free i (by simp [hf])
    have hnd := h.nodup
    rw [hf] at hnd
    simp only [List.nodup_cons] at hnd
    refine ⟨hi.2.2, hi.1, by simp [hi.2.1], by simp [hi.2.1], ?_, hnd.1, by simp,
      fun b hb => by simp [hb], ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial,
      by simp, fun h => by simp at h⟩
    · intro b hb; simp [Ne.symm hb]
    · refine ⟨by simp [h.pos], fun g hg => by simpa using h.mem g hg, fun g hg => ?_, hnd.2⟩
      have := h.free g (by simp [hf, hg]); simpa using this
    · intro b _ hb e; subst e; exact hb (by simp [])

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Lists -/

theorem replace1_mid {l1 l2 ys : List Nat} {x : Nat} (h : x ∉ l1) :
    (l1 ++ x :: l2).replace1 x ys = l1 ++ ys ++ l2 := by
  induction l1 with
  | nil => simp [List.replace1]
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at h
    simp [List.replace1, Ne.symm h.1, ih h.2]

theorem replace1_not_mem {l ys : List Nat} {x : Nat} (h : x ∉ l) : l.replace1 x ys = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at h
    simp [List.replace1, Ne.symm h.1, ih h.2]

theorem replace1_append (x : Nat) (ys a b : List Nat) :
    (a ++ b).replace1 x ys = if x ∈ a then a.replace1 x ys ++ b else a ++ b.replace1 x ys := by
  induction a with
  | nil => simp
  | cons c t ih =>
    simp only [List.cons_append, List.replace1, List.mem_cons]
    by_cases hc : c = x
    · simp [hc]
    · simp only [hc, ite_false, ih, Ne.symm hc, false_or]
      split <;> simp

theorem flatMap_replace1 {L : List Nat} {F F' : Nat → List Nat} {c g : Nat} {ys : List Nat}
    (hnd : (L.flatMap F).Nodup) (hcnd : L.Nodup) (hc : c ∈ L) (hg : g ∈ F c)
    (hF : ∀ b, F' b = if b = c then (F c).replace1 g ys else F b) :
    L.flatMap F' = (L.flatMap F).replace1 g ys := by
  induction L with
  | nil => simp at hc
  | cons b t ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    rw [replace1_append, hF b]
    simp only [List.nodup_cons] at hcnd
    by_cases hb : b = c
    · subst hb
      simp only [ite_true, hg]
      congr 1
      refine List.flatMap_congr fun b' hb' => ?_
      rw [hF b', ite_eq_right (fun (e : b' = b) => hcnd.1 (e ▸ hb'))]
    · have hgb : g ∉ F b := by
        intro hgb
        have hct : c ∈ t := by simpa [Ne.symm hb] using hc
        have : g ∈ t.flatMap F := List.mem_flatMap.mpr ⟨c, hct, hg⟩
        exact (List.nodup_append.mp hnd).2.2 g hgb g this rfl
      simp only [hb, ite_false, hgb]
      congr 1
      exact ih (List.nodup_append.mp hnd).2.1 hcnd.2 (by simpa [Ne.symm hb] using hc)

/-- Sortedness after inserting `a` before and `b` after `x`. -/
theorem isChain_around {l1 l2 : List Nat} {x a b : Nat} {f f' : Nat → Nat}
    (hs : ((l1 ++ x :: l2).map f).IsChain (· < ·)) (hagree : ∀ z ∈ l1 ++ x :: l2, f' z = f z)
    (ha1 : ∀ w ∈ l1.getLast?, f w < f' a) (ha2 : f' a < f x) (hb1 : f x < f' b)
    (hb2 : ∀ w ∈ l2.head?, f' b < f w) :
    ((l1 ++ a :: x :: b :: l2).map f').IsChain (· < ·) := by
  have e1 : l1.map f' = l1.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have e2 : l2.map f' = l2.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have ex : f' x = f x := hagree x (by simp)
  simp only [List.map_append, List.map_cons, e1, e2, ex] at hs ⊢
  rw [List.isChain_append] at hs ⊢
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨ha2, hb1, ?_⟩
    rw [List.isChain_cons]
    refine ⟨fun w hw => ?_, (List.isChain_cons.mp h2).2⟩
    cases l2 with
    | nil => simp at hw
    | cons c t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hw
      subst hw; exact hb2 c (by simp)
  · intro u hu v hv
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
    subst hv
    rcases l1.eq_nil_or_concat with h | ⟨l1', w, rfl⟩
    · subst h; simp at hu
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
        Option.some.injEq] at hu
      subst hu; exact ha1 w (by simp)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The records after `linkGroupPair` -/

section link
variable (s : Core) (g gl gr labL labR : Nat)

/-- The hypotheses under which `linkGroupPair` does what it should: distinct indices, in range. -/
structure LinkOK : Prop where
  szl : gl < s.Gs.size
  szr : gr < s.Gs.size
  szg : g < s.Gs.size
  szp : gP s g ≠ NIL → gP s g < s.Gs.size
  szn : gN s g ≠ NIL → gN s g < s.Gs.size
  d1 : gl ≠ gr
  d2 : gl ≠ g
  d3 : gr ≠ g
  d4 : gP s g ≠ gl
  d5 : gP s g ≠ gr
  d6 : gN s g ≠ gl
  d7 : gN s g ≠ gr
  d8 : gP s g ≠ g
  d9 : gN s g ≠ g
  d10 : gP s g ≠ NIL → gP s g ≠ gN s g

variable {s g gl gr labL labR}

theorem LinkOK.gN' (h : LinkOK s g gl gr) (z : Nat) :
    gN (linkGroupPair s g gl gr labL labR) z =
      if z = g then gr else if z = gl then g else if z = gr then gN s g
      else if z = gP s g ∧ gP s g ≠ NIL then gl else gN s z := by
  obtain ⟨szl, szr, szg, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [gN, gP] at *
  generalize hp : (s.Gs.getX g).prev = p at *
  generalize hn : (s.Gs.getX g).next = n at *
  simp only [linkGroupPair, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.next)]
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3; have e4 := Ne.symm d4
  have e5 := Ne.symm d5; have e6 := Ne.symm d6; have e7 := Ne.symm d7; have e8 := Ne.symm d8
  have e9 := Ne.symm d9
  by_cases hzg : z = g
  · simp [hzg, szg,       ]
  · have hzg' := Ne.symm hzg
    by_cases hzl : z = gl
    · simp [hzl, szl,  d2, e1, e2, d4, d6, ]
    · have hzl' := Ne.symm hzl
      by_cases hzr : z = gr
      · simp [hzr, szr,  d3, e1, e3,  d7, ]
      · have hzr' := Ne.symm hzr
        by_cases hp0 : p = NIL
        · simp [hzg, hzg', hzl, hzl', hzr, hzr', hp0]
        · by_cases hzp : z = p
          · subst hzp
            have := d10 hp0
            simp [hzg, hzl, hzr, hzg',  hzr', hp0, szp hp0,  Ne.symm this]
          · simp [hzg, hzg', hzl, hzl', hzr, hzr', hp0, hzp, Ne.symm hzp]

theorem LinkOK.gP' (h : LinkOK s g gl gr) (z : Nat) :
    gP (linkGroupPair s g gl gr labL labR) z =
      if z = g then gl else if z = gl then gP s g else if z = gr then g
      else if z = gN s g ∧ gN s g ≠ NIL then gr else gP s z := by
  obtain ⟨szl, szr, szg, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [gN, gP] at *
  generalize hp : (s.Gs.getX g).prev = p at *
  generalize hn : (s.Gs.getX g).next = n at *
  simp only [linkGroupPair, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.prev)]
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3; have e4 := Ne.symm d4
  have e5 := Ne.symm d5; have e6 := Ne.symm d6; have e7 := Ne.symm d7; have e8 := Ne.symm d8
  have e9 := Ne.symm d9
  by_cases hzg : z = g
  · simp [hzg, szg,      ]
  · have hzg' := Ne.symm hzg
    by_cases hzl : z = gl
    · simp [hzl, szl,  d2, e1, e2, d4, d6, ]
    · have hzl' := Ne.symm hzl
      by_cases hzr : z = gr
      · simp [hzr, szr,  d3, e1, e3,  d7, ]
      · have hzr' := Ne.symm hzr
        by_cases hn0 : n = NIL
        · simp [hzg, hzg', hzl, hzl', hzr, hzr', hn0]
        · by_cases hzn : z = n
          · subst hzn
            simp [hzg, hzl, hzr, hzg',   hn0, szn hn0]
          · simp [hzg, hzg', hzl, hzl', hzr, hzr', hn0, hzn, Ne.symm hzn]

theorem linkGroupPair_gF (z : Nat) : gF (linkGroupPair s g gl gr labL labR) z = gF s z := by
  simp only [linkGroupPair, gF, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.first)]
  split_ifs <;> rfl

theorem linkGroupPair_gLs (z : Nat) : gLs (linkGroupPair s g gl gr labL labR) z = gLs s z := by
  simp only [linkGroupPair, gLs, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.last)]
  split_ifs <;> rfl

theorem linkGroupPair_gC (z : Nat) : gC (linkGroupPair s g gl gr labL labR) z = gC s z := by
  simp only [linkGroupPair, gC, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.chk)]
  split_ifs <;> rfl

theorem linkGroupPair_gA (z : Nat) : gA (linkGroupPair s g gl gr labL labR) z = gA s z := by
  simp only [linkGroupPair, gA, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.alive)]
  split_ifs <;> rfl

theorem LinkOK.gL' (h : LinkOK s g gl gr) (z : Nat) :
    gL (linkGroupPair s g gl gr labL labR) z =
      if z = gl then labL else if z = gr then labR else gL s z := by
  obtain ⟨szl, szr, szg, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [gN, gP] at *
  generalize hp : (s.Gs.getX g).prev = p at *
  generalize hn : (s.Gs.getX g).next = n at *
  simp only [linkGroupPair, gL, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.lab)]
  by_cases hzl : z = gl
  · simp [hzl, szl,   Ne.symm d1, Ne.symm d2, d4, d6, ]
  · by_cases hzr : z = gr
    · simp [hzr, szr,   Ne.symm d1, Ne.symm d3,  d7, ]
    · simp [hzl, hzr, Ne.symm hzl, Ne.symm hzr]

theorem linkGroupPair_Gsize : (linkGroupPair s g gl gr labL labR).Gs.size = s.Gs.size := by
  simp only [linkGroupPair, Array.size_modify', Array.size_ite]; split_ifs <;> rfl

theorem linkGroupPair_C (z : Nat) (hc : gC s g < s.C.size) :
    (linkGroupPair s g gl gr labL labR).C.getX z =
      if z = gC s g then
        { s.C.getX z with
          first := if cF s (gC s g) = g then gl else cF s (gC s g)
          last := if cLs s (gC s g) = g then gr else cLs s (gC s g) }
      else s.C.getX z := by
  simp only [linkGroupPair, gC, cF, cLs, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, beq_iff_eq] at *
  by_cases hz : z = (s.Gs.getX g).chk
  · subst hz; split_ifs <;> simp_all
  · simp [hz, Ne.symm hz]

theorem linkGroupPair_rest :
    (linkGroupPair s g gl gr labL labR).E = s.E ∧
      (linkGroupPair s g gl gr labL labR).C.size = s.C.size ∧
      (linkGroupPair s g gl gr labL labR).freeG = s.freeG ∧
      (linkGroupPair s g gl gr labL labR).head = s.head ∧
      (linkGroupPair s g gl gr labL labR).tail = s.tail ∧
      (linkGroupPair s g gl gr labL labR).firstChunk = s.firstChunk ∧
      (linkGroupPair s g gl gr labL labR).firstGroup =
        (if gP s g ≠ NIL then s.firstGroup else gl) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [linkGroupPair, Array.size_modify', Array.size_ite]; split_ifs <;> rfl
  · simp only [linkGroupPair, gP, bne_iff_ne, ne_eq]

end link

end OrderMaintenance.Proof


namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The abstract nesting after a split start: `gl`, `g`, `gr` in place of `g` in chunk `c`, with
empty runs for `gl` and `gr`. -/
def Abs.splitStart (A : Abs) (c g gl gr : Nat) : Abs where
  chunks := A.chunks
  grps := fun c' => if c' = c then (A.grps c).replace1 g [gl, g, gr] else A.grps c'
  elts := fun b => if b = gl ∨ b = gr then [] else A.elts b

theorem INV.mem_of_alive {s : Core} {A : Abs} (h : INV s A) {g : Nat} (h0 : g ≠ NIL)
    (hs : g < s.Gs.size) (ha : gA s g = true) : g ∈ A.glist :=
  (h.gAlive g (by unfold NIL at h0; omega) hs).mp ha

theorem INV.gP_mem {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gP s g = NIL ∨ gP s g ∈ A.glist := by
  rw [h.gList.prev g hg]
  rcases predOf_mem_or (l := A.glist) (x := g) with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

theorem INV.gN_mem {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gN s g = NIL ∨ gN s g ∈ A.glist := by
  rw [h.gList.next g hg]
  rcases succOf_mem_or (l := A.glist) (x := g) with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

/-- Concrete field changes and fresh indices produced by starting a group split. -/
structure GroupSplitFrame (s t : Core) (A : Abs) (g gl gr labL labR : Nat) : Prop where
  leftFresh : gl ∉ A.glist
  rightFresh : gr ∉ A.glist
  distinct : gl ≠ gr
  leftNonzero : gl ≠ NIL
  rightNonzero : gr ≠ NIL
  leftBound : gl < t.Gs.size
  rightBound : gr < t.Gs.size
  sizeMonotone : s.Gs.size ≤ t.Gs.size
  newIndex : ∀ b, b < t.Gs.size → b < s.Gs.size ∨ b = gl ∨ b = gr
  freeSub : ∀ b ∈ t.freeG, b ∈ s.freeG ∧ b ≠ gl ∧ b ≠ gr
  freeNodup : t.freeG.Nodup
  groupNext : ∀ z, gN t z = if z = g then gr else if z = gl then g else if z = gr then gN s g
    else if z = gP s g ∧ gP s g ≠ NIL then gl else gN s z
  groupPrevious : ∀ z, gP t z = if z = g then gl else if z = gl then gP s g else if z = gr then g
    else if z = gN s g ∧ gN s g ≠ NIL then gr else gP s z
  groupFirst : ∀ z, gF t z = if z = gl ∨ z = gr then NIL else gF s z
  groupLast : ∀ z, gLs t z = if z = gl ∨ z = gr then NIL else gLs s z
  groupChunk : ∀ z, gC t z = if z = gl ∨ z = gr then gC s g else gC s z
  groupAlive : ∀ z, gA t z = if z = gl ∨ z = gr then true else gA s z
  groupLabel : ∀ z, gL t z = if z = gl then labL else if z = gr then labR else gL s z
  chunkRead : ∀ z, t.C.getX z = if z = gC s g then
    { s.C.getX z with first := if cF s (gC s g) = g then gl else cF s (gC s g),
                      last := if cLs s (gC s g) = g then gr else cLs s (gC s g) }
    else s.C.getX z
  elements : t.E = s.E
  head : t.head = s.head
  tail : t.tail = s.tail
  firstChunk : t.firstChunk = s.firstChunk
  firstGroup : t.firstGroup = if gP s g ≠ NIL then s.firstGroup else gl
  chunksSize : t.C.size = s.C.size
  parameters : t.P = s.P

theorem groupSplit_frame {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
    (hg : g ∈ A.glist) (labL labR : Nat) :
    let left := allocGroup s (gC s g)
    let right := allocGroup left.2 (gC s g)
    GroupSplitFrame s (linkGroupPair right.2 g left.1 right.1 labL labR)
      A g left.1 right.1 labL labR := by
  dsimp only
  have hgs : g < s.Gs.size := hI.gAlloc g hg
  have hg0 : g ≠ NIL := fun e => hI.gList.nonil (e ▸ hg)
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc ⊢
  -- the two allocations
  have hF := hI.freeOK
  obtain ⟨al1, al2, al3, al4, al5, al6, al7, al8, hF1, al10, alE, alC, alH, alT, alFG, alFC,
    alS1, alS2⟩ := allocGroup_spec hF c
  have alP := allocGroup_P s c
  generalize hp1 : allocGroup s c = p1 at *
  obtain ⟨gl, s1⟩ := p1
  simp only at al1 al2 al3 al4 al5 al6 al7 al8 hF1 al10 alE alC alH alT alFG alFC alS1 alS2
  obtain ⟨bl1, bl2, bl3, bl4, bl5, bl6, bl7, bl8, hF2, bl10, blE, blC, blH, blT, blFG, blFC,
    blS1, blS2⟩ := allocGroup_spec hF1 c
  have blP := allocGroup_P s1 c
  generalize hp2 : allocGroup s1 c = p2 at *
  obtain ⟨gr, s2⟩ := p2
  simp only at bl1 bl2 bl3 bl4 bl5 bl6 bl7 bl8 hF2 bl10 blE blC blH blT blFG blFC blS1 blS2
  -- basic facts
  have hglr : gl ≠ gr := bl10 gl al3 al6
  have hggl : g ≠ gl := fun e => al1 (e ▸ hg)
  have hggr : g ≠ gr := fun e => bl1 (e ▸ hg)
  have hs2G : ∀ z, z ≠ gl → z ≠ gr → s2.Gs.getX z = s.Gs.getX z := by
    intro z h1 h2; rw [bl5 z h2, al5 z h1]
  have hs2gl : s2.Gs.getX gl = { chk := c } := by rw [bl5 gl hglr, al4]
  have hs2gr : s2.Gs.getX gr = { chk := c } := bl4
  have hsz12 : s.Gs.size ≤ s2.Gs.size := le_trans al7 bl7
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have hp2 : gP s2 g = p := by simp only [gP, hs2G g hggl hggr]; exact hpdef
  have hn2 : gN s2 g = n := by simp only [gN, hs2G g hggl hggr]; exact hndef
  have hpm : p = NIL ∨ p ∈ A.glist := hpdef ▸ hI.gP_mem hg
  have hnm : n = NIL ∨ n ∈ A.glist := hndef ▸ hI.gN_mem hg
  have hgl0 : gl ≠ NIL := by unfold NIL; omega
  have hgr0 : gr ≠ NIL := by unfold NIL; omega
  have hpgl : p ≠ gl := by
    rcases hpm with h | h <;> intro e
    · exact hgl0 (e ▸ h)
    · exact al1 (e ▸ h)
  have hpgr : p ≠ gr := by
    rcases hpm with h | h <;> intro e
    · exact hgr0 (e ▸ h)
    · exact bl1 (e ▸ h)
  have hngl : n ≠ gl := by
    rcases hnm with h | h <;> intro e
    · exact hgl0 (e ▸ h)
    · exact al1 (e ▸ h)
  have hngr : n ≠ gr := by
    rcases hnm with h | h <;> intro e
    · exact hgr0 (e ▸ h)
    · exact bl1 (e ▸ h)
  have hpg : p ≠ g := by
    rw [← hpdef, hI.gList.prev g hg]; exact predOf_ne_self hI.gList.nodup g hg0
  have hng : n ≠ g := by
    rw [← hndef, hI.gList.next g hg]; exact succOf_ne_self hI.gList.nodup g hg0
  have hpn : p ≠ NIL → p ≠ n := by
    intro h0; rw [← hpdef, ← hndef, hI.gList.prev g hg, hI.gList.next g hg]
    exact predOf_ne_succOf hI.gList.nodup hg (by rw [← hI.gList.prev g hg, hpdef]; exact h0)
  have hLink : LinkOK s2 g gl gr := by
    refine ⟨by omega, bl3, by omega, fun h => ?_, fun h => ?_, hglr, Ne.symm hggl, Ne.symm hggr,
      by rw [hp2]; exact hpgl, by rw [hp2]; exact hpgr, by rw [hn2]; exact hngl,
      by rw [hn2]; exact hngr, by rw [hp2]; exact hpg, by rw [hn2]; exact hng,
      fun h => by rw [hp2, hn2] at *; exact hpn h⟩
    · rw [hp2] at h ⊢
      rcases hpm with h' | h'
      · exact absurd h' h
      · have := hI.gAlloc p h'; omega
    · rw [hn2] at h ⊢
      rcases hnm with h' | h'
      · exact absurd h' h
      · have := hI.gAlloc n h'; omega
  -- the new state's accessors, in terms of `s`
  set s' := linkGroupPair s2 g gl gr labL labR with hs'
  obtain ⟨rE, rCs, rF, rH, rT, rFC, rFG⟩ := linkGroupPair_rest (s := s2) (g := g) (gl := gl)
    (gr := gr) (labL := labL) (labR := labR)
  have gN' : ∀ z, gN s' z = if z = g then gr else if z = gl then g else if z = gr then n
      else if z = p ∧ p ≠ NIL then gl else gN s z := by
    intro z
    rw [hLink.gN' z, hp2, hn2]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [h2, hggl.symm]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    simp only [h1, h2, h3, ite_false]
    split_ifs <;> simp [gN, hs2G z h2 h3]
  have gP' : ∀ z, gP s' z = if z = g then gl else if z = gl then p else if z = gr then g
      else if z = n ∧ n ≠ NIL then gr else gP s z := by
    intro z
    rw [hLink.gP' z, hp2, hn2]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [h2, hggl.symm]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    simp only [h1, h2, h3, ite_false]
    split_ifs <;> simp [gP, hs2G z h2 h3]
  have gF' : ∀ z, gF s' z = if z = gl ∨ z = gr then NIL else gF s z := by
    intro z; rw [linkGroupPair_gF]
    by_cases h2 : z = gl; · simp [h2, gF, hs2gl]
    by_cases h3 : z = gr; · simp [h3, gF, hs2gr]
    simp [h2, h3, gF, hs2G z h2 h3]
  have gLs' : ∀ z, gLs s' z = if z = gl ∨ z = gr then NIL else gLs s z := by
    intro z; rw [linkGroupPair_gLs]
    by_cases h2 : z = gl; · simp [h2, gLs, hs2gl]
    by_cases h3 : z = gr; · simp [h3, gLs, hs2gr]
    simp [h2, h3, gLs, hs2G z h2 h3]
  have gC' : ∀ z, gC s' z = if z = gl ∨ z = gr then c else gC s z := by
    intro z; rw [linkGroupPair_gC]
    by_cases h2 : z = gl; · simp [h2, gC, hs2gl]
    by_cases h3 : z = gr; · simp [h3, gC, hs2gr]
    simp [h2, h3, gC, hs2G z h2 h3]
  have gA' : ∀ z, gA s' z = if z = gl ∨ z = gr then true else gA s z := by
    intro z; rw [linkGroupPair_gA]
    by_cases h2 : z = gl; · simp [h2, gA, hs2gl]
    by_cases h3 : z = gr; · simp [h3, gA, hs2gr]
    simp [h2, h3, gA, hs2G z h2 h3]
  have gL' : ∀ z, gL s' z = if z = gl then labL else if z = gr then labR else gL s z := by
    intro z; rw [hLink.gL' z]
    by_cases h2 : z = gl; · simp [h2]
    by_cases h3 : z = gr; · simp [h3, hglr.symm]
    simp [h2, h3, gL, hs2G z h2 h3]
  have hcs : c < s.C.size := ((hI.cAlloc c).mp hc).2
  have hC' : ∀ z, s'.C.getX z = if z = c then
      { s.C.getX z with first := if cF s c = g then gl else cF s c,
                        last := if cLs s c = g then gr else cLs s c } else s.C.getX z := by
    intro z
    have := linkGroupPair_C (s := s2) (g := g) (gl := gl) (gr := gr) (labL := labL)
      (labR := labR) z (by
      simp only [gC, hs2G g hggl hggr, blC, alC]
      rw [← hcdef] at hcs; exact hcs)
    simp only [gC, hs2G g hggl hggr, blC, alC, cF, cLs] at this
    rw [show (s.Gs.getX g).chk = c from hcdef] at this
    exact this
  have hE' : s'.E = s.E := by rw [rE, blE, alE]
  have hH' : s'.head = s.head := by rw [rH, blH, alH]
  have hT' : s'.tail = s.tail := by rw [rT, blT, alT]
  have hFC' : s'.firstChunk = s.firstChunk := by rw [rFC, blFC, alFC]
  have hFG' : s'.firstGroup = if p ≠ NIL then s.firstGroup else gl := by
    rw [rFG, hp2, blFG, alFG]
  have hCs' : s'.C.size = s.C.size := by rw [rCs, blC, alC]
  have hGs' : s'.Gs.size = s2.Gs.size := linkGroupPair_Gsize
  change GroupSplitFrame s s' A g gl gr labL labR
  refine
    { leftFresh := al1, rightFresh := bl1, distinct := hglr,
      leftNonzero := hgl0, rightNonzero := hgr0,
      leftBound := by rw [hGs']; omega,
      rightBound := by rw [hGs']; exact bl3,
      sizeMonotone := by rw [hGs']; exact hsz12,
      newIndex := ?_, freeSub := ?_,
      freeNodup := by rw [rF]; exact hF2.nodup,
      groupNext := by simpa only [hpdef, hndef] using gN',
      groupPrevious := by simpa only [hpdef, hndef] using gP',
      groupFirst := gF', groupLast := gLs',
      groupChunk := by simpa only [hcdef] using gC',
      groupAlive := gA', groupLabel := gL',
      chunkRead := by simpa only [hcdef] using hC',
      elements := hE', head := hH', tail := hT', firstChunk := hFC',
      firstGroup := by simpa only [hpdef] using hFG', chunksSize := hCs',
      parameters := by simp only at alP blP; rw [hs', ← alP, ← blP]; rfl }
  · intro b hb
    rw [hGs'] at hb
    by_cases hb0 : b < s.Gs.size
    · exact Or.inl hb0
    · right
      by_cases hb1 : b < s1.Gs.size
      · left; have := alS2 (by omega); omega
      · right; have := blS2 (by omega); omega
  · intro b hb
    rw [rF] at hb
    exact ⟨al8 b (bl8 b hb), fun e => al6 (e ▸ bl8 b hb), fun e => bl6 (e ▸ hb)⟩

variable {s t : Core} {A : Abs} {g gl gr labL labR : Nat}

theorem GroupSplitFrame.groupList (F : GroupSplitFrame s t A g gl gr labL labR)
    (hI : INV s A) (hg : g ∈ A.glist) :
    LList (gN t) (gP t) t.firstGroup (A.splitStart (gC s g) g gl gr).glist := by
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc ⊢
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have gN' := F.groupNext
  have gP' := F.groupPrevious
  have hFG' := F.firstGroup
  simp only [hpdef, hndef] at gN' gP'
  simp only [hpdef] at hFG'
  have al1 := F.leftFresh
  have bl1 := F.rightFresh
  have hglr := F.distinct
  have hgl0 := F.leftNonzero
  have hgr0 := F.rightNonzero
  have hggl : g ≠ gl := fun e => al1 (e ▸ hg)
  have hggr : g ≠ gr := fun e => bl1 (e ▸ hg)
  have hgnd := hI.gList.nodup
  obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hg
  have hnd' := hgnd
  rw [hsplit] at hnd'
  have hg1 : g ∉ l1 := fun h => (List.nodup_append.mp hnd').2.2 g h g (by simp) rfl
  have hgl' : (A.splitStart c g gl gr).glist = l1 ++ gl :: g :: gr :: l2 := by
    have : (A.splitStart c g gl gr).glist = A.glist.replace1 g [gl, g, gr] :=
      flatMap_replace1 hgnd hI.cList.nodup hc hgc fun b => rfl
    rw [this, hsplit, replace1_mid hg1]; simp
  rw [hgl']
  have hL := hI.gList
  rw [hsplit] at hL
  have := LList.insert_around (nxt' := gN t) (prv' := gP t) hL (by rw [← hsplit]; exact al1)
    (by rw [← hsplit]; exact bl1) hglr hgl0 hgr0 (fun z hz => ?_) (fun z hz => ?_)
  · rw [hFG', hpdef] at *
    by_cases hp0 : p = NIL
    · rw [ite_eq_left hp0] at this; rw [ite_eq_right (not_not.mpr hp0)]; exact this
    · rw [ite_eq_right hp0] at this; rw [ite_eq_left hp0]; exact this
  · rw [gN', hpdef, hndef]
    have hz0 : z ≠ NIL := fun e => by
      rw [e] at hz; rcases mem_around_iff.mp hz with h | h | h
      · exact hgl0 h.symm
      · exact hgr0 h.symm
      · exact hI.gList.nonil (hsplit ▸ h)
    by_cases h1 : z = gl; · simp [h1, hggl.symm]
    by_cases h2 : z = g; · simp [h2, hggl]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    by_cases h4 : z = p
    · subst h4; simp [h1, h2, h3, hz0]
    · simp [h1, h2, h3, h4]
  · rw [gP', hpdef, hndef]
    have hz0 : z ≠ NIL := fun e => by
      rw [e] at hz; rcases mem_around_iff.mp hz with h | h | h
      · exact hgl0 h.symm
      · exact hgr0 h.symm
      · exact hI.gList.nonil (hsplit ▸ h)
    by_cases h1 : z = gl; · simp [h1, hggl.symm]
    by_cases h2 : z = g; · simp [h2, hggl]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    by_cases h4 : z = n
    · subst h4; simp [h1, h2, h3, hz0]
    · simp [h1, h2, h3, h4]

theorem GroupSplitFrame.groupSorted (F : GroupSplitFrame s t A g gl gr labL labR)
    (hI : INV s A) (hg : g ∈ A.glist)
    (hL1 : labL < gL s g) (hL2 : g ≠ cF s (gC s g) → gL s (gP s g) < labL)
    (hR1 : gL s g < labR) (hR2 : g ≠ cLs s (gC s g) → labR < gL s (gN s g)) :
    ∀ c ∈ (A.splitStart (gC s g) g gl gr).chunks,
      (((A.splitStart (gC s g) g gl gr).grps c).map (gL t)).IsChain (· < ·) := by
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc hL2 hR2 ⊢
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have al1 := F.leftFresh
  have bl1 := F.rightFresh
  have hglr := F.distinct
  have gL' := F.groupLabel
  have hgnd := hI.gList.nodup
  -- chunk `c`'s run
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hrnd : (A.grps c).Nodup := by
    have := hgnd; rw [INV.glist_flatten] at this
    exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hr1 : g ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 g h g (by simp) rfl
  have hr2 : g ∉ r2 := by
    rw [hrun] at hrnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
  have hgrps' : (A.splitStart c g gl gr).grps c = r1 ++ gl :: g :: gr :: r2 := by
    simp [Abs.splitStart, hrun, replace1_mid hr1]
  have hgrpsO : ∀ c', c' ≠ c → (A.splitStart c g gl gr).grps c' = A.grps c' := by
    intro c' h; simp [Abs.splitStart, h]
  have helts' : ∀ b, (A.splitStart c g gl gr).elts b =
      if b = gl ∨ b = gr then [] else A.elts b := fun b => rfl
  have hchunks' : (A.splitStart c g gl gr).chunks = A.chunks := rfl
  -- `g` is first (last) in its chunk iff `r1` (`r2`) is empty
  have hcE := hI.cEnds c hc
  rw [hrun] at hcE
  have hfirst : cF s c = g ↔ r1 = [] := by
    rw [hcE.1]
    constructor
    · intro e
      cases r1 with
      | nil => rfl
      | cons a t =>
        change a = g at e
        exact absurd (e ▸ (by simp : a ∈ a :: t)) hr1
    · rintro rfl; rfl
  have hlast : cLs s c = g ↔ r2 = [] := by
    rw [hcE.2]
    constructor
    · intro e
      cases r2 with
      | nil => rfl
      | cons a t =>
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp, getLastD_append_cons] at e
        exact absurd (e ▸ getLastD_cons_mem a t NIL) hr2
    · rintro rfl; simp
  -- `p` and `n` are `g`'s neighbours in its chunk, when it has them there
  have hpblk : r1 ≠ [] → p = r1.getLastD NIL := by
    intro h1
    rw [← hpdef, hI.gList.prev g hg, INV.glist_flatten]
    rw [INV.glist_flatten] at hgnd
    rw [predOf_flatten hgnd (List.mem_map.mpr ⟨c, hc, rfl⟩) hgc (by
      rw [hrun]; cases r1 with
      | nil => exact absurd rfl h1
      | cons a t =>
        simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
        intro e; exact hr1 (e ▸ (by simp)))]
    rw [hrun, predOf_mid (hrun ▸ hrnd)]
  have hnblk : r2 ≠ [] → n = r2.headD NIL := by
    intro h2
    rw [← hndef, hI.gList.next g hg, INV.glist_flatten]
    rw [INV.glist_flatten] at hgnd
    rw [succOf_flatten hgnd (List.mem_map.mpr ⟨c, hc, rfl⟩) hgc (by
      rw [hrun]; cases r2 with
      | nil => exact absurd rfl h2
      | cons a t =>
        intro e
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp,
          List.getLast?_append_of_ne_nil _ (by simp)] at e
        exact hr2 (List.mem_of_getLast? e))]
    rw [hrun, succOf_mid (hrun ▸ hrnd)]
  intro c' hc'
  rw [hchunks'] at hc'
  by_cases hcc : c' = c
  · subst hcc
    rw [hgrps']
    have hs := hI.gSorted c' hc'
    rw [hrun] at hs
    refine isChain_around hs (fun z hz => ?_) ?_ ?_ ?_ ?_
    · have hz' : z ∈ A.glist := A.grps_sub_glist hc' (hrun ▸ hz)
      have h1 : z ≠ gl := by rintro rfl; exact al1 hz'
      have h2 : z ≠ gr := by rintro rfl; exact bl1 hz'
      rw [gL', ite_eq_right h1, ite_eq_right h2]
    · intro w hw
      rw [gL', ite_eq_left rfl]
      have h1 : r1 ≠ [] := by rintro rfl; simp at hw
      have hw' : w = r1.getLastD NIL := by
        rcases r1.eq_nil_or_concat with h | ⟨l', a, rfl⟩
        · exact absurd h h1
        · simp at hw; simp [hw]
      rw [hw', ← hpblk h1, ← hpdef]
      exact hL2 (fun e => h1 (hfirst.mp e.symm))
    · simp only [gL',   hglr, ite_true, ite_false]; exact hL1
    · simp only [gL',   hglr.symm, ite_true, ite_false]; exact hR1
    · intro w hw
      rw [gL', ite_eq_right hglr.symm, ite_eq_left rfl]
      have h2 : r2 ≠ [] := by rintro rfl; simp at hw
      have hw' : w = r2.headD NIL := by
        cases r2 with
        | nil => exact absurd rfl h2
        | cons a t => simp at hw; simp [hw]
      rw [hw', ← hnblk h2, ← hndef]
      exact hR2 (fun e => h2 (hlast.mp e.symm))
  · rw [hgrpsO c' hcc]
    have : (A.grps c').map (gL t) = (A.grps c').map (gL s) := by
      refine List.map_congr_left fun z hz => ?_
      have hz' := A.grps_sub_glist hc' hz
      have h1 : z ≠ gl := by rintro rfl; exact al1 hz'
      have h2 : z ≠ gr := by rintro rfl; exact bl1 hz'
      rw [gL', ite_eq_right h1, ite_eq_right h2]
    rw [this]; exact hI.gSorted c' hc'

theorem GroupSplitFrame.chunkEnds (F : GroupSplitFrame s t A g gl gr labL labR)
    (hI : INV s A) (hg : g ∈ A.glist) :
    ∀ c ∈ (A.splitStart (gC s g) g gl gr).chunks,
      Ends (cF t c) (cLs t c) ((A.splitStart (gC s g) g gl gr).grps c) := by
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc ⊢
  have hC' := F.chunkRead
  simp only [hcdef] at hC'
  have hgnd := hI.gList.nodup
  -- chunk `c`'s run
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hrnd : (A.grps c).Nodup := by
    have := hgnd; rw [INV.glist_flatten] at this
    exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hr1 : g ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 g h g (by simp) rfl
  have hr2 : g ∉ r2 := by
    rw [hrun] at hrnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
  have hgrps' : (A.splitStart c g gl gr).grps c = r1 ++ gl :: g :: gr :: r2 := by
    simp [Abs.splitStart, hrun, replace1_mid hr1]
  have hgrpsO : ∀ c', c' ≠ c → (A.splitStart c g gl gr).grps c' = A.grps c' := by
    intro c' h; simp [Abs.splitStart, h]
  have hchunks' : (A.splitStart c g gl gr).chunks = A.chunks := rfl
  -- `g` is first (last) in its chunk iff `r1` (`r2`) is empty
  have hcE := hI.cEnds c hc
  rw [hrun] at hcE
  have hfirst : cF s c = g ↔ r1 = [] := by
    rw [hcE.1]
    constructor
    · intro e
      cases r1 with
      | nil => rfl
      | cons a t =>
        change a = g at e
        exact absurd (e ▸ (by simp : a ∈ a :: t)) hr1
    · rintro rfl; rfl
  have hlast : cLs s c = g ↔ r2 = [] := by
    rw [hcE.2]
    constructor
    · intro e
      cases r2 with
      | nil => rfl
      | cons a t =>
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp, getLastD_append_cons] at e
        exact absurd (e ▸ getLastD_cons_mem a t NIL) hr2
    · rintro rfl; simp
  intro c' hc'
  rw [hchunks'] at hc'
  by_cases hcc : c' = c
  · subst hcc
    rw [hgrps']
    simp only [cF, cLs, hC', ite_true]
    simp only [cF, cLs] at hfirst hlast hcE
    constructor
    · by_cases h1 : r1 = []
      · subst h1; simp [hfirst.mpr rfl]
      · rw [ite_eq_right (fun e => h1 (hfirst.mp e)), hcE.1]
        cases r1 with
        | nil => exact absurd rfl h1
        | cons a t => rfl
    · by_cases h2 : r2 = []
      · subst h2; simp [hlast.mpr rfl]
      · rw [ite_eq_right (fun e => h2 (hlast.mp e)), hcE.2]
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h2
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp, getLastD_append_cons,
          show r1 ++ gl :: g :: gr :: a :: t = (r1 ++ [gl, g, gr]) ++ a :: t by simp,
          getLastD_append_cons]
  · rw [hgrpsO c' hcc]
    simp only [cF, cLs, hC', hcc, ite_false]
    exact hI.cEnds c' hc'

theorem GroupSplitFrame.invariant (F : GroupSplitFrame s t A g gl gr labL labR)
    (hI : INV s A) (hg : g ∈ A.glist)
    (hL1 : labL < gL s g) (hL2 : g ≠ cF s (gC s g) → gL s (gP s g) < labL)
    (hR1 : gL s g < labR) (hR2 : g ≠ cLs s (gC s g) → labR < gL s (gN s g)) :
    INV t (A.splitStart (gC s g) g gl gr) ∧
      (A.splitStart (gC s g) g gl gr).elist = A.elist := by
  have hList := F.groupList hI hg
  have hSorted := F.groupSorted hI hg hL1 hL2 hR1 hR2
  have hEnds := F.chunkEnds hI hg
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc hList hSorted hEnds ⊢
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have hpm : p = NIL ∨ p ∈ A.glist := hpdef ▸ hI.gP_mem hg
  have hnm : n = NIL ∨ n ∈ A.glist := hndef ▸ hI.gN_mem hg
  have al1 := F.leftFresh
  have bl1 := F.rightFresh
  have hggl : g ≠ gl := fun e => al1 (e ▸ hg)
  have hggr : g ≠ gr := fun e => bl1 (e ▸ hg)
  have gN' := F.groupNext
  have gP' := F.groupPrevious
  have gF' := F.groupFirst
  have gLt := F.groupLast
  have gC' := F.groupChunk
  have gA' := F.groupAlive
  have hC' := F.chunkRead
  simp only [hpdef, hndef] at gN' gP'
  simp only [hcdef] at gC' hC'
  have hE' := F.elements
  have hH' := F.head
  have hT' := F.tail
  have hFC' := F.firstChunk
  have hCs' := F.chunksSize
  have hgnd := hI.gList.nodup
  obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hg
  have hnd' := hgnd
  rw [hsplit] at hnd'
  have hg1 : g ∉ l1 := fun h => (List.nodup_append.mp hnd').2.2 g h g (by simp) rfl
  have hgl' : (A.splitStart c g gl gr).glist = l1 ++ gl :: g :: gr :: l2 := by
    have : (A.splitStart c g gl gr).glist = A.glist.replace1 g [gl, g, gr] :=
      flatMap_replace1 hgnd hI.cList.nodup hc hgc fun b => rfl
    rw [this, hsplit, replace1_mid hg1]; simp
  have hl12 : ∀ b ∈ l1 ++ l2, b ≠ gl ∧ b ≠ gr := by
    intro b hb
    have : b ∈ A.glist := by rw [hsplit]; exact mem_split_of_mem hb
    exact ⟨fun e => al1 (e ▸ this), fun e => bl1 (e ▸ this)⟩
  have hel' : (A.splitStart c g gl gr).elist = A.elist := by
    unfold Abs.elist
    rw [hgl', hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, Abs.splitStart]
    have h1 : l1.flatMap (fun b => if b = gl ∨ b = gr then [] else A.elts b) = l1.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl12 b (by simp [hb]); simp [this.1, this.2]
    have h2 : l2.flatMap (fun b => if b = gl ∨ b = gr then [] else A.elts b) = l2.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl12 b (by simp [hb]); simp [this.1, this.2]
    simp [h1, h2, hggl, hggr]
  have hmem' : ∀ z, z ∈ (A.splitStart c g gl gr).glist ↔ z = gl ∨ z = gr ∨ z ∈ A.glist := by
    intro z; rw [hgl', hsplit]; exact mem_around_iff
  refine ⟨?_, hel'⟩
  -- chunk `c`'s run
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hrnd : (A.grps c).Nodup := by
    have := hgnd; rw [INV.glist_flatten] at this
    exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hr1 : g ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 g h g (by simp) rfl
  have hr2 : g ∉ r2 := by
    rw [hrun] at hrnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
  have hgrps' : (A.splitStart c g gl gr).grps c = r1 ++ gl :: g :: gr :: r2 := by
    simp [Abs.splitStart, hrun, replace1_mid hr1]
  have hgrpsO : ∀ c', c' ≠ c → (A.splitStart c g gl gr).grps c' = A.grps c' := by
    intro c' h; simp [Abs.splitStart, h]
  have helts' : ∀ b, (A.splitStart c g gl gr).elts b =
      if b = gl ∨ b = gr then [] else A.elts b := fun b => rfl
  have hchunks' : (A.splitStart c g gl gr).chunks = A.chunks := rfl
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · rw [hel']
    have e1 : eN t = eN s := by funext e; simp [eN, hE']
    have e2 : eP t = eP s := by funext e; simp [eP, hE']
    rw [e1, e2, hH']; exact hI.eList
  · rw [hel', hE']; exact hI.eAlloc
  · rw [hel', hT']; exact hI.tail
  · exact hList
  · intro b hb
    rcases (hmem' b).mp hb with h | h | h
    · rw [h]; exact F.leftBound
    · rw [h]; exact F.rightBound
    · exact lt_of_lt_of_le (hI.gAlloc b h) F.sizeMonotone
  · exact le_trans hI.gPos F.sizeMonotone
  · intro b hb1 hb2
    rw [gA', hmem']
    by_cases h1 : b = gl; · simp [h1]
    by_cases h2 : b = gr; · simp [h2]
    have hbs : b < s.Gs.size := by
      rcases F.newIndex b hb2 with hbs | h | h
      · exact hbs
      · exact (h1 h).elim
      · exact (h2 h).elim
    simp only [h1, h2, false_or, ite_false]
    exact hI.gAlive b hb1 hbs
  · intro b hb
    rw [hmem'] at hb
    push Not at hb
    obtain ⟨h1, h2, h3⟩ := hb
    have hbg : b ≠ g := fun e => h3 (e ▸ hg)
    have hbp : ¬ (b = p ∧ p ≠ NIL) := fun ⟨e, hp0⟩ => h3 (by
      rcases hpm with h' | h'
      · exact absurd h' hp0
      · exact e ▸ h')
    have hbn : ¬ (b = n ∧ n ≠ NIL) := fun ⟨e, hn0⟩ => h3 (by
      rcases hnm with h' | h'
      · exact absurd h' hn0
      · exact e ▸ h')
    rw [gN', gP']
    simp only [hbg, h1, h2, hbp, hbn, ite_false]
    exact hI.gOut b h3
  · intro b hb
    obtain ⟨hb0, hbl, hbr⟩ := F.freeSub b hb
    obtain ⟨hpos, hbound, hnot⟩ := hI.free b hb0
    refine ⟨hpos, lt_of_lt_of_le hbound F.sizeMonotone, ?_⟩
    rw [hmem']
    push Not
    exact ⟨hbl, hbr, hnot⟩
  · exact F.freeNodup
  · have e1 : cN t = cN s := by
      funext z; simp only [cN, hC']; split <;> rfl
    have e2 : cP t = cP s := by
      funext z; simp only [cP, hC']; split <;> rfl
    rw [hchunks', e1, e2, hFC']; exact hI.cList
  · rw [hchunks', hCs']; exact hI.cAlloc
  · intro z hz
    rw [hchunks'] at hz
    have hzc : z ≠ c := fun e => hz (e ▸ hc)
    simp only [cN, cP, cF, hC', hzc, ite_false]
    exact hI.cOut z hz
  · intro b hb
    rw [gF', gLt, helts']
    rcases (hmem' b).mp hb with h | h | h
    · simp [h, Ends]
    · simp [h, Ends]
    · have h1 : b ≠ gl := fun e => al1 (e ▸ h)
      have h2 : b ≠ gr := fun e => bl1 (e ▸ h)
      simp only [h1, h2, false_or, ite_false]
      exact hI.gEnds b h
  · exact hEnds
  · intro b hb e he
    rw [helts'] at he
    rcases (hmem' b).mp hb with h | h | h
    · simp [h] at he
    · simp [h] at he
    · have h1 : b ≠ gl := fun e => al1 (e ▸ h)
      have h2 : b ≠ gr := fun e => bl1 (e ▸ h)
      simp only [h1, h2, false_or, ite_false] at he
      simp only [eG, hE']
      exact hI.grp b h e he
  · intro c' hc' b hb
    rw [hchunks'] at hc'
    rw [gC']
    by_cases hcc : c' = c
    · subst hcc
      rw [hgrps'] at hb
      rcases mem_around_iff.mp hb with h | h | h
      · simp [h]
      · simp [h]
      · have hb' : b ∈ A.grps c' := hrun ▸ h
        have h1 : b ≠ gl := fun e => al1 (e ▸ A.grps_sub_glist hc' hb')
        have h2 : b ≠ gr := fun e => bl1 (e ▸ A.grps_sub_glist hc' hb')
        simp only [h1, h2, false_or, ite_false]
        exact hI.chk c' hc' b hb'
    · rw [hgrpsO c' hcc] at hb
      have h1 : b ≠ gl := fun e => al1 (e ▸ A.grps_sub_glist hc' hb)
      have h2 : b ≠ gr := fun e => bl1 (e ▸ A.grps_sub_glist hc' hb)
      simp only [h1, h2, false_or, ite_false]
      exact hI.chk c' hc' b hb
  · intro b hb
    rw [helts']
    have e1 : eL t = eL s := by funext e; simp [eL, hE']
    rcases (hmem' b).mp hb with h | h | h
    · simp [h]
    · simp [h]
    · have h1 : b ≠ gl := fun e => al1 (e ▸ h)
      have h2 : b ≠ gr := fun e => bl1 (e ▸ h)
      simp only [h1, h2, false_or, ite_false, e1]
      exact hI.eSorted b h
  · exact hSorted
  · have : cT t = cT s := by
      funext z; simp only [cT, hC']; split <;> rfl
    rw [hchunks', this]; exact hI.cSorted

theorem GroupSplitFrame.elementFrame (F : GroupSplitFrame s t A g gl gr labL labR) :
    EFrame s t :=
  ⟨by rw [F.elements], fun e => by simp [eN, F.elements],
    fun e => by simp [eP, F.elements], fun e => by rw [F.elements],
    fun e => by rw [F.elements], F.head, F.tail, F.parameters⟩

/-- **Starting a group split preserves INV-S.** -/
theorem good_startGroupSplit (g : Nat) : Good (startGroupSplit g) := by
  intro s A hI
  rcases startGroupSplit_run s g with
    ⟨labL, labR, hg0, hgs, hga, hL1, hL2, hR1, hR2, hr⟩ | ⟨msg, hr⟩
  · rw [hr]
    have hg := hI.mem_of_alive hg0 hgs hga
    let left := allocGroup s (gC s g)
    let right := allocGroup left.2 (gC s g)
    let t := linkGroupPair right.2 g left.1 right.1 labL labR
    have F : GroupSplitFrame s t A g left.1 right.1 labL labR :=
      groupSplit_frame hI hg labL labR
    obtain ⟨hInv, hElements⟩ := F.invariant hI hg hL1 hL2 hR1 hR2
    exact ⟨F.elementFrame, A.splitStart (gC s g) g left.1 right.1, hInv, hElements⟩
  · rw [hr]; exact EFrame.refl s

end OrderMaintenance.Proof
