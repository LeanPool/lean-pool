/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Init


/-!
# The live handles of a core

The client sees a core through the handles of its live elements, in list order:
`liveH c l = (l.filter live).map h`. This file relates it to insertion, deletion, order queries
and appending, for generic `p` (live) and `f` (handle).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Filter-map lemmas -/

section fm
variable (p : Nat → Bool) (f : Nat → Nat)

/-- Filter element indices by liveness and map the retained indices to their handles. -/
def FM (l : List Nat) : List Nat := (l.filter p).map f

@[simp] theorem FM_nil : FM p f [] = [] := rfl
theorem FM_cons (a : Nat) (l : List Nat) :
    FM p f (a :: l) = if p a then f a :: FM p f l else FM p f l := by
  unfold FM; by_cases h : p a <;> simp [ h]
theorem FM_append (l1 l2 : List Nat) : FM p f (l1 ++ l2) = FM p f l1 ++ FM p f l2 := by
  simp [FM, List.filter_append]

theorem mem_FM {l : List Nat} {x : Nat} : x ∈ FM p f l ↔ ∃ e ∈ l, p e = true ∧ f e = x := by
  simp [FM, and_assoc]

theorem FM_mem_of {l : List Nat} {e : Nat} (he : e ∈ l) (hp : p e = true) : f e ∈ FM p f l :=
  (mem_FM p f).mpr ⟨e, he, hp, rfl⟩

theorem FM_congr {p' : Nat → Bool} {f' : Nat → Nat} {l : List Nat}
    (h : ∀ e ∈ l, p' e = p e ∧ f' e = f e) : FM p' f' l = FM p f l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [FM_cons, FM_cons, (h a List.mem_cons_self).1, (h a List.mem_cons_self).2,
      ih fun e he => h e (List.mem_cons_of_mem _ he)]

theorem FM_insertAfterL {l : List Nat} {a b : Nat} (ha : a ∈ l) (hpa : p a = true)
    (hnd : (FM p f l).Nodup) (hb : b ∉ l) (hpb : p b = true) :
    FM p f (OrderMaintenance.Spec.insertAfterL a b l) =
      OrderMaintenance.Spec.insertAfterL (f a) (f b) (FM p f l) := by
  induction l with
  | nil => simp at ha
  | cons c t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    by_cases hca : c = a
    · subst hca
      rw [ite_eq_left rfl, FM_cons, FM_cons, FM_cons, ite_eq_left hpa, ite_eq_left hpb,
        ite_eq_left hpa]
      simp [OrderMaintenance.Spec.insertAfterL]
    · rw [ite_eq_right hca]
      have ha' : a ∈ t := by simpa [Ne.symm hca] using ha
      have hb' : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      rw [FM_cons, FM_cons]
      by_cases hpc : p c = true
      · rw [ite_eq_left hpc, ite_eq_left hpc] at *
        rw [FM_cons, ite_eq_left hpc] at hnd
        have hfa : f a ∈ FM p f t := FM_mem_of p f ha' hpa
        have hfc : f c ≠ f a := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hfa)
        rw [ih ha' (List.nodup_cons.mp hnd).2 hb']
        simp [OrderMaintenance.Spec.insertAfterL, hfc]
      · rw [ite_eq_right hpc, ite_eq_right hpc]
        rw [FM_cons, ite_eq_right hpc] at hnd
        exact ih ha' hnd hb'

theorem FM_insertAfterL_head {a b : Nat} (t : List Nat) (hpa : p a = false) (hpb : p b = true) :
    FM p f (OrderMaintenance.Spec.insertAfterL a b (a :: t)) = f b :: FM p f t := by
  simp [OrderMaintenance.Spec.insertAfterL, FM_cons, hpa, hpb]

/-- Killing `a` erases its handle. -/
theorem FM_kill {p' : Nat → Bool} {l : List Nat} {a : Nat} (ha : a ∈ l) (hpa : p a = true)
    (hp'a : p' a = false) (hp' : ∀ e, e ≠ a → p' e = p e) (hl : l.Nodup) (hnd : (FM p f l).Nodup) :
    FM p' f l = (FM p f l).erase (f a) := by
  induction l with
  | nil => simp at ha
  | cons c t ih =>
    have hct := List.nodup_cons.mp hl
    rw [FM_cons, FM_cons]
    by_cases hca : c = a
    · subst hca
      rw [ite_eq_right (by simp [hp'a]), ite_eq_left hpa, List.erase_cons_head]
      exact FM_congr p f fun e he => ⟨hp' e (fun h => hct.1 (h ▸ he)), rfl⟩
    · have ha' : a ∈ t := by simpa [Ne.symm hca] using ha
      rw [hp' c hca]
      by_cases hpc : p c = true
      · rw [ite_eq_left hpc, ite_eq_left hpc]
        rw [FM_cons, ite_eq_left hpc] at hnd
        have hfa : f a ∈ FM p f t := FM_mem_of p f ha' hpa
        have hfc : f c ≠ f a := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hfa)
        rw [List.erase_cons_tail (by simpa using hfc), ih ha' hct.2 (List.nodup_cons.mp hnd).2]
      · rw [ite_eq_right hpc, ite_eq_right hpc]
        rw [FM_cons, ite_eq_right hpc] at hnd
        exact ih ha' hct.2 hnd

/-- Positions of handles compare as positions of elements. -/
theorem FM_idxOf_lt {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hpa : p a = true)
    (hpb : p b = true) (hnd : (FM p f l).Nodup) :
    (FM p f l).idxOf (f a) < (FM p f l).idxOf (f b) ↔ l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at ha
  | cons c t ih =>
    rw [FM_cons] at hnd ⊢
    by_cases hpc : p c = true
    · rw [ite_eq_left hpc] at hnd ⊢
      have hnt := (List.nodup_cons.mp hnd)
      by_cases hca : c = a
      · subst hca
        by_cases hcb : c = b
        · subst hcb; simp
        · have hb' : b ∈ t := by simpa [Ne.symm hcb] using hb
          have hfb : f b ∈ FM p f t := FM_mem_of p f hb' hpb
          have : f c ≠ f b := fun e => hnt.1 (e ▸ hfb)
          simp [ this, hcb]
      · have ha' : a ∈ t := by simpa [Ne.symm hca] using ha
        have hfa : f a ∈ FM p f t := FM_mem_of p f ha' hpa
        have hfca : f c ≠ f a := fun e => hnt.1 (e ▸ hfa)
        by_cases hcb : c = b
        · subst hcb; simp [ hca, hfca]
        · have hb' : b ∈ t := by simpa [Ne.symm hcb] using hb
          have hfb : f b ∈ FM p f t := FM_mem_of p f hb' hpb
          have hfcb : f c ≠ f b := fun e => hnt.1 (e ▸ hfb)
          simp only [List.idxOf_cons, beq_iff_eq, hca, hcb, hfca, hfcb, ite_false]
          rw [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right]; exact ih ha' hb' hnt.2
    · rw [ite_eq_right hpc] at hnd ⊢
      have hca : c ≠ a := fun e => hpc (e ▸ hpa)
      have hcb : c ≠ b := fun e => hpc (e ▸ hpb)
      have ha' : a ∈ t := by simpa [Ne.symm hca] using ha
      have hb' : b ∈ t := by simpa [Ne.symm hcb] using hb
      simp only [List.idxOf_cons, beq_iff_eq, hca, hcb, ite_false]
      rw [Nat.add_lt_add_iff_right]; exact ih ha' hb' hnd

/-- In a split `pre ++ post` with distinct handles, an element's handle is among `pre`'s iff the
element is in `pre`. -/
theorem FM_mem_pre {pre post : List Nat} {e : Nat} (he : e ∈ pre ++ post) (hp : p e = true)
    (hnd : (FM p f (pre ++ post)).Nodup) : f e ∈ FM p f pre ↔ e ∈ pre := by
  refine ⟨fun h => ?_, fun h => FM_mem_of p f h hp⟩
  rcases List.mem_append.mp he with h' | h'
  · exact h'
  · rw [FM_append] at hnd
    exact absurd rfl ((List.nodup_append.mp hnd).2.2 _ h _ (FM_mem_of p f h' hp))

end fm

theorem insertAfterL_getLastD {l : List Nat} (hl : l.Nodup) (hne : l ≠ []) (y : Nat) :
    OrderMaintenance.Spec.insertAfterL (l.getLastD NIL) y l = l ++ [y] := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => simp [OrderMaintenance.Spec.insertAfterL]
    | cons b u =>
      have hlast : (a :: b :: u).getLastD NIL = (b :: u).getLastD NIL := by
        simp [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
      have hmem : (b :: u).getLastD NIL ∈ b :: u := getLastD_cons_mem _ _ _
      have hne' : a ≠ (b :: u).getLastD NIL := fun e => (List.nodup_cons.mp hl).1 (e ▸ hmem)
      rw [hlast]
      have e : OrderMaintenance.Spec.insertAfterL ((b :: u).getLastD NIL) y (a :: b :: u) =
          a :: OrderMaintenance.Spec.insertAfterL ((b :: u).getLastD NIL) y (b :: u) := by
        conv_lhs => unfold OrderMaintenance.Spec.insertAfterL
        rw [ite_eq_right hne']
      rw [e, ih (List.nodup_cons.mp hl).2 (by simp)]
      rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Cores seen through handles -/

/-- Read the liveness flag of an element in a core. -/
def live (c : Core) (e : Nat) : Bool := (c.E.getX e).live
/-- Read the external handle stored in an element. -/
def hdl (c : Core) (e : Nat) : Nat := (c.E.getX e).h
/-- List the live external handles in an ordered list of element indices. -/
abbrev liveH (c : Core) (l : List Nat) : List Nat := FM (live c) (hdl c) l

/-- A well-formed core: INV-S, good parameters, and a dead sentinel at the head. -/
structure CoreR (c : Core) (A : Abs) : Prop where
  inv : INV c A
  P : CoreP c.P
  ne : A.elist ≠ []
  dead : live c c.head = false

theorem CoreR.head {c : Core} {A : Abs} (h : CoreR c A) : c.head ∈ A.elist := by
  rw [h.inv.eList.head]
  cases hA : A.elist with
  | nil => exact absurd hA h.ne
  | cons a t => simp

/-- `idx` maps every handle of `L` to a live element with that handle. -/
def IdxOK (c : Core) (A : Abs) (idx : Array Nat) (L : List Nat) : Prop :=
  ∀ x ∈ L, idx.getX x ∈ A.elist ∧ live c (idx.getX x) = true ∧ hdl c (idx.getX x) = x

theorem liveH_frame {c c' : Core} {l : List Nat}
    (h : ∀ e ∈ l, live c' e = live c e ∧ hdl c' e = hdl c e) : liveH c' l = liveH c l :=
  FM_congr _ _ h

theorem insertAfterL_headD {x y : Nat} {l : List Nat} (hne : l ≠ []) :
    (OrderMaintenance.Spec.insertAfterL x y l).headD NIL = l.headD NIL := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => simp only [OrderMaintenance.Spec.insertAfterL]; split <;> rfl

/-- **Core insertion through handles.** -/
theorem core_insert {c : Core} {A : Abs} (hR : CoreR c A) {xi : Nat}
    (hx : xi ∈ A.elist) (hh : Nat) :
    ∃ c' A', (insertAfter xi hh).run c = .ok c.E.size c' ∧ CoreR c' A' ∧
      A'.elist = OrderMaintenance.Spec.insertAfterL xi c.E.size A.elist ∧
      (∀ e ∈ A.elist, live c' e = live c e ∧ hdl c' e = hdl c e) ∧
      live c' c.E.size = true ∧ hdl c' c.E.size = hh ∧ c.E.size ∉ A.elist ∧ c.E.size ≠ NIL ∧
      c'.head = c.head ∧ c'.P = c.P := by
  obtain ⟨c', A', hr, I', e', F⟩ := insertAfter_run hR.inv hx hR.P hh
  have hy : c.E.size ∉ A.elist := fun h => by have := (hR.inv.eAlloc _).mp h; omega
  have hy0 : c.E.size ≠ NIL := by have := hR.inv.size_pos hx; unfold NIL; omega
  have hrec : ∀ e ∈ A.elist, live c' e = live c e ∧ hdl c' e = hdl c e := fun e he => by
    have hne : e ≠ c.E.size := fun h => hy (h ▸ he)
    exact ⟨by simp only [live]; rw [F.live, ite_eq_right hne],
      by simp only [hdl]; rw [F.h, ite_eq_right hne]⟩
  have hhead : c'.head = c.head := by
    rw [I'.eList.head, hR.inv.eList.head, e', insertAfterL_headD hR.ne]
  refine ⟨c', A', hr, ⟨I', F.P ▸ hR.P, ?_, ?_⟩, e', hrec, ?_, ?_, hy, hy0, hhead, F.P⟩
  · rw [e']; exact List.ne_nil_of_mem ((OrderMaintenance.Spec.mem_insertAfterL hx).mpr (Or.inl rfl))
  · rw [hhead, (hrec _ hR.head).1]; exact hR.dead
  · simp only [live]; rw [F.live, ite_eq_left rfl]
  · simp only [hdl]; rw [F.h, ite_eq_left rfl]

/-- **Core deletion through handles.** -/
theorem core_kill {c : Core} {A : Abs} (hR : CoreR c A) {xi : Nat} (hx : xi ∈ A.elist)
    (hl : live c xi = true) (hnd : (liveH c A.elist).Nodup) :
    ∃ c', (markDead xi).run c = .ok () c' ∧ CoreR c' A ∧
      liveH c' A.elist = (liveH c A.elist).erase (hdl c xi) ∧
      (∀ e, e ≠ xi → live c' e = live c e) ∧ (∀ e, hdl c' e = hdl c e) ∧ c'.head = c.head ∧
      live c' xi = false := by
  have hsz : xi < c.E.size := ((hR.inv.eAlloc xi).mp hx).2
  have hlive : ∀ e, live { c with E := c.E.modify xi fun e => { e with live := false } } e =
      if e = xi then false else live c e := by
    intro e; simp only [live, Array.getX_modify]
    by_cases h : e = xi
    · subst h; simp [hsz]
    · simp [Ne.symm h, h]
  have hhdl : ∀ e, hdl { c with E := c.E.modify xi fun e => { e with live := false } } e = hdl c
    e := by
    intro e; simp only [hdl, Array.getX_modify]; split <;> rfl
  refine ⟨_, markDead_run c xi, ⟨markDead_inv hR.inv xi, hR.P, hR.ne, ?_⟩, ?_, fun e he => ?_,
    hhdl, rfl, by rw [hlive, ite_eq_left rfl]⟩
  · change live _ c.head = false
    rw [hlive]; split
    · rfl
    · exact hR.dead
  · rw [liveH_frame (c := { c with E := c.E.modify xi fun e => { e with live := false } })
      (c' := { c with E := c.E.modify xi fun e => { e with live := false } }) (fun _ _ => ⟨rfl,
        rfl⟩)]
    have := FM_kill (live c) (hdl c) (p' := live { c with E := c.E.modify xi fun e => { e with
      live := false } })
      hx hl (by rw [hlive, ite_eq_left rfl]) (fun e he => by rw [hlive, ite_eq_right he])
        hR.inv.eList.nodup hnd
    rw [← this]
    exact FM_congr _ _ fun e _ => ⟨rfl, hhdl e⟩
  · rw [hlive, ite_eq_right he]

end OrderMaintenance.Proof
