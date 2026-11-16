/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Defs
public import LeanPool.OrderMaintenance.Proof.Correct.Wrapper


/-!
# Theorem W, stage B1: the framework

* Arrays whose entries all satisfy a predicate, across `modify`, `push`, `set!` and `setX`.
* Updates of single fields of a core keep `WB K` when the new values are below `2^K`.
* `HT K P0 m Q`: a Hoare triple for the stored-value bound at fixed parameters `P0`. From every
  state with `WB K` and parameters `P0`, every run of `m` (normal, or ended by an error) ends in
  such a state, and a normal result satisfies `Q`. Reads return bounded values (the result
  predicate of `get` is `WB K` itself), so a value read from the state and written back is
  bounded without any invariant (class R of `docs/WORD.md` §2). The tactic `ht` decomposes a
  computation into its primitive updates, like `pres`.

Values that need more than `WB` (labels: the guards and `LabRoom`; sizes: the cost invariants;
fresh indices: the record counts) appear as hypotheses of the lemmas that write them.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Arrays whose entries satisfy a predicate -/

section arr
variable {α : Type} [Inhabited α] {p : α → Prop}

theorem allX_modify {a : Array α} (h : ∀ j, p (a.getX j)) {f : α → α} (hf : ∀ X, p X → p (f X))
    (i : Nat) : ∀ j, p ((a.modify i f).getX j) := fun j => by
  rw [Array.getX_modify]; split
  · exact hf _ (h j)
  · exact h j

/-- `modify` where the update is only known to be good at the modified index. -/
theorem allX_modify_at {a : Array α} (h : ∀ j, p (a.getX j)) {f : α → α} {i : Nat}
    (hf : p (f (a.getX i))) : ∀ j, p ((a.modify i f).getX j) := fun j => by
  rw [Array.getX_modify]; split
  · next hh => rw [← hh.1]; exact hf
  · exact h j

theorem allX_push {a : Array α} (h : ∀ j, p (a.getX j)) {v : α} (hv : p v) :
    ∀ j, p ((a.push v).getX j) := fun j => by
  rw [Array.getX_push]; split
  · exact hv
  · exact h j

theorem allX_set! {a : Array α} (h : ∀ j, p (a.getX j)) {v : α} (hv : p v) (i : Nat) :
    ∀ j, p ((a.set! i v).getX j) := fun j => by
  rw [Array.getX_set!]; split
  · exact hv
  · exact h j

theorem allX_setX {a : Array α} (h : ∀ j, p (a.getX j)) {v : α} (hv : p v) (i : Nat) :
    ∀ j, p ((a.setX i v).getX j) := fun j => by
  rw [Array.getX_setX]; split
  · exact hv
  · exact h j

theorem allX_ite {c : Prop} [Decidable c] {a b : Array α} (ha : ∀ j, p (a.getX j))
    (hb : ∀ j, p (b.getX j)) : ∀ j, p ((if c then a else b).getX j) := by
  split
  · exact ha
  · exact hb

end arr

theorem arrB_setX {K : Nat} {a : Array Nat} (h : ArrB K a) {v : Nat} (hv : v < 2 ^ K) (i : Nat) :
    ArrB K (a.setX i v) := allX_setX (p := (· < 2 ^ K)) h hv i

/-! ### Single-field updates -/

section upd
variable {K : Nat} {s : Core} (h : WB K s)
include h

theorem WB.withE {E' : Array Elem} (hE : ∀ i, ElemB K (E'.getX i)) : WB K { s with E := E' } :=
  { h with E := hE }
theorem WB.withGs {G' : Array Group} (hG : ∀ i, GroupB K (G'.getX i)) : WB K { s with Gs := G' } :=
  { h with Gs := hG }
theorem WB.withC {C' : Array Chunk} (hC : ∀ i, ChunkB K (C'.getX i)) : WB K { s with C := C' } :=
  { h with C := hC }
theorem WB.withNodes {N' : Array Node} (hN : ∀ i, NodeB K (N'.getX i)) :
    WB K { s with nodes := N' } := { h with nodes := hN }
theorem WB.withFreeG {l : List Nat} (hl : ∀ g ∈ l, g < 2 ^ K) : WB K { s with freeG := l } :=
  { h with freeG := hl }
theorem WB.withPqHead {a : Array Nat} (ha : ArrB K a) : WB K { s with pqHead := a } :=
  { h with pq := ⟨ha, h.pq.2⟩ }
theorem WB.withPqNext {a : Array Nat} (ha : ArrB K a) : WB K { s with pqNext := a } :=
  { h with pq := ⟨h.pq.1, ha, h.pq.2.2⟩ }
theorem WB.withPqPrev {a : Array Nat} (ha : ArrB K a) : WB K { s with pqPrev := a } :=
  { h with pq := ⟨h.pq.1, h.pq.2.1, ha, h.pq.2.2.2⟩ }
theorem WB.withPqWhere {a : Array Nat} (ha : ArrB K a) : WB K { s with pqWhere := a } :=
  { h with pq := ⟨h.pq.1, h.pq.2.1, h.pq.2.2.1, ha, h.pq.2.2.2.2⟩ }
theorem WB.withNbNext {a : Array Nat} (ha : ArrB K a) : WB K { s with nbNext := a } :=
  { h with pq := ⟨h.pq.1, h.pq.2.1, h.pq.2.2.1, h.pq.2.2.2.1, ha, h.pq.2.2.2.2.2⟩ }
theorem WB.withNbPrev {a : Array Nat} (ha : ArrB K a) : WB K { s with nbPrev := a } :=
  { h with pq := ⟨h.pq.1, h.pq.2.1, h.pq.2.2.1, h.pq.2.2.2.1, h.pq.2.2.2.2.1, ha⟩ }
theorem WB.withPqHi {v : Nat} (hv : v < 2 ^ K) : WB K { s with pqHi := v } :=
  { h with scalars := by obtain ⟨a, b, c, d, e, f, -, g⟩ := h.scalars; exact ⟨a, b, c, d, e, f, hv, g⟩ }
theorem WB.withPqLo {v : Nat} (hv : v < 2 ^ K) : WB K { s with pqLo := v } :=
  { h with scalars := by obtain ⟨a, b, c, d, e, f, g, -⟩ := h.scalars; exact ⟨a, b, c, d, e, f, g, hv⟩ }
theorem WB.withCount {v : Nat} (hv : v < 2 ^ K) : WB K { s with count := v } :=
  { h with scalars := by obtain ⟨-, b, c, d, e, f, g, i⟩ := h.scalars; exact ⟨hv, b, c, d, e, f, g, i⟩ }
theorem WB.withTail {v : Nat} (hv : v < 2 ^ K) : WB K { s with tail := v } :=
  { h with scalars := by obtain ⟨a, b, -, d, e, f, g, i⟩ := h.scalars; exact ⟨a, b, hv, d, e, f, g, i⟩ }
theorem WB.withFirstGroup {v : Nat} (hv : v < 2 ^ K) : WB K { s with firstGroup := v } :=
  { h with scalars := by obtain ⟨a, b, c, -, e, f, g, i⟩ := h.scalars; exact ⟨a, b, c, hv, e, f, g, i⟩ }
theorem WB.withFirstChunk {v : Nat} (hv : v < 2 ^ K) : WB K { s with firstChunk := v } :=
  { h with scalars := by obtain ⟨a, b, c, d, -, f, g, i⟩ := h.scalars; exact ⟨a, b, c, d, hv, f, g, i⟩ }
theorem WB.withResJob {j : Option Job} (hj : ∀ x, j = some x → JobB K x) :
    WB K { s with resJob := j } := { h with job := hj }
theorem WB.withReady {b : Bool} : WB K { s with ready := b } := { h with }

/-! Reading the bound back. -/

theorem WB.getE (i : Nat) : ElemB K (s.E.getX i) := h.E i
theorem WB.getG (i : Nat) : GroupB K (s.Gs.getX i) := h.Gs i
theorem WB.getC (i : Nat) : ChunkB K (s.C.getX i) := h.C i
theorem WB.count : s.count < 2 ^ K := h.scalars.1
theorem WB.head : s.head < 2 ^ K := h.scalars.2.1
theorem WB.tail : s.tail < 2 ^ K := h.scalars.2.2.1
theorem WB.firstGroup : s.firstGroup < 2 ^ K := h.scalars.2.2.2.1
theorem WB.firstChunk : s.firstChunk < 2 ^ K := h.scalars.2.2.2.2.1
theorem WB.pqHi : s.pqHi < 2 ^ K := h.scalars.2.2.2.2.2.2.1
theorem WB.pqLo : s.pqLo < 2 ^ K := h.scalars.2.2.2.2.2.2.2
theorem WB.pqHead (i : Nat) : s.pqHead.getX i < 2 ^ K := h.pq.1 i
theorem WB.pqNext (i : Nat) : s.pqNext.getX i < 2 ^ K := h.pq.2.1 i
theorem WB.pqPrev (i : Nat) : s.pqPrev.getX i < 2 ^ K := h.pq.2.2.1 i
theorem WB.pqWhere (i : Nat) : s.pqWhere.getX i < 2 ^ K := h.pq.2.2.2.1 i
theorem WB.nbNext (i : Nat) : s.nbNext.getX i < 2 ^ K := h.pq.2.2.2.2.1 i
theorem WB.nbPrev (i : Nat) : s.nbPrev.getX i < 2 ^ K := h.pq.2.2.2.2.2 i

end upd


/-! ### Reads, in `apply` form (for the tactic `vb`) -/

section reads
variable {K : Nat} {s : Core}

theorem WB.eNext (h : WB K s) (i : Nat) : (s.E.getX i).next < 2 ^ K := (h.E i).1
theorem WB.ePrev (h : WB K s) (i : Nat) : (s.E.getX i).prev < 2 ^ K := (h.E i).2.1
theorem WB.eGrp (h : WB K s) (i : Nat) : (s.E.getX i).grp < 2 ^ K := (h.E i).2.2.1
theorem WB.eLab (h : WB K s) (i : Nat) : (s.E.getX i).lab < 2 ^ K := (h.E i).2.2.2
theorem WB.gNext (h : WB K s) (i : Nat) : (s.Gs.getX i).next < 2 ^ K := (h.Gs i).1
theorem WB.gPrev (h : WB K s) (i : Nat) : (s.Gs.getX i).prev < 2 ^ K := (h.Gs i).2.1
theorem WB.gFirst (h : WB K s) (i : Nat) : (s.Gs.getX i).first < 2 ^ K := (h.Gs i).2.2.1
theorem WB.gLast (h : WB K s) (i : Nat) : (s.Gs.getX i).last < 2 ^ K := (h.Gs i).2.2.2.1
theorem WB.gChk (h : WB K s) (i : Nat) : (s.Gs.getX i).chk < 2 ^ K := (h.Gs i).2.2.2.2.1
theorem WB.gLab (h : WB K s) (i : Nat) : (s.Gs.getX i).lab < 2 ^ K := (h.Gs i).2.2.2.2.2.1
theorem WB.gSize (h : WB K s) (i : Nat) : (s.Gs.getX i).size < 2 ^ K := (h.Gs i).2.2.2.2.2.2.1
theorem WB.gSrc (h : WB K s) (i : Nat) : (s.Gs.getX i).src < 2 ^ K := (h.Gs i).2.2.2.2.2.2.2.1
theorem WB.gL (h : WB K s) (i : Nat) : (s.Gs.getX i).l < 2 ^ K := (h.Gs i).2.2.2.2.2.2.2.2.1
theorem WB.gR (h : WB K s) (i : Nat) : (s.Gs.getX i).r < 2 ^ K := (h.Gs i).2.2.2.2.2.2.2.2.2
theorem WB.cNext (h : WB K s) (i : Nat) : (s.C.getX i).next < 2 ^ K := (h.C i).1
theorem WB.cPrev (h : WB K s) (i : Nat) : (s.C.getX i).prev < 2 ^ K := (h.C i).2.1
theorem WB.cFirst (h : WB K s) (i : Nat) : (s.C.getX i).first < 2 ^ K := (h.C i).2.2.1
theorem WB.cLast (h : WB K s) (i : Nat) : (s.C.getX i).last < 2 ^ K := (h.C i).2.2.2.1
theorem WB.cSize (h : WB K s) (i : Nat) : (s.C.getX i).size < 2 ^ K := (h.C i).2.2.2.2.1
theorem WB.cSrc (h : WB K s) (i : Nat) : (s.C.getX i).src < 2 ^ K := (h.C i).2.2.2.2.2.1
theorem WB.cL (h : WB K s) (i : Nat) : (s.C.getX i).l < 2 ^ K := (h.C i).2.2.2.2.2.2.1
theorem WB.cR (h : WB K s) (i : Nat) : (s.C.getX i).r < 2 ^ K := (h.C i).2.2.2.2.2.2.2.1
theorem WB.cTag (h : WB K s) (i : Nat) : (s.C.getX i).tag < 2 ^ K := (h.C i).2.2.2.2.2.2.2.2
theorem WB.pqHeadA (h : WB K s) : ArrB K s.pqHead := h.pq.1
theorem WB.pqNextA (h : WB K s) : ArrB K s.pqNext := h.pq.2.1
theorem WB.pqPrevA (h : WB K s) : ArrB K s.pqPrev := h.pq.2.2.1
theorem WB.pqWhereA (h : WB K s) : ArrB K s.pqWhere := h.pq.2.2.2.1
theorem WB.nbNextA (h : WB K s) : ArrB K s.nbNext := h.pq.2.2.2.2.1
theorem WB.nbPrevA (h : WB K s) : ArrB K s.nbPrev := h.pq.2.2.2.2.2

end reads

/-- Close `v < 2 ^ K` for a value read from a good state, a bounded argument, or `0`. -/
syntax "vb" : tactic
macro_rules
  | `(tactic| vb) => `(tactic| first
      | assumption
      | with_reducible exact pos _
      | (with_reducible apply WB.pqHi; assumption) | (with_reducible apply WB.pqLo; assumption)
      | (with_reducible apply WB.count; assumption) | (with_reducible apply WB.head; assumption) | (with_reducible apply WB.tail; assumption)
      | (with_reducible apply WB.firstGroup; assumption) | (with_reducible apply WB.firstChunk; assumption)
      | (with_reducible apply WB.pqHead; assumption) | (with_reducible apply WB.pqNext; assumption)
      | (with_reducible apply WB.pqPrev; assumption) | (with_reducible apply WB.pqWhere; assumption)
      | (with_reducible apply WB.nbNext; assumption) | (with_reducible apply WB.nbPrev; assumption)
      | (with_reducible apply WB.eNext; assumption) | (with_reducible apply WB.ePrev; assumption) | (with_reducible apply WB.eGrp; assumption)
      | (with_reducible apply WB.eLab; assumption)
      | (with_reducible apply WB.gNext; assumption) | (with_reducible apply WB.gPrev; assumption) | (with_reducible apply WB.gFirst; assumption)
      | (with_reducible apply WB.gLast; assumption) | (with_reducible apply WB.gChk; assumption) | (with_reducible apply WB.gLab; assumption)
      | (with_reducible apply WB.gSize; assumption) | (with_reducible apply WB.gSrc; assumption) | (with_reducible apply WB.gL; assumption)
      | (with_reducible apply WB.gR; assumption)
      | (with_reducible apply WB.cNext; assumption) | (with_reducible apply WB.cPrev; assumption) | (with_reducible apply WB.cFirst; assumption)
      | (with_reducible apply WB.cLast; assumption) | (with_reducible apply WB.cSize; assumption) | (with_reducible apply WB.cSrc; assumption)
      | (with_reducible apply WB.cL; assumption) | (with_reducible apply WB.cR; assumption) | (with_reducible apply WB.cTag; assumption)
      | (with_reducible exact lt_of_le_of_lt (Nat.sub_le _ _) (by vb))
      | (split <;> vb)
      | ((try simp only [ElemB, GroupB, ChunkB, NIL] at *); omega))

theorem WB.allE {K : Nat} {s : Core} (h : WB K s) : ∀ i, ElemB K (s.E.getX i) := h.E
theorem WB.allG {K : Nat} {s : Core} (h : WB K s) : ∀ i, GroupB K (s.Gs.getX i) := h.Gs
theorem WB.allC {K : Nat} {s : Core} (h : WB K s) : ∀ i, ChunkB K (s.C.getX i) := h.C
theorem WB.allFree {K : Nat} {s : Core} (h : WB K s) : ∀ g ∈ s.freeG, g < 2 ^ K := h.freeG

/-- A record bound after an update with bounded values: unfold, split, and close each field. -/
syntax "recb" : tactic
macro_rules
  | `(tactic| recb) => `(tactic| (
      (try intro _ _)
      simp only [ElemB, GroupB, ChunkB] at *
      (try split_ifs)
      all_goals (try casesm* _ ∧ _)
      all_goals repeat' apply And.intro
      all_goals (try dsimp only)
      all_goals first | assumption | vb))

/-- Close the changed components left by `wbx`: arrays written with `setX`, `modify`, `push` or
`set!`, records updated with bounded values, and values. -/
syntax "wbv" : tactic
macro_rules
  | `(tactic| wbv) => `(tactic| ((try dsimp only); repeat' (first
      | (with_reducible apply WB.pqHeadA; assumption) | (with_reducible apply WB.pqNextA; assumption)
      | (with_reducible apply WB.pqPrevA; assumption) | (with_reducible apply WB.pqWhereA; assumption)
      | (with_reducible apply WB.nbNextA; assumption) | (with_reducible apply WB.nbPrevA; assumption)
      | (with_reducible apply WB.allE; assumption) | (with_reducible apply WB.allG; assumption) | (with_reducible apply WB.allC; assumption)
      | (with_reducible refine WB.allFree ?_; assumption)
      | (with_reducible refine List.forall_mem_cons.2 ⟨?_, ?_⟩)
      | with_reducible apply arrB_setX
      | with_reducible apply allX_ite
      | (with_reducible refine allX_modify ?_ ?_ _; on_goal 2 => (recb; done))
      | with_reducible refine allX_modify_at ?_ ?_
      | with_reducible apply allX_push
      | with_reducible apply allX_set!
      | with_reducible apply allX_setX
      | recb
      | vb)))

/-! ### Records -/

/-- Unfold the record bounds into plain inequalities (for `omega`). -/
macro "bnd" : tactic => `(tactic| (simp only [ElemB, GroupB, ChunkB, JobB, JobPcB, NIL] at *; omega))

theorem elemB_default' (K : Nat) : ElemB K {} := elemB_default K
theorem groupB_mk {K c : Nat} (hc : c < 2 ^ K) : GroupB K { chk := c } := by
  have := pos K; bnd
theorem chunkB_default' (K : Nat) : ChunkB K {} := chunkB_default K

/-! ### The Hoare triple -/

/-- **The stored-value bound across a computation**, at fixed parameters `P0`: from a state with
`WB K` and parameters `P0`, every run of `m` ends (normally or by an error) in such a state, and
a normal result satisfies `Q`. -/
def HT {α : Type} (K : Nat) (P0 : Params) (m : CM α) (Q : α → Prop) : Prop :=
  ∀ s, WB K s → s.P = P0 → match m.run s with
    | .ok a s' => (WB K s' ∧ s'.P = P0) ∧ Q a
    | .error _ s' => WB K s' ∧ s'.P = P0

section ht
variable {K : Nat} {P0 : Params} {α β : Type}

theorem HT.pure {a : α} {Q : α → Prop} (h : Q a) : HT K P0 (pure a : CM α) Q :=
  fun _ hs hP => ⟨⟨hs, hP⟩, h⟩

/-- `pure`, remembering the value. -/
theorem HT.pure_eq {a : α} : HT K P0 (Pure.pure a : CM α) (· = a) := HT.pure (Q := (· = a)) rfl

theorem HT.get : HT K P0 (get : CM Core) (WB K) :=
  fun _ hs hP => ⟨⟨hs, hP⟩, hs⟩

theorem HT.throw {e : Err} {Q : α → Prop} : HT K P0 (throw e : CM α) Q :=
  fun _ hs hP => ⟨hs, hP⟩

theorem HT.guard {msg : String} {Q : α → Prop} : HT K P0 (OrderMaintenance.Model.guard msg : CM α) Q :=
  fun _ hs hP => ⟨hs, hP⟩

/-- A failed guard has no normal result. -/
theorem HT.guard_false {msg : String} : HT K P0 (OrderMaintenance.Model.guard msg : CM α) (fun _ => False) :=
  fun _ hs hP => ⟨hs, hP⟩

theorem HT.modify {f : Core → Core} (h : ∀ s, WB K s → s.P = P0 → WB K (f s) ∧ (f s).P = P0) :
    HT K P0 (modify f : CM PUnit) (fun _ => True) :=
  fun s hs hP => ⟨h s hs hP, trivial⟩

theorem HT.modifyGet {f : Core → α × Core} {Q : α → Prop}
    (h : ∀ s, WB K s → s.P = P0 → (WB K (f s).2 ∧ (f s).2.P = P0) ∧ Q (f s).1) :
    HT K P0 (modifyGet f : CM α) Q := h

theorem HT.bind {m : CM α} {f : α → CM β} {Q : α → Prop} {Q' : β → Prop} (hm : HT K P0 m Q)
    (hf : ∀ a, Q a → HT K P0 (f a) Q') : HT K P0 (m >>= f) Q' := by
  intro s hs hP
  have h1 := hm s hs hP
  rw [run_bind]
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1
    exact hf a h1.2 s' h1.1.1 h1.1.2
  · rw [hms] at h1; exact h1

theorem HT.ite {c : Prop} [Decidable c] {a b : CM α} {Q : α → Prop} (ha : c → HT K P0 a Q)
    (hb : ¬ c → HT K P0 b Q) : HT K P0 (if c then a else b) Q := by
  split
  · next h => exact ha h
  · next h => exact hb h

theorem HT.mono {m : CM α} {Q Q' : α → Prop} (h : HT K P0 m Q) (hQ : ∀ a, Q a → Q' a) :
    HT K P0 m Q' := by
  intro s hs hP
  have h1 := h s hs hP
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1; exact ⟨h1.1, hQ a h1.2⟩
  · rw [hms] at h1; exact h1

theorem HT.forIn_list {γ : Type} (l : List γ) (b : β) {f : γ → β → CM (ForInStep β)}
    {I : β → Prop} (hb : I b) (hf : ∀ x b, I b → HT K P0 (f x b) (fun r => I r.value)) :
    HT K P0 (forIn l b f) I := by
  induction l generalizing b with
  | nil => exact HT.pure hb
  | cons x t ih =>
    simp only [List.forIn_cons]
    refine HT.bind (hf x b hb) fun r hr => ?_
    cases r with
    | done b' => exact HT.pure hr
    | yield b' => exact ih b' hr

/-- A loop over a list, each iteration knowing its element is in the list. -/
theorem HT.forIn_mem {γ : Type} {f : γ → β → CM (ForInStep β)} {I : β → Prop} :
    ∀ (l : List γ) (b : β), I b → (∀ x ∈ l, ∀ b, I b → HT K P0 (f x b) (fun r => I r.value)) →
      HT K P0 (forIn l b f) I
  | [], b, hb, _ => HT.pure hb
  | x :: t, b, hb, hf => by
    simp only [List.forIn_cons]
    refine HT.bind (hf x (by simp) b hb) fun r hr => ?_
    cases r with
    | done b' => exact HT.pure hr
    | yield b' => exact HT.forIn_mem t b' hr (fun y hy => hf y (by simp [hy]))

theorem HT.forM_list {γ : Type} (l : List γ) {f : γ → CM PUnit}
    (hf : ∀ x ∈ l, HT K P0 (f x) (fun _ => True)) : HT K P0 (l.forM f) (fun _ => True) := by
  induction l with
  | nil => exact HT.pure trivial
  | cons x t ih =>
    show HT K P0 (do f x; t.forM f) _
    exact HT.bind (hf x (by simp)) fun _ _ => ih (fun y hy => hf y (by simp [hy]))

theorem HT.mapM_list {γ δ : Type} (l : List γ) {f : γ → CM δ} {Q : δ → Prop}
    (hf : ∀ x ∈ l, HT K P0 (f x) Q) : HT K P0 (l.mapM f) (fun r => ∀ y ∈ r, Q y) := by
  induction l with
  | nil => exact HT.pure (by simp)
  | cons x t ih =>
    simp only [List.mapM_cons]
    refine HT.bind (hf x (by simp)) fun a ha => HT.bind (ih (fun y hy => hf y (by simp [hy])))
      fun r hr => HT.pure ?_
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ha
    · exact hr y hy

/-- A normal run from a good state ends in a good state. -/
theorem HT.ok {m : CM α} {Q : α → Prop} (h : HT K P0 m Q) {s s' : Core} {a : α} (hs : WB K s)
    (hP : s.P = P0) (hr : m.run s = .ok a s') : (WB K s' ∧ s'.P = P0) ∧ Q a := by
  have := h s hs hP; rw [hr] at this; exact this

/-- Any run from a good state ends in a good state. -/
theorem HT.state {m : CM α} {Q : α → Prop} (h : HT K P0 m Q) {s : Core} (hs : WB K s)
    (hP : s.P = P0) : WB K (Result.state (m.run s)) ∧ (Result.state (m.run s)).P = P0 := by
  have := h s hs hP
  rcases hr : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hr] at this; exact this.1
  · rw [hr] at this; exact this

/-! Reads. -/

theorem HT.getE (i : Nat) : HT K P0 (getE i) (ElemB K) := fun _ hs hP => ⟨⟨hs, hP⟩, hs.E i⟩
theorem HT.getG (i : Nat) : HT K P0 (getG i) (GroupB K) := fun _ hs hP => ⟨⟨hs, hP⟩, hs.Gs i⟩
theorem HT.getC (i : Nat) : HT K P0 (getC i) (ChunkB K) := fun _ hs hP => ⟨⟨hs, hP⟩, hs.C i⟩
theorem HT.getN (i : Nat) : HT K P0 (getN i) (NodeB K) := fun _ hs hP => ⟨⟨hs, hP⟩, hs.nodes i⟩
theorem HT.getP : HT K P0 getP (fun P => P = P0 ∧ ParamsB K P) :=
  fun _ hs hP => ⟨⟨hs, hP⟩, hP, hs.P⟩
/-- Reading the parameters gives `P0`. -/
theorem HT.getP_bind {f : Params → CM β} {Q : β → Prop} (h : HT K P0 (f P0) Q) :
    HT K P0 (OrderMaintenance.Model.getP >>= f) Q := by
  intro s hs hP
  have := h s hs hP
  rw [run_getP_bind, hP]; exact this

theorem HT.pqEmpty : HT K P0 pqEmpty (fun _ => True) := fun _ hs hP => ⟨⟨hs, hP⟩, trivial⟩

theorem HT.require {b : Bool} {msg : String} : HT K P0 (OrderMaintenance.Model.require b msg) (fun _ => True) := by
  unfold OrderMaintenance.Model.require; split
  · exact HT.pure trivial
  · exact HT.guard

end ht

/-- Decompose a computation into primitive state updates, using the given lemmas for calls. The
results of binds become anonymous hypotheses. Leaves goals of the form
`∀ s, WB K s → s.P = P0 → WB K (f s) ∧ (f s).P = P0` for the updates, and the result
predicates of `pure`. -/
syntax "ht_core" "[" term,* "]" : tactic
macro_rules
  | `(tactic| ht_core [$ts,*]) => `(tactic| repeat' (first
      | contradiction
      | with_reducible exact HT.get
      | with_reducible exact HT.getE _
      | with_reducible exact HT.getG _
      | with_reducible exact HT.getC _
      | with_reducible exact HT.getN _
      | with_reducible exact HT.getP
      | with_reducible exact HT.pqEmpty
      | with_reducible exact HT.guard_false
      | with_reducible exact HT.guard
      | with_reducible exact HT.throw
      | with_reducible exact HT.require
      | with_reducible exact HT.pure_eq
      | with_reducible refine HT.pure ?_
      | with_reducible refine HT.getP_bind ?_
      | with_reducible refine HT.bind (Q := ?_) ?_ fun _ _ => ?_
      | with_reducible refine HT.forM_list _ fun _ _ => ?_
      | with_reducible refine HT.forIn_mem _ _ (I := fun _ => True) trivial fun _ _ _ _ => ?_
      | with_reducible refine HT.ite (fun _ => ?_) (fun _ => ?_)
      | with_reducible refine HT.modify ?_
      | with_reducible refine HT.modifyGet ?_
      | (first $[| with_reducible refine $ts:term]*)
      | split
      | (dsimp only; done)
      | dsimp only))

syntax "ht" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| ht) => `(tactic| ht [HT.get])
  | `(tactic| ht [$ts,*]) => `(tactic| (ht_core [$ts,*]; all_goals try (with_reducible exact fun _ => True)))

end OrderMaintenance.Proof.Word

namespace OrderMaintenance.Proof.Word

/-- Split `WB K s'` into its components and close those that `s'` shares with a state `t` of which
`h : WB K t`. The remaining goals are the components that changed. -/
syntax "wbx " term : tactic
macro_rules
  | `(tactic| wbx $h) => `(tactic| (
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      on_goal 25 => try with_reducible exact ($h).lpar
      on_goal 24 => try with_reducible exact ($h).cin
      on_goal 23 => try with_reducible exact ($h).path
      on_goal 22 => try with_reducible exact ($h).pq.2.2.2.2.2
      on_goal 21 => try with_reducible exact ($h).pq.2.2.2.2.1
      on_goal 20 => try with_reducible exact ($h).pq.2.2.2.1
      on_goal 19 => try with_reducible exact ($h).pq.2.2.1
      on_goal 18 => try with_reducible exact ($h).pq.2.1
      on_goal 17 => try with_reducible exact ($h).pq.1
      on_goal 16 => try with_reducible exact ($h).job
      on_goal 15 => try with_reducible exact ($h).prep
      on_goal 14 => try with_reducible exact ($h).scalars.2.2.2.2.2.2.2
      on_goal 13 => try with_reducible exact ($h).scalars.2.2.2.2.2.2.1
      on_goal 12 => try with_reducible exact ($h).scalars.2.2.2.2.2.1
      on_goal 11 => try with_reducible exact ($h).scalars.2.2.2.2.1
      on_goal 10 => try with_reducible exact ($h).scalars.2.2.2.1
      on_goal 9 => try with_reducible exact ($h).scalars.2.2.1
      on_goal 8 => try with_reducible exact ($h).scalars.2.1
      on_goal 7 => try with_reducible exact ($h).scalars.1
      on_goal 6 => try with_reducible exact ($h).freeG
      on_goal 5 => try with_reducible exact ($h).nodes
      on_goal 4 => try with_reducible exact ($h).C
      on_goal 3 => try with_reducible exact ($h).Gs
      on_goal 2 => try with_reducible exact ($h).E
      on_goal 1 => try with_reducible exact ($h).P))

end OrderMaintenance.Proof.Word

namespace OrderMaintenance.Proof.Word

/-- Close the goals `ht` leaves: an update goal, by `wbx` and `wbv`; a result goal, by `vb`. -/
syntax "htfin" : tactic
macro_rules
  | `(tactic| htfin) => `(tactic| first
      | trivial
      | (intro t ht hP; refine ⟨?_, hP⟩; (try casesm* _ ∧ _); wbx ht; all_goals wbv; done)
      | vb)

end OrderMaintenance.Proof.Word
