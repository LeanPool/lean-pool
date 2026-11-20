/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.CoreInsert


/-!
# Fresh cores and their deferred preparation

`NoErr m`: `m` always succeeds. With `Pres R m` it gives the result and the relation.
A fresh core (`initState`) satisfies INV-S with the single-element nesting; `initCore` and
`prepareStep` only touch the top structure and tags afterwards.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Actions that always succeed -/

/-- A core computation succeeds from every initial state. -/
def NoErr {α : Type} (m : CM α) : Prop := ∀ s, ∃ a s', m.run s = .ok a s'

section noerr
variable {α β : Type}

theorem NoErr.pure (a : α) : NoErr (pure a : CM α) := fun s => ⟨a, s, rfl⟩
theorem NoErr.get : NoErr (get : CM Core) := fun s => ⟨s, s, rfl⟩
theorem NoErr.set (t : Core) : NoErr (set t : CM PUnit) := fun _ => ⟨⟨⟩, t, rfl⟩
theorem NoErr.modify (f : Core → Core) : NoErr (modify f : CM PUnit) := fun s => ⟨⟨⟩, f s, rfl⟩
theorem NoErr.modifyGet (f : Core → α × Core) : NoErr (modifyGet f : CM α) :=
  fun s => ⟨(f s).1, (f s).2, rfl⟩

theorem NoErr.bind {m : CM α} {f : α → CM β} (hm : NoErr m) (hf : ∀ a, NoErr (f a)) :
    NoErr (m >>= f) := by
  intro s
  obtain ⟨a, s1, h1⟩ := hm s
  obtain ⟨b, s2, h2⟩ := hf a s1
  exact ⟨b, s2, by rw [run_bind, h1]; exact h2⟩

theorem NoErr.ite {c : Prop} [Decidable c] {a b : CM α} (ha : NoErr a) (hb : NoErr b) :
    NoErr (if c then a else b) := by
  split <;> assumption

theorem NoErr.forIn_list {γ : Type} (l : List γ) (b : β) {f : γ → β → CM (ForInStep β)}
    (hf : ∀ x b, NoErr (f x b)) : NoErr (forIn l b f) := by
  induction l generalizing b with
  | nil => exact NoErr.pure b
  | cons x t ih =>
    simp only [List.forIn_cons]
    refine NoErr.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact NoErr.pure b'
    | yield b' => exact ih b'

theorem NoErr.run {R : Core → Core → Prop} {m : CM α} (hn : NoErr m) (hp : Pres R m) (s : Core) :
    ∃ a s', m.run s = .ok a s' ∧ R s s' := by
  obtain ⟨a, s', h⟩ := hn s
  have := hp s
  rw [h] at this
  exact ⟨a, s', h, this⟩

end noerr

/-- Prove total success of a core computation by decomposing monadic primitives and loops. -/
syntax "noerr" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| noerr) => `(tactic| noerr [NoErr.get])
  | `(tactic| noerr [$ts,*]) => `(tactic| repeat' (first
      | with_reducible exact NoErr.pure _
      | with_reducible exact NoErr.get
      | with_reducible exact NoErr.set _
      | with_reducible exact NoErr.modify _
      | with_reducible exact NoErr.modifyGet _
      | with_reducible refine NoErr.bind ?_ fun _ => ?_
      | with_reducible refine NoErr.forIn_list _ _ fun _ _ => ?_
      | with_reducible refine NoErr.ite ?_ ?_
      | (first $[| with_reducible exact $ts:term]*)
      | split
      | (dsimp only; done)
      | dsimp only))

theorem noerr_initStep : NoErr initStep := by
  unfold initStep resetTop setInTables newNode modN setLpar setPath modC getP
  noerr

theorem pres_initStep : Pres SameLinks initStep := by
  unfold initStep
  pres [pres_getP, pres_resetTop.sameLinks, (pres_setInTables _ _ _).sameLinks,
    (pres_newNode _).sameLinks, (pres_modN _ _).sameLinks, (pres_setLpar _ _).sameLinks,
    (pres_setPath _ _).sameLinks, pres_modC_tag _ _]
  all_goals (intro s; constructor <;> intros <;> rfl)

theorem noerr_prepareStep : NoErr prepareStep := by
  unfold prepareStep; noerr [noerr_initStep]

theorem pres_prepareStep : Pres SameLinks prepareStep := by
  unfold prepareStep
  pres [pres_initStep]
  intro s
  constructor <;> intros <;> rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The fresh core -/

/-- Abstract nesting of the initial sentinel-only core. -/
def initAbs : Abs :=
  ⟨[1], fun c => if c = 1 then [1] else [], fun g => if g = 1 then [1] else []⟩

theorem initAbs_glist : initAbs.glist = [1] := by
  simp only [Abs.glist, initAbs, List.flatMap_cons, ↓reduceIte, List.flatMap_nil, List.append_nil]
theorem initAbs_elist : initAbs.elist = [1] := by rw [Abs.elist, initAbs_glist]; simp only [
    initAbs,
    List.flatMap_cons,
    ↓reduceIte,
    List.flatMap_nil,
    List.append_nil]

theorem getX_two {α : Type} [Inhabited α] (a b : α) (i : Nat) :
    #[a, b].getX i = if i = 0 then a else if i = 1 then b else default := by
  rcases i with _ | _ | i <;> simp only [Array.getX, Array.getD, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, Nat.zero_lt_succ, ↓reduceDIte,
      Array.getInternal_eq_getElem, List.getElem_toArray,
      List.getElem_cons_zero, ↓reduceIte, Nat.lt_add_one,
      List.getElem_cons_succ, one_ne_zero, Nat.add_eq_zero_iff,
      and_false, and_self, Nat.add_eq_right, dite_eq_right_iff,
      isEmpty_Prop, not_lt, Nat.le_add_left, IsEmpty.forall_iff]

theorem llist_one {nxt prv : Nat → Nat} (hn : nxt 1 = NIL) (hp : prv 1 = NIL) :
    LList nxt prv 1 [1] := by
  refine ⟨by simp, by simp [NIL], rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    rw [hn]
    rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    rw [hp]
    rfl

theorem inv_initState (P : Params) : INV (initState P) initAbs := by
  have hE := getX_two (default : Elem)
    { grp := 1, lab := 1 <<< (P.elementBits - 1), h := 0, live := false }
  have hG := getX_two (default : Group)
    { chk := 1, lab := 1 <<< (P.groupBits - 1), first := 1, last := 1, size := 1 }
  have hC := getX_two (default : Chunk) { first := 1, last := 1, size := 1 }
  have hgl := initAbs_glist
  have hel := initAbs_elist
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hel]; exact llist_one (by simp only [eN, initState, hE, one_ne_zero, ↓reduceIte]) (by
    simp only [eP, initState, hE, one_ne_zero, ↓reduceIte])
  · intro e; rw [hel]; simp only [List.mem_cons, List.not_mem_nil, or_false, initState,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd]; omega
  · rw [hel]; rfl
  · rw [hgl]; exact llist_one (by simp only [gN, initState, hG, one_ne_zero, ↓reduceIte]) (by
    simp only [gP, initState, hG, one_ne_zero, ↓reduceIte])
  · intro g hg; rw [hgl] at hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg;
    subst hg; simp only [initState, List.size_toArray,
      List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd,
      Nat.lt_add_one]
  · simp only [initState, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, Nat.reduceLeDiff]
  · intro g h1 h2; rw [hgl]; simp only [initState, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd] at h2
    have : g = 1 := by omega
    subst this; simp only [gA, initState, hG, one_ne_zero, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false]
  · intro g hg; rw [hgl] at hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    simp only [gN, gP, initState, hG, ite_eq_right hg]
    split <;> exact ⟨rfl, rfl⟩
  · intro g hg; simp only [initState, List.not_mem_nil] at hg
  · simp only [initState, List.nodup_nil]
  · exact llist_one (by simp only [cN, initState, hC, one_ne_zero, ↓reduceIte]) (by
    simp only [cP, initState, hC, one_ne_zero, ↓reduceIte])
  · intro c; simp only [initAbs, List.mem_cons, List.not_mem_nil, or_false, initState,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd]; omega
  · intro c hc; simp only [initAbs, List.mem_cons, List.not_mem_nil, or_false] at hc
    simp only [cN, cP, cF, initState, hC, ite_eq_right hc]
    split <;> exact ⟨rfl, rfl, rfl⟩
  · intro g hg; rw [hgl] at hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg;
    subst hg
    simp only [Ends, gF, initState, hG, one_ne_zero, ↓reduceIte, initAbs,
        List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, gLs,
        List.getLastD_eq_getLast?, List.getLast?_singleton, and_self]
  · intro c hc; simp only [initAbs, List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
    simp only [Ends, cF, initState, hC, one_ne_zero, ↓reduceIte, initAbs,
        List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, cLs,
        List.getLastD_eq_getLast?, List.getLast?_singleton, and_self]
  · intro g hg e he
    rw [hgl] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [initAbs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at he; subst he;
      simp only [eG, initState, hE, one_ne_zero, ↓reduceIte]
  · intro c hc g hg; simp only [initAbs, List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
    simp only [initAbs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg;
      simp only [gC, initState, hG, one_ne_zero, ↓reduceIte]
  · intro g hg; rw [hgl] at hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg;
    subst hg; simp only [initAbs, ↓reduceIte,
      List.map_cons, List.map_nil,
      List.IsChain.singleton]
  · intro c hc; simp only [initAbs, List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc;
    simp only [initAbs, ↓reduceIte, List.map_cons,
      List.map_nil, List.IsChain.singleton]
  · simp only [initAbs, List.map_cons, List.map_nil, List.IsChain.singleton]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem noerr_initTop (lazy : Bool) : NoErr (initTop lazy) := by
  unfold initTop getP; noerr [noerr_initStep]

theorem pres_initTop (lazy : Bool) : Pres SameLinks (initTop lazy) := by
  unfold initTop
  pres [pres_getP, pres_initStep]
  all_goals (intro s; constructor <;> intros <;> rfl)

/-- **A fresh core** satisfies INV-S with the sentinel alone. -/
theorem initCore_run (lazy : Bool) (s : Core) :
    ∃ s', (initCore lazy).run s = .ok () s' ∧ INV s' initAbs ∧ SameLinks (initState s.P) s' := by
  unfold initCore
  simp only [run_getP_bind]
  rw [run_bind, run_set]
  obtain ⟨⟨⟩, s', h1, h2⟩ := (noerr_initTop lazy).run (pres_initTop lazy) (initState s.P)
  exact ⟨s', h1, (inv_initState s.P).of_sameLinks' h2 (by
    simp only [initAbs, List.map_cons, List.map_nil, List.IsChain.singleton]), h2⟩

end OrderMaintenance.Proof
