/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Machine.ThueBridge
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Lattice

/-!
# PostMachineThue

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

namespace PostMachine

/-- The two head movements of a binary single-tape machine. -/
inductive Direction
  | left
  | right

/-- One binary-machine transition writes a bit, moves once, and enters a new
state.  This is the machine model used in Post's 1947 construction and in the
Coq Library of Undecidability's SBTM-to-rewriting reduction. -/
structure Command (Q : Type*) where
  /-- The state entered after executing the Post-machine command. -/
  next : Q
  /-- The Boolean symbol written by the Post-machine command. -/
  write : Bool
  /-- The tape direction taken by the Post-machine command. -/
  move : Direction

/-- A deterministic Post-machine transition function, with `none` representing halting. -/
abbrev Machine (Q : Type*) := Q → Bool → Option (Command Q)

/-- The left and right lists are stored nearest-to-the-head first. -/
structure Config (Q : Type*) where
  /-- The current control state of a Post-machine configuration. -/
  state : Q
  /-- The symbols to the left of the head, ordered from nearest to farthest. -/
  left : List Bool
  /-- The Boolean symbol currently under the tape head. -/
  head : Bool
  /-- The symbols to the right of the head, ordered from nearest to farthest. -/
  right : List Bool

/-- Blank cells contain `false`. -/
def step {Q : Type*} (M : Machine Q) (c : Config Q) : Option (Config Q) :=
  match M c.state c.head with
  | none => none
  | some cmd =>
      some <| match cmd.move with
      | .left =>
          match c.left with
          | [] => ⟨cmd.next, [], false, cmd.write :: c.right⟩
          | b :: left => ⟨cmd.next, left, b, cmd.write :: c.right⟩
      | .right =>
          match c.right with
          | [] => ⟨cmd.next, cmd.write :: c.left, false, []⟩
          | b :: right => ⟨cmd.next, cmd.write :: c.left, b, right⟩

/-- Alphabet of Post's rewriting simulation.  Constructor separation makes
the marker and unique-state-symbol invariants explicit. -/
inductive Symbol (Q : Type*)
  | leftMarker
  | rightMarker
  | tape (b : Bool)
  | state (q : Q)

instance {Q : Type*} [Finite Q] : Finite (Symbol Q) :=
  Finite.of_injective
    (fun s => match s with
      | Symbol.leftMarker => Sum.inl false
      | Symbol.rightMarker => Sum.inl true
      | Symbol.tape b => Sum.inr (Sum.inl b)
      | Symbol.state q => Sum.inr (Sum.inr q))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- The word of tape-symbol letters encoding a Boolean tape segment. -/
def encodeTape {Q : Type*} (w : List Bool) : List (Symbol Q) :=
  w.map Symbol.tape

/-- A configuration is written
`L (reverse left) head state right R`. -/
def encode {Q : Type*} (c : Config Q) : List (Symbol Q) :=
  [Symbol.leftMarker] ++ encodeTape c.left.reverse ++
    [Symbol.tape c.head, Symbol.state c.state] ++
    encodeTape c.right ++ [Symbol.rightMarker]

/-- The two-marker target word reached by the halting simulation. -/
def target {Q : Type*} : List (Symbol Q) :=
  [Symbol.rightMarker, Symbol.leftMarker]

/-- Post's rules.  The first three constructors clean a halted configuration;
the remaining four simulate one boundary case and one interior case for
each head direction. -/
inductive Rule {Q : Type*} (M : Machine Q) :
    List (Symbol Q) → List (Symbol Q) → Prop
  | halt {q a} (h : M q a = none) :
      Rule M
        [Symbol.leftMarker, Symbol.tape a, Symbol.state q, Symbol.rightMarker]
        [Symbol.rightMarker, Symbol.leftMarker]
  | eraseLeft {q a} (h : M q a = none) (b : Bool) :
      Rule M
        [Symbol.tape b, Symbol.tape a, Symbol.state q]
        [Symbol.tape a, Symbol.state q]
  | eraseRight {q a} (h : M q a = none) (b : Bool) :
      Rule M
        [Symbol.tape a, Symbol.state q, Symbol.tape b]
        [Symbol.tape a, Symbol.state q]
  | moveLeftBoundary {q a q' a'}
      (h : M q a = some ⟨q', a', Direction.left⟩) :
      Rule M
        [Symbol.leftMarker, Symbol.tape a, Symbol.state q]
        [Symbol.leftMarker, Symbol.tape false, Symbol.state q', Symbol.tape a']
  | moveLeft {q a q' a'}
      (h : M q a = some ⟨q', a', Direction.left⟩) (b : Bool) :
      Rule M
        [Symbol.tape b, Symbol.tape a, Symbol.state q]
        [Symbol.tape b, Symbol.state q', Symbol.tape a']
  | moveRightBoundary {q a q' a'}
      (h : M q a = some ⟨q', a', Direction.right⟩) :
      Rule M
        [Symbol.tape a, Symbol.state q, Symbol.rightMarker]
        [Symbol.tape a', Symbol.tape false, Symbol.state q', Symbol.rightMarker]
  | moveRight {q a q' a'}
      (h : M q a = some ⟨q', a', Direction.right⟩) (b : Bool) :
      Rule M
        [Symbol.tape a, Symbol.state q, Symbol.tape b]
        [Symbol.tape a', Symbol.tape b, Symbol.state q']

/-- The Thue system comprising the Post-machine transition and halting rules. -/
def system {Q : Type*} (M : Machine Q) : ThueSystem (Symbol Q) :=
  { p | Rule M p.1 p.2 }

/-- The rewriting rule replacing a halting state and scanned symbol by the target markers. -/
def haltPair {Q : Type*} (i : Q × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a⟩ := i
  ([Symbol.leftMarker, Symbol.tape a, Symbol.state q, Symbol.rightMarker],
    [Symbol.rightMarker, Symbol.leftMarker])

/-- The rewriting rule erasing a tape symbol on the left during the halting cleanup. -/
def eraseLeftPair {Q : Type*} (i : Q × Bool × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, b⟩ := i
  ([Symbol.tape b, Symbol.tape a, Symbol.state q],
    [Symbol.tape a, Symbol.state q])

/-- The rewriting rule erasing a tape symbol on the right during the halting cleanup. -/
def eraseRightPair {Q : Type*} (i : Q × Bool × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, b⟩ := i
  ([Symbol.tape a, Symbol.state q, Symbol.tape b],
    [Symbol.tape a, Symbol.state q])

/-- The rewriting rule simulating a left move at the encoded tape boundary. -/
def moveLeftBoundaryPair {Q : Type*}
    (i : Q × Bool × Q × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, q', a'⟩ := i
  ([Symbol.leftMarker, Symbol.tape a, Symbol.state q],
    [Symbol.leftMarker, Symbol.tape false, Symbol.state q', Symbol.tape a'])

/-- The rewriting rule simulating a left move across an existing neighboring tape symbol. -/
def moveLeftPair {Q : Type*}
    (i : Q × Bool × Q × Bool × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, q', a', b⟩ := i
  ([Symbol.tape b, Symbol.tape a, Symbol.state q],
    [Symbol.tape b, Symbol.state q', Symbol.tape a'])

/-- The rewriting rule simulating a right move at the encoded tape boundary. -/
def moveRightBoundaryPair {Q : Type*}
    (i : Q × Bool × Q × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, q', a'⟩ := i
  ([Symbol.tape a, Symbol.state q, Symbol.rightMarker],
    [Symbol.tape a', Symbol.tape false, Symbol.state q', Symbol.rightMarker])

/-- The rewriting rule simulating a right move across an existing neighboring tape symbol. -/
def moveRightPair {Q : Type*}
    (i : Q × Bool × Q × Bool × Bool) :
    List (Symbol Q) × List (Symbol Q) :=
  let ⟨q, a, q', a', b⟩ := i
  ([Symbol.tape a, Symbol.state q, Symbol.tape b],
    [Symbol.tape a', Symbol.tape b, Symbol.state q'])

/-- A machine with finitely many states produces a finite Thue system.  The
proof bounds the actual rules by seven finite families, without requiring the
transition function itself to carry any computability data. -/
theorem system_finite {Q : Type*} [Finite Q] (M : Machine Q) :
    Set.Finite (system M) := by
  let S₀ := Set.range (@haltPair Q)
  let S₁ := Set.range (@eraseLeftPair Q)
  let S₂ := Set.range (@eraseRightPair Q)
  let S₃ := Set.range (@moveLeftBoundaryPair Q)
  let S₄ := Set.range (@moveLeftPair Q)
  let S₅ := Set.range (@moveRightBoundaryPair Q)
  let S₆ := Set.range (@moveRightPair Q)
  have hf : Set.Finite (S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅ ∪ S₆) :=
    ((((((Set.finite_range _).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  refine hf.subset ?_
  intro p hp
  rcases p with ⟨x, y⟩
  change Rule M x y at hp
  cases hp with
  | @halt q a h =>
      have hs :
          ([Symbol.leftMarker, Symbol.tape a, Symbol.state q, Symbol.rightMarker],
            [Symbol.rightMarker, Symbol.leftMarker]) ∈ S₀ :=
        ⟨(q, a), rfl⟩
      simp only [Set.mem_union, hs, true_or]
  | @eraseLeft q a h b =>
      have hs :
          ([Symbol.tape b, Symbol.tape a, Symbol.state q],
            [Symbol.tape a, Symbol.state q]) ∈ S₁ :=
        ⟨(q, a, b), rfl⟩
      simp only [Set.mem_union, hs, true_or, or_true]
  | @eraseRight q a h b =>
      have hs :
          ([Symbol.tape a, Symbol.state q, Symbol.tape b],
            [Symbol.tape a, Symbol.state q]) ∈ S₂ :=
        ⟨(q, a, b), rfl⟩
      simp only [Set.mem_union, hs, true_or, or_true]
  | @moveLeftBoundary q a q' a' h =>
      have hs :
          ([Symbol.leftMarker, Symbol.tape a, Symbol.state q],
            [Symbol.leftMarker, Symbol.tape false, Symbol.state q', Symbol.tape a']) ∈ S₃ :=
        ⟨(q, a, q', a'), rfl⟩
      simp only [Set.mem_union, hs, true_or, or_true]
  | @moveLeft q a q' a' h b =>
      have hs :
          ([Symbol.tape b, Symbol.tape a, Symbol.state q],
            [Symbol.tape b, Symbol.state q', Symbol.tape a']) ∈ S₄ :=
        ⟨(q, a, q', a', b), rfl⟩
      simp only [Set.mem_union, hs, true_or, or_true]
  | @moveRightBoundary q a q' a' h =>
      have hs :
          ([Symbol.tape a, Symbol.state q, Symbol.rightMarker],
            [Symbol.tape a', Symbol.tape false, Symbol.state q', Symbol.rightMarker]) ∈ S₅ :=
        ⟨(q, a, q', a'), rfl⟩
      simp only [Set.mem_union, hs, true_or, or_true]
  | @moveRight q a q' a' h b =>
      have hs :
          ([Symbol.tape a, Symbol.state q, Symbol.tape b],
            [Symbol.tape a', Symbol.tape b, Symbol.state q']) ∈ S₆ :=
        ⟨(q, a, q', a', b), rfl⟩
      simp only [Set.mem_union, hs, or_true]

theorem rule_step {Q : Type*} {M : Machine Q}
    {x y : List (Symbol Q)} (hxy : Rule M x y) (l r : List (Symbol Q)) :
    ThueStep (system M) (l ++ x ++ r) (l ++ y ++ r) :=
  ⟨l, r, x, y, hxy, Or.inl ⟨rfl, rfl⟩⟩

/-- Every nonhalting machine step is one application of a Post rule. -/
theorem simulation_step {Q : Type*} {M : Machine Q} {c d : Config Q}
    (hcd : step M c = some d) :
    ThueStep (system M) (encode c) (encode d) := by
  rcases c with ⟨q, left, a, right⟩
  simp only [step] at hcd
  split at hcd
  next h => contradiction
  next cmd hcmd =>
    rcases cmd with ⟨q', a', move⟩
    cases move with
    | left =>
        cases left with
        | nil =>
            simp only at hcd
            injection hcd with hd
            subst d
            simpa [encode, encodeTape, List.map_reverse] using
              rule_step (Rule.moveLeftBoundary hcmd) ([] : List (Symbol Q))
                (encodeTape right ++ [Symbol.rightMarker])
        | cons b left =>
            simp only at hcd
            injection hcd with hd
            subst d
            simpa [encode, encodeTape, List.map_reverse, List.reverse_cons,
              List.map_append, List.append_assoc] using
              rule_step (Rule.moveLeft hcmd b)
                (Symbol.leftMarker :: encodeTape left.reverse)
                (encodeTape right ++ [Symbol.rightMarker])
    | right =>
        cases right with
        | nil =>
            simp only at hcd
            injection hcd with hd
            subst d
            simpa [encode, encodeTape, List.map_reverse, List.append_assoc] using
              rule_step (Rule.moveRightBoundary hcmd)
                (Symbol.leftMarker :: encodeTape left.reverse)
                ([] : List (Symbol Q))
        | cons b right =>
            simp only at hcd
            injection hcd with hd
            subst d
            simpa [encode, encodeTape, List.map_reverse, List.append_assoc] using
              rule_step (Rule.moveRight hcmd b)
                (Symbol.leftMarker :: encodeTape left.reverse)
                (encodeTape right ++ [Symbol.rightMarker])

private theorem erase_left {Q : Type*} (M : Machine Q)
    (q : Q) (a : Bool) (right left : List Bool) (hhalt : M q a = none) :
    ThueEq (system M) (encode ⟨q, left, a, right⟩)
      (encode ⟨q, [], a, right⟩) := by
  induction left with
  | nil => exact Relation.ReflTransGen.refl
  | cons b left ih =>
      have hs := rule_step (Rule.eraseLeft hhalt b)
        (Symbol.leftMarker :: encodeTape left.reverse)
        (encodeTape right ++ [Symbol.rightMarker])
      have hs' : ThueStep (system M) (encode ⟨q, b :: left, a, right⟩)
          (encode ⟨q, left, a, right⟩) := by
        simpa [encode, encodeTape, List.map_reverse, List.reverse_cons,
          List.map_append, List.append_assoc] using hs
      exact (Relation.ReflTransGen.single hs').trans ih

private theorem erase_right {Q : Type*} (M : Machine Q)
    (q : Q) (a : Bool) (left right : List Bool) (hhalt : M q a = none) :
    ThueEq (system M) (encode ⟨q, left, a, right⟩)
      (encode ⟨q, left, a, []⟩) := by
  induction right with
  | nil => exact Relation.ReflTransGen.refl
  | cons b right ih =>
      have hs := rule_step (Rule.eraseRight hhalt b)
        (Symbol.leftMarker :: encodeTape left.reverse)
        (encodeTape right ++ [Symbol.rightMarker])
      have hs' : ThueStep (system M) (encode ⟨q, left, a, b :: right⟩)
          (encode ⟨q, left, a, right⟩) := by
        simpa [encode, encodeTape, List.map_reverse, List.append_assoc] using hs
      exact (Relation.ReflTransGen.single hs').trans ih

/-- Once the machine halts, deletion rules remove both finite tape fragments
and the final rule produces the fixed target. -/
theorem simulation_halt {Q : Type*} {M : Machine Q} {c : Config Q}
    (hc : step M c = none) :
    ThueEq (system M) (encode c) (target : List (Symbol Q)) := by
  rcases c with ⟨q, left, a, right⟩
  have hhalt : M q a = none := by
    cases h : M q a with
    | none => rfl
    | some cmd => simp [step, h] at hc
  refine (erase_left M q a right left hhalt).trans
    ((erase_right M q a [] right hhalt).trans ?_)
  exact Relation.ReflTransGen.single <| by
    simpa [encode, encodeTape, target] using
      rule_step (Rule.halt hhalt) ([] : List (Symbol Q)) []

theorem target_ne_encode {Q : Type*} (c : Config Q) :
    (target : List (Symbol Q)) ≠ encode c := by
  intro h
  have := congrArg List.head? h
  simp [target, encode] at this

private theorem state_not_mem_encodeTape {Q : Type*} (q : Q) (w : List Bool) :
    Symbol.state q ∉ (encodeTape w : List (Symbol Q)) := by
  simp [encodeTape]

/-- The Boolean predicate recognizing control-state letters in the encoded alphabet. -/
def isState {Q : Type*} : Symbol Q → Bool
  | Symbol.state _ => true
  | _ => false

/-- The number of control-state letters in an encoded word. -/
def stateCount {Q : Type*} (w : List (Symbol Q)) : ℕ :=
  w.countP isState

@[simp] private theorem stateCount_tape_cons {Q : Type*}
    (b : Bool) (w : List (Symbol Q)) :
    stateCount (Symbol.tape b :: w) = stateCount w := by
  simp [stateCount, isState]

@[simp] private theorem stateCount_leftMarker_cons {Q : Type*}
    (w : List (Symbol Q)) :
    stateCount (Symbol.leftMarker :: w) = stateCount w := by
  simp [stateCount, isState]

@[simp] private theorem stateCount_rightMarker_cons {Q : Type*}
    (w : List (Symbol Q)) :
    stateCount (Symbol.rightMarker :: w) = stateCount w := by
  simp [stateCount, isState]

@[simp] private theorem stateCount_state_cons {Q : Type*}
    (q : Q) (w : List (Symbol Q)) :
    stateCount (Symbol.state q :: w) = stateCount w + 1 := by
  simp [stateCount, List.countP_cons, isState]

@[simp]
private theorem stateCount_encodeTape {Q : Type*} (w : List Bool) :
    stateCount (encodeTape w : List (Symbol Q)) = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      change stateCount (Symbol.tape b :: encodeTape w) = 0
      simpa only [stateCount_tape_cons] using ih

@[simp]
private theorem stateCount_append {Q : Type*} (u v : List (Symbol Q)) :
    stateCount (u ++ v) = stateCount u + stateCount v := by
  simp [stateCount, List.countP_append]

@[simp]
private theorem stateCount_encode {Q : Type*} (c : Config Q) :
    stateCount (encode c) = 1 := by
  have stateCount_nil : stateCount ([] : List (Symbol Q)) = 0 := rfl
  simp only [encode, stateCount_append, stateCount_encodeTape,
    stateCount_leftMarker_cons, stateCount_tape_cons, stateCount_state_cons,
    stateCount_rightMarker_cons, stateCount_nil]

private theorem append_state_unique {Q : Type*}
    {A B R S : List (Symbol Q)} {q q' : Q}
    (hA : ∀ p, Symbol.state p ∉ A)
    (hB : ∀ p, Symbol.state p ∉ B)
    (h : A ++ Symbol.state q :: R = B ++ Symbol.state q' :: S) :
    A = B ∧ q = q' ∧ R = S := by
  induction A generalizing B with
  | nil =>
      cases B with
      | nil =>
          simp only [List.nil_append] at h
          injection h with hq hRS
          injection hq with hqq
          exact ⟨rfl, hqq, hRS⟩
      | cons b B =>
          simp only [List.nil_append, List.cons_append] at h
          injection h with hb _
          have hm : Symbol.state q ∈ b :: B := by simp [← hb]
          exact (hB q hm).elim
  | cons a A ih =>
      cases B with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          injection h with ha _
          have hm : Symbol.state q' ∈ a :: A := by simp [ha]
          exact (hA q' hm).elim
      | cons b B =>
          simp only [List.cons_append] at h
          injection h with hab htail
          subst b
          have hAt : ∀ p, Symbol.state p ∉ A := by
            intro p hp
            exact hA p (by simp [hp])
          have hBt : ∀ p, Symbol.state p ∉ B := by
            intro p hp
            exact hB p (by simp [hp])
          obtain ⟨hAB, hqq, hRS⟩ := ih hAt hBt htail
          exact ⟨by simp [hAB], hqq, hRS⟩

/-- The state symbol occurs exactly once in an encoded configuration, so an
occurrence of `tape a, state q` identifies the head bit, state, and both
contexts. -/
private theorem encode_eq_tape_state {Q : Type*} (c : Config Q)
    (u v : List (Symbol Q)) (a : Bool) (q : Q)
    (h : encode c = u ++ [Symbol.tape a, Symbol.state q] ++ v) :
    c.head = a ∧ c.state = q ∧
      u = Symbol.leftMarker :: encodeTape c.left.reverse ∧
      v = encodeTape c.right ++ [Symbol.rightMarker] := by
  let A : List (Symbol Q) :=
    Symbol.leftMarker :: encodeTape c.left.reverse ++ [Symbol.tape c.head]
  let B : List (Symbol Q) := u ++ [Symbol.tape a]
  have h' : A ++ Symbol.state c.state ::
      (encodeTape c.right ++ [Symbol.rightMarker]) =
      B ++ Symbol.state q :: v := by
    calc
      _ = encode c := by simp [A, encode, List.append_assoc]
      _ = u ++ [Symbol.tape a, Symbol.state q] ++ v := h
      _ = _ := by simp [B, List.append_assoc]
  have hA : ∀ p, Symbol.state p ∉ A := by
    intro p
    simp [A, state_not_mem_encodeTape]
  have hcount := congrArg stateCount h
  have hu0 : stateCount u = 0 := by
    have stateCount_nil : stateCount ([] : List (Symbol Q)) = 0 := rfl
    simp only [stateCount_encode, stateCount_append, stateCount_tape_cons,
      stateCount_state_cons, stateCount_nil] at hcount
    omega
  have hB : ∀ p, Symbol.state p ∉ B := by
    intro p
    simp only [B, List.mem_append, List.mem_singleton]
    rintro (hp | hp)
    · have hz := (List.countP_eq_zero.mp hu0) (Symbol.state p) hp
      simp [isState] at hz
    · simp at hp
  obtain ⟨hAB, hstate, hv⟩ := append_state_unique hA hB h'
  have htail :
      (Symbol.leftMarker :: encodeTape c.left.reverse) ++
          [Symbol.tape c.head] = u ++ [Symbol.tape a] := by
    simpa [A, B, List.append_assoc] using hAB
  have hlast := congrArg List.reverse htail
  have hhead : c.head = a := by
    simp only [List.reverse_append, List.reverse_singleton] at hlast
    injection hlast with htape _
    injection htape
  subst a
  have hu : u = Symbol.leftMarker :: encodeTape c.left.reverse := by
    apply List.append_cancel_right
    exact htail.symm
  exact ⟨rfl, hstate, hu, hv.symm⟩

private theorem append_leftMarker_ne_encodeTape {Q : Type*}
    (u : List (Symbol Q)) (w : List Bool) :
    u ++ [Symbol.leftMarker] ≠ (encodeTape w : List (Symbol Q)) := by
  induction w generalizing u with
  | nil => simp [encodeTape]
  | cons b w ih =>
      cases u with
      | nil => simp [encodeTape]
      | cons x u =>
          simp only [encodeTape, List.map_cons, List.cons_append]
          intro h
          injection h with _ ht
          exact ih u ht

private theorem append_leftMarker_eq {Q : Type*}
    (u : List (Symbol Q)) (w : List Bool)
    (h : u ++ [Symbol.leftMarker] =
      Symbol.leftMarker :: (encodeTape w : List (Symbol Q))) :
    u = [] ∧ w = [] := by
  cases w with
  | nil =>
      simp only [encodeTape, List.map_nil, List.append_left_eq_self] at h
      exact ⟨h, rfl⟩
  | cons b w =>
      cases u with
      | nil => simp [encodeTape] at h
      | cons x u =>
          simp only [List.cons_append] at h
          injection h with _ ht
          exact (append_leftMarker_ne_encodeTape u (b :: w) ht).elim

private theorem append_tape_eq_left {Q : Type*}
    (u : List (Symbol Q)) (left : List Bool) (b : Bool)
    (h : u ++ [Symbol.tape b] =
      Symbol.leftMarker :: (encodeTape left.reverse : List (Symbol Q))) :
    ∃ rest, left = b :: rest ∧
      u = Symbol.leftMarker :: encodeTape rest.reverse := by
  cases left with
  | nil =>
      cases u <;> simp [encodeTape] at h
  | cons b' rest =>
      have htail : u ++ [Symbol.tape b] =
          (Symbol.leftMarker :: encodeTape rest.reverse) ++
            [Symbol.tape b'] := by
        simpa [encodeTape, List.reverse_cons, List.map_append,
          List.append_assoc] using h
      have hlast := congrArg List.reverse htail
      have hb : b = b' := by
        simp only [List.reverse_append, List.reverse_singleton] at hlast
        injection hlast with htape _
        injection htape
      subst b'
      refine ⟨rest, rfl, ?_⟩
      apply List.append_cancel_right
      exact htail

private theorem rightMarker_cons_eq {Q : Type*}
    (r : List (Symbol Q)) (w : List Bool)
    (h : Symbol.rightMarker :: r =
      (encodeTape w : List (Symbol Q)) ++ [Symbol.rightMarker]) :
    r = [] ∧ w = [] := by
  cases w with
  | nil =>
      simp only [encodeTape, List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨h, rfl⟩
  | cons b w => simp [encodeTape] at h

private theorem tape_cons_eq_right {Q : Type*}
    (r : List (Symbol Q)) (right : List Bool) (b : Bool)
    (h : Symbol.tape b :: r =
      (encodeTape right : List (Symbol Q)) ++ [Symbol.rightMarker]) :
    ∃ rest, right = b :: rest ∧
      r = encodeTape rest ++ [Symbol.rightMarker] := by
  cases right with
  | nil => simp [encodeTape] at h
  | cons b' rest =>
      simp only [encodeTape, List.map_cons, List.cons_append] at h
      injection h with hb hr
      injection hb with hbb
      exact ⟨rest, by simp [hbb], hr⟩

/-- The Boolean marker encoding of a boundary letter, empty for other letters. -/
def marker {Q : Type*} : Symbol Q → List Bool
  | Symbol.leftMarker => [false]
  | Symbol.rightMarker => [true]
  | _ => []

/-- The boundary-marker sequence extracted from an encoded word. -/
def markers {Q : Type*} (w : List (Symbol Q)) : List Bool :=
  w.flatMap marker

@[simp] private theorem markers_tape_cons {Q : Type*}
    (b : Bool) (w : List (Symbol Q)) :
    markers (Symbol.tape b :: w) = markers w := rfl

@[simp] private theorem markers_state_cons {Q : Type*}
    (q : Q) (w : List (Symbol Q)) :
    markers (Symbol.state q :: w) = markers w := rfl

@[simp] private theorem markers_leftMarker_cons {Q : Type*}
    (w : List (Symbol Q)) :
    markers (Symbol.leftMarker :: w) = false :: markers w := rfl

@[simp] private theorem markers_rightMarker_cons {Q : Type*}
    (w : List (Symbol Q)) :
    markers (Symbol.rightMarker :: w) = true :: markers w := rfl

@[simp]
private theorem markers_append {Q : Type*} (u v : List (Symbol Q)) :
    markers (u ++ v) = markers u ++ markers v := by
  simp [markers, List.flatMap_append]

@[simp]
private theorem markers_encodeTape {Q : Type*} (w : List Bool) :
    markers (encodeTape w : List (Symbol Q)) = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      change markers (Symbol.tape b :: encodeTape w) = []
      simpa only [markers_tape_cons] using ih

@[simp]
private theorem markers_encode {Q : Type*} (c : Config Q) :
    markers (encode c) = [false, true] := by
  have markers_nil : markers ([] : List (Symbol Q)) = [] := rfl
  simp only [encode, markers_append, markers_encodeTape,
    markers_leftMarker_cons, markers_tape_cons, markers_state_cons,
    markers_rightMarker_cons, markers_nil, List.append_nil]
  rfl

@[simp]
private theorem markers_target {Q : Type*} :
    markers (target : List (Symbol Q)) = [true, false] := rfl

private theorem target_not_occurs {Q : Type*} (c : Config Q)
    (l r : List (Symbol Q)) :
    encode c ≠ l ++ (target : List (Symbol Q)) ++ r := by
  intro h
  have hm : [false, true] = markers l ++ [true, false] ++ markers r := by
    simpa only [markers_encode, markers_append, markers_target] using
      congrArg markers h
  have hlen := congrArg List.length hm
  have hl : (markers l).length = 0 := by
    simp only [List.length_cons, List.length_nil, List.length_append] at hlen
    omega
  have hr : (markers r).length = 0 := by
    simp only [List.length_cons, List.length_nil, List.length_append] at hlen
    omega
  have hlnil : markers l = [] := List.length_eq_zero_iff.mp hl
  have hrnil : markers r = [] := List.length_eq_zero_iff.mp hr
  simp [hlnil, hrnil] at hm

private theorem forward_rule_of_step {Q : Type*} {M : Machine Q}
    {c d : Config Q} {l r x y : List (Symbol Q)}
    (hrule : Rule M x y) (hsource : encode c = l ++ x ++ r)
    (hstep : step M c = some d) :
    l ++ y ++ r = encode d := by
  cases hrule with
  | @halt q a hhalt =>
      have ho : encode c = (l ++ [Symbol.leftMarker]) ++
          [Symbol.tape a, Symbol.state q] ++
          (Symbol.rightMarker :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, -, -⟩ := encode_eq_tape_state c _ _ a q ho
      have hc : M c.state c.head = none := by simpa [ha, hq] using hhalt
      simp [step, hc] at hstep
  | @eraseLeft q a hhalt b =>
      have ho : encode c = (l ++ [Symbol.tape b]) ++
          [Symbol.tape a, Symbol.state q] ++ r := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, -, -⟩ := encode_eq_tape_state c _ _ a q ho
      have hc : M c.state c.head = none := by simpa [ha, hq] using hhalt
      simp [step, hc] at hstep
  | @eraseRight q a hhalt b =>
      have ho : encode c = l ++ [Symbol.tape a, Symbol.state q] ++
          (Symbol.tape b :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, -, -⟩ := encode_eq_tape_state c _ _ a q ho
      have hc : M c.state c.head = none := by simpa [ha, hq] using hhalt
      simp [step, hc] at hstep
  | @moveLeftBoundary q a q' a' hcmd =>
      have ho : encode c = (l ++ [Symbol.leftMarker]) ++
          [Symbol.tape a, Symbol.state q] ++ r := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ := encode_eq_tape_state c _ _ a q ho
      obtain ⟨hl, hleftrev⟩ := append_leftMarker_eq l c.left.reverse hp
      have hleft : c.left = [] := by simpa using hleftrev
      have hc : M c.state c.head = some ⟨q', a', Direction.left⟩ := by
        simpa [ha, hq] using hcmd
      have hd : d = ⟨q', [], false, a' :: c.right⟩ := by
        simpa [step, hc, hleft] using hstep.symm
      subst d
      rw [hl, hs]
      simp [encode, encodeTape]
  | @moveLeft q a q' a' hcmd b =>
      have ho : encode c = (l ++ [Symbol.tape b]) ++
          [Symbol.tape a, Symbol.state q] ++ r := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ := encode_eq_tape_state c _ _ a q ho
      obtain ⟨left, hleft, hl⟩ := append_tape_eq_left l c.left b hp
      have hc : M c.state c.head = some ⟨q', a', Direction.left⟩ := by
        simpa [ha, hq] using hcmd
      have hd : d = ⟨q', left, b, a' :: c.right⟩ := by
        simpa [step, hc, hleft] using hstep.symm
      subst d
      rw [hl, hs]
      simp [encode, encodeTape, List.append_assoc]
  | @moveRightBoundary q a q' a' hcmd =>
      have ho : encode c = l ++ [Symbol.tape a, Symbol.state q] ++
          (Symbol.rightMarker :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ := encode_eq_tape_state c _ _ a q ho
      obtain ⟨hr, hright⟩ := rightMarker_cons_eq r c.right hs
      have hc : M c.state c.head = some ⟨q', a', Direction.right⟩ := by
        simpa [ha, hq] using hcmd
      have hd : d = ⟨q', a' :: c.left, false, []⟩ := by
        simpa [step, hc, hright] using hstep.symm
      subst d
      rw [hp, hr]
      simp [encode, encodeTape, List.append_assoc]
  | @moveRight q a q' a' hcmd b =>
      have ho : encode c = l ++ [Symbol.tape a, Symbol.state q] ++
          (Symbol.tape b :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ := encode_eq_tape_state c _ _ a q ho
      obtain ⟨right, hright, hr⟩ := tape_cons_eq_right r c.right b hs
      have hc : M c.state c.head = some ⟨q', a', Direction.right⟩ := by
        simpa [ha, hq] using hcmd
      have hd : d = ⟨q', a' :: c.left, b, right⟩ := by
        simpa [step, hc, hright] using hstep.symm
      subst d
      rw [hp, hr]
      simp [encode, encodeTape, List.append_assoc]
private theorem backward_rule_of_step {Q : Type*} {M : Machine Q}
    {c d : Config Q} {l r x y : List (Symbol Q)}
    (hrule : Rule M x y) (hsource : encode c = l ++ y ++ r)
    (hstep : step M c = some d) :
    ∃ p, l ++ x ++ r = encode p ∧ step M p = some c := by
  rcases c with ⟨qc, left₀, a₀, right₀⟩
  cases hrule with
  | @halt q a hhalt =>
      have ht : encode (⟨qc, left₀, a₀, right₀⟩ : Config Q) =
          l ++ (target : List (Symbol Q)) ++ r := by
        simpa [target, List.append_assoc] using hsource
      exact (target_not_occurs ⟨qc, left₀, a₀, right₀⟩ l r ht).elim
  | @eraseLeft q a hhalt b =>
      obtain ⟨ha, hq, -, -⟩ :=
        encode_eq_tape_state (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          l r a q (by simpa [List.append_assoc] using hsource)
      change a₀ = a at ha
      change qc = q at hq
      have hc : M qc a₀ = none := by simpa [ha, hq] using hhalt
      simp [step, hc] at hstep
  | @eraseRight q a hhalt b =>
      obtain ⟨ha, hq, -, -⟩ :=
        encode_eq_tape_state (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          l r a q (by simpa [List.append_assoc] using hsource)
      change a₀ = a at ha
      change qc = q at hq
      have hc : M qc a₀ = none := by simpa [ha, hq] using hhalt
      simp [step, hc] at hstep
  | @moveLeftBoundary q a q' a' hcmd =>
      have ho : encode (⟨qc, left₀, a₀, right₀⟩ : Config Q) =
          (l ++ [Symbol.leftMarker]) ++
            [Symbol.tape false, Symbol.state q'] ++
            (Symbol.tape a' :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ :=
        encode_eq_tape_state
          (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          _ _ false q' ho
      change a₀ = false at ha
      change qc = q' at hq
      obtain ⟨hl, hleftrev⟩ := append_leftMarker_eq l left₀.reverse hp
      have hleft : left₀ = [] := by simpa using hleftrev
      obtain ⟨right, hright, hr⟩ :=
        tape_cons_eq_right r right₀ a' hs
      subst qc
      subst a₀
      subst left₀
      subst right₀
      refine ⟨⟨q, [], a, right⟩, ?_, ?_⟩
      · rw [hl, hr]
        simp [encode, encodeTape]
      · simp [step, hcmd]
  | @moveLeft q a q' a' hcmd b =>
      have ho : encode (⟨qc, left₀, a₀, right₀⟩ : Config Q) =
          l ++ [Symbol.tape b, Symbol.state q'] ++
            (Symbol.tape a' :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ :=
        encode_eq_tape_state
          (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          _ _ b q' ho
      change a₀ = b at ha
      change qc = q' at hq
      obtain ⟨right, hright, hr⟩ :=
        tape_cons_eq_right r right₀ a' hs
      subst qc
      subst a₀
      subst right₀
      refine ⟨⟨q, b :: left₀, a, right⟩, ?_, ?_⟩
      · rw [hp, hr]
        simp [encode, encodeTape, List.append_assoc]
      · simp [step, hcmd]
  | @moveRightBoundary q a q' a' hcmd =>
      have ho : encode (⟨qc, left₀, a₀, right₀⟩ : Config Q) =
          (l ++ [Symbol.tape a']) ++
            [Symbol.tape false, Symbol.state q'] ++
            (Symbol.rightMarker :: r) := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ :=
        encode_eq_tape_state
          (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          _ _ false q' ho
      change a₀ = false at ha
      change qc = q' at hq
      obtain ⟨left, hleft, hl⟩ := append_tape_eq_left l left₀ a' hp
      obtain ⟨hr, hright⟩ := rightMarker_cons_eq r right₀ hs
      subst qc
      subst a₀
      subst left₀
      subst right₀
      refine ⟨⟨q, left, a, []⟩, ?_, ?_⟩
      · rw [hl, hr]
        simp [encode, encodeTape, List.append_assoc]
      · simp [step, hcmd]
  | @moveRight q a q' a' hcmd b =>
      have ho : encode (⟨qc, left₀, a₀, right₀⟩ : Config Q) =
          (l ++ [Symbol.tape a']) ++
            [Symbol.tape b, Symbol.state q'] ++ r := by
        simpa [List.append_assoc] using hsource
      obtain ⟨ha, hq, hp, hs⟩ :=
        encode_eq_tape_state
          (⟨qc, left₀, a₀, right₀⟩ : Config Q)
          _ _ b q' ho
      change a₀ = b at ha
      change qc = q' at hq
      obtain ⟨left, hleft, hl⟩ := append_tape_eq_left l left₀ a' hp
      subst qc
      subst a₀
      subst left₀
      refine ⟨⟨q, left, a, b :: right₀⟩, ?_, ?_⟩
      · rw [hl, hs]
        simp [encode, encodeTape, List.append_assoc]
      · simp [step, hcmd]

/-- Post's inverse-simulation invariant for one symmetric rewrite out of a
live encoded configuration. -/
theorem classify_step {Q : Type*} {M : Machine Q} {c d : Config Q}
    (hstep : step M c = some d) {w : List (Symbol Q)}
    (hrew : ThueStep (system M) (encode c) w) :
    w = encode d ∨ ∃ p, w = encode p ∧ step M p = some c := by
  rcases hrew with ⟨l, r, x, y, hrule, h⟩
  change Rule M x y at hrule
  rcases h with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · exact Or.inl <| htarget.trans (forward_rule_of_step hrule hsource hstep)
  · right
    obtain ⟨p, hpword, hpstep⟩ :=
      backward_rule_of_step hrule hsource hstep
    exact ⟨p, htarget.trans hpword, hpstep⟩

/-- The complete machine-to-fixed-target symmetric-Thue coding. -/
def coding {Q : Type*} (M : Machine Q) :
    MachineThue.Coding (Config Q) (Symbol Q) where
  step := step M
  system := system M
  encode := encode
  target := target
  target_ne_encode := target_ne_encode
  simulate_step := simulation_step
  simulate_halt := simulation_halt
  classify := fun hstep hrew => classify_step hstep hrew

/-- A binary machine terminates exactly when its Post word is equivalent to
the fixed word `R L`. -/
theorem terminates_iff {Q : Type*} (M : Machine Q) (c : Config Q) :
    MachineThue.Terminates (step M) c ↔
      ThueEq (system M) (encode c) (target : List (Symbol Q)) :=
  @MachineThue.Coding.terminates_iff (Config Q) (Symbol Q) (coding M) c

end PostMachine

end Undecidability
