/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Fintype.Powerset
public import LeanPool.DeciSigma1.Automata.Constraints
public import LeanPool.DeciSigma1.Full.Closure.Basic
public import LeanPool.DeciSigma1.Satisfiability.Decide
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Run automata for signed configurations

The moves of a flat constraint over `{⊥, f, ⊤}` with variance `c` are the moves of its signed
translation `signed c Γ`, a covariant constraint on the signed variables `V × Bool`
(`moves_iff_signed`); hence the upper and lower run automata of `DeciSigma1.Automata.Constraints`
describe the signed derivations, and exchanging the signs turns upper runs into lower runs
(`lowerRun_flip`). Membership in the least closure is then a condition on lower runs
(`leastClosure_membership`), and, for a satisfiable constraint, a configuration is dead exactly
when its upper run reaches a variable below a negative fact or its opposite sign lies in the least
closure (`HasUnaryObstruction`), or when it derives its own opposite sign
(`SelfCollisionEvent`). These finite-state conditions characterize the holes of the compiled
readers. Satisfiability is decided by testing the signed translation for a label clash
(`decideSat`).

## Main declarations

- `Closure.assoc`, `Closure.moves_iff_signed`: moves as moves of the signed translation.
- `Closure.lowerRun_flip`: sign exchange on runs.
- `Closure.factReachableVariables`, `Closure.forbiddenPredecessors`: the signed variables reachable
  from facts and those below negative facts.
- `Closure.leastClosure_membership`, `Closure.leastClosure_flip_membership`: least-closure
  membership through runs.
- `Closure.HasUnaryObstruction`, `Closure.SelfCollisionEvent`,
  `Closure.not_live_iff_unaryObstruction_or_selfCollision`: dead configurations.
- `Closure.decideSat`: the decision procedure for satisfiability with variance.
-/

@[expose] public section


namespace DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
export DeciSigma1.Semantics.SignSelection (flipV flipV_flipV)
variable {n : ℕ} {V : Type*}

/-- Signed configurations as configurations over the signed variables. -/
def assoc : Config n V ≃ Automata.Config n (V × Bool) where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, p.1.2, p.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {c : Fin n → Bool} {Γ : List (LitT n V)}

private theorem signed_mem {l : LitT n V} {k : LitT n (V × Bool)}
    (hl : l ∈ Γ) (hk : k ∈ signedLit c l) : k ∈ signed c Γ :=
  List.mem_flatMap.mpr ⟨l, hl, hk⟩

private theorem move_to_signed {p q : Config n V} (h : Move c Γ p q) :
    Automata.Move (signed c Γ) (assoc p) (assoc q) := by
  cases h with
  | copyPlus hl => exact .copy (signed_mem hl (by simp [signedLit]))
  | copyMinus hl => exact .copy (signed_mem hl (by simp [signedLit]))
  | @fLePush a u w i hl =>
    exact Automata.Move.push (w := w) i (signed_mem (c := c) hl
      (show LitT.fLe (fun j => (a j, c j)) (u, false) ∈ signedLit c (.fLe a u) by
        simp [signedLit]))
  | @fLePop a u w i hl =>
    exact Automata.Move.pop (w := w) i (signed_mem (c := c) hl
      (show LitT.leF (u, true) (fun j => (a j, !(c j))) ∈ signedLit c (.fLe a u) by
        simp [signedLit]))
  | @leFPop u a w i hl =>
    exact Automata.Move.pop (w := w) i (signed_mem (c := c) hl
      (show LitT.leF (u, false) (fun j => (a j, c j)) ∈ signedLit c (.leF u a) by
        simp [signedLit]))
  | @leFPush u a w i hl =>
    exact Automata.Move.push (w := w) i (signed_mem (c := c) hl
      (show LitT.fLe (fun j => (a j, !(c j))) (u, true) ∈ signedLit c (.leF u a) by
        simp [signedLit]))

private theorem signed_to_move {p q : Automata.Config n (V × Bool)}
    (h : Automata.Move (signed c Γ) p q) :
    Move c Γ (assoc.symm p) (assoc.symm q) := by
  cases h with
  | copy hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, LitT.le.injEq, List.not_mem_nil,
        or_false, reduceCtorEq, or_self] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .copyPlus hsrc
    · exact .copyMinus hsrc
  | push i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, reduceCtorEq, List.not_mem_nil,
        or_self, LitT.fLe.injEq, or_false, false_or] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .fLePush (c := c) i hsrc
    · exact .leFPush (c := c) i hsrc
  | pop i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, reduceCtorEq, List.not_mem_nil,
        or_self, LitT.leF.injEq, or_false, false_or] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .fLePop _ hsrc
    · exact .leFPop _ hsrc

/-- Move derivations are the move derivations of the signed translation. -/
theorem moves_iff_signed {p q : Config n V} :
    Relation.ReflTransGen (Move c Γ) p q ↔
      Automata.Moves (signed c Γ) (assoc p) (assoc q) := by
  constructor
  · intro h
    exact h.lift assoc fun _ _ hm => move_to_signed hm
  · intro h
    have h' : Relation.ReflTransGen (Move c Γ) (assoc.symm (assoc p)) (assoc.symm (assoc q)) :=
      h.lift assoc.symm fun _ _ hm => signed_to_move hm
    simpa only [Equiv.symm_apply_apply] using h'

/-- Exchanging the sign, as an embedding. -/
def flipEmb : (V × Bool) ↪ (V × Bool) :=
  ⟨flipV, fun _ _ h => by simpa using congrArg flipV h⟩

@[simp] theorem flipEmb_apply (p : V × Bool) : flipEmb p = flipV p := rfl

/-- A move preserves the sign of a configuration shifted by the polarity of its path. -/
theorem move_sign {p q : Config n V} (h : Move c Γ p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by
  cases h <;> simp

theorem moves_sign {p q : Config n V}
    (h : Relation.ReflTransGen (Move c Γ) p q) :
    Bool.xor q.2.1 (polarity c q.2.2) =
      Bool.xor p.2.1 (polarity c p.2.2) := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact (move_sign hm).trans ih

section Automata
variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem mem_map_flip {S : Finset (V × Bool)} {x : V × Bool} :
    x ∈ S.map flipEmb ↔ flipV x ∈ S := by
  simp only [Finset.mem_map, flipEmb_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨flipV x, h, flipV_flipV x⟩

/-- Exchanging the signs turns the upper run of a signed variable into the lower run of its
opposite sign. -/
theorem lowerRun_flip (y : V × Bool) (w : List (Fin n)) :
    Automata.lowerRun (signed c Γ) (flipV y) w =
      (Automata.upperRun (signed c Γ) y w).map flipEmb := by
  ext x
  rw [mem_map_flip, ← lowerAt_iff_run, ← upperAt_iff_run]
  constructor
  · intro h
    simpa using SignSelection.lowerAt_flip (SignSelection.signed_flipClosed c Γ) h
  · intro h
    simpa using SignSelection.upperAt_flip (SignSelection.signed_flipClosed c Γ) h

omit [Fintype V] [DecidableEq V] in
/-- The bounded variable of an upper constructor bound of the signed translation is the root of a
negative fact. -/
theorem signed_upper_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : LitT.leF r a ∈ signed c Γ) : Neg Γ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [signedLit, List.mem_cons, reduceCtorEq, List.not_mem_nil,
      or_self, LitT.leF.injEq, or_false, false_or] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fLe hl
  · exact .leF hl

theorem popRoot {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Automata.upperRun (signed c Γ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Automata.upperRun (signed c Γ) x β, Neg Γ (r.1, r.2, []) := by
  obtain ⟨a, ha⟩ := h
  rw [Automata.upperRun_snoc, Automata.mem_upperStep] at ha
  obtain ⟨r, hr, a, hl, _⟩ := ha
  exact ⟨r, hr, signed_upper_neg hl⟩

theorem upperRun_nil_absorb {x : V × Bool} {β : List (Fin n)}
    (h : Automata.upperRun (signed c Γ) x β = ∅) (γ : List (Fin n)) :
    Automata.upperRun (signed c Γ) x (β ++ γ) = ∅ := by
  induction γ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w i ih =>
      rw [← List.append_assoc, Automata.upperRun_snoc, ih, Automata.upperStep_empty]

theorem lowest_point_leaf {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c Γ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.upperRun (signed c Γ) (p, s) (u.take i) ∩
          Automata.lowerRun (signed c Γ) (q, s') (t.take e)).Nonempty := by
  rw [moves_iff_signed]
  exact Automata.lowest_point

/-- All signed variables in an upper run state have the sign of the start shifted by the polarity of
the path. -/
theorem sign_coherent {p : V} {s : Bool} {r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Automata.upperRun (signed c Γ) (p, s) w) :
    r.2 = Bool.xor s (polarity c w) := by
  have hm := (Automata.mem_upperRun_iff_moves w).mp h
  have hh : Relation.ReflTransGen (Move c Γ) (p, s, w) (r.1, r.2, []) :=
    moves_iff_signed.mpr hm
  simpa using moves_sign hh

end Automata

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints

variable {n : ℕ} {V : Type*}

/-- The facts of a constraint, as a list. -/
def factList (Γ : List (LitT n V)) : List (Config n V) :=
  Γ.flatMap fun l => match l with
    | .eqBot v => [(v, true, [])]
    | .eqTop v => [(v, false, [])]
    | _ => []

/-- The negative facts of a constraint, as a list. -/
def negList (Γ : List (LitT n V)) : List (Config n V) :=
  Γ.flatMap fun l => match l with
    | .fLe _ v => [(v, true, [])]
    | .leF v _ => [(v, false, [])]
    | _ => []

@[simp] theorem mem_factList {Γ : List (LitT n V)} {f : Config n V} :
    f ∈ factList Γ ↔ Fact Γ f := by
  constructor
  · intro h
    obtain ⟨l, hl, hf⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hf
    · subst f; exact .bot hl
    · subst f; exact .top hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

@[simp] theorem mem_negList {Γ : List (LitT n V)} {n : Config n V} :
    n ∈ negList Γ ↔ Neg Γ n := by
  constructor
  · intro h
    obtain ⟨l, hl, hn⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hn
    · subst n; exact .fLe hl
    · subst n; exact .leF hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

theorem Fact.word_nil {Γ : List (LitT n V)} {f : Config n V} (h : Fact Γ f) :
    f.2.2 = [] := by cases h <;> rfl

theorem Neg.word_nil {Γ : List (LitT n V)} {n : Config n V} (h : Neg Γ n) :
    n.2.2 = [] := by cases h <;> rfl

/-- A state reachable by some word is reachable by a word of length at most the number of states. -/
theorem bounded_run_iff {S : Type*} [Fintype S] (M : Semiautomaton (Fin n) S)
    (q : S) (H : S → Prop) :
    (∃ w ∈ wordsUpTo (α := Fin n) (Fintype.card S), H (runFrom M.step q w)) ↔
      ∃ w, H (runFrom M.step q w) := by
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, _, he⟩ := M.short_safe_path (fun _ => True) q w
      ((M.pathSafe_iff _ _ _).mpr (by simp))
    exact ⟨v, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hv), he ▸ hw⟩

variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))

/-- The signed variables reached by an upper run from a fact. -/
def factReachableVariables : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ f ∈ factList Γ, ∃ β ∈ wordsUpTo (α := Fin n) (Fintype.card (Finset (V × Bool))),
    x ∈ Automata.upperRun (signed c Γ) (f.1, f.2.1) β

/-- The signed variables derivably below the root of a negative fact. -/
def forbiddenPredecessors : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ n ∈ negList Γ, (x, (n.1, n.2.1)) ∈ Constraints.derivedPairs (signed c Γ)

variable {c Γ}

theorem mem_factReachableVariables {x : V × Bool} : x ∈ factReachableVariables c Γ ↔
    ∃ f β, Fact Γ f ∧ x ∈ Automata.upperRun (signed c Γ) (f.1, f.2.1) β := by
  simp only [factReachableVariables, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, β, _, hβ⟩; exact ⟨f, β, mem_factList.mp hf, hβ⟩
  · rintro ⟨f, β, hf, hβ⟩
    refine ⟨f, mem_factList.mpr hf, ?_⟩
    exact (bounded_run_iff (Automata.upper (signed c Γ) (f.1, f.2.1))
      _ (fun S => x ∈ S)).mpr ⟨β, hβ⟩

theorem mem_forbiddenPredecessors {x : V × Bool} : x ∈ forbiddenPredecessors c Γ ↔
    ∃ n, Neg Γ n ∧ (x, (n.1, n.2.1)) ∈ Constraints.derivedPairs (signed c Γ) := by
  simp [forbiddenPredecessors]

/-- A signed configuration lies in the least closure exactly when the lower run of its signed
variable on some prefix of its path meets the signed variables reachable from facts. -/
theorem leastClosure_membership {q : V} {s : Bool} {t : List (Fin n)} :
    (q, s, t) ∈ leastClosure c Γ ↔ ∃ e ≤ t.length,
      (Automata.lowerRun (signed c Γ) (q,
          s) (t.take e) ∩ factReachableVariables c Γ).Nonempty := by
  constructor
  · rintro hm
    obtain ⟨⟨f, s', w⟩, hf, hr⟩ := mem_leastClosure.mp hm
    have hw := hf.word_nil; dsimp at hw; subst w
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, _, e, he, _, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    exact ⟨e, he, r, Finset.mem_inter.mpr ⟨hq,
      mem_factReachableVariables.mpr ⟨(f, s', []), α.take i, hf, hp⟩⟩⟩
  · rintro ⟨e, he, r, hr⟩
    obtain ⟨hq, hf⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨f, s', w⟩, β, hf, hp⟩ := mem_factReachableVariables.mp hf
    have hw := hf.word_nil; dsimp at hw; subst w
    apply mem_leastClosure.mpr
    refine ⟨(f, s', []), hf, reach_iff_moves.mpr ⟨β ++ t.drop e, ?_⟩⟩
    apply lowest_point_leaf.mpr
    refine ⟨β.length, by simp, e, he, by simp, r, ?_⟩
    simpa using Finset.mem_inter.mpr ⟨hp, hq⟩

theorem reach_neg_iff {p : V} {s : Bool} {u : List (Fin n)} :
    (∃ n, Neg Γ n ∧ Reach c Γ (p, s, u) n) ↔
      ∃ z, (Automata.upperRun (signed c Γ) (p,
          s) (u ++ z) ∩ forbiddenPredecessors c Γ).Nonempty := by
  constructor
  · rintro ⟨⟨n, sn, w⟩, hn, hr⟩
    have hw := hn.word_nil; dsimp at hw; subst w
    obtain ⟨z, hz⟩ := reach_iff_moves.mp hr
    have hp := (mem_upperRun_iff_moves (u ++ z)).mpr (moves_iff_signed.mp hz)
    exact ⟨z, (n, sn), Finset.mem_inter.mpr ⟨hp,
      mem_forbiddenPredecessors.mpr ⟨(n, sn, []), hn, Automata.derivedPairs_refl _ _⟩⟩⟩
  · rintro ⟨z, r, hr⟩
    obtain ⟨hp, hn⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨n, sn, w⟩, hn, hd⟩ := mem_forbiddenPredecessors.mp hn
    have hw := hn.word_nil; dsimp at hw; subst w
    refine ⟨(n, sn, []), hn, reach_iff_moves.mpr ⟨z, ?_⟩⟩
    apply moves_iff_signed.mpr
    exact ((mem_upperRun_iff_moves _).mp hp).trans (Automata.derivedPairs_moves hd [])

variable (c Γ)

/-- The set `S` with exchanged signs meets the signed variables reachable from facts. -/
def FlippedIntersectsFacts (S : Finset (V × Bool)) : Prop :=
  (S.map flipEmb ∩ factReachableVariables c Γ).Nonempty

/-- The configuration `(p, u)` reaches a variable below a negative fact along some extension of `u`,
or its opposite sign lies in the least closure at some extension of `u`. -/
def HasUnaryObstruction (p : V × Bool) (u : List (Fin n)) : Prop :=
  (∃ z,
      (Automata.upperRun (signed c Γ) p (u ++ z) ∩ forbiddenPredecessors c Γ).Nonempty) ∨
    ∃ δ, (p.1, !p.2, u ++ δ) ∈ leastClosure c Γ

/-- The upper runs of `p` at the cuts `i < j` of `u` contain opposite signs of one variable, and the
suffix of `u` after `j` is a prefix of the suffix after `i`: the configuration derives its own
opposite sign. -/
def SelfCollisionEvent (p : V × Bool) (u : List (Fin n)) (i j : ℕ) : Prop :=
  i < j ∧ j ≤ u.length ∧ (u.drop j).IsPrefix (u.drop i) ∧
    (Automata.upperRun (signed c Γ) p (u.take i) ∩
      (Automata.upperRun (signed c Γ) p (u.take j)).map flipEmb).Nonempty

variable {c Γ}

/-- The opposite sign of `(p, t)` lies in the least closure exactly when the upper run of `p` on
some prefix of `t`, with exchanged signs, meets the signed variables reachable from facts. -/
theorem leastClosure_flip_membership {p : V × Bool} {t : List (Fin n)} :
    (p.1, !p.2, t) ∈ leastClosure c Γ ↔
      ∃ e ≤
          t.length, FlippedIntersectsFacts c Γ
              (Automata.upperRun (signed c Γ) p (t.take e)) := by
  rw [leastClosure_membership]
  change (∃ e ≤ t.length,
    (Automata.lowerRun (signed c Γ) (flipV p)
        (t.take e) ∩ factReachableVariables c Γ).Nonempty) ↔ _
  simp only [lowerRun_flip, FlippedIntersectsFacts]

/-- If the upper run on `v` is nonempty, so is the upper run on every prefix of `v`. -/
theorem upperRun_nonempty_prefix {p : V × Bool} {u v : List (Fin n)}
    (hp : u.IsPrefix v) (h : (Automata.upperRun (signed c Γ) p v).Nonempty) :
    (Automata.upperRun (signed c Γ) p u).Nonempty := by
  obtain ⟨z, rfl⟩ := hp
  by_contra hn
  have he := upperRun_nil_absorb (Finset.not_nonempty_iff_eq_empty.mp hn) z
  simp [he] at h

/-- If the upper run on `γ` is nonempty, the upper run on every proper prefix of `γ` meets the
signed variables below a negative fact. -/
theorem upperRun_proper_prefix_neg {p : V × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.upperRun (signed c Γ) p γ).Nonempty) (hi : i < γ.length) :
    (Automata.upperRun (signed c Γ) p
        (γ.take i) ∩ forbiddenPredecessors c Γ).Nonempty := by
  have hnext := upperRun_nonempty_prefix (List.take_prefix (i + 1) γ) h
  rw [List.take_succ_eq_append_getElem hi] at hnext
  obtain ⟨r, hr, hn⟩ := popRoot hnext
  exact ⟨r, Finset.mem_inter.mpr ⟨hr,
    mem_forbiddenPredecessors.mpr ⟨(r.1, r.2, []), hn, Automata.derivedPairs_refl _ _⟩⟩⟩

/-- Without a unary obstruction at `(p, u)`, a nonempty upper run along `u ++ α` ends within `u`:
the cut `i` is at most `|u|`. -/
theorem cut_le_of_not_hasUnaryObstruction {p : V × Bool} {u α : List (Fin n)} {i : ℕ}
    (hdead : ¬ HasUnaryObstruction c Γ p u) (hi : i ≤ (u ++ α).length)
    (hp : (Automata.upperRun (signed c Γ) p ((u ++ α).take i)).Nonempty) :
    i ≤ u.length := by
  by_contra hn
  have hh := upperRun_proper_prefix_neg hp
    (show u.length < ((u ++ α).take i).length by
      rw [List.length_take, Nat.min_eq_left hi]; omega)
  apply hdead
  exact Or.inl ⟨[], by
    simpa [List.take_take, Nat.min_eq_left (by omega : u.length ≤ i)] using hh⟩

/-- If the upper run of `p` on a prefix of `u` meets the lower run of `q` on a prefix of `t`, and
the rest of `u` is a prefix of the rest of `t`, then `(p, u)` derives `(q, t)`. -/
theorem reach_of_cuts {p q : V × Bool} {u t : List (Fin n)} {i e : ℕ}
    (hi : i ≤ u.length) (he : e ≤ t.length)
    (hpre : (u.drop i).IsPrefix (t.drop e))
    (hg : (Automata.upperRun (signed c Γ) p (u.take i) ∩
      Automata.lowerRun (signed c Γ) q (t.take e)).Nonempty) :
    Reach c Γ (p.1, p.2, u) (q.1, q.2, t) := by
  obtain ⟨α, hα⟩ := hpre
  apply reach_iff_moves.mpr
  refine ⟨α, lowest_point_leaf.mpr ⟨i, by simp; omega, e, he, ?_, ?_⟩⟩
  · simpa [List.drop_append_of_le_length hi] using hα
  · simpa [List.take_append_of_le_length hi] using hg

theorem reach_iff_cuts_of_not_hasUnaryObstruction {p q : V × Bool} {u t : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c Γ p u) :
    Reach c Γ (p.1, p.2, u) (q.1, q.2, t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.upperRun (signed c Γ) p (u.take i) ∩
          Automata.lowerRun (signed c Γ) q (t.take e)).Nonempty := by
  constructor
  · intro hr
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, hi, e, he, hdrops, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    have hib := cut_le_of_not_hasUnaryObstruction hd hi ⟨r, hp⟩
    refine ⟨i, hib, e, he, ⟨α, ?_⟩, r, Finset.mem_inter.mpr ⟨?_, hq⟩⟩
    · simpa [List.drop_append_of_le_length hib] using hdrops
    · simpa [List.take_append_of_le_length hib] using hp
  · rintro ⟨i, hi, e, he, hp, hg⟩
    exact reach_of_cuts hi he hp hg

omit [Fintype V] in
/-- `A` meets the sign exchange of `B` exactly when `B` meets the sign exchange of `A`. -/
theorem flip_inter_symm {A B : Finset (V × Bool)} :
    (A ∩ B.map flipEmb).Nonempty ↔ (B ∩ A.map flipEmb).Nonempty := by
  have turn {A B : Finset (V × Bool)} (h : (A ∩ B.map flipEmb).Nonempty) :
      (B ∩ A.map flipEmb).Nonempty := by
    obtain ⟨r, hr⟩ := h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hr
    exact ⟨flipV r, Finset.mem_inter.mpr ⟨mem_map_flip.mp hb,
      mem_map_flip.mpr (by simpa using ha)⟩⟩
  exact ⟨turn, turn⟩

theorem self_guard_ne {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (hg : (Automata.upperRun (signed c Γ) p (u.take i) ∩
      (Automata.upperRun (signed c Γ) p (u.take j)).map flipEmb).Nonempty) : i ≠ j := by
  rintro rfl
  obtain ⟨r, hr⟩ := hg
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
  have h₁ := sign_coherent hp
  have h₂ := sign_coherent (mem_map_flip.mp hq)
  change (!r.2) = _ at h₂
  rw [← h₁] at h₂
  cases r.2 <;> simp at h₂

theorem selfCollisionEvent_return {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (h : SelfCollisionEvent c Γ p u i j) :
    ∃ δ, Reach c Γ (p.1, p.2, u) (p.1, !p.2, u ++ δ) := by
  obtain ⟨hij, hj, ⟨δ, hδ⟩, hg⟩ := h
  refine ⟨δ, reach_of_cuts (p := p) (q := flipV p) (i := i)
    (Nat.le_trans (Nat.le_of_lt hij) hj)
    (show j ≤ (u ++ δ).length by simp; omega) ?_ ?_⟩
  · rw [List.drop_append_of_le_length hj, hδ]
  · rw [List.take_append_of_le_length hj, lowerRun_flip]
    exact hg

/-- Without a unary obstruction, a derivation of the opposite sign at an extension of the path
gives a self-collision event. -/
theorem return_selfCollisionEvent_of_not_hasUnaryObstruction {p : V × Bool} {u δ : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c Γ p u)
    (hr : Reach c Γ (p.1, p.2, u) (p.1, !p.2, u ++ δ)) :
    ∃ i j, SelfCollisionEvent c Γ p u i j := by
  obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
  obtain ⟨i, hi, j, hj, heq, r, hg⟩ := lowest_point_leaf.mp hα
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hg
  change r ∈ Automata.lowerRun (signed c Γ) (flipV p) ((u ++ δ).take j) at hq
  rw [lowerRun_flip, mem_map_flip] at hq
  have hib := cut_le_of_not_hasUnaryObstruction hd hi ⟨r, hp⟩
  have hjb := cut_le_of_not_hasUnaryObstruction hd hj ⟨flipV r, hq⟩
  rw [List.take_append_of_le_length hib] at hp
  rw [List.take_append_of_le_length hjb] at hq
  rw [List.drop_append_of_le_length hib, List.drop_append_of_le_length hjb] at heq
  have guard : (Automata.upperRun (signed c Γ) p (u.take i) ∩
      (Automata.upperRun (signed c Γ) p (u.take j)).map flipEmb).Nonempty :=
    ⟨r, Finset.mem_inter.mpr ⟨hp, mem_map_flip.mpr hq⟩⟩
  have hne := self_guard_ne guard
  have pi : (u.drop i).IsPrefix (u.drop i ++ α) := List.prefix_append _ _
  have pj : (u.drop j).IsPrefix (u.drop i ++ α) := heq.symm ▸ List.prefix_append _ _
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, hjb,
      List.prefix_of_prefix_length_le pj pi (by simp; omega), guard⟩
  · exact ⟨j, i, hji, hib,
      List.prefix_of_prefix_length_le pi pj (by simp; omega), flip_inter_symm.mp guard⟩

/-- For a satisfiable constraint, a configuration is not live exactly when it has a unary
obstruction or a self-collision event. -/
theorem not_live_iff_unaryObstruction_or_selfCollision
    (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V × Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p.1, p.2, u) ↔
      HasUnaryObstruction c Γ p u ∨ ∃ i j, SelfCollisionEvent c Γ p u i j := by
  classical
  rw [dead_iff hsat]
  constructor
  · rintro (hn | hm | ⟨δ, hr⟩)
    · exact Or.inl (Or.inl (reach_neg_iff.mp hn))
    · exact Or.inl (Or.inr hm)
    · by_cases hd : HasUnaryObstruction c Γ p u
      · exact Or.inl hd
      · exact Or.inr (return_selfCollisionEvent_of_not_hasUnaryObstruction hd hr)
  · rintro ((hn | hm) | ⟨i, j, hs⟩)
    · exact Or.inl (reach_neg_iff.mpr hn)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (selfCollisionEvent_return hs))

end DeciSigma1.Full.Closure

namespace DeciSigma1.Full.Closure

variable {n : ℕ}
open DeciSigma1.Automata
open DeciSigma1.Constraints

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))

/-- Satisfiability with variance `c` is decidable: the signed translation is tested for a label
clash. -/
def decideSat : Decidable (∃ ρ, SatT c ρ Γ) :=
  decidable_of_iff (Satisfiability.satInfB (signed c Γ) = true)
    ((Satisfiability.satInfB_iff_not_labelClash _).trans
      (Satisfiability.sat_iff_signed_not_labelClash c Γ).symm)

end DeciSigma1.Full.Closure
