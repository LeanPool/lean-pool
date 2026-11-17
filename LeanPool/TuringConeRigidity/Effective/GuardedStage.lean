/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedPair
public import LeanPool.TuringConeRigidity.CohenForcing.EffectiveForcing
public import LeanPool.TuringConeRigidity.Effective.FiniteInjuryLimits
public import LeanPool.TuringConeRigidity.Effective.FiniteInjurySchedule

/-!
# Guarded Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The selected guarded pair procedure, exposed for the stage construction. -/
def pairProcedure (A : Oracle) : ℕ → ℕ := GuardedPair.procedure A

theorem pairProcedure_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (pairProcedure A v)) :=
  (Classical.choose_spec (GuardedPair.pair_exists A)).1

/-- The candidate condition produced at priority `t`, normalized back to level `t`. -/
def candidate (A : Oracle) (t : ℕ) (p : Condition) : Condition :=
  atLevel (condition (pairProcedure A (Nat.pair t (code (atLevel p t))))) t

theorem candidate_extends (A : Oracle) (t : ℕ) (p : Condition) :
    Extends (columns A) (atLevel p t) (candidate A t p) := by
  have h := ((Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code (atLevel p t))).1
  rw [condition_code] at h
  exact ⟨h.1,h.2.1,le_rfl,h.2.2.2⟩

/-- The guarded candidate changes at least one of the two condition words. -/
def Changes (A : Oracle) (t : ℕ) (p : Condition) : Prop :=
  (candidate A t p).left ≠ p.left ∨ (candidate A t p).right ≠ p.right

/-- Search the bounded priority range for an unfinished candidate that changes the condition. -/
def scan (A : Oracle) (p : Condition) (done : Finset ℕ) (t : ℕ) : ℕ → Option ℕ
  | 0 => none
  | n+1 => if t ∉ done ∧ Changes A t p then some t else scan A p done (t+1) n

theorem scan_spec {A : Oracle} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan A p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes A i p := by
  induction n generalizing t with
  | zero => simp [scan] at h
  | succ n ih =>
    simp only [scan] at h
    split at h
    · rename_i ht
      have he := Option.some.inj h
      subst i
      exact ⟨le_rfl,by omega,ht⟩
    · obtain ⟨hlo,hhi,hd,hc⟩ := ih h
      exact ⟨by omega,by omega,hd,hc⟩

/-- Select a uniform procedure deciding the open requirements relative to `A`. -/
def openProcedure (A : Oracle) : ℕ → ℕ :=
  Classical.choose (EffectiveForcing.uniform_open_decision A A (reduces_refl A))

theorem open_extends (A : Oracle) (e : ℕ) (p : Condition) :
    Extends (columns A) p (condition (openProcedure A (Nat.pair e (code p)))) := by
  have h := ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl
    A))).2 e (code p)).1
  simpa only [condition_code,openProcedure] using h

/-- A guarded construction state with its condition, completed priorities, and visited
priorities. -/
structure State where
  /-- The current pair of finite condition words and active level. -/
  condition : Condition
  /-- The priorities currently marked completed. -/
  done : Finset ℕ
  /-- The priorities visited since their most recent injury reset. -/
  seen : Finset ℕ

/-- Extend the current condition to meet its least unvisited open requirement. -/
def generic (A : Oracle) (p : State) : Condition :=
  EncodedForcing.condition (openProcedure A (Nat.pair (FiniteInjurySchedule.visit p.seen) (code
    p.condition)))

/-- The bounded guarded-priority action selected after the generic extension. -/
def stageAction (A : Oracle) (s : ℕ) (p : State) : Option ℕ := scan A (generic A p) p.done 0 s

/-- The stage condition obtained from the generic extension and any selected guarded action. -/
def stageWord (A : Oracle) (s : ℕ) (p : State) : Condition :=
  match stageAction A s p with
  | none => generic A p
  | some t => candidate A t (generic A p)

/-- Advance the guarded condition and update the completed and visited priority records. -/
def advance (A : Oracle) (s : ℕ) (p : State) : State where
  condition := atLevel (append (stageWord A s p) [false]) (s+1)
  done := FiniteInjury.update p.done (stageAction A s p)
  seen := FiniteInjurySchedule.reset (insert (FiniteInjurySchedule.visit p.seen) p.seen)
    (stageAction A s p)

/-- The guarded state sequence starting from the empty condition and empty records. -/
def construction (A : Oracle) : ℕ → State
  | 0 => ⟨⟨[],[],rfl,0⟩,∅,∅⟩
  | s+1 => advance A s (construction A s)

/-- The condition component of the guarded state at stage `s`. -/
def conditions (A : Oracle) (s : ℕ) := (construction A s).condition

/-- The injury proposal generated by the guarded state at the specified stage. -/
def proposal (A : Oracle) (s : ℕ) (_ : Finset ℕ) : Option ℕ :=
  stageAction A s (construction A s)

theorem action_not_done (A : Oracle) (s : ℕ) (p : State) (t : ℕ)
    (h : stageAction A s p = some t) : t ∉ p.done := (scan_spec h).2.2.1

theorem accept_action (A : Oracle) (s : ℕ) (p : State) :
    FiniteInjury.accept p.done (stageAction A s p) = stageAction A s p := by
  cases ha : stageAction A s p with
  | none => simp [FiniteInjury.accept]
  | some t => simp [FiniteInjury.accept,action_not_done A s p t ha]

theorem done_eq (A : Oracle) (s : ℕ) :
    (construction A s).done = FiniteInjury.state (proposal A) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjury.update (construction A s).done (stageAction A s (construction A s)) = _
    rw [FiniteInjury.state]
    rw [← ih]
    simp only [proposal,accept_action]

theorem action_eq (A : Oracle) (s : ℕ) :
    FiniteInjury.action (proposal A) s = stageAction A s (construction A s) := by
  rw [FiniteInjury.action,← done_eq]
  exact accept_action A s _

theorem seen_eq (A : Oracle) (s : ℕ) :
    (construction A s).seen = FiniteInjurySchedule.seen (proposal A) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjurySchedule.reset _ _ = _
    rw [FiniteInjurySchedule.seen,action_eq,← ih]

theorem active_eq (A : Oracle) (s : ℕ) : (conditions A s).active = s := by
  cases s <;> rfl

theorem stage_words (A : Oracle) (s : ℕ) (p : State) :
    p.condition.left <+: (stageWord A s p).left ∧ p.condition.right <+: (stageWord A s p).right :=
      by
  have ho := open_extends A (FiniteInjurySchedule.visit p.seen) p.condition
  cases ha : stageAction A s p with
  | none => exact ⟨by simpa [stageWord, ha, generic] using ho.1, by simpa [stageWord, ha, generic]
      using ho.2.1⟩
  | some t =>
    have hc := candidate_extends A t (generic A p)
    exact ⟨by simpa [stageWord,ha] using ho.1.trans hc.1,
      by simpa [stageWord,ha] using ho.2.1.trans hc.2.1⟩

theorem word_growth (A : Oracle) (s : ℕ) :
    (conditions A s).left <+: (conditions A (s+1)).left ∧
    (conditions A s).right <+: (conditions A (s+1)).right := by
  have h := stage_words A s (construction A s)
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem length_bound (A : Oracle) (s : ℕ) : s ≤ (conditions A s).left.length := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have h := (stage_words A s (construction A s)).1.length_le
    change s+1 ≤ ((stageWord A s (construction A s)).left ++ [false]).length
    simp only [List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (ih.trans h) 1

theorem level_step (A : Oracle) (s k : ℕ) (hk : k ≤ s)
    (hact : ∀ t, FiniteInjury.action (proposal A) s = some t → k ≤ t) :
    Extends (columns A) (atLevel (conditions A s) k) (atLevel (conditions A (s+1)) k) := by
  let p := construction A s
  have ho := open_extends A (FiniteInjurySchedule.visit p.seen) p.condition
  have hg : Extends (columns A) (atLevel p.condition k) (atLevel (generic A p) k) := by
    refine ⟨ho.1,ho.2.1,le_rfl,?_⟩
    intro m hm hlen
    apply ho.2.2.2 m ⟨hm.1,?_,hm.2.2⟩ hlen
    exact hm.2.1.trans_le (by
      change k ≤ (conditions A s).active
      rw [active_eq]
      exact hk)
  have hw : Extends (columns A) (atLevel (generic A p) k) (atLevel (stageWord A s p) k) := by
    cases ha : stageAction A s p with
    | none => simpa [stageWord,ha] using extends_refl (columns A) (atLevel (generic A p) k)
    | some t =>
      have hkt : k ≤ t := hact t (by simpa [action_eq,p] using ha)
      have hc := candidate_extends A t (generic A p)
      have hc' : Extends (columns A) (atLevel (generic A p) t) (atLevel (candidate A t (generic A
        p)) t) := hc
      simpa [stageWord,ha] using level_mono hc' hkt
  have htail : Extends (columns A) (atLevel (stageWord A s p) k)
      (atLevel (conditions A (s+1)) k) := append_extends _ _ [false]
  exact extends_trans hg (extends_trans hw htail)

theorem surviving_columns (A : Oracle) (k : ℕ) : ∃ S, ∀ m,
    (conditions A S).left.length ≤ m → (Nat.unpair m).1 < k →
    columns A (Nat.unpair m).1 (Nat.unpair m).2 = true →
    leftLimit (conditions A) m = rightLimit (conditions A) m :=
  eventual_column_agreement (columns A) (proposal A) (conditions A)
    (word_growth A) (length_bound A) (level_step A) k

theorem surviving_generic_visit (A : Oracle) (t : ℕ) : ∃ s,
    FiniteInjurySchedule.visit (construction A s).seen = t ∧
      ∀ u, s ≤ u → ∀ i < t, stageAction A u (construction A u) ≠ some i := by
  obtain ⟨s,hs,hh⟩ := FiniteInjurySchedule.surviving_visit (proposal A) t
  refine ⟨s,?_,?_⟩
  · simpa [seen_eq,FiniteInjurySchedule.scheduled] using hs
  · simpa only [action_eq] using hh

end
end TuringRigidity.GuardedStage

end OAI
