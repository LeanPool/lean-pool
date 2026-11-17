/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/PriorityStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPair
public import LeanPool.TuringConeRigidity.CohenForcing.EffectiveForcing
public import LeanPool.TuringConeRigidity.Effective.StageEngine

/-!
# Priority Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PriorityStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Select the uniform pair procedure used by the priority construction. -/
def pairProcedure (A : Oracle) : ℕ → ℕ := Classical.choose (UniformPair.pair_exists A)

theorem pairProcedure_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (pairProcedure A v)) :=
  (Classical.choose_spec (UniformPair.pair_exists A)).1

/-- Select a uniform procedure deciding open requirements relative to `A`. -/
def openProcedure (A : Oracle) : ℕ → ℕ :=
  Classical.choose (EffectiveForcing.uniform_open_decision A A (reduces_refl A))

theorem open_extends (A : Oracle) (e : ℕ) (p : Condition) :
    Extends (columns A) p (condition (openProcedure A (Nat.pair e (code p)))) := by
  have h := ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl
    A))).2 e (code p)).1
  simpa only [condition_code,openProcedure] using h

/-- The two selected procedures supplied to the shared stage engine. -/
def procedures (A : Oracle) : StageEngine.Procedures :=
  ⟨pairProcedure A, openProcedure A⟩

/-- The pair-procedure candidate at priority `t`, normalized to level `t`. -/
def candidate (A : Oracle) (t : ℕ) (p : Condition) : Condition :=
  StageEngine.candidate (procedures A) t p

theorem candidate_extends (A : Oracle) (t : ℕ) (p : Condition) :
    Extends (columns A) (atLevel p t) (candidate A t p) := by
  have h := ((Classical.choose_spec (UniformPair.pair_exists A)).2 t (code (atLevel p t))).1
  rw [condition_code] at h
  exact ⟨h.1,h.2.1,le_rfl,h.2.2.2⟩

/-- The priority candidate changes at least one of the two condition words. -/
def Changes (A : Oracle) (t : ℕ) (p : Condition) : Prop :=
  StageEngine.Changes (procedures A) t p

/-- Search a bounded range for an unfinished priority that changes the condition. -/
def scan (A : Oracle) (p : Condition) (done : Finset ℕ) (t : ℕ) : ℕ → Option ℕ :=
  StageEngine.scan (procedures A) p done t

/-- A bounded scan of length zero selects no action. -/
theorem scan_zero (A : Oracle) (p : Condition) (done : Finset ℕ) (t : ℕ) :
    scan A p done t 0 = none := rfl

/-- A nonempty scan first examines its least priority. -/
theorem scan_succ (A : Oracle) (p : Condition) (done : Finset ℕ) (t n : ℕ) :
    scan A p done t (n+1) =
      if t ∉ done ∧ Changes A t p then some t else scan A p done (t+1) n := rfl

/-- The two defining cases of the bounded scan, with a stable public equation name. -/
theorem scan_eq_match (A : Oracle) (p : Condition) (done : Finset ℕ) (t n : ℕ) :
    scan A p done t n = match n with
      | 0 => none
      | n+1 => if t ∉ done ∧ Changes A t p then some t else scan A p done (t+1) n := by
  cases n <;> rfl

theorem scan_spec {A : Oracle} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan A p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes A i p :=
  StageEngine.scan_spec h

/-- A priority state containing its condition, completed priorities, and visited priorities. -/
structure State where
  /-- The current priority-construction condition. -/
  condition : Condition
  /-- The priorities currently marked completed. -/
  done : Finset ℕ
  /-- The priorities visited since their last injury reset. -/
  seen : Finset ℕ

/-- The unchanged public state representation, exposed to the shared engine. -/
def stateInterface : StageEngine.StateInterface State where
  condition := State.condition
  done := State.done
  seen := State.seen
  make := State.mk
  condition_make := fun _ _ _ => rfl
  done_make := fun _ _ _ => rfl
  seen_make := fun _ _ _ => rfl

/-- Extend the condition to meet the least unvisited open requirement. -/
def generic (A : Oracle) (p : State) : Condition :=
  StageEngine.generic stateInterface (procedures A) p

/-- The bounded priority action selected after the generic extension. -/
def stageAction (A : Oracle) (s : ℕ) (p : State) : Option ℕ :=
  StageEngine.stageAction stateInterface (procedures A) s p

/-- Select the stage condition from the generic extension and any priority candidate. -/
def stageWord (A : Oracle) (s : ℕ) (p : State) : Condition :=
  StageEngine.stageWord stateInterface (procedures A) s p

/-- Advance the priority condition and update its completed and visited records. -/
def advance (A : Oracle) (s : ℕ) (p : State) : State :=
  StageEngine.advance stateInterface (procedures A) s p

/-- The priority state sequence starting from the empty condition and empty records. -/
def construction (A : Oracle) : ℕ → State :=
  StageEngine.construction stateInterface (procedures A)

/-- The construction begins at the original empty state. -/
theorem construction_zero (A : Oracle) : construction A 0 = ⟨⟨[], [], rfl, 0⟩, ∅, ∅⟩ := rfl

/-- Each construction step applies the stage transition to its predecessor. -/
theorem construction_succ (A : Oracle) (s : ℕ) :
    construction A (s+1) = advance A s (construction A s) := rfl

/-- The two construction cases, with a stable public equation name. -/
theorem construction_eq_match (A : Oracle) (s : ℕ) :
    construction A s = match s with
      | 0 => ⟨⟨[], [], rfl, 0⟩, ∅, ∅⟩
      | s+1 => advance A s (construction A s) := by
  cases s <;> rfl

/-- The condition component of the priority state at stage `s`. -/
def conditions (A : Oracle) (s : ℕ) :=
  StageEngine.conditions stateInterface (procedures A) s

/-- The finite-injury action proposal produced by the priority state at stage `s`. -/
def proposal (A : Oracle) (s : ℕ) (_ : Finset ℕ) : Option ℕ :=
  StageEngine.proposal stateInterface (procedures A) s ∅

theorem action_not_done (A : Oracle) (s : ℕ) (p : State) (t : ℕ)
    (h : stageAction A s p = some t) : t ∉ p.done :=
  StageEngine.action_not_done stateInterface (procedures A) s p t h

theorem accept_action (A : Oracle) (s : ℕ) (p : State) :
    FiniteInjury.accept p.done (stageAction A s p) = stageAction A s p :=
  StageEngine.accept_action stateInterface (procedures A) s p

theorem done_eq (A : Oracle) (s : ℕ) :
    (construction A s).done = FiniteInjury.state (proposal A) s :=
  StageEngine.done_eq stateInterface (procedures A) s

theorem action_eq (A : Oracle) (s : ℕ) :
    FiniteInjury.action (proposal A) s = stageAction A s (construction A s) :=
  StageEngine.action_eq stateInterface (procedures A) s

theorem seen_eq (A : Oracle) (s : ℕ) :
    (construction A s).seen = FiniteInjurySchedule.seen (proposal A) s :=
  StageEngine.seen_eq stateInterface (procedures A) s

theorem active_eq (A : Oracle) (s : ℕ) : (conditions A s).active = s :=
  StageEngine.active_eq stateInterface (procedures A) s

theorem stage_words (A : Oracle) (s : ℕ) (p : State) :
    p.condition.left <+: (stageWord A s p).left ∧ p.condition.right <+: (stageWord A s p).right :=
  StageEngine.stage_words stateInterface (procedures A) (candidate_extends A) (open_extends A) s p

theorem word_growth (A : Oracle) (s : ℕ) :
    (conditions A s).left <+: (conditions A (s+1)).left ∧
    (conditions A s).right <+: (conditions A (s+1)).right :=
  StageEngine.word_growth stateInterface (procedures A) (candidate_extends A) (open_extends A) s

theorem length_bound (A : Oracle) (s : ℕ) : s ≤ (conditions A s).left.length :=
  StageEngine.length_bound stateInterface (procedures A) (candidate_extends A) (open_extends A) s

theorem level_step (A : Oracle) (s k : ℕ) (hk : k ≤ s)
    (hact : ∀ t, FiniteInjury.action (proposal A) s = some t → k ≤ t) :
    Extends (columns A) (atLevel (conditions A s) k) (atLevel (conditions A (s+1)) k) :=
  StageEngine.level_step stateInterface (procedures A) (candidate_extends A) (open_extends A)
    s k hk hact

theorem surviving_columns (A : Oracle) (k : ℕ) : ∃ S, ∀ m,
    (conditions A S).left.length ≤ m → (Nat.unpair m).1 < k →
    columns A (Nat.unpair m).1 (Nat.unpair m).2 = true →
    leftLimit (conditions A) m = rightLimit (conditions A) m :=
  StageEngine.surviving_columns stateInterface (procedures A) (candidate_extends A) (open_extends A)
    k

theorem surviving_generic_visit (A : Oracle) (t : ℕ) : ∃ s,
    FiniteInjurySchedule.visit (construction A s).seen = t ∧
      ∀ u, s ≤ u → ∀ i < t, stageAction A u (construction A u) ≠ some i :=
  StageEngine.surviving_generic_visit stateInterface (procedures A) t

end
end TuringRigidity.PriorityStage

end OAI
