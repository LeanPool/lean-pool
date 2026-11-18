/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalInputs
public import LeanPool.TuringConeRigidity.Effective.StageEngine

/-!
# Local Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The selected pair procedure associated with the local input data. -/
def pairProcedure (D : LocalInputs.Data) : ℕ → ℕ := D.pairProcedure

theorem pairProcedure_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun v => Part.some (pairProcedure D v)) :=
      D.pair_recursive

/-- The selected open-decision procedure associated with the local input data. -/
def openProcedure (D : LocalInputs.Data) : ℕ → ℕ := D.openProcedure

theorem open_extends (D : LocalInputs.Data) (e : ℕ) (p : Condition) :
    Extends D.F p (condition (openProcedure D (Nat.pair e (code p)))) := by
  simpa only [condition_code,openProcedure] using (D.open_spec e (code p)).1

/-- The two selected procedures supplied to the shared stage engine. -/
def procedures (D : LocalInputs.Data) : StageEngine.Procedures :=
  ⟨pairProcedure D, openProcedure D⟩

/-- The local candidate condition at priority `t`, normalized to level `t`. -/
def candidate (D : LocalInputs.Data) (t : ℕ) (p : Condition) : Condition :=
  StageEngine.candidate (procedures D) t p

theorem candidate_extends (D : LocalInputs.Data) (t : ℕ) (p : Condition) :
    Extends D.F (atLevel p t) (candidate D t p) := by
  have h := (D.pair_spec t (code (atLevel p t))).1
  rw [condition_code] at h
  exact ⟨h.1,h.2.1,le_rfl,h.2.2.2⟩

/-- The local candidate changes at least one condition word. -/
def Changes (D : LocalInputs.Data) (t : ℕ) (p : Condition) : Prop :=
  StageEngine.Changes (procedures D) t p

/-- Search a bounded priority range for an unfinished local candidate that changes the
condition. -/
def scan (D : LocalInputs.Data) (p : Condition) (done : Finset ℕ) (t : ℕ) : ℕ → Option ℕ :=
  StageEngine.scan (procedures D) p done t

/-- A bounded scan of length zero selects no action. -/
theorem scan_zero (D : LocalInputs.Data) (p : Condition) (done : Finset ℕ) (t : ℕ) :
    scan D p done t 0 = none := rfl

/-- A nonempty scan first examines its least priority. -/
theorem scan_succ (D : LocalInputs.Data) (p : Condition) (done : Finset ℕ) (t n : ℕ) :
    scan D p done t (n+1) =
      if t ∉ done ∧ Changes D t p then some t else scan D p done (t+1) n := rfl

/-- The two defining cases of the bounded scan, with a stable public equation name. -/
theorem scan_eq_match (D : LocalInputs.Data) (p : Condition) (done : Finset ℕ) (t n : ℕ) :
    scan D p done t n = match n with
      | 0 => none
      | n+1 => if t ∉ done ∧ Changes D t p then some t else scan D p done (t+1) n := by
  cases n <;> rfl

theorem scan_spec {D : LocalInputs.Data} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan D p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes D i p :=
  StageEngine.scan_spec h

/-- A local priority state containing its condition and two finite priority records. -/
structure State where
  /-- The current local coding condition. -/
  condition : Condition
  /-- The local priorities currently marked completed. -/
  done : Finset ℕ
  /-- The local priorities visited since their last injury reset. -/
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

/-- Extend the local condition to meet its least unvisited open requirement. -/
def generic (D : LocalInputs.Data) (p : State) : Condition :=
  StageEngine.generic stateInterface (procedures D) p

/-- The bounded local action selected after the open extension. -/
def stageAction (D : LocalInputs.Data) (s : ℕ) (p : State) : Option ℕ :=
  StageEngine.stageAction stateInterface (procedures D) s p

/-- Select the local stage condition from the open extension and any action candidate. -/
def stageWord (D : LocalInputs.Data) (s : ℕ) (p : State) : Condition :=
  StageEngine.stageWord stateInterface (procedures D) s p

/-- Advance the local condition and its completed and visited priority records. -/
def advance (D : LocalInputs.Data) (s : ℕ) (p : State) : State :=
  StageEngine.advance stateInterface (procedures D) s p

/-- The local state sequence starting from the empty state. -/
def construction (D : LocalInputs.Data) : ℕ → State :=
  StageEngine.construction stateInterface (procedures D)

/-- The construction begins at the original empty state. -/
theorem construction_zero (D : LocalInputs.Data) : construction D 0 = ⟨⟨[], [], rfl, 0⟩, ∅, ∅⟩
  := rfl

/-- Each construction step applies the stage transition to its predecessor. -/
theorem construction_succ (D : LocalInputs.Data) (s : ℕ) :
    construction D (s+1) = advance D s (construction D s) := rfl

/-- The two construction cases, with a stable public equation name. -/
theorem construction_eq_match (D : LocalInputs.Data) (s : ℕ) :
    construction D s = match s with
      | 0 => ⟨⟨[], [], rfl, 0⟩, ∅, ∅⟩
      | s+1 => advance D s (construction D s) := by
  cases s <;> rfl

/-- The condition component of the local state at stage `s`. -/
def conditions (D : LocalInputs.Data) (s : ℕ) :=
  StageEngine.conditions stateInterface (procedures D) s

/-- The finite-injury action proposal generated by the local state at stage `s`. -/
def proposal (D : LocalInputs.Data) (s : ℕ) (_ : Finset ℕ) : Option ℕ :=
  StageEngine.proposal stateInterface (procedures D) s ∅

theorem action_not_done (D : LocalInputs.Data) (s : ℕ) (p : State) (t : ℕ)
    (h : stageAction D s p = some t) : t ∉ p.done :=
  StageEngine.action_not_done stateInterface (procedures D) s p t h

theorem accept_action (D : LocalInputs.Data) (s : ℕ) (p : State) :
    FiniteInjury.accept p.done (stageAction D s p) = stageAction D s p :=
  StageEngine.accept_action stateInterface (procedures D) s p

theorem done_eq (D : LocalInputs.Data) (s : ℕ) :
    (construction D s).done = FiniteInjury.state (proposal D) s :=
  StageEngine.done_eq stateInterface (procedures D) s

theorem action_eq (D : LocalInputs.Data) (s : ℕ) :
    FiniteInjury.action (proposal D) s = stageAction D s (construction D s) :=
  StageEngine.action_eq stateInterface (procedures D) s

theorem seen_eq (D : LocalInputs.Data) (s : ℕ) :
    (construction D s).seen = FiniteInjurySchedule.seen (proposal D) s :=
  StageEngine.seen_eq stateInterface (procedures D) s

theorem active_eq (D : LocalInputs.Data) (s : ℕ) : (conditions D s).active = s :=
  StageEngine.active_eq stateInterface (procedures D) s

theorem stage_words (D : LocalInputs.Data) (s : ℕ) (p : State) :
    p.condition.left <+: (stageWord D s p).left ∧ p.condition.right <+: (stageWord D s p).right :=
  StageEngine.stage_words stateInterface (procedures D) (candidate_extends D) (open_extends D) s p

theorem word_growth (D : LocalInputs.Data) (s : ℕ) :
    (conditions D s).left <+: (conditions D (s+1)).left ∧
    (conditions D s).right <+: (conditions D (s+1)).right :=
  StageEngine.word_growth stateInterface (procedures D) (candidate_extends D) (open_extends D) s

theorem length_bound (D : LocalInputs.Data) (s : ℕ) : s ≤ (conditions D s).left.length :=
  StageEngine.length_bound stateInterface (procedures D) (candidate_extends D) (open_extends D) s

theorem level_step (D : LocalInputs.Data) (s k : ℕ) (hk : k ≤ s)
    (hact : ∀ t, FiniteInjury.action (proposal D) s = some t → k ≤ t) :
    Extends D.F (atLevel (conditions D s) k) (atLevel (conditions D (s+1)) k) :=
  StageEngine.level_step stateInterface (procedures D) (candidate_extends D) (open_extends D)
    s k hk hact

theorem surviving_columns (D : LocalInputs.Data) (k : ℕ) : ∃ S, ∀ m,
    (conditions D S).left.length ≤ m → (Nat.unpair m).1 < k →
    D.F (Nat.unpair m).1 (Nat.unpair m).2 = true →
    leftLimit (conditions D) m = rightLimit (conditions D) m :=
  StageEngine.surviving_columns stateInterface (procedures D) (candidate_extends D) (open_extends D)
    k

theorem surviving_generic_visit (D : LocalInputs.Data) (t : ℕ) : ∃ s,
    FiniteInjurySchedule.visit (construction D s).seen = t ∧
      ∀ u, s ≤ u → ∀ i < t, stageAction D u (construction D u) ≠ some i :=
  StageEngine.surviving_generic_visit stateInterface (procedures D) t

end
end TuringRigidity.LocalStage

end OAI
