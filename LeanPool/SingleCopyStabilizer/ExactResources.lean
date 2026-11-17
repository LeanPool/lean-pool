/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Round
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


/-!
# Symbolic gate and copy costs of the exact protocol

An outcome list determines explicit symbolic CNOT/S/H instructions. Costs
count those instructions and their repeated execution on fresh copies. These
are not running-time claims about Lean's noncomputable state simulation.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.ExactResources

open Finset

/-- Elementary instructions counted by the protocol's gate model. -/
inductive Instruction (ι : Type*)
  | cnot (control target : ι)
  | phase (site : ι)
  | hadamard (site : ι)

/-- The classical difference and correction coin recorded for one round. -/
abbrev RoundOutcome (ι : Type*) := BinaryVec ι × ZMod 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual targets in the simultaneous pivot-controlled CNOT circuit. -/
def cnotTargets (u : BinaryVec ι) (pivot : ι) : Finset ι :=
  Finset.univ.filter (fun j => j ≠ pivot ∧ u j = 1)

/-- The pivot itself is never a CNOT target. -/
theorem cnotTargets_card_add_one_le (u : BinaryVec ι) (pivot : ι) :
    (cnotTargets u pivot).card + 1 ≤ Fintype.card ι := by
  have hsubset : cnotTargets u pivot ⊆ (Finset.univ : Finset ι).erase pivot := by
    intro j hj
    have hne : j ≠ pivot := (Finset.mem_filter.mp hj).2.1
    simp [hne]
  have hcard := Finset.card_le_card hsubset
  have herase := Finset.card_erase_add_one (Finset.mem_univ pivot)
  simp only [Finset.card_univ] at herase
  omega

/-- In chronological order: the pivot CNOTs, optional S, then H. A zero
computational difference appends no gates. -/
def roundInstructions (outcome : RoundOutcome ι) : List (Instruction ι) := by
  classical
  exact if hzero : outcome.1 = 0 then [] else
    let pivot := binaryPivot outcome.1 hzero
    ((cnotTargets outcome.1 pivot).toList.map (Instruction.cnot pivot)) ++
      (if outcome.2 = 0 then [] else [Instruction.phase pivot]) ++
      [Instruction.hadamard pivot]

/-- Gate cost is the length of the actual symbolic instruction list. -/
def roundGateCount (outcome : RoundOutcome ι) : ℕ := (roundInstructions outcome).length

@[simp] theorem roundInstructions_zero (b : ZMod 2) :
    roundInstructions ((0 : BinaryVec ι), b) = [] := by
  simp [roundInstructions]

@[simp] theorem roundGateCount_zero (b : ZMod 2) :
    roundGateCount ((0 : BinaryVec ι), b) = 0 := by
  simp [roundGateCount]

/-- The nonzero branch has exactly the chosen CNOTs, one H, and at most one S. -/
theorem roundGateCount_of_ne (outcome : RoundOutcome ι) (hzero : outcome.1 ≠ 0) :
    roundGateCount outcome =
      (cnotTargets outcome.1 (binaryPivot outcome.1 hzero)).card + 1 +
        if outcome.2 = 0 then 0 else 1 := by
  classical
  by_cases hb : outcome.2 = 0 <;>
    simp [roundGateCount, roundInstructions, hzero, hb]

/-- One round appends at most `n+1` gates, including both possible corrections. -/
theorem roundGateCount_le (outcome : RoundOutcome ι) :
    roundGateCount outcome ≤ Fintype.card ι + 1 := by
  classical
  by_cases hzero : outcome.1 = 0
  · simp [roundGateCount, roundInstructions, hzero]
  · have htargets := cnotTargets_card_add_one_le outcome.1 (binaryPivot outcome.1 hzero)
    rw [roundGateCount_of_ne outcome hzero]
    split_ifs <;> omega

/-- The accumulated circuit appends each round's instructions in order. -/
def circuitInstructions (outcomes : List (RoundOutcome ι)) : List (Instruction ι) :=
  outcomes.flatMap roundInstructions

/-- The accumulated gate count is the sum of all appended round costs. -/
def listCircuitGateCount (outcomes : List (RoundOutcome ι)) : ℕ :=
  (outcomes.map roundGateCount).sum

/-- The sum-based cost equals the length of the actual flattened gate list. -/
theorem circuitInstructions_length (outcomes : List (RoundOutcome ι)) :
    (circuitInstructions outcomes).length = listCircuitGateCount outcomes := by
  induction outcomes with
  | nil => simp [circuitInstructions, listCircuitGateCount]
  | cons outcome outcomes ih =>
    simpa [circuitInstructions, listCircuitGateCount, roundGateCount] using
      congrArg ((roundInstructions outcome).length + ·) ih

/-- A circuit accumulated over `T` rounds has at most `(n+1)T` gates. -/
theorem listCircuitGateCount_le (outcomes : List (RoundOutcome ι)) :
    listCircuitGateCount outcomes ≤ (Fintype.card ι + 1) * outcomes.length := by
  induction outcomes with
  | nil => simp [listCircuitGateCount]
  | cons outcome outcomes ih =>
    have hround := roundGateCount_le outcome
    simp only [listCircuitGateCount, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

/-- Prefix circuits have a gate count linear in the prefix index. -/
theorem prefixCircuitGateCount_le (outcomes : List (RoundOutcome ι)) (t : ℕ) :
    listCircuitGateCount (outcomes.take t) ≤ (Fintype.card ι + 1) * t := by
  have h := listCircuitGateCount_le (outcomes.take t)
  have hlength : (outcomes.take t).length ≤ t := by simp
  exact h.trans (Nat.mul_le_mul_left _ hlength)

/-- Total gate applications: execute the current prefix twice in every round,
then execute the complete circuit once for the final computational readout. -/
def protocolGateCost (outcomes : List (RoundOutcome ι)) : ℕ :=
  2 * (∑ t ∈ Finset.range outcomes.length, listCircuitGateCount (outcomes.take t)) +
    listCircuitGateCount outcomes

/-- Twice the triangular sum plus its endpoint equals the square. -/
theorem twice_prefix_sum_add (T : ℕ) :
    2 * (∑ t ∈ Finset.range T, t) + T = T ^ 2 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- Total quantum gate applications are at most `(n+1)T²`, for every possible
outcome history, including unsuccessful histories. -/
theorem protocolGateCost_le (outcomes : List (RoundOutcome ι)) :
    protocolGateCost outcomes ≤ (Fintype.card ι + 1) * outcomes.length ^ 2 := by
  have hprefix : (∑ t ∈ Finset.range outcomes.length,
      listCircuitGateCount (outcomes.take t)) ≤
      (Fintype.card ι + 1) * (∑ t ∈ Finset.range outcomes.length, t) := by
    calc
      _ ≤ ∑ t ∈ Finset.range outcomes.length, (Fintype.card ι + 1) * t :=
        Finset.sum_le_sum (fun t _ => prefixCircuitGateCount_le outcomes t)
      _ = _ := (Finset.mul_sum _ _ _).symm
  calc
    protocolGateCost outcomes ≤
        2 * ((Fintype.card ι + 1) * (∑ t ∈ Finset.range outcomes.length, t)) +
          (Fintype.card ι + 1) * outcomes.length := by
      unfold protocolGateCost
      exact Nat.add_le_add (Nat.mul_le_mul_left 2 hprefix) (listCircuitGateCount_le outcomes)
    _ = (Fintype.card ι + 1) *
        (2 * (∑ t ∈ Finset.range outcomes.length, t) + outcomes.length) := by ring
    _ = (Fintype.card ι + 1) * outcomes.length ^ 2 := by rw [twice_prefix_sum_add]

/-- For at least one qubit this is the explicit `2nT²` gate-resource bound. -/
theorem protocolGateCost_le_two_n (outcomes : List (RoundOutcome ι))
    (hn : 1 ≤ Fintype.card ι) :
    protocolGateCost outcomes ≤ 2 * Fintype.card ι * outcomes.length ^ 2 := by
  apply (protocolGateCost_le outcomes).trans
  exact Nat.mul_le_mul_right _ (by omega)

/-- A zero-qubit register can produce no nonzero difference and appends no gates. -/
theorem roundGateCount_of_zero_qubits (outcome : RoundOutcome ι)
    (hn : Fintype.card ι = 0) : roundGateCount outcome = 0 := by
  have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
  have hzero : outcome.1 = 0 := by ext i; exact isEmptyElim i
  simp [roundGateCount, roundInstructions, hzero]

/-- The full symbolic circuit is empty on a zero-qubit register. -/
theorem listCircuitGateCount_of_zero_qubits (outcomes : List (RoundOutcome ι))
    (hn : Fintype.card ι = 0) : listCircuitGateCount outcomes = 0 := by
  unfold listCircuitGateCount
  induction outcomes with
  | nil => simp
  | cons outcome outcomes ih => simp [roundGateCount_of_zero_qubits outcome hn, ih]

/-- Zero-qubit executions require no gates, regardless of the round count. -/
theorem protocolGateCost_of_zero_qubits (outcomes : List (RoundOutcome ι))
    (hn : Fintype.card ι = 0) : protocolGateCost outcomes = 0 := by
  simp [protocolGateCost, listCircuitGateCount_of_zero_qubits _ hn]

/-- Every round consumes two input copies, and final readout consumes one.
Even rounds whose difference is zero consume their two measurement copies. -/
def protocolCopyCount (outcomes : List (RoundOutcome ι)) : ℕ := 2 * outcomes.length + 1

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem protocolCopyCount_nil : protocolCopyCount ([] : List (RoundOutcome ι)) = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Appending a round always consumes exactly two additional copies. -/
theorem protocolCopyCount_cons (outcome : RoundOutcome ι) (outcomes : List (RoundOutcome ι)) :
    protocolCopyCount (outcome :: outcomes) = protocolCopyCount outcomes + 2 := by
  simp [protocolCopyCount]
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- The protocol's exact total copy count. -/
theorem protocolCopyCount_eq (outcomes : List (RoundOutcome ι)) (T : ℕ)
    (hT : outcomes.length = T) : protocolCopyCount outcomes = 2 * T + 1 := by
  simp [protocolCopyCount, hT]

end LeanPool.SingleCopyStabilizer.ExactResources
