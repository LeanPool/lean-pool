/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.ExactResources
public import LeanPool.SingleCopyStabilizer.Circuit


/-!
# Elementary gate semantics of the recorded learning circuit

The instruction lists counted in `ExactResources` denote exactly the
complex-linear Clifford operations in `Circuit`. In particular the counted
individual CNOTs implement the simultaneous target-mask operation.
-/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer.InstructionSemantics

open Measurement CNOTAction CliffordAction Circuit ExactResources

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A CNOT's control and target must be distinct. -/
def WellFormed : Instruction ι → Prop
  | .cnot i j => i ≠ j
  | .phase _ => True
  | .hadamard _ => True

/-- Elementary physical gate interpretation. A malformed self-target CNOT is
totalized as the identity; generated instruction lists never use that case. -/
def instructionEquiv : Instruction ι → (Amplitude ι ≃ₗ[ℂ] Amplitude ι)
  | .cnot i j => if h : j = i then LinearEquiv.refl ℂ _
      else cnotEquiv i (Pi.single j 1) (by simp [Ne.symm h])
  | .phase i => localPhaseLinearEquiv i
  | .hadamard i => localHadamardLinearEquiv i

omit [Fintype ι] in
theorem instructionEquiv_cnot_of_ne (i j : ι) (h : j ≠ i) :
    instructionEquiv (.cnot i j) =
      cnotEquiv i (Pi.single j 1) (by simp [Ne.symm h]) := by
  classical
  simp [instructionEquiv, h]

/-- Chronological composition of elementary instructions. -/
def instructionsEquiv : List (Instruction ι) → (Amplitude ι ≃ₗ[ℂ] Amplitude ι)
  | [] => LinearEquiv.refl ℂ _
  | g :: gs => (instructionEquiv g).trans (instructionsEquiv gs)

omit [Fintype ι] in
@[simp] theorem instructionsEquiv_nil :
    instructionsEquiv ([] : List (Instruction ι)) = LinearEquiv.refl ℂ _ := rfl

omit [Fintype ι] in
@[simp] theorem instructionsEquiv_cons (g : Instruction ι) (gs : List (Instruction ι)) :
    instructionsEquiv (g :: gs) = (instructionEquiv g).trans (instructionsEquiv gs) := rfl

omit [Fintype ι] in
theorem instructionsEquiv_append (xs ys : List (Instruction ι)) :
    instructionsEquiv (xs ++ ys) = (instructionsEquiv xs).trans (instructionsEquiv ys) := by
  classical
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    ext ψ x
    simp only [List.cons_append, instructionsEquiv_cons, ih, LinearEquiv.trans_apply]

omit [DecidableEq ι] [Fintype ι] in
/-- CNOT masks sharing a control add under composition. -/
theorem cnotEquiv_trans (i : ι) (w v : Bits ι) (hw : w i = 0) (hv : v i = 0) :
    (cnotEquiv i w hw).trans (cnotEquiv i v hv) =
      cnotEquiv i (w + v) (by simp [hw, hv]) := by
  classical
  ext ψ x
  change ψ ((x + x i • v) + (x + x i • v) i • w) = ψ (x + x i • (w + v))
  congr 1
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, mul_zero, add_zero]
  ring

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem cnotEquiv_zero (i : ι) :
    cnotEquiv i (0 : Bits ι) (by simp) = LinearEquiv.refl ℂ _ := by
  classical
  ext ψ x
  change ψ (x + x i • (0 : Bits ι)) = ψ x
  simp

/-- Mask obtained from a list of CNOT targets, counting repeated targets
modulo two. -/
def targetMask (targets : List ι) : Bits ι :=
  (targets.map (fun j => (Pi.single j 1 : Bits ι))).sum

omit [Fintype ι] in
theorem targetMask_control_zero (i : ι) (targets : List ι) (hi : i ∉ targets) :
    targetMask targets i = 0 := by
  classical
  induction targets with
  | nil => simp [targetMask]
  | cons j js ih =>
    have hij : i ≠ j := by
      intro h
      exact hi (by simp [h])
    have hin : i ∉ js := by intro h; exact hi (List.mem_cons_of_mem j h)
    simpa [targetMask, hij] using ih hin

omit [Fintype ι] in
/-- A list of single-target CNOTs realizes its simultaneous target mask. -/
theorem instructionsEquiv_cnots (i : ι) (targets : List ι) (hi : i ∉ targets) :
    instructionsEquiv (targets.map (Instruction.cnot i)) =
      cnotEquiv i (targetMask targets) (targetMask_control_zero i targets hi) := by
  classical
  induction targets with
  | nil => simp [targetMask]
  | cons j js ih =>
    have hji : j ≠ i := by
      intro h
      subst j
      exact hi (by simp)
    have hin : i ∉ js := by intro h; exact hi (List.mem_cons_of_mem j h)
    rw [List.map_cons, instructionsEquiv_cons, instructionEquiv_cnot_of_ne i j hji,
      ih hin, cnotEquiv_trans]
    rfl

theorem pivot_not_mem_targets (u : Bits ι) (i : ι) : i ∉ cnotTargets u i := by
  simp [cnotTargets]

theorem roundInstructions_wellFormed (outcome : RoundOutcome ι)
    (g : Instruction ι) (hg : g ∈ roundInstructions outcome) : WellFormed g := by
  by_cases hu : outcome.1 = 0
  · simp [roundInstructions, hu] at hg
  · simp only [roundInstructions, dite_eq_right hu, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      have ht : j ∈ cnotTargets outcome.1 (binaryPivot outcome.1 hu) := by simpa using hj
      exact Ne.symm (Finset.mem_filter.mp ht).2.1
    · by_cases hb : outcome.2 = 0
      · simp [hb] at hg
      · simp only [hb, ite_false, List.mem_singleton] at hg
        subst g
        trivial
    · simp only [List.mem_singleton] at hg
      subst g
      trivial

/-- For a pivot bit equal to one, the elementary target list is exactly the
paper's mask `u - eᵢ`. -/
theorem cnotTargets_mask (u : Bits ι) (i : ι) (hu : u i = 1) :
    targetMask (cnotTargets u i).toList = u - Pi.single i 1 := by
  unfold targetMask
  rw [Finset.sum_map_toList]
  ext j
  rw [Finset.sum_apply]
  by_cases hji : j = i
  · subst j
    simp [cnotTargets, hu]
  · have hui : u j = 0 ∨ u j = 1 := CliffordAction.bit_eq_zero_or_one (u j)
    rcases hui with hj | hj
    · simp [cnotTargets, Pi.single_apply, hji, hj]
    · simp [cnotTargets, Pi.single_apply, hji, hj]

theorem instructionsEquiv_cnotTargets (u : Bits ι) (i : ι) (hu : u i = 1) :
    instructionsEquiv ((cnotTargets u i).toList.map (Instruction.cnot i)) =
      cnotEquiv i (u - Pi.single i 1) (by simp [hu]) := by
  rw [instructionsEquiv_cnots i _ (by simpa using pivot_not_mem_targets u i)]
  congr 1
  exact cnotTargets_mask u i hu

/-- The counted elementary instructions implement exactly one physical
learning round, including its zero-difference branch. -/
theorem roundInstructions_denote (outcome : RoundOutcome ι) :
    instructionsEquiv (roundInstructions outcome) = roundEquiv outcome.1 outcome.2 := by
  by_cases hu : outcome.1 = 0
  · simp [roundInstructions, roundEquiv, hu]
  · simp only [roundInstructions, dite_eq_right hu, instructionsEquiv_append]
    rw [instructionsEquiv_cnotTargets _ _ (binaryPivot_spec _ hu)]
    ext ψ x
    by_cases hb : outcome.2 = 0 <;>
      simp [roundEquiv, hu, correctionEquiv, hb, instructionsEquiv, instructionEquiv]

/-- The complete counted elementary circuit implements exactly the same
operation as the recorded outcome circuit used by the decoder. -/
theorem circuitInstructions_denote (outcomes : List (RoundOutcome ι)) :
    instructionsEquiv (circuitInstructions outcomes) = circuitEquiv outcomes := by
  induction outcomes with
  | nil => rfl
  | cons outcome outcomes ih =>
    change instructionsEquiv (roundInstructions outcome ++ circuitInstructions outcomes) = _
    rw [instructionsEquiv_append, roundInstructions_denote, ih]
    rfl

theorem circuitInstructions_wellFormed (outcomes : List (RoundOutcome ι))
    (g : Instruction ι) (hg : g ∈ circuitInstructions outcomes) : WellFormed g := by
  obtain ⟨outcome, _, hg⟩ := List.mem_flatMap.mp hg
  exact roundInstructions_wellFormed outcome g hg

/-- The learned amplitude is exactly the inverse of the counted elementary
instruction circuit, applied to the final computational basis string. -/
theorem decode_eq_inverse_instructions (outcomes : List (RoundOutcome ι)) (z : Bits ι) :
    decode outcomes z = (instructionsEquiv (circuitInstructions outcomes)).symm (basis z) := by
  rw [circuitInstructions_denote]
  rfl

end LeanPool.SingleCopyStabilizer.InstructionSemantics
