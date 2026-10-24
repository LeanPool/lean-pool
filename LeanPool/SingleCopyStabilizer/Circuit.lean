/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.CNOTAction
public import LeanPool.SingleCopyStabilizer.CliffordAction
public import LeanPool.SingleCopyStabilizer.Round


/-!
# Recorded binary Clifford circuits and exact decoding

Each recorded outcome specifies precisely the CNOTs and correction used by
one learning round. Lists are chronological: the head is performed first.
The inverse acts on the final computational basis vector to reconstruct the
original amplitude, with its physically irrelevant global phase explicit.
-/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer.Circuit

open Measurement CNOTAction CliffordAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The simultaneous CNOT operation, with its explicit inverse permutation. -/
def cnotEquiv (i : ι) (w : Bits ι) (hw : w i = 0) :
    Amplitude ι ≃ₗ[ℂ] Amplitude ι where
  toFun := applyCNOTs i w hw
  invFun ψ x := ψ (basisShear i w hw x)
  left_inv ψ := inverse_action i w hw ψ
  right_inv ψ := by
    funext x
    simp [applyCNOTs]
  map_add' ψ φ := rfl
  map_smul' c ψ := rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem cnotEquiv_apply (i : ι) (w : Bits ι) (hw : w i = 0)
    (ψ : Amplitude ι) : cnotEquiv i w hw ψ = applyCNOTs i w hw ψ := rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem cnotEquiv_symm_apply (i : ι) (w : Bits ι) (hw : w i = 0)
    (ψ : Amplitude ι) :
    (cnotEquiv i w hw).symm ψ = fun x => ψ (basisShear i w hw x) := rfl

/-- The correction is H for bit zero and HS for bit one. -/
def correctionEquiv (i : ι) (b : ZMod 2) : Amplitude ι ≃ₗ[ℂ] Amplitude ι :=
  if b = 0 then localHadamardLinearEquiv i
  else (localPhaseLinearEquiv i).trans (localHadamardLinearEquiv i)

omit [Fintype ι] in
theorem correctionEquiv_apply (i : ι) (b : ZMod 2) (ψ : Amplitude ι) :
    correctionEquiv i b ψ =
      localHadamard i (if b = 0 then ψ else localPhase i ψ) := by
  classical
  by_cases hb : b = 0 <;> simp [correctionEquiv, hb,
    localHadamardLinearEquiv, localHadamardEquiv,
    localPhaseLinearEquiv, localPhaseEquiv]

theorem correctionEquiv_normalized (i : ι) (b : ZMod 2) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized (correctionEquiv i b ψ) := by
  rw [correctionEquiv_apply]
  apply localHadamard_normalized
  by_cases hb : b = 0
  · simpa only [ite_eq_left hb] using hψ
  · simpa only [ite_eq_right hb] using localPhase_normalized i ψ hψ

theorem correctionEquiv_norm_preserving (i : ι) (b : ZMod 2) (ψ : Amplitude ι) :
    (∑ x, bornWeight (correctionEquiv i b ψ) x) = ∑ x, bornWeight ψ x := by
  rw [correctionEquiv_apply, localHadamard_norm_preserving]
  by_cases hb : b = 0
  · simp only [ite_eq_left hb]
  · simp only [ite_eq_right hb, localPhase_bornWeight]

omit [Fintype ι] in
/-- The pivot-coordinate vanishes in the CNOT target vector. -/
theorem pivot_target_zero (u : Bits ι) (hu : u ≠ 0) :
    (u - (Pi.single (binaryPivot u hu) 1 : Bits ι)) (binaryPivot u hu) = 0 := by
  classical
  simp [binaryPivot_spec]

/-- The physical Clifford operation determined by the sampled difference
and the correction coin. A zero difference records the identity operation. -/
def roundEquiv (u : Bits ι) (b : ZMod 2) : Amplitude ι ≃ₗ[ℂ] Amplitude ι :=
  if hu : u = 0 then LinearEquiv.refl ℂ (Amplitude ι)
  else (cnotEquiv (binaryPivot u hu) (u - Pi.single (binaryPivot u hu) 1)
    (pivot_target_zero u hu)).trans (correctionEquiv (binaryPivot u hu) b)

@[simp] theorem roundEquiv_zero (b : ZMod 2) :
    roundEquiv (0 : Bits ι) b = LinearEquiv.refl ℂ (Amplitude ι) := by
  simp [roundEquiv]

theorem roundEquiv_apply_of_ne (u : Bits ι) (b : ZMod 2) (hu : u ≠ 0)
    (ψ : Amplitude ι) :
    roundEquiv u b ψ = correctionEquiv (binaryPivot u hu) b
      (applyCNOTs (binaryPivot u hu) (u - Pi.single (binaryPivot u hu) 1)
        (pivot_target_zero u hu) ψ) := by
  simp [roundEquiv, hu]

theorem roundEquiv_normalized (u : Bits ι) (b : ZMod 2) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized (roundEquiv u b ψ) := by
  by_cases hu : u = 0
  · subst u
    simpa using hψ
  · rw [roundEquiv_apply_of_ne u b hu]
    exact correctionEquiv_normalized _ b _ (CNOTAction.normalized _ _ _ ψ hψ)

theorem roundEquiv_norm_preserving (u : Bits ι) (b : ZMod 2) (ψ : Amplitude ι) :
    (∑ x, bornWeight (roundEquiv u b ψ) x) = ∑ x, bornWeight ψ x := by
  by_cases hu : u = 0
  · subst u
    simp
  · rw [roundEquiv_apply_of_ne u b hu, correctionEquiv_norm_preserving,
      CNOTAction.norm_preserved]

/-- A recorded outcome is sufficient to specify all gates in a round. -/
abbrev Outcome (ι : Type*) := Bits ι × ZMod 2

/-- Circuit composition in chronological order. -/
def circuitEquiv : List (Outcome ι) → (Amplitude ι ≃ₗ[ℂ] Amplitude ι)
  | [] => LinearEquiv.refl ℂ (Amplitude ι)
  | op :: ops => (roundEquiv op.1 op.2).trans (circuitEquiv ops)

@[simp] theorem circuitEquiv_nil :
    circuitEquiv ([] : List (Outcome ι)) = LinearEquiv.refl ℂ (Amplitude ι) := rfl

@[simp] theorem circuitEquiv_cons (op : Outcome ι) (ops : List (Outcome ι)) :
    circuitEquiv (op :: ops) = (roundEquiv op.1 op.2).trans (circuitEquiv ops) := rfl

@[simp] theorem circuitEquiv_cons_apply (op : Outcome ι) (ops : List (Outcome ι))
    (ψ : Amplitude ι) :
    circuitEquiv (op :: ops) ψ = circuitEquiv ops (roundEquiv op.1 op.2 ψ) := rfl

theorem circuitEquiv_append (xs ys : List (Outcome ι)) :
    circuitEquiv (xs ++ ys) = (circuitEquiv xs).trans (circuitEquiv ys) := by
  induction xs with
  | nil => rfl
  | cons op ops ih =>
    ext ψ x
    simp only [List.cons_append, circuitEquiv_cons, ih, LinearEquiv.trans_apply]

theorem circuitEquiv_normalized (ops : List (Outcome ι)) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized (circuitEquiv ops ψ) := by
  induction ops generalizing ψ with
  | nil => exact hψ
  | cons op ops ih =>
    exact ih _ (roundEquiv_normalized op.1 op.2 ψ hψ)

theorem circuitEquiv_norm_preserving (ops : List (Outcome ι)) (ψ : Amplitude ι) :
    (∑ x, bornWeight (circuitEquiv ops ψ) x) = ∑ x, bornWeight ψ x := by
  induction ops generalizing ψ with
  | nil => rfl
  | cons op ops ih =>
    rw [circuitEquiv_cons_apply, ih, roundEquiv_norm_preserving]

theorem circuitEquiv_symm_normalized (ops : List (Outcome ι)) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) : IsNormalized ((circuitEquiv ops).symm ψ) := by
  unfold IsNormalized
  rw [← circuitEquiv_norm_preserving ops, LinearEquiv.apply_symm_apply]
  exact hψ

/-- Computational basis amplitudes, with value one at the chosen string. -/
def basis (z : Bits ι) : Amplitude ι := Pi.single z 1

omit [DecidableEq ι] in
@[simp] theorem basis_apply (z x : Bits ι) :
    basis z x = if x = z then 1 else 0 := by
  classical
  simp [basis, Pi.single_apply, eq_comm]

theorem basis_normalized (z : Bits ι) : IsNormalized (basis z) := by
  simp [IsNormalized, bornWeight, basis_apply]

/-- Classical description of the learned state: undo the recorded circuit
on the final measured basis string. -/
def decode (ops : List (Outcome ι)) (z : Bits ι) : Amplitude ι :=
  (circuitEquiv ops).symm (basis z)

@[simp] theorem decode_nil (z : Bits ι) : decode [] z = basis z := rfl

@[simp] theorem decode_cons (op : Outcome ι) (ops : List (Outcome ι)) (z : Bits ι) :
    decode (op :: ops) z = (roundEquiv op.1 op.2).symm (decode ops z) := rfl

theorem decode_append (xs ys : List (Outcome ι)) (z : Bits ι) :
    decode (xs ++ ys) z = (circuitEquiv xs).symm (decode ys z) := by
  simp only [decode, circuitEquiv_append, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply]

@[simp] theorem circuitEquiv_decode (ops : List (Outcome ι)) (z : Bits ι) :
    circuitEquiv ops (decode ops z) = basis z :=
  LinearEquiv.apply_symm_apply _ _

theorem decode_normalized (ops : List (Outcome ι)) (z : Bits ι) :
    IsNormalized (decode ops z) :=
  circuitEquiv_symm_normalized ops _ (basis_normalized z)

/-- Inverting the recorded circuit recovers the original amplitude with the
same global phase as its final computational basis amplitude. -/
theorem reconstruction_eq_smul_decode (ops : List (Outcome ι))
    (ψ : Amplitude ι) (z : Bits ι) (c : ℂ)
    (h : circuitEquiv ops ψ = c • basis z) : ψ = c • decode ops z := by
  apply (circuitEquiv ops).injective
  simpa only [map_smul, circuitEquiv_decode] using h

omit [DecidableEq ι] in
theorem smul_basis (z : Bits ι) (c : ℂ) :
    c • basis z = fun x => if x = z then c else 0 := by
  classical
  funext x
  by_cases hx : x = z <;> simp [hx]

/-- Version matching `StabilizerState.full_diagonal_basis_amplitude`. -/
theorem reconstruction_of_basis_amplitude (ops : List (Outcome ι))
    (ψ : Amplitude ι) (z : Bits ι) (c : ℂ)
    (h : circuitEquiv ops ψ = fun x => if x = z then c else 0) :
    ψ = c • decode ops z := by
  apply reconstruction_eq_smul_decode ops ψ z c
  simpa only [smul_basis] using h

/-- If the input is normalized, the scalar occurring at a basis-vector
endpoint must have unit modulus. -/
theorem reconstruction_phase_normSq (ops : List (Outcome ι)) (ψ : Amplitude ι)
    (hψ : IsNormalized ψ) (z : Bits ι) (c : ℂ)
    (h : circuitEquiv ops ψ = c • basis z) : Complex.normSq c = 1 := by
  have hn := circuitEquiv_normalized ops ψ hψ
  rw [h, smul_basis] at hn
  simpa [IsNormalized, bornWeight, apply_ite] using hn

/-- The circuit endpoint condition and exact recovery up to a specified
global phase are equivalent. -/
theorem reconstruction_iff (ops : List (Outcome ι)) (ψ : Amplitude ι)
    (z : Bits ι) (c : ℂ) :
    circuitEquiv ops ψ = c • basis z ↔ ψ = c • decode ops z := by
  constructor
  · exact reconstruction_eq_smul_decode ops ψ z c
  · intro h
    rw [h, map_smul, circuitEquiv_decode]

end LeanPool.SingleCopyStabilizer.Circuit
