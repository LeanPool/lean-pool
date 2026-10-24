/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.StabilizerState
public import LeanPool.SingleCopyStabilizer.CNOTAction
public import LeanPool.SingleCopyStabilizer.CliffordAction
public import LeanPool.SingleCopyStabilizer.ExactLearning
public import LeanPool.SingleCopyStabilizer.Circuit


/-!
# A physical adaptive round on stabilizer amplitudes

The round is the actual CNOT basis permutation, followed by H or HS at
the chosen pivot. Its label-space action is proved to be `binaryRound`.
No membership oracle is used to define the amplitude action.
-/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer.QuantumRound

open Measurement CliffordAction
open scoped CharTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Apply H for correction bit zero, and HS for correction bit one. -/
def correctionAmplitude (i : ι) (b : ZMod 2) (ψ : Amplitude ι) : Amplitude ι :=
  localHadamard i (if b = 0 then ψ else localPhase i ψ)

theorem correctionAmplitude_normalized (i : ι) (b : ZMod 2)
    (ψ : Amplitude ι) (hψ : IsNormalized ψ) :
    IsNormalized (correctionAmplitude i b ψ) := by
  classical
  apply localHadamard_normalized
  split_ifs
  · exact hψ
  · exact localPhase_normalized i ψ hψ

omit [Fintype ι] in
theorem localCorrection_zero (i : ι) (u v : Bits ι) :
    localCorrection i (0 : ZMod 2) (u, v) =
      (hadamardXLabel i u v, hadamardZLabel i u v) := by
  classical
  simp [localCorrection, hadamardXLabel, hadamardZLabel]

omit [Fintype ι] in
theorem localCorrection_one (i : ι) (u v : Bits ι) :
    localCorrection i (1 : ZMod 2) (u, v) =
      (hadamardXLabel i u (phaseZLabel i u v),
       hadamardZLabel i u (phaseZLabel i u v)) := by
  classical
  apply Prod.ext
  · simp [localCorrection, hadamardXLabel, phaseZLabel]
  · funext j
    by_cases hj : j = i
    · subst j
      simp [localCorrection, hadamardZLabel]
    · simp [localCorrection, hadamardZLabel, phaseZLabel, hj]

/-- Actual H/HS eigenvector covariance yields the correction's label action;
the output eigenvalue includes the physically relevant phase factors. -/
theorem correctionAmplitude_eigenvector (i : ι) (b : ZMod 2)
    (ψ : Amplitude ι) (u v : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ u v ζ) :
    ∃ η, IsPauliEigenvector (correctionAmplitude i b ψ)
      (localCorrection i b (u, v)).1 (localCorrection i b (u, v)).2 η := by
  classical
  rcases bit_eq_zero_or_one b with hb | hb
  · subst b
    rw [localCorrection_zero]
    refine ⟨paritySign (u i * v i) * ζ, ?_⟩
    simpa [correctionAmplitude] using localHadamard_eigenvector i ψ u v ζ heig
  · subst b
    rw [localCorrection_one]
    refine ⟨paritySign (u i * phaseZLabel i u v i) *
      (star (phaseBit (u i)) * ζ), ?_⟩
    simpa [correctionAmplitude] using
      localHadamard_eigenvector i (localPhase i ψ) u (phaseZLabel i u v)
        (star (phaseBit (u i)) * ζ) (localPhase_eigenvector i ψ u v ζ heig)

/-- The physical round depends only on its observed difference and random bit.
When the observed difference is zero, the state is left unchanged. -/
def applyRoundAmplitude (u : BinaryVec ι) (b : ZMod 2)
    (ψ : Amplitude ι) : Amplitude ι :=
  if hu : u = 0 then ψ else
    let i := binaryPivot u hu
    correctionAmplitude i b
      (CNOTAction.applyCNOTs i (u - Pi.single i 1)
        (by simp [i, binaryPivot_spec u hu]) ψ)

@[simp] theorem applyRoundAmplitude_zero (b : ZMod 2) (ψ : Amplitude ι) :
    applyRoundAmplitude 0 b ψ = ψ := by
  classical
  simp [applyRoundAmplitude]

theorem applyRoundAmplitude_of_ne (u : BinaryVec ι) (b : ZMod 2)
    (ψ : Amplitude ι) (hu : u ≠ 0) :
    applyRoundAmplitude u b ψ = correctionAmplitude (binaryPivot u hu) b
      (CNOTAction.applyCNOTs (binaryPivot u hu) (u - Pi.single (binaryPivot u hu) 1)
        (by simp [binaryPivot_spec u hu]) ψ) := by
  classical
  simp [applyRoundAmplitude, hu]

/-- The amplitude round is exactly the recorded complex-linear circuit round. -/
theorem roundEquiv_apply_eq_applyRoundAmplitude (u : BinaryVec ι) (b : ZMod 2)
    (ψ : Amplitude ι) : Circuit.roundEquiv u b ψ = applyRoundAmplitude u b ψ := by
  classical
  by_cases hu : u = 0
  · subst u
    simp
  · rw [Circuit.roundEquiv_apply_of_ne u b hu,
      applyRoundAmplitude_of_ne u b ψ hu, Circuit.correctionEquiv_apply]
    rfl

theorem applyRoundAmplitude_normalized (u : BinaryVec ι) (b : ZMod 2)
    (ψ : Amplitude ι) (hψ : IsNormalized ψ) :
    IsNormalized (applyRoundAmplitude u b ψ) := by
  classical
  by_cases hu : u = 0
  · subst u
    simpa using hψ
  · rw [applyRoundAmplitude_of_ne u b ψ hu]
    apply correctionAmplitude_normalized
    exact CNOTAction.normalized _ _ _ ψ hψ

/-- Composition of the concrete CNOT and H/HS covariance theorems transports
every eigenlabel through the paper's algebraic adaptive update. -/
theorem adaptiveUpdate_eigenvector (i : ι) (u : BinaryVec ι) (b : ZMod 2)
    (hu : u i = 1) (ψ : Amplitude ι) (a : Label (ZMod 2) ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ a.1 a.2 ζ) :
    ∃ η, IsPauliEigenvector
      (correctionAmplitude i b (CNOTAction.applyCNOTs i (u - Pi.single i 1)
        (by simp [hu]) ψ))
      (adaptiveUpdate i u b a).1 (adaptiveUpdate i u b a).2 η := by
  classical
  exact correctionAmplitude_eigenvector i b _ _ _ ζ
    (CNOTAction.transports_eigenvector i (u - Pi.single i 1) (by simp [hu])
      ψ a.1 a.2 ζ heig)

/-- The physical gate round implements the full unsigned label-space update,
including arbitrary outcomes with zero probability. -/
theorem applyRoundAmplitude_eigenlabels (u : BinaryVec ι) (b : ZMod 2)
    (ψ : Amplitude ι) (L : BinarySpace ι) (heig : HasEigenlabels ψ L) :
    HasEigenlabels (applyRoundAmplitude u b ψ) (binaryRound L u b) := by
  classical
  by_cases hu : u = 0
  · subst u
    simpa using heig
  · rw [applyRoundAmplitude_of_ne u b ψ hu, binaryRound_of_ne L u b hu]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨ζ, hζ⟩ := heig a ha
    exact adaptiveUpdate_eigenvector (binaryPivot u hu) u b
      (binaryPivot_spec u hu) ψ a ζ hζ

/-- An actual normalized pure stabilizer state after the physical round. -/
def quantumRound (S : PureStabilizerState ι) (o : ExactLearning.Outcome ι) :
    PureStabilizerState ι where
  amplitude := applyRoundAmplitude o.1 o.2 S.amplitude
  normalized := applyRoundAmplitude_normalized o.1 o.2 S.amplitude S.normalized
  labels := binaryRound S.labels o.1 o.2
  isotropic := binaryRound_isotropic S.labels S.isotropic o.1 o.2
  maximal := (binaryRound_finrank S.labels o.1 o.2).trans S.maximal
  eigenlabels := applyRoundAmplitude_eigenlabels o.1 o.2 S.amplitude S.labels S.eigenlabels

@[simp] theorem quantumRound_labels (S : PureStabilizerState ι)
    (o : ExactLearning.Outcome ι) :
    (quantumRound S o).labels = binaryRound S.labels o.1 o.2 := rfl

@[simp] theorem quantumRound_amplitude (S : PureStabilizerState ι)
    (o : ExactLearning.Outcome ι) :
    (quantumRound S o).amplitude = applyRoundAmplitude o.1 o.2 S.amplitude := rfl

theorem quantumRound_amplitude_eq_roundEquiv (S : PureStabilizerState ι)
    (o : ExactLearning.Outcome ι) :
    (quantumRound S o).amplitude = Circuit.roundEquiv o.1 o.2 S.amplitude :=
  (roundEquiv_apply_eq_applyRoundAmplitude o.1 o.2 S.amplitude).symm

end LeanPool.SingleCopyStabilizer.QuantumRound
