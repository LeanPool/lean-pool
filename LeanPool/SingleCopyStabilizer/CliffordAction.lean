/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Measurement
public import LeanPool.SingleCopyStabilizer.HadamardCoefficient


/-! Actual arbitrary-qubit local phase and Hadamard actions on amplitudes. -/

@[expose] public section


noncomputable section

namespace LeanPool.SingleCopyStabilizer.CliffordAction

open Measurement
open scoped BigOperators CharTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every residue modulo two is zero or one. -/
theorem bit_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  -- Exhaust the two canonical residues in the kernel.
  revert a
  decide

theorem paritySign_add (a b : ZMod 2) :
    paritySign (a + b) = paritySign a * paritySign b := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;>
    rcases bit_eq_zero_or_one b with rfl | rfl <;>
    norm_num [paritySign, CharTwo.add_self_eq_zero]
  all_goals decide

theorem paritySign_mul_self (a : ZMod 2) : paritySign a * paritySign a = 1 := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;> norm_num [paritySign, CharTwo.add_self_eq_zero]

/-- Scalar phase contributed by a computational-basis bit under an S gate. -/
def phaseBit (a : ZMod 2) : ℂ := if a = 0 then 1 else Complex.I

@[simp] theorem phaseBit_normSq (a : ZMod 2) : Complex.normSq (phaseBit a) = 1 := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;> norm_num [phaseBit]

theorem phaseBit_twist (a x : ZMod 2) :
    paritySign (a * (x - a)) * phaseBit (x - a) =
      star (phaseBit a) * phaseBit x := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;>
    rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num [paritySign, phaseBit]

omit [Fintype ι] in
theorem update_sub (x u : Bits ι) (i : ι) (b : ZMod 2) :
    Function.update x i b - u = Function.update (x - u) i (b - u i) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

omit [Fintype ι] in
theorem sub_update (x u : Bits ι) (i : ι) (b : ZMod 2) :
    x - Function.update u i b = Function.update (x - u) i (x i - b) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

omit [Fintype ι] in
theorem update_as_add_single (x : Bits ι) (i : ι) (b : ZMod 2) :
    Function.update x i b = x + (b - x i) • (Pi.single i 1 : Bits ι) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp [add_left_comm]
  · simp [hj]

theorem dot_update_left (u v : Bits ι) (i : ι) (b : ZMod 2) :
    Function.update u i b ⬝ᵥ v = u ⬝ᵥ v + (b - u i) * v i := by
  rw [update_as_add_single]
  simp

theorem dot_update_right (u v : Bits ι) (i : ι) (b : ZMod 2) :
    u ⬝ᵥ Function.update v i b = u ⬝ᵥ v + u i * (b - v i) := by
  rw [update_as_add_single]
  simp [mul_comm]

/-- Apply S at one site of the full register amplitude. -/
def localPhase (i : ι) (ψ : Amplitude ι) (x : Bits ι) : ℂ :=
  phaseBit (x i) * ψ x

/-- The Z-label update under conjugation by a local S gate. -/
def phaseZLabel (i : ι) (u v : Bits ι) : Bits ι :=
  v + u i • (Pi.single i 1 : Bits ι)

omit [DecidableEq ι] [Fintype ι] in
theorem localPhase_bornWeight (i : ι) (ψ : Amplitude ι) (x : Bits ι) :
    bornWeight (localPhase i ψ) x = bornWeight ψ x := by
  classical
  simp [bornWeight, localPhase, Complex.normSq_mul]

theorem localPhase_normalized (i : ι) (ψ : Amplitude ι) (hψ : IsNormalized ψ) :
    IsNormalized (localPhase i ψ) := by
  simpa only [IsNormalized, localPhase_bornWeight] using hψ

theorem localPhase_covariance (i : ι) (u v : Bits ι) (ψ : Amplitude ι) (x : Bits ι) :
    pauliAction u (phaseZLabel i u v) (localPhase i ψ) x =
      star (phaseBit (u i)) * localPhase i (pauliAction u v ψ) x := by
  unfold pauliAction localPhase phaseZLabel
  simp only [add_dotProduct, smul_dotProduct, single_dotProduct, Pi.sub_apply,
    smul_eq_mul, one_mul, paritySign_add]
  calc
    paritySign (v ⬝ᵥ (x - u)) * paritySign (u i * (x i - u i)) *
        (phaseBit (x i - u i) * ψ (x - u)) =
      (paritySign (u i * (x i - u i)) * phaseBit (x i - u i)) *
        (paritySign (v ⬝ᵥ (x - u)) * ψ (x - u)) := by ring
    _ = _ := by rw [phaseBit_twist]; ring

theorem localPhase_eigenvector (i : ι) (ψ : Amplitude ι) (u v : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ u v ζ) :
    IsPauliEigenvector (localPhase i ψ) u (phaseZLabel i u v)
      (star (phaseBit (u i)) * ζ) := by
  intro x
  rw [localPhase_covariance]
  unfold localPhase
  rw [heig x]
  ring

/-- Apply H at one site through its two-term amplitude formula. -/
def localHadamard (i : ι) (ψ : Amplitude ι) (x : Bits ι) : ℂ :=
  QubitGates.hadamardCoefficient *
    (ψ (Function.update x i 0) + paritySign (x i) * ψ (Function.update x i 1))

/-- Replace the selected X label by its old Z label. -/
def hadamardXLabel (i : ι) (u v : Bits ι) : Bits ι := Function.update u i (v i)
/-- Replace the selected Z label by its old X label. -/
def hadamardZLabel (i : ι) (u v : Bits ι) : Bits ι := Function.update v i (u i)

theorem localHadamard_covariance (i : ι) (u v : Bits ι) (ψ : Amplitude ι)
    (x : Bits ι) :
    pauliAction (hadamardXLabel i u v) (hadamardZLabel i u v)
      (localHadamard i ψ) x =
      paritySign (u i * v i) * localHadamard i (pauliAction u v ψ) x := by
  simp only [pauliAction, localHadamard, hadamardXLabel, hadamardZLabel,
    sub_update, update_sub, dot_update_left, dot_update_right,
    Function.update_self, Function.update_idem, Pi.sub_apply]
  simp only [paritySign_add]
  generalize ha : u i = a
  generalize hb : v i = b
  generalize hc : x i = c
  rcases bit_eq_zero_or_one a with rfl | rfl <;>
    rcases bit_eq_zero_or_one b with rfl | rfl <;>
    rcases bit_eq_zero_or_one c with rfl | rfl <;>
    norm_num [paritySign, CharTwo.add_self_eq_zero] <;> split_ifs <;>
    try simp only [CharTwo.neg_eq]
  all_goals ring

theorem localHadamard_eigenvector (i : ι) (ψ : Amplitude ι) (u v : Bits ι) (ζ : ℂ)
    (heig : IsPauliEigenvector ψ u v ζ) :
    IsPauliEigenvector (localHadamard i ψ) (hadamardXLabel i u v)
      (hadamardZLabel i u v) (paritySign (u i * v i) * ζ) := by
  intro x
  rw [localHadamard_covariance]
  unfold localHadamard
  rw [heig (Function.update x i 0), heig (Function.update x i 1)]
  ring

theorem hadamardCoefficient_normSq :
    Complex.normSq QubitGates.hadamardCoefficient = 1 / 2 := by
  rw [QubitGates.hadamardCoefficient, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem hadamard_pair_norm (a b : ℂ) :
    Complex.normSq (QubitGates.hadamardCoefficient * (a + b)) +
      Complex.normSq (QubitGates.hadamardCoefficient * (a - b)) =
      Complex.normSq a + Complex.normSq b := by
  simp only [Complex.normSq_mul, hadamardCoefficient_normSq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

omit [Fintype ι] in
theorem localHadamard_pair_bornWeight (i : ι) (ψ : Amplitude ι) (x : Bits ι) :
    bornWeight (localHadamard i ψ) (Function.update x i 0) +
      bornWeight (localHadamard i ψ) (Function.update x i 1) =
      bornWeight ψ (Function.update x i 0) + bornWeight ψ (Function.update x i 1) := by
  classical
  simpa [bornWeight, localHadamard, paritySign, sub_eq_add_neg] using
    hadamard_pair_norm (ψ (Function.update x i 0)) (ψ (Function.update x i 1))


omit [Fintype ι] in
theorem flip_eq_update (i : ι) (x : Bits ι) :
    x + (Pi.single i 1 : Bits ι) = Function.update x i (x i + 1) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

theorem sum_update_pair (i : ι) (f : Bits ι → ℝ) :
    (∑ x, (f (Function.update x i 0) + f (Function.update x i 1))) =
      2 * ∑ x, f x := by
  have hpair (x : Bits ι) :
      f (Function.update x i 0) + f (Function.update x i 1) =
        f x + f (x + (Pi.single i 1 : Bits ι)) := by
    have hfix : Function.update x i (x i) = x := Function.update_eq_self i x
    rcases bit_eq_zero_or_one (x i) with hx | hx
    · have h0 : Function.update x i 0 = x := by simpa only [hx] using hfix
      rw [flip_eq_update, hx]
      norm_num
      rw [h0]
    · have h1 : Function.update x i 1 = x := by simpa only [hx] using hfix
      rw [flip_eq_update, hx, show (1 + 1 : ZMod 2) = 0 by decide, h1, add_comm]
  have hflip : (∑ x, f (x + (Pi.single i 1 : Bits ι))) = ∑ x, f x :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i 1 : Bits ι)) _ _ (fun _ => rfl)
  simp_rw [hpair]
  rw [Finset.sum_add_distrib, hflip]
  ring

theorem localHadamard_norm_preserving (i : ι) (ψ : Amplitude ι) :
    (∑ x, bornWeight (localHadamard i ψ) x) = ∑ x, bornWeight ψ x := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Bits ι))) rfl
    (fun x _ => localHadamard_pair_bornWeight i ψ x)
  rw [sum_update_pair, sum_update_pair] at h
  linarith

theorem localHadamard_normalized (i : ι) (ψ : Amplitude ι) (hψ : IsNormalized ψ) :
    IsNormalized (localHadamard i ψ) := by
  unfold IsNormalized
  rw [localHadamard_norm_preserving]
  exact hψ

/-- The adjoint S action on amplitudes. -/
def localPhaseInverse (i : ι) (ψ : Amplitude ι) (x : Bits ι) : ℂ :=
  star (phaseBit (x i)) * ψ x

theorem phaseBit_star_mul (a : ZMod 2) : star (phaseBit a) * phaseBit a = 1 := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;> norm_num [phaseBit]

omit [DecidableEq ι] [Fintype ι] in
theorem localPhaseInverse_localPhase (i : ι) (ψ : Amplitude ι) :
    localPhaseInverse i (localPhase i ψ) = ψ := by
  classical
  funext x
  simp only [localPhaseInverse, localPhase, ← mul_assoc, phaseBit_star_mul, one_mul]

omit [DecidableEq ι] [Fintype ι] in
theorem localPhase_localPhaseInverse (i : ι) (ψ : Amplitude ι) :
    localPhase i (localPhaseInverse i ψ) = ψ := by
  classical
  funext x
  unfold localPhase localPhaseInverse
  rw [← mul_assoc, mul_comm (phaseBit _), phaseBit_star_mul, one_mul]

omit [Fintype ι] in
theorem localHadamard_involutive (i : ι) (ψ : Amplitude ι) :
    localHadamard i (localHadamard i ψ) = ψ := by
  classical
  have ht : QubitGates.hadamardCoefficient ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two] using QubitGates.hadamardCoefficient_mul
  funext x
  have hfix : Function.update x i (x i) = x := Function.update_eq_self i x
  rcases bit_eq_zero_or_one (x i) with hx | hx
  · have h0 : Function.update x i 0 = x := by simpa only [hx] using hfix
    simp only [localHadamard, Function.update_self, Function.update_idem,
      hx, paritySign]
    norm_num
    rw [h0]
    ring_nf
    rw [ht]
    ring
  · have h1 : Function.update x i 1 = x := by simpa only [hx] using hfix
    simp only [localHadamard, Function.update_self, Function.update_idem,
      hx, paritySign]
    norm_num
    rw [h1]
    ring_nf
    rw [ht]
    ring

/-- H is a bijection on the full amplitude space, with itself as inverse. -/
def localHadamardEquiv (i : ι) : Amplitude ι ≃ Amplitude ι where
  toFun := localHadamard i
  invFun := localHadamard i
  left_inv := localHadamard_involutive i
  right_inv := localHadamard_involutive i

/-- S is a bijection on the full amplitude space with the explicit S† inverse. -/
def localPhaseEquiv (i : ι) : Amplitude ι ≃ Amplitude ι where
  toFun := localPhase i
  invFun := localPhaseInverse i
  left_inv := localPhaseInverse_localPhase i
  right_inv := localPhase_localPhaseInverse i

/-- The complex-linear involution induced by H at a selected site. -/
def localHadamardLinearEquiv (i : ι) : Amplitude ι ≃ₗ[ℂ] Amplitude ι where
  toEquiv := localHadamardEquiv i
  map_add' ψ φ := by
    funext x
    simp only [localHadamardEquiv, localHadamard, Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext x
    simp only [localHadamardEquiv, localHadamard, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The complex-linear equivalence induced by S at a selected site. -/
def localPhaseLinearEquiv (i : ι) : Amplitude ι ≃ₗ[ℂ] Amplitude ι where
  toEquiv := localPhaseEquiv i
  map_add' ψ φ := by
    funext x
    simp [localPhaseEquiv, localPhase, mul_add]
  map_smul' c ψ := by
    funext x
    simp only [localPhaseEquiv, localPhase, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

end LeanPool.SingleCopyStabilizer.CliffordAction
