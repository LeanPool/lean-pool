/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Nonresonance
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.ShiftedFourier

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Complex
namespace KamProject.Arnold1963

/-- Pairing with an integer Fourier index as a continuous complex linear functional. -/
def indexPairingCLM {n : ℕ} (k : FourierIndex n) : ComplexSpace n →L[ℂ] ℂ :=
  ∑ j, (k j : ℂ) • ContinuousLinearMap.proj j

@[simp] theorem indexPairingCLM_apply {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    indexPairingCLM k q = indexPairing k q := by
  simp [indexPairingCLM, indexPairing]

theorem fderiv_fourierMonomial {n : ℕ} (k : FourierIndex n) (q v : ComplexSpace n) :
    fderiv ℂ (fourierMonomial k) q v =
      (I * indexPairing k v) * fourierMonomial k q := by
  have hd := ((indexPairingCLM k).hasFDerivAt (x := q)).const_mul I |>.cexp
  simp only [indexPairingCLM_apply] at hd
  change HasFDerivAt (𝕜 := ℂ) (fourierMonomial k) _ q at hd
  rw [hd.fderiv]
  simp [fourierMonomial, mul_comm, mul_left_comm]

theorem fourierMonomial_periodic {n : ℕ} (k m : FourierIndex n) (q : ComplexSpace n) :
    fourierMonomial k (q + angleShift m) = fourierMonomial k q := by
  rw [fourierMonomial_add]
  have he : I * indexPairing k (angleShift m) =
      (∑ j, k j * m j : ℤ) * (2 * Real.pi * I) := by
    simp only [indexPairing, angleShift, complexify, Int.cast_sum, Int.cast_mul,
      ofReal_mul, ofReal_ofNat, ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [fourierMonomial]
  rw [he, exp_int_mul_two_pi_mul_I, mul_one]

theorem fourierMonomial_conj_neg {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    fourierMonomial (-k) (conjVec q) = star (fourierMonomial k q) := by
  simp only [fourierMonomial, indexPairing_neg, indexPairing_conj]
  simp [← Complex.exp_conj]

theorem sum_lowModes_neg {n : ℕ} {A : Type*} [AddCommMonoid A]
    (N : ℝ) (f : FourierIndex n → A) :
    ∑ k ∈ lowModes n N, f (-k) = ∑ k ∈ lowModes n N, f k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk; exact neg_mem_lowModes.mpr hk
  · intro a _ b _ he; exact neg_injective he
  · intro k hk; exact ⟨-k, neg_mem_lowModes.mpr hk, neg_neg k⟩
  · intro k _; rfl

theorem angle_fderiv_eq_sum_qGradient {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {p q : ComplexSpace n} (ha : AnalyticAt ℂ S (p, q)) (v : ComplexSpace n) :
    fderiv ℂ (fun t => S (p, t)) q v = ∑ j, v j * qGradient S (p, q) j := by
  have hd := ha.differentiableAt.hasFDerivAt.comp q
    ((hasFDerivAt_const p q).prodMk (hasFDerivAt_id (𝕜 := ℂ) q))
  change fderiv ℂ (S ∘ Prod.mk p) q v = _
  rw [hd.fderiv]
  change fderiv ℂ S (p, q) (0, v) = _
  have he : (0, v) = ∑ j, v j • qDirection j := by
    apply Prod.ext
    · simp [qDirection, Prod.fst_sum]
    · simpa [qDirection, Prod.snd_sum] using (pi_eq_sum_univ' v)
  rw [he, map_sum]
  simp [qGradient, map_smul]

end KamProject.Arnold1963
