/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Siegel.Integral

/-!
# `∑ n^{-s} = 1/(s-1) + H(s)` and real values on the real axis

`H(s) = 1 - s ∫_{t>1} {t} t^{-(s+1)}` is holomorphic on `Re s > 0`, bounded by `1 + |s|/Re s`,
real and `≤ 1` on the positive real axis. We also show that `L(β, χ)` is real for real `β > 0`
and real `χ`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Asymptotics Topology

namespace SiegelThmLib

/-- `J` of a real-valued function at a real point is real. -/
lemma J_ofReal (g : ℝ → ℝ) (β : ℝ) :
    J (fun t => (g t : ℂ)) β = ((∫ t in Ioi (1 : ℝ), g t * t ^ (-(β + 1)) : ℝ) : ℂ) := by
  rw [J, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
  rw [ofReal_mul, ofReal_cpow ht']
  push_cast
  try ring

/-- `fract`, as a complex function. -/
noncomputable abbrev fr (t : ℝ) : ℂ := ((Int.fract t : ℝ) : ℂ)

lemma measurable_fr : Measurable fr := measurable_ofReal.comp measurable_fract

lemma norm_fr_le (t : ℝ) : ‖fr t‖ ≤ 1 := by
  rw [fr, norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

/-- `H(s) = 1 - s ∫_{t>1} {t} t^{-(s+1)}`. -/
noncomputable def Hz (s : ℂ) : ℂ := 1 - s * J fr s

lemma differentiableAt_Hz {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Hz s :=
  (differentiableAt_const _).sub
    (differentiableAt_id.mul (differentiableAt_J measurable_fr norm_fr_le hs))

lemma norm_J_fr_le {s : ℂ} (hs : 0 < s.re) : ‖J fr s‖ ≤ 1 / s.re := by
  have := norm_J_le (g := fr) (B := 1) (κ := 0)
    (fun t _ => by simpa using norm_fr_le t) hs
  simpa using this

lemma norm_Hz_le {s : ℂ} (hs : 0 < s.re) : ‖Hz s‖ ≤ 1 + ‖s‖ / s.re := by
  rw [Hz]
  calc ‖1 - s * J fr s‖ ≤ ‖(1 : ℂ)‖ + ‖s * J fr s‖ := norm_sub_le _ _
    _ = 1 + ‖s‖ * ‖J fr s‖ := by rw [norm_one, norm_mul]
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by
        gcongr; exact norm_J_fr_le hs
    _ = 1 + ‖s‖ / s.re := by ring

/-- `∑ n^{-s} = 1/(s-1) + H(s)` for `Re s > 1`. -/
lemma LSeries_one_eq {s : ℂ} (hs : 1 < s.re) : LSeries 1 s = 1 / (s - 1) + Hz s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp
  rw [LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hs (LSeriesSummable_one_iff.mpr hs) hO]
  have hs0 : 0 < s.re := by linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hint2 : IntegrableOn (fun t : ℝ => fr t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_J (g := fr) measurable_fr.aestronglyMeasurable (B := 1) (κ := 0)
      (fun t _ => by simpa using norm_fr_le t) hs0
  have hcongr : ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) *
      (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (-s) - fr t * (t : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor ht0.le]; push_cast; ring
    have hsum : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k = ((t - Int.fract t : ℝ) : ℂ) := by
      rw [← hfl]; simp
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      have h := cpow_add (x := (t : ℂ)) (-(s + 1)) 1 (by exact_mod_cast ht0.ne')
      rw [show -(s + 1) + 1 = -s by ring, cpow_one] at h
      rw [h, mul_comm]
    rw [hsum, hpow, fr]
    push_cast
    ring
  rw [hcongr, integral_sub hint1 hint2, integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have hs2 : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  rw [Hz, J]
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-- `H(β)` is real and `≤ 1` for real `β > 0`. -/
lemma Hz_real {β : ℝ} (hβ : 0 < β) : ∃ x : ℝ, Hz β = x ∧ x ≤ 1 := by
  have hJ := J_ofReal (fun t => Int.fract t) β
  refine ⟨1 - β * ∫ t in Ioi (1 : ℝ), Int.fract t * t ^ (-(β + 1)), ?_, ?_⟩
  · rw [Hz]
    have : J fr β = J (fun t => ((Int.fract t : ℝ) : ℂ)) β := rfl
    rw [this, hJ]; push_cast; try ring
  · have : 0 ≤ ∫ t in Ioi (1 : ℝ), Int.fract t * t ^ (-(β + 1)) := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      exact mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (by linarith [mem_Ioi.mp ht]) _)
    nlinarith

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- For a real character, `A_χ` is real-valued. -/
lemma A_eq_ofReal {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (t : ℝ) :
    A χ t = ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (χ k).re : ℝ) : ℂ) := by
  rw [A]; push_cast
  exact Finset.sum_congr rfl fun k _ => val_eq_ofReal_re hχ _

/-- `L(β, χ)` is real for a real non-principal `χ` and real `β > 0`. -/
lemma LFunction_real {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {β : ℝ}
    (hβ : 0 < β) : ∃ x : ℝ, DirichletCharacter.LFunction χ β = x := by
  rw [LFunction_eq_mul_J hχ (by simpa using hβ)]
  have : J (A χ) β = J (fun t => ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (χ k).re : ℝ) : ℂ)) β := by
    rw [J, J]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [A_eq_ofReal hχ2]
  rw [this, J_ofReal]
  exact ⟨_, (ofReal_mul _ _).symm⟩

end SiegelThmLib
