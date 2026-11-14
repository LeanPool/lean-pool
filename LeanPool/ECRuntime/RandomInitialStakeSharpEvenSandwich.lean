/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel
public import LeanPool.ECRuntime.RandomInitialStakeDyadicLogTwoLimit
public import LeanPool.ECRuntime.RandomInitialStakeFiniteHarmonicTailEnclosure

/-!
Quantitative dyadic harmonic-tail bounds and the sharp even-dimensional
correction. The finite enclosure and convergence to `log 2` give signed
`O(1/m)` bounds, which yield `-1/2` after rescaling.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter

namespace ECRuntime

/-! The two elementary limit bridges below isolate all analytic ingredients
of the sharp finite bound. The key input is the *certified* finite Stage 199
comparison, not an assumed harmonic expansion. -/

private theorem stage189_tendsto_shifted_reciprocal (k : Nat) :
    Tendsto (fun n : Nat => 1 / (4 * (((k + n : Nat) : Real))))
      atTop (nhds (0 : Real)) := by
  have hshift : Tendsto (fun n : Nat => k + n) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun n : Nat => (show n ≤ k + n by omega)))
      tendsto_id
  have hcast : Tendsto (fun n : Nat => (((k + n : Nat) : Real)))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hshift
  have hinv : Tendsto (fun n : Nat => (((k + n : Nat) : Real))⁻¹)
      atTop (nhds (0 : Real)) := tendsto_inv_atTop_zero.comp hcast
  have hscaled := hinv.const_mul (1 / 4 : Real)
  convert hscaled using 1
  · funext n
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  · ring_nf

/-- A quantitative dyadic harmonic-tail enclosure. The scale of both
    endpoints is 1/m; mere convergence to log(2) does not imply this. -/
theorem proposed_randomInitialStake_evenTail_sharpSandwich
    (m : Nat) (hm : 1 ≤ m) :
    -(1 / (4 * (m : Real))) ≤
        harmonicReal (2 * m) - harmonicReal m - Real.log 2 ∧
      harmonicReal (2 * m) - harmonicReal m - Real.log 2 ≤
        -(1 / (4 * ((m + 1 : Nat) : Real))) := by
  have hshift : Tendsto (fun n : Nat => m + n) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun n : Nat => (show n ≤ m + n by omega)))
      tendsto_id
  have hA : Tendsto
      (fun n : Nat => harmonicReal (2 * (m + n)) - harmonicReal (m + n))
      atTop (nhds (Real.log 2)) := by
    simpa only [Function.comp_def] using
      (proposed_randomInitialStake_dyadicHarmonic_tendsto_logTwo.comp hshift)
  have hmid : Tendsto
      (fun n : Nat =>
        (harmonicReal (2 * (m + n)) - harmonicReal (m + n)) -
          (harmonicReal (2 * m) - harmonicReal m))
      atTop
      (nhds (Real.log 2 - (harmonicReal (2 * m) - harmonicReal m))) := by
    exact hA.sub tendsto_const_nhds
  have hlo : Tendsto
      (fun n : Nat =>
        1 / (4 * (((m + 1 : Nat) : Real))) -
          1 / (4 * (((m + 1 + n : Nat) : Real))))
      atTop (nhds (1 / (4 * (((m + 1 : Nat) : Real))))) := by
    have hc : Tendsto
        (fun _ : Nat => 1 / (4 * (((m + 1 : Nat) : Real))))
        atTop (nhds (1 / (4 * (((m + 1 : Nat) : Real))))) :=
      tendsto_const_nhds
    simpa only [sub_zero] using
      hc.sub (stage189_tendsto_shifted_reciprocal (m + 1))
  have hhi : Tendsto
      (fun n : Nat =>
        1 / (4 * (m : Real)) -
          1 / (4 * (((m + n : Nat) : Real))))
      atTop (nhds (1 / (4 * (m : Real)))) := by
    have hc : Tendsto (fun _ : Nat => 1 / (4 * (m : Real)))
        atTop (nhds (1 / (4 * (m : Real)))) := tendsto_const_nhds
    simpa only [sub_zero] using
      hc.sub (stage189_tendsto_shifted_reciprocal m)
  have hleft :
      1 / (4 * (((m + 1 : Nat) : Real))) <=
        Real.log 2 - (harmonicReal (2 * m) - harmonicReal m) :=
    le_of_tendsto_of_tendsto' hlo hmid
      (fun n : Nat =>
        (proposed_randomInitialStake_finiteHarmonicTailEnclosure m n hm).1)
  have hright :
      Real.log 2 - (harmonicReal (2 * m) - harmonicReal m) <=
        1 / (4 * (m : Real)) :=
    le_of_tendsto_of_tendsto' hmid hhi
      (fun n : Nat =>
        (proposed_randomInitialStake_finiteHarmonicTailEnclosure m n hm).2)
  constructor <;> linarith

/-- The sharp constant follows by squeezing as soon as the explicit finite
    sandwich has been established. This does not prove the sandwich itself. -/
theorem stage189_evenSharp_of_finiteSandwich
    (hbound : ∀ m : Nat, 1 ≤ m →
      -(1 / (4 * (m : Real))) ≤
        harmonicReal (2 * m) - harmonicReal m - Real.log 2 ∧
      harmonicReal (2 * m) - harmonicReal m - Real.log 2 ≤
        -(1 / (4 * ((m + 1 : Nat) : Real)))) :
    Tendsto (fun m : Nat =>
      ((2 * m : Nat) : Real) *
        (harmonicReal (2 * m) - harmonicReal m - Real.log 2))
      atTop (nhds (-(1 / 2 : Real))) := by
  let D : Nat → Real := fun m =>
    harmonicReal (2 * m) - harmonicReal m - Real.log 2
  have hden : Tendsto (fun m : Nat => ((m + 1 : Nat) : Real))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => by
        exact_mod_cast (Nat.le_succ m)))
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : Nat => ((m + 1 : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp hden
  have hupper : Tendsto
      (fun m : Nat => (1 / 2 : Real) * ((m + 1 : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hinv.const_mul (1 / 2 : Real)
  have hpoint (m : Nat) :
      0 ≤ ((2 * m : Nat) : Real) * D m + 1 / 2 ∧
        ((2 * m : Nat) : Real) * D m + 1 / 2 ≤
          (1 / 2 : Real) * ((m + 1 : Nat) : Real)⁻¹ := by
    by_cases hm : 1 ≤ m
    · obtain ⟨hl, hu⟩ := hbound m hm
      have hmp : (0 : Real) < (m : Real) := by
        exact_mod_cast (by omega : 0 < m)
      have hcast : ((2 * m : Nat) : Real) = 2 * (m : Real) := by
        push_cast
        ring
      have hcastSucc : ((m + 1 : Nat) : Real) = (m : Real) + 1 := by
        push_cast
        ring
      have hsp : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
      have hlow := mul_le_mul_of_nonneg_left hl (by positivity : (0 : Real) ≤ 2 * (m : Real))
      have hupp := mul_le_mul_of_nonneg_left hu (by positivity : (0 : Real) ≤ 2 * (m : Real))
      have hidlow : (2 * (m : Real)) * (-(1 / (4 * (m : Real)))) =
          -(1 / 2 : Real) := by
        field_simp
        ring
      have hidupp : (2 * (m : Real)) *
            (-(1 / (4 * ((m + 1 : Nat) : Real)))) + 1 / 2 =
          (1 / 2 : Real) * ((m + 1 : Nat) : Real)⁻¹ := by
        rw [hcastSucc]
        field_simp
        ring
      constructor
      · dsimp [D]
        rw [hcast]
        linarith
      · dsimp [D]
        rw [hcast]
        linarith
    · have hz : m = 0 := by omega
      subst m
      simp only [Nat.mul_zero, Nat.cast_zero, zero_mul,
        zero_add, Nat.cast_one, inv_one, mul_one]
      norm_num
  have hshift : Tendsto
      (fun m : Nat => ((2 * m : Nat) : Real) * D m + 1 / 2)
      atTop (nhds (0 : Real)) := by
    apply squeeze_zero
    · intro m; exact (hpoint m).1
    · intro m; exact (hpoint m).2
    · exact hupper
  have hfinal := hshift.sub
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 / 2 : Real))
      atTop (nhds (1 / 2 : Real)))
  simpa only [add_sub_cancel_right, zero_sub, D] using hfinal

end ECRuntime
