/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveScan
public import LeanPool.KLRandomness.MaximalInequality
public import LeanPool.KLRandomness.ComputableRational
import Mathlib.Tactic.Linarith

/-!
# Martin-Löf randomness implies Kolmogorov–Loveland randomness

A fixed-precision rational approximation to capital suffices to construct the
test: enumerate transcripts where the approximation exceeds `2^m + 1`. The
error is at most one, so the maximal inequality gives the level bound; capital
above `2^m + 2` ensures membership. Uniform higher precision is not needed in
this particular argument.
-/

@[expose] public section

namespace Klr

open MeasureTheory RationalComputability
open scoped ENNReal

private theorem computable_two_pow_rat : Computable (fun n : ℕ => (2 : ℚ) ^ n) := by
  have hproj : Computable (fun p : ℕ × (ℕ × ℚ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hs₀ := primrec_rat_mul.to_comp.comp hproj (Computable.const 2)
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 * 2) :=
    hs₀.to₂.of_eq (fun _ => rfl)
  apply (Computable.nat_rec Computable.id (Computable.const 1) hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [id_eq, Nat.rec_add_one, pow_succ] using congrArg (· * 2) ih

/-- Every total computable-real betting strategy has one genuine Martin-Löf test covering
all inputs on which it succeeds. -/
theorem BettingStrategy.exists_test_covers_success (s : BettingStrategy) :
    ∃ T : MartinLofTest, ∀ X, s.Succeeds X → T.Fails X := by
  obtain ⟨q, hq, herror⟩ := s.computable_capital
  have hc₀ := (computable_rat_of_numDen hq).comp (Computable.id.pair (Computable.const 0))
  have hc : Computable (fun v : List Bool => q v 0) := hc₀.of_eq (fun _ => rfl)
  let R : ℕ × List Bool → Prop := fun p => (2 : ℚ) ^ p.1 + 1 < q p.2 0
  have hR : ComputablePred R := by
    have hq₀ := hc.comp (Computable.snd : Computable (fun p : ℕ × List Bool => p.2))
    have hp₀ := computable_two_pow_rat.comp
      (Computable.fst : Computable (fun p : ℕ × List Bool => p.1))
    have ht₀ := primrec_rat_add.to_comp.comp hp₀ (Computable.const 1)
    have hbool₀ := primrec_rat_le.computablePred.decide.comp (hq₀.pair ht₀)
    have hbool : Computable (fun p : ℕ × List Bool =>
        decide (q p.2 0 ≤ (2 : ℚ) ^ p.1 + 1)) := hbool₀.of_eq (fun _ => rfl)
    have hle : ComputablePred (fun p : ℕ × List Bool => q p.2 0 ≤ (2 : ℚ) ^ p.1 + 1) :=
      hbool.computablePred
    exact hle.not.of_eq (fun _ => not_le)
  let U := EffectiveScan.openEvent s.scan R
  have hU : IsUniformlyEffectivelyOpen U := EffectiveScan.openEvent_uniform s.scan hR
  have hbound : ∀ m, fairCoin (U m) ≤ (1 / 2 : ℝ≥0∞) ^ m := by
    intro m
    apply (measure_mono (show U m ⊆ s.capital.exceeds s.scan ((2 : ℝ) ^ m) from ?_)).trans
      (s.capital.measure_exceeds_pow_le s.scan m)
    rintro X ⟨v, hv, hX⟩
    have he := herror v 0
    simp only [pow_zero] at he
    have hqv : (2 : ℝ) ^ m + 1 < (q v 0 : ℝ) := by
      have hcast := (Rat.cast_lt (K := ℝ)).mpr (show (2 : ℚ) ^ m + 1 < q v 0 from hv)
      simpa only [Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hcast
    have hd : (2 : ℝ) ^ m < s.capital.value v := by
      have he' := (abs_le.mp he).2
      linarith
    exact ⟨v.length, by simpa only [hX] using hd⟩
  obtain ⟨T, hT⟩ := MartinLofTest.exists_of_uniform hU hbound
  refine ⟨T, fun X hsuccess m => ?_⟩
  change X ∈ programOpen T.code m
  rw [hT m]
  obtain ⟨n, hn⟩ := hsuccess ((2 : ℝ) ^ m + 2)
  let v := s.scan.transcript X n
  have he := herror v 0
  simp only [pow_zero] at he
  have hqv : (2 : ℝ) ^ m + 1 < (q v 0 : ℝ) := by
    have he' := (abs_le.mp he).1
    change (2 : ℝ) ^ m + 2 < s.capital.value v at hn
    linarith
  refine ⟨v, ?_, ?_⟩
  · change (2 : ℚ) ^ m + 1 < q v 0
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hqv
  · simp [v]

/-- The standard containment, for the repository's actual effective-test and strategy types. -/
theorem MartinLofRandom.kolmogorovLovelandRandom {X : Cantor} (hX : MartinLofRandom X) :
    KolmogorovLovelandRandom X := by
  intro s hs
  obtain ⟨T, hT⟩ := s.exists_test_covers_success
  exact hX T (hT X hs)

end Klr
