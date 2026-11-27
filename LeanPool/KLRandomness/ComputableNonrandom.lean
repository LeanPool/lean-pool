/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Betting
public import LeanPool.KLRandomness.MartinLof

/-!
# Computable sequences fail Martin-Löf randomness

The test at level `n` is the single cylinder determined by the first `n` bits
of the sequence. Its uniform effectiveness is proved from actual computability
of the sequence, and its measure is exactly `(1/2)^n`.
-/

@[expose] public section

namespace Klr

open MeasureTheory
open scoped ENNReal

namespace ScanRule

@[simp] theorem length_inputPrefix (X : Cantor) (n : ℕ) :
    (inputPrefix X n).length = n := by
  simp [inputPrefix]

theorem getD_inputPrefix (X : Cantor) {n i : ℕ} (hi : i < n) :
    (inputPrefix X n).getD i false = X i := by
  simp [inputPrefix, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem mem_cylinder_inputPrefix (X : Cantor) (n : ℕ) :
    X ∈ cylinder (inputPrefix X n) := by
  intro i hi
  exact (getD_inputPrefix X (by simpa using hi)).symm

/-- A computable binary sequence has a computable function of finite prefixes. -/
theorem computable_inputPrefix {X : Cantor} (hX : Computable X) :
    Computable (inputPrefix X) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × List Bool) => p.2 ++ [X p.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hX.comp (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.id (Computable.const []) hstep).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [inputPrefix, List.range_succ] using congrArg (fun s => s ++ [X n]) ih

end ScanRule

/-- The single-cylinder test for a computable sequence is uniformly effectively open. -/
theorem computable_prefix_uniform {X : Cantor} (hX : Computable X) :
    IsUniformlyEffectivelyOpen (fun n => cylinder (ScanRule.inputPrefix X n)) := by
  have hp : ComputablePred (fun p : ℕ × List Bool => p.2 = ScanRule.inputPrefix X p.1) :=
    Computable.computablePred <|
      Primrec.eq.computablePred.decide.comp <|
        Computable.snd.pair ((ScanRule.computable_inputPrefix hX).comp Computable.fst)
  refine ⟨fun p => p.2 = ScanRule.inputPrefix X p.1, hp.to_re, fun n => ?_⟩
  ext Y
  simp [cylinderUnion]

/-- No computable binary sequence is Martin-Löf random. -/
theorem not_martinLofRandom_of_computable {X : Cantor} (hX : Computable X) :
    ¬MartinLofRandom X := by
  apply not_martinLofRandom_of_uniform (computable_prefix_uniform hX)
  · intro n
    simp
  · exact ScanRule.mem_cylinder_inputPrefix X

/-- In particular, Martin-Löf randomness implies incomputability. -/
theorem MartinLofRandom.not_computable {X : Cantor} (hX : MartinLofRandom X) :
    ¬Computable X :=
  fun h => not_martinLofRandom_of_computable h hX

end Klr
