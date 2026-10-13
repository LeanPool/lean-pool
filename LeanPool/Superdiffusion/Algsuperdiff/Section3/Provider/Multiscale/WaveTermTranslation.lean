/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.WaveTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTermSquared

/-!
# WaveTermTranslation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Measurability of the Step-2 tail leg

The tail leg of `e.wave.influence.bound` is a random sum: its number of
summands is the truncation depth `hsep`, an observable of the sample built from
a lattice of bad sites and a cluster-diameter count.  This module proves that
the sum is a random variable, the measurability datum every transport of the
tail leg consumes.

The truncation depth is NOT a pathwise translation invariant — stationarity
equalizes its law, not its values — so nothing here identifies the depths read
at two different cubes.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.measurable_waveTailTerm`: the tail
  leg `waveTailTerm M m E b lout ell` is measurable.  The depth `hsep` is a
  measurable `ℕ`-valued observable by `measurableSet_lt_hsep`, and a
  `Finset.range` sum of measurable summands over a measurable depth is
  measurable because the sample space splits along the countably many values of
  the depth.

## References

* ABK26, `e.wave.influence.bound`, with the layer decomposition and the tail
  bookkeeping.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## The per-layer wave gauge at an arbitrary cube -/


/-! ## The deterministic domination at an arbitrary cube -/


/-! ## The per-layer `Gamma_2` display at an arbitrary cube -/


/-! ## The macroscopic leg at an arbitrary cube -/


/-! ## The tail leg at an arbitrary cube -/


/-! ## Measurability of the truncated tail sum -/

private theorem measurable_sum_range {Omega : Type*} [MeasurableSpace Omega]
    {N : Omega → ℕ} (hN : Measurable N) {Y : ℕ → Omega → ℝ}
    (hY : ∀ i, Measurable (Y i)) :
    Measurable fun omega : Omega => ∑ i ∈ Finset.range (N omega), Y i omega := by
  intro s hs
  have hset : (fun omega : Omega => ∑ i ∈ Finset.range (N omega), Y i omega) ⁻¹' s =
      ⋃ k : ℕ, N ⁻¹' {k} ∩
        (fun omega : Omega => ∑ i ∈ Finset.range k, Y i omega) ⁻¹' s := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨N omega, rfl, h⟩
    · rintro ⟨k, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun k => ?_
  exact (hN (measurableSet_singleton k)).inter
    ((Finset.measurable_sum (Finset.range k) fun i _ => hY i) hs)

private theorem measurable_hsep (M : ABKModel d) (m : ℤ) (E b : ℝ) :
    Measurable (hsep M m E b) := by
  refine measurable_to_countable' fun k => ?_
  cases k with
  | zero =>
      have hset : hsep M m E b ⁻¹' {0} =
          {omega : CutoffSample d | 0 < hsep M m E b omega}ᶜ := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
          Set.mem_ofPred_eq]
        omega
      rw [hset]
      exact (measurableSet_lt_hsep M m E b 0).compl
  | succ j =>
      have hset : hsep M m E b ⁻¹' {j + 1} =
          {omega : CutoffSample d | j < hsep M m E b omega} ∩
            {omega : CutoffSample d | j + 1 < hsep M m E b omega}ᶜ := by
        ext omega
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_compl_iff, Set.mem_ofPred_eq]
        omega
      rw [hset]
      exact (measurableSet_lt_hsep M m E b j).inter
        (measurableSet_lt_hsep M m E b (j + 1)).compl

/-- The origin tail leg is a random variable.  This is the measurability datum
the abstract transport consumes; the truncation depth `hsep` is a measurable
`Nat`-valued observable by `measurableSet_lt_hsep`. -/
theorem measurable_waveTailTerm (M : ABKModel d) (m : ℤ) (E b : ℝ) (lout ell : ℤ) :
    Measurable (waveTailTerm M m E b lout ell) := by
  have hrw : waveTailTerm M m E b lout ell = fun omega : CutoffSample d =>
      Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        ∑ i ∈ Finset.range (hsep M m E b omega),
          waveL4Tail M lout ell (i + 1) omega := rfl
  rw [hrw]
  exact measurable_const.mul
    (measurable_sum_range (measurable_hsep M m E b)
      fun i => measurable_waveL4Tail M lout ell (i + 1))

/-! ## The tail leg at an arbitrary cube -/


end

end Algsuperdiff.Section3.Provider.Multiscale
