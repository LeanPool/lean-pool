/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz

/-!
# TwoTermPromotion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Promotion of a one-sided Orlicz bound to the two-term shape

Model-free: a one-sided `Gamma_{sigma_1}` bound gives the two-term shape at any
larger first amplitude and any positive second amplitude, by taking the second
witness identically `0`.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory

/-- A one-sided `Gamma_{sigma_1}` bound gives the two-term shape used by
`inductionState`, at any larger first amplitude and any positive second
amplitude: take the second witness identically `0`, whose upper tail event is
empty at every threshold `t >= 1`. -/
theorem isTwoTermBigOWith_of_isOneSidedOrlicz {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X : Omega → ℝ} {A A1 A2 : ℝ}
    {s1 s2 : ℝ} (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hX : Probability.IsOneSidedOrlicz mu
      (HCPolySupport.IndependentSums.gammaSigma s1) X A)
    (hA1 : A ≤ A1) (hA1pos : 0 < A1) (hA2 : 0 < A2) :
    Probability.IsTwoTermBigOWith mu
      (HCPolySupport.IndependentSums.gammaSigma s1)
      (HCPolySupport.IndependentSums.gammaSigma s2) X A1 A2 := by
  obtain ⟨-, -, hmeas, htail⟩ := hX
  refine ⟨X, fun _ => 0, Probability.isAdmissibleTail_gammaSigma hs1,
    Probability.isAdmissibleTail_gammaSigma hs2, hA1pos, hA2, hmeas, hmeas,
    measurable_const, fun _ => by simp, htail.mono_scale hA1, ?_⟩
  intro t ht
  have hpos : 0 < A2 * t := mul_pos hA2 (lt_of_lt_of_le zero_lt_one ht)
  have hempty : {omega : Omega | A2 * t < (0 : ℝ)} = (∅ : Set Omega) := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hpos.le
  change mu.real (HCPolySupport.IndependentSums.upperTailEvent (fun _ => (0 : ℝ)) (A2 * t))
    ≤ _
  rw [show HCPolySupport.IndependentSums.upperTailEvent (fun _ : Omega => (0 : ℝ)) (A2 * t)
      = {omega : Omega | A2 * t < (0 : ℝ)} from rfl, hempty]
  simp only [measureReal_empty]
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  exact (Real.exp_pos _).le

end Algsuperdiff.Section3.Provider.Orlicz
