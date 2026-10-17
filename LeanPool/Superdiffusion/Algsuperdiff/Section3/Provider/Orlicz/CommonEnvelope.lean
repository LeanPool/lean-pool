/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# CommonEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Common envelopes for two countable Orlicz channels

The Section 3.5 cutoff union is countable, but its conclusion requires one
pair of measurable witnesses chosen before every cutoff index.  This module
performs exactly that quantifier exchange for two summable families of
weak-Orlicz scales.  It does not use independence or identify any
source-facing node.

The proof takes the sum of measurable absolute-value representatives in each
channel.  Summability almost everywhere follows from the channel tails, and
the countable `Gamma_sigma` triangle inequality controls the resulting common
envelopes.

## References

* ABK26, Appendix.
* ABK26, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

/-- Two countable families with summable positive `Gamma_sigma` scales admit
one measurable envelope in each channel.  The witnesses are selected before
the family index, and each domination statement holds on a conull event.

This is a candidate countable-envelope mechanism for the Section 3.5 cutoff
union.  It deliberately keeps the two tail exponents and their scales
separate. -/
theorem exists_twoChannel_commonEnvelope_of_summable
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {sigmaOne sigmaTwo : ℝ}
    (hsigmaOne : 0 < sigmaOne) (hsigmaTwo : 0 < sigmaTwo)
    {aOne aTwo : ℕ → ℝ}
    (haOne : ∀ j, 0 < aOne j) (haTwo : ∀ j, 0 < aTwo j)
    (haOneSummable : Summable aOne) (haTwoSummable : Summable aTwo)
    {FOne FTwo : ℕ → Omega → ℝ}
    (hFOneMeas : ∀ j, AEMeasurable (FOne j) mu)
    (hFTwoMeas : ∀ j, AEMeasurable (FTwo j) mu)
    (hFOne : ∀ j, IsBigO mu (gammaSigma sigmaOne) (FOne j) (aOne j))
    (hFTwo : ∀ j, IsBigO mu (gammaSigma sigmaTwo) (FTwo j) (aTwo j)) :
    ∃ SOne STwo : Omega → ℝ,
      Measurable SOne ∧
        Measurable STwo ∧
          (∀ j, (fun omega => |FOne j omega|) ≤ᵐ[mu] SOne) ∧
            (∀ j, (fun omega => |FTwo j omega|) ≤ᵐ[mu] STwo) ∧
              IsBigOWith mu (gammaSigma sigmaOne) SOne
                (gammaTriangleConst sigmaOne * ∑' j, aOne j) ∧
                IsBigOWith mu (gammaSigma sigmaTwo) STwo
                  (gammaTriangleConst sigmaTwo * ∑' j, aTwo j) := by
  let WOne : ℕ → Omega → ℝ := fun j omega =>
    |(hFOneMeas j).mk (FOne j) omega|
  let WTwo : ℕ → Omega → ℝ := fun j omega =>
    |(hFTwoMeas j).mk (FTwo j) omega|
  have hWOneMeas : ∀ j, Measurable (WOne j) := fun j =>
    continuous_abs.measurable.comp (hFOneMeas j).measurable_mk
  have hWTwoMeas : ∀ j, Measurable (WTwo j) := fun j =>
    continuous_abs.measurable.comp (hFTwoMeas j).measurable_mk
  have hWOneNonneg : ∀ j omega, 0 ≤ WOne j omega := fun j omega => by
    exact abs_nonneg _
  have hWTwoNonneg : ∀ j omega, 0 ≤ WTwo j omega := fun j omega => by
    exact abs_nonneg _
  have hWOneBigO : ∀ j,
      IsBigO mu (gammaSigma sigmaOne) (WOne j) (aOne j) := by
    intro j
    have hmk : IsBigO mu (gammaSigma sigmaOne)
        ((hFOneMeas j).mk (FOne j)) (aOne j) :=
      (HCPolySupport.Book.Ch04.isBigO_congr_ae
        (hFOneMeas j).ae_eq_mk).mp (hFOne j)
    unfold WOne IsBigO at hmk ⊢
    simpa only [abs_abs] using hmk
  have hWTwoBigO : ∀ j,
      IsBigO mu (gammaSigma sigmaTwo) (WTwo j) (aTwo j) := by
    intro j
    have hmk : IsBigO mu (gammaSigma sigmaTwo)
        ((hFTwoMeas j).mk (FTwo j)) (aTwo j) :=
      (HCPolySupport.Book.Ch04.isBigO_congr_ae
        (hFTwoMeas j).ae_eq_mk).mp (hFTwo j)
    unfold WTwo IsBigO at hmk ⊢
    simpa only [abs_abs] using hmk
  have hWOneTail : ∀ j,
      IsBigOWith mu (gammaSigma sigmaOne) (WOne j) (aOne j) := fun j =>
    (isBigOWith_iff_isBigO_of_nonneg (hWOneNonneg j)).2 (hWOneBigO j)
  have hWTwoTail : ∀ j,
      IsBigOWith mu (gammaSigma sigmaTwo) (WTwo j) (aTwo j) := fun j =>
    (isBigOWith_iff_isBigO_of_nonneg (hWTwoNonneg j)).2 (hWTwoBigO j)
  have hsumOne : ∀ᵐ omega ∂mu, Summable fun j => WOne j omega :=
    ae_summable_of_isBigOWith_gammaSigma hsigmaOne hWOneNonneg
      (fun j => (hWOneMeas j).aemeasurable) haOne haOneSummable hWOneTail
  have hsumTwo : ∀ᵐ omega ∂mu, Summable fun j => WTwo j omega :=
    ae_summable_of_isBigOWith_gammaSigma hsigmaTwo hWTwoNonneg
      (fun j => (hWTwoMeas j).aemeasurable) haTwo haTwoSummable hWTwoTail
  let TOne : Omega → ℝ := fun omega => ∑' j, WOne j omega
  let TTwo : Omega → ℝ := fun omega => ∑' j, WTwo j omega
  have hTOneNonneg : ∀ omega, 0 ≤ TOne omega := fun omega => by
    exact tsum_nonneg fun j => hWOneNonneg j omega
  have hTTwoNonneg : ∀ omega, 0 ≤ TTwo omega := fun omega => by
    exact tsum_nonneg fun j => hWTwoNonneg j omega
  have hTOneMeas : AEMeasurable TOne mu :=
    AEMeasurable.tsum (L := SummationFilter.unconditional ℕ)
      (fun j => (hWOneMeas j).aemeasurable)
  have hTTwoMeas : AEMeasurable TTwo mu :=
    AEMeasurable.tsum (L := SummationFilter.unconditional ℕ)
      (fun j => (hWTwoMeas j).aemeasurable)
  let SOne : Omega → ℝ := fun omega => |hTOneMeas.mk TOne omega|
  let STwo : Omega → ℝ := fun omega => |hTTwoMeas.mk TTwo omega|
  have hSOneMeas : Measurable SOne :=
    continuous_abs.measurable.comp hTOneMeas.measurable_mk
  have hSTwoMeas : Measurable STwo :=
    continuous_abs.measurable.comp hTTwoMeas.measurable_mk
  have hTOneEq : TOne =ᵐ[mu] SOne := by
    filter_upwards [hTOneMeas.ae_eq_mk] with omega homega
    dsimp only [SOne]
    rw [← homega, abs_of_nonneg (hTOneNonneg omega)]
  have hTTwoEq : TTwo =ᵐ[mu] STwo := by
    filter_upwards [hTTwoMeas.ae_eq_mk] with omega homega
    dsimp only [STwo]
    rw [← homega, abs_of_nonneg (hTTwoNonneg omega)]
  have hTOneTail : IsBigOWith mu (gammaSigma sigmaOne) TOne
      (gammaTriangleConst sigmaOne * ∑' j, aOne j) := by
    exact isBigOWith_gammaSigma_tsum_aemeasurable hsigmaOne hWOneNonneg
      (fun j => (hWOneMeas j).aemeasurable) haOne haOneSummable hWOneTail
  have hTTwoTail : IsBigOWith mu (gammaSigma sigmaTwo) TTwo
      (gammaTriangleConst sigmaTwo * ∑' j, aTwo j) := by
    exact isBigOWith_gammaSigma_tsum_aemeasurable hsigmaTwo hWTwoNonneg
      (fun j => (hWTwoMeas j).aemeasurable) haTwo haTwoSummable hWTwoTail
  have hSOneTail : IsBigOWith mu (gammaSigma sigmaOne) SOne
      (gammaTriangleConst sigmaOne * ∑' j, aOne j) := by
    have hTOneBigO :=
      (isBigOWith_iff_isBigO_of_nonneg hTOneNonneg).1 hTOneTail
    have hSOneBigO :=
      (HCPolySupport.Book.Ch04.isBigO_congr_ae hTOneEq).mp hTOneBigO
    exact (isBigOWith_iff_isBigO_of_nonneg fun omega => abs_nonneg _).2
      hSOneBigO
  have hSTwoTail : IsBigOWith mu (gammaSigma sigmaTwo) STwo
      (gammaTriangleConst sigmaTwo * ∑' j, aTwo j) := by
    have hTTwoBigO :=
      (isBigOWith_iff_isBigO_of_nonneg hTTwoNonneg).1 hTTwoTail
    have hSTwoBigO :=
      (HCPolySupport.Book.Ch04.isBigO_congr_ae hTTwoEq).mp hTTwoBigO
    exact (isBigOWith_iff_isBigO_of_nonneg fun omega => abs_nonneg _).2
      hSTwoBigO
  refine ⟨SOne, STwo, hSOneMeas, hSTwoMeas, ?_, ?_, hSOneTail, hSTwoTail⟩
  · intro j
    filter_upwards [(hFOneMeas j).ae_eq_mk, hsumOne, hTOneEq] with omega hmk hsum hsumEq
    rw [hmk, ← hsumEq]
    have hterm := hsum.sum_le_tsum {j} fun i _ => hWOneNonneg i omega
    simpa only [WOne, Finset.sum_singleton] using hterm
  · intro j
    filter_upwards [(hFTwoMeas j).ae_eq_mk, hsumTwo, hTTwoEq] with omega hmk hsum hsumEq
    rw [hmk, ← hsumEq]
    have hterm := hsum.sum_le_tsum {j} fun i _ => hWTwoNonneg i omega
    simpa only [WTwo, Finset.sum_singleton] using hterm

end

end Algsuperdiff.Section3.Provider.Orlicz
