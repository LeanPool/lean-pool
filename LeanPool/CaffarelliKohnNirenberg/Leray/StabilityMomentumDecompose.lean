/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumSupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalBoxEnclosure

/-!
# Stability Momentum Decompose

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The four nonzero pieces of the zero-force momentum pairing may be
integrated separately on a local box. -/
theorem stability_momentum_integral_decompose_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p 0)
    (hbox : localBox Ω I Ω' J)
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    (∫ z in spaceTimeSet Ω' J,
      (-(∑ i, u z i * timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
        - p z * ∑ i, spatialPartial (fun w => φ w i) i z
        - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i) =
      -(∫ z in spaceTimeSet Ω' J,
        ∑ i, u z i * timePartial (fun w => φ w i) z)
      - (∫ z in spaceTimeSet Ω' J,
        ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z)
      + (∫ z in spaceTimeSet Ω' J,
        ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z)
      - (∫ z in spaceTimeSet Ω' J,
        p z * ∑ i, spatialPartial (fun w => φ w i) i z) := by
  obtain ⟨K, hKcompact, hboxsub, hKsub⟩ :=
    stability_localBox_compact_enclosure hbox
  have hT : IntegrableOn
      (fun z => ∑ i, u z i * timePartial (fun w => φ w i) z)
      (spaceTimeSet Ω' J) volume :=
    (momentum_timeTerm_integrableOn_of_data hdata hKcompact hKsub hφ).mono_set
      hboxsub
  have hN : IntegrableOn
      (fun z => ∑ i, ∑ j,
        u z i * u z j * spatialPartial (fun w => φ w i) j z)
      (spaceTimeSet Ω' J) volume :=
    (momentum_nonlinearTerm_integrableOn_of_data hdata hKcompact hKsub hφ).mono_set
      hboxsub
  have hV : IntegrableOn
      (fun z => ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => φ w i) j z)
      (spaceTimeSet Ω' J) volume :=
    (momentum_viscousTerm_integrableOn_of_data hdata hKcompact hKsub hφ).mono_set
      hboxsub
  have hP : IntegrableOn
      (fun z => p z * ∑ i, spatialPartial (fun w => φ w i) i z)
      (spaceTimeSet Ω' J) volume :=
    (momentum_pressureTerm_integrableOn_of_data hdata hKcompact hKsub hφ).mono_set
      hboxsub
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
  let T : ParabolicPoint → ℝ := fun z =>
    ∑ i, u z i * timePartial (fun w => φ w i) z
  let N : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
  let V : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
  let P : ParabolicPoint → ℝ := fun z =>
    p z * ∑ i, spatialPartial (fun w => φ w i) i z
  change IntegrableOn T (spaceTimeSet Ω' J) volume at hT
  change IntegrableOn N (spaceTimeSet Ω' J) volume at hN
  change IntegrableOn V (spaceTimeSet Ω' J) volume at hV
  change IntegrableOn P (spaceTimeSet Ω' J) volume at hP
  change (∫ z in spaceTimeSet Ω' J, ((-T - N + V - P) z)) =
    -(∫ z in spaceTimeSet Ω' J, T z) -
      (∫ z in spaceTimeSet Ω' J, N z) +
      (∫ z in spaceTimeSet Ω' J, V z) -
      (∫ z in spaceTimeSet Ω' J, P z)
  rw [integral_sub' (((hT.neg).sub hN).add hV) hP,
    integral_add' ((hT.neg).sub hN) hV,
    integral_sub' hT.neg hN, integral_neg']

end CKN
