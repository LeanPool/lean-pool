/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.LocalStateDefs
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import LeanPool.VacuumBellSeparation.Bell.StateRestriction
public import LeanPool.VacuumBellSeparation.Bell.Theorem31

/-!
# The probability criterion for a state on the joint local algebra

The Bell correlation and event constants here evaluate the given positive unital
functional directly on a closed star subalgebra containing both local algebras.
Theorem `probability_criterion_on_subalgebra` proves Theorem 3.1 in this intrinsic
state domain. Its proof constructs an ambient state extension and proves equality
of the quantities; existence of such an extension is not an extra hypothesis.
-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) (f : S →ₚ[ℂ] ℂ)
    (𝔄 𝔅 : VonNeumannAlgebra H)
    (h𝔄 : (𝔄 : Set (H →L[ℂ] H)) ⊆ S) (h𝔅 : (𝔅 : Set (H →L[ℂ] H)) ⊆ S)
    (ω : State H) (hω : ∀ x : S, ω x = f x)

include hω in
theorem localBellCorrelation_eq_extension :
    localBellCorrelation S f 𝔄 𝔅 h𝔄 h𝔅 = bellCorrelation ω 𝔄 𝔅 := by
  unfold localBellCorrelation bellCorrelation
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz⟩
    refine ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz.trans ?_⟩
    rw [hω ⟨chshOp A₀ A₁ B₀ B₁, chshOp_mem_starSubalgebra S
      (h𝔄 hA₀.1) (h𝔄 hA₁.1) (h𝔅 hB₀.1) (h𝔅 hB₁.1)⟩]
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz⟩
    refine ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz.trans ?_⟩
    rw [hω ⟨chshOp A₀ A₁ B₀ B₁, chshOp_mem_starSubalgebra S
      (h𝔄 hA₀.1) (h𝔄 hA₁.1) (h𝔅 hB₀.1) (h𝔅 hB₁.1)⟩]

include hω in
theorem localEventConstPlus_eq_extension (r : ℝ) :
    localEventConstPlus S f 𝔄 𝔅 h𝔄 h𝔅 r = eventConstPlus ω 𝔄 𝔅 r := by
  unfold localEventConstPlus eventConstPlus
  apply iSup_congr
  intro E
  apply iSup_congr
  intro hE
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hω ⟨E, h𝔄 hE.1⟩, hω ⟨P, h𝔅 hP.1⟩,
    hω ⟨E * P, S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1)⟩]

include hω in
theorem localEventConstMinus_eq_extension (r : ℝ) :
    localEventConstMinus S f 𝔄 𝔅 h𝔄 h𝔅 r = eventConstMinus ω 𝔄 𝔅 r := by
  unfold localEventConstMinus eventConstMinus
  apply iSup_congr
  intro E
  apply iSup_congr
  intro hE
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hω ⟨E, h𝔄 hE.1⟩, hω ⟨P, h𝔅 hP.1⟩,
    hω ⟨E * P, S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1)⟩]

/-- **Theorem 3.1**, for a positive unital state on the joint local algebra,
with no ambient-state-extension hypothesis. -/
theorem probability_criterion_on_subalgebra [IsClosed (S : Set (H →L[ℂ] H))]
    (hf : f 1 = 1) (hcomm : Commuting 𝔄 𝔅)
    {rp rm q : ℝ} (hrp : 2 < rp) (hrm : 1 < rm) (hrm2 : rm < 2)
    (hη : 0 < expEta rp rm)
    (hKp : localEventConstPlus S f 𝔄 𝔅 h𝔄 h𝔅 rp ≠ ⊤)
    (hKm : localEventConstMinus S f 𝔄 𝔅 h𝔄 h𝔅 rm ≠ ⊤)
    (hcl : ∀ (A : H →L[ℂ] H) (hA : A ∈ saContractions 𝔄),
      ∀ (B : H →L[ℂ] H) (hB : B ∈ saContractions 𝔅),
        ‖f ⟨A * B, S.mul_mem (h𝔄 hA.1) (h𝔅 hB.1)⟩ -
          f ⟨A, h𝔄 hA.1⟩ * f ⟨B, h𝔅 hB.1⟩‖ ≤ q)
    (hcut : q ^ expEta rp rm * (localEventConstPlus S f 𝔄 𝔅 h𝔄 h𝔅 rp).toReal ^ nuPlus rp rm
        * (localEventConstMinus S f 𝔄 𝔅 h𝔄 h𝔅 rm).toReal ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp)))) :
    localBellCorrelation S f 𝔄 𝔅 h𝔄 h𝔅 = 1 := by
  obtain ⟨ω, hω⟩ := exists_state_extension S f hf
  have hp := localEventConstPlus_eq_extension S f 𝔄 𝔅 h𝔄 h𝔅 ω hω rp
  have hm := localEventConstMinus_eq_extension S f 𝔄 𝔅 h𝔄 h𝔅 ω hω rm
  rw [localBellCorrelation_eq_extension S f 𝔄 𝔅 h𝔄 h𝔅 ω hω]
  apply probability_criterion ω hcomm hrp hrm hrm2 hη
    (by simpa only [← hp] using hKp) (by simpa only [← hm] using hKm)
  · intro A hA B hB
    rw [hω ⟨A * B, S.mul_mem (h𝔄 hA.1) (h𝔅 hB.1)⟩,
      hω ⟨A, h𝔄 hA.1⟩, hω ⟨B, h𝔅 hB.1⟩]
    exact hcl A hA B hB
  · simpa only [← hp, ← hm] using hcut

end VacuumBellSeparation
