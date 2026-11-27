/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.StateRestriction

/-!
# Statement seed extracted from Bell/LocalState

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Local bell correlation. -/
noncomputable def localBellCorrelation (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (f : S →ₚ[ℂ] ℂ) (𝔄 𝔅 : VonNeumannAlgebra H)
    (h𝔄 : (𝔄 : Set (H →L[ℂ] H)) ⊆ S) (h𝔅 : (𝔅 : Set (H →L[ℂ] H)) ⊆ S) : ℝ :=
  sSup {x : ℝ | ∃ (A₀ : H →L[ℂ] H) (hA₀ : A₀ ∈ saContractions 𝔄),
    ∃ (A₁ : H →L[ℂ] H) (hA₁ : A₁ ∈ saContractions 𝔄),
    ∃ (B₀ : H →L[ℂ] H) (hB₀ : B₀ ∈ saContractions 𝔅),
    ∃ (B₁ : H →L[ℂ] H) (hB₁ : B₁ ∈ saContractions 𝔅),
    x = (1 / 2 : ℝ) * ‖f ⟨chshOp A₀ A₁ B₀ B₁,
      chshOp_mem_starSubalgebra S (h𝔄 hA₀.1) (h𝔄 hA₁.1) (h𝔅 hB₀.1) (h𝔅 hB₁.1)⟩‖}

/-- Forward likelihood-ratio constant for pairs of local projections. -/
noncomputable def localEventConstPlus (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (f : S →ₚ[ℂ] ℂ) (𝔄 𝔅 : VonNeumannAlgebra H)
    (h𝔄 : (𝔄 : Set (H →L[ℂ] H)) ⊆ S) (h𝔅 : (𝔅 : Set (H →L[ℂ] H)) ⊆ S)
    (r : ℝ) : ℝ≥0∞ :=
  ⨆ (E : H →L[ℂ] H) (hE : E ∈ projections 𝔄),
    ⨆ (P : H →L[ℂ] H) (hP : P ∈ projections 𝔅),
      ⨆ (_ : 0 < (f ⟨E, h𝔄 hE.1⟩).re * (f ⟨P, h𝔅 hP.1⟩).re),
        ENNReal.ofReal ((f ⟨E * P, S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1)⟩).re ^ r /
          ((f ⟨E, h𝔄 hE.1⟩).re * (f ⟨P, h𝔅 hP.1⟩).re) ^ (r - 1))

/-- Reverse likelihood-ratio constant for pairs of local projections. -/
noncomputable def localEventConstMinus (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (f : S →ₚ[ℂ] ℂ) (𝔄 𝔅 : VonNeumannAlgebra H)
    (h𝔄 : (𝔄 : Set (H →L[ℂ] H)) ⊆ S) (h𝔅 : (𝔅 : Set (H →L[ℂ] H)) ⊆ S)
    (r : ℝ) : ℝ≥0∞ :=
  ⨆ (E : H →L[ℂ] H) (hE : E ∈ projections 𝔄),
    ⨆ (P : H →L[ℂ] H) (hP : P ∈ projections 𝔅),
      ⨆ (_ : 0 < (f ⟨E, h𝔄 hE.1⟩).re * (f ⟨P, h𝔅 hP.1⟩).re),
        ENNReal.ofReal (((f ⟨E, h𝔄 hE.1⟩).re * (f ⟨P, h𝔅 hP.1⟩).re) ^ r) /
          ENNReal.ofReal ((f ⟨E * P, S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1)⟩).re ^ (r - 1))


end VacuumBellSeparation
