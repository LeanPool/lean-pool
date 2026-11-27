/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.EventConstantDefs

/-!
# Bell quantities depend only on the jointly generated algebra

Two ambient state extensions agreeing on a star subalgebra containing both local
algebras give identical Bell correlations and event constants. No normality or
commutativity assumption is required for these invariance identities.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem chshOp_mem_starSubalgebra (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {A₀ A₁ B₀ B₁ : H →L[ℂ] H} (hA₀ : A₀ ∈ S) (hA₁ : A₁ ∈ S)
    (hB₀ : B₀ ∈ S) (hB₁ : B₁ ∈ S) : chshOp A₀ A₁ B₀ B₁ ∈ S :=
  S.add_mem (S.mul_mem hA₀ (S.add_mem hB₀ hB₁))
    (S.mul_mem hA₁ (S.sub_mem hB₀ hB₁))

variable (ω₀ ω₁ : State H) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hω : ∀ T ∈ S, ω₀ T = ω₁ T) (𝔄 𝔅 : VonNeumannAlgebra H)
    (h𝔄 : (𝔄 : Set (H →L[ℂ] H)) ⊆ S) (h𝔅 : (𝔅 : Set (H →L[ℂ] H)) ⊆ S)

include hω h𝔄 h𝔅

theorem chshValues_eq_of_agree_on : chshValues ω₀ 𝔄 𝔅 = chshValues ω₁ 𝔄 𝔅 := by
  ext z
  constructor
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz⟩
    refine ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz.trans ?_⟩
    rw [hω _ (chshOp_mem_starSubalgebra S (h𝔄 hA₀.1) (h𝔄 hA₁.1)
      (h𝔅 hB₀.1) (h𝔅 hB₁.1))]
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz⟩
    refine ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, hz.trans ?_⟩
    rw [hω _ (chshOp_mem_starSubalgebra S (h𝔄 hA₀.1) (h𝔄 hA₁.1)
      (h𝔅 hB₀.1) (h𝔅 hB₁.1))]

theorem bellCorrelation_eq_of_agree_on :
    bellCorrelation ω₀ 𝔄 𝔅 = bellCorrelation ω₁ 𝔄 𝔅 :=
  congrArg sSup (chshValues_eq_of_agree_on ω₀ ω₁ S hω 𝔄 𝔅 h𝔄 h𝔅)

theorem eventConstPlus_eq_of_agree_on (r : ℝ) :
    eventConstPlus ω₀ 𝔄 𝔅 r = eventConstPlus ω₁ 𝔄 𝔅 r := by
  unfold eventConstPlus
  apply iSup_congr
  intro E
  apply iSup_congr
  intro hE
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hω E (h𝔄 hE.1), hω P (h𝔅 hP.1),
    hω (E * P) (S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1))]

theorem eventConstMinus_eq_of_agree_on (r : ℝ) :
    eventConstMinus ω₀ 𝔄 𝔅 r = eventConstMinus ω₁ 𝔄 𝔅 r := by
  unfold eventConstMinus
  apply iSup_congr
  intro E
  apply iSup_congr
  intro hE
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  rw [hω E (h𝔄 hE.1), hω P (h𝔅 hP.1),
    hω (E * P) (S.mul_mem (h𝔄 hE.1) (h𝔅 hP.1))]

end VacuumBellSeparation
