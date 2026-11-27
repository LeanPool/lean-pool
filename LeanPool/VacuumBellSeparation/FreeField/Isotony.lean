/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs
public import LeanPool.VacuumBellSeparation.Bell.EventConstants

/-!
# Isotony of the local algebras and monotonicity of the Bell correlation

Two ingredients of the proof of Corollary 1.2 of the manuscript (Step 3, isotony: "If one region
is contained in another, its local algebra is contained in that of the other. The supremum (2.4)
can only increase when both algebras are enlarged"):

* `localAlgebra_mono`: `O ⊆ O'` implies `𝔄(O) ⊆ 𝔄(O')`;
* `bellCorrelation_mono`: the Bell correlation is monotone in both algebras;
* `freeFieldBell`-level consequence `bellCorrelation_localAlgebra_le`.
-/

@[expose] public section

open scoped Pointwise

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_commutantOf_iff {S : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ commutantOf S ↔ x ∈ (S ∪ star S).centralizer := by
  rw [← SetLike.mem_coe]
  exact Set.ext_iff.mp (StarSubalgebra.coe_centralizer (R := ℂ) S) x

/-- The commutant of a larger set is smaller. -/
theorem commutantOf_antitone {S T : Set (H →L[ℂ] H)} (h : S ⊆ T) :
    commutantOf T ≤ commutantOf S := by
  intro x hx
  rw [mem_commutantOf_iff] at hx ⊢
  exact Set.centralizer_subset (Set.union_subset_union h (Set.star_subset_star.mpr h)) hx

/-- The generated von Neumann algebra is monotone in the generating set. -/
theorem generatedVNA_mono {S T : Set (H →L[ℂ] H)} (h : S ⊆ T) :
    generatedVNA S ≤ generatedVNA T := by
  intro x hx
  rw [generatedVNA, VonNeumannAlgebra.mem_commutant_iff] at hx ⊢
  exact fun g hg => hx g (commutantOf_antitone h hg)

/-- Isotony: `O ⊆ O'` implies `𝔄(O) ⊆ 𝔄(O')`. -/
theorem localAlgebra_mono {m : ℝ} (V : FreeFieldVacuum m H) {O O' : Set Spacetime}
    (h : O ⊆ O') : localAlgebra V O ≤ localAlgebra V O' := by
  apply generatedVNA_mono
  rintro T ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans h, rfl⟩

/-- Self-adjoint contractions of a smaller algebra are self-adjoint contractions of a larger
one. -/
theorem saContractions_mono {𝔄 𝔄' : VonNeumannAlgebra H} (h : 𝔄 ≤ 𝔄') :
    saContractions 𝔄 ⊆ saContractions 𝔄' :=
  fun _ hA => ⟨h hA.1, hA.2⟩

/-- The CHSH values only grow with the algebras. -/
theorem chshValues_mono (ω : State H) {𝔄 𝔄' 𝔅 𝔅' : VonNeumannAlgebra H} (hA : 𝔄 ≤ 𝔄')
    (hB : 𝔅 ≤ 𝔅') : chshValues ω 𝔄 𝔅 ⊆ chshValues ω 𝔄' 𝔅' := by
  rintro x ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
  exact ⟨A₀, saContractions_mono hA hA₀, A₁, saContractions_mono hA hA₁,
    B₀, saContractions_mono hB hB₀, B₁, saContractions_mono hB hB₁, rfl⟩

/-- The Bell correlation is monotone in both algebras. -/
theorem bellCorrelation_mono (ω : State H) {𝔄 𝔄' 𝔅 𝔅' : VonNeumannAlgebra H} (hA : 𝔄 ≤ 𝔄')
    (hB : 𝔅 ≤ 𝔅') : bellCorrelation ω 𝔄 𝔅 ≤ bellCorrelation ω 𝔄' 𝔅' :=
  csSup_le_csSup (bddAbove_chshValues ω 𝔄' 𝔅') ⟨1, one_mem_chshValues ω 𝔄 𝔅⟩
    (chshValues_mono ω hA hB)

/-- Isotony for the vacuum Bell correlation of a free-field vacuum system: enlarging both
regions can only increase it. -/
theorem bellCorrelation_localAlgebra_le {m : ℝ} (V : FreeFieldVacuum m H)
    {O₁ O₂ O₁' O₂' : Set Spacetime} (h₁ : O₁ ⊆ O₁') (h₂ : O₂ ⊆ O₂') :
    bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁) (localAlgebra V O₂)
      ≤ bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁')
          (localAlgebra V O₂') :=
  bellCorrelation_mono _ (localAlgebra_mono V h₁) (localAlgebra_mono V h₂)

end VacuumBellSeparation
