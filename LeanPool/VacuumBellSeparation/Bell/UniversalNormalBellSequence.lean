/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalUpperLimit
public import LeanPool.VacuumBellSeparation.Bell.SW88MaximalCorrelationEquivalence
public import Mathlib.Topology.Order.IsLUB

/-!
One sequence of literal normalized CHSH operators approaches the sharp
bound in every normal state of the original joint algebra. The sequence
is selected in one faithful normal state; domination gives the common
limit. This is the real-normal-expectation prerequisite for the common
sequence in SW87c Theorem 2.3.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 TopologicalSpace Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual original-algebra CHSH operators, with the source's factor one half. -/
def jointNormalizedBellOperators (A B : VonNeumannAlgebra H) :
    Set (jointAlgebra A B).toStarSubalgebra :=
  {T | ∃ X₀ X₁ Y₀ Y₁ : (jointAlgebra A B).toStarSubalgebra,
    (X₀ : H →L[ℂ] H) ∈ saContractions A ∧
    (X₁ : H →L[ℂ] H) ∈ saContractions A ∧
    (Y₀ : H →L[ℂ] H) ∈ saContractions B ∧
    (Y₁ : H →L[ℂ] H) ∈ saContractions B ∧
    T = (1 / 2 : ℂ) • (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁))}

theorem normalizedBellOperator_eval (M : VonNeumannAlgebra H)
    (φ : StrongDual ℂ M.toStarSubalgebra) (T : M.toStarSubalgebra) :
    (φ ((1 / 2 : ℂ) • T)).re = (1 / 2 : ℝ) * (φ T).re := by
  simp [map_smul, smul_eq_mul, Complex.mul_re]

theorem norm_le_two_of_mem_jointNormalizedBellOperators
    (A B : VonNeumannAlgebra H) {T : (jointAlgebra A B).toStarSubalgebra}
    (hT : T ∈ jointNormalizedBellOperators A B) : ‖T‖ ≤ 2 := by
  obtain ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩ := hT
  have hb : ‖X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)‖ ≤ 4 := by
    change ‖chshOp (X₀ : H →L[ℂ] H) (X₁ : H →L[ℂ] H)
      (Y₀ : H →L[ℂ] H) (Y₁ : H →L[ℂ] H)‖ ≤ 4
    exact norm_chshOp_le hX₀.2.2 hX₁.2.2 hY₀.2.2 hY₁.2.2
  rw [norm_smul]
  norm_num
  change ‖(X₀ : H →L[ℂ] H) * ((Y₀ : H →L[ℂ] H) + Y₁) +
    (X₁ : H →L[ℂ] H) * ((Y₀ : H →L[ℂ] H) - Y₁)‖ ≤ 4 at hb
  linarith

theorem eval_mem_jointSignedBellValues_of_normalized
    (A B : VonNeumannAlgebra H)
    (φ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra)
    {T : (jointAlgebra A B).toStarSubalgebra}
    (hT : T ∈ jointNormalizedBellOperators A B) :
    (φ T).re ∈ jointSignedBellValues A B φ := by
  obtain ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩ := hT
  exact ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁,
    normalizedBellOperator_eval _ φ _⟩

theorem exists_normalizedBellOperator_of_signed_value
    (A B : VonNeumannAlgebra H)
    (φ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra)
    {r : ℝ} (hr : r ∈ jointSignedBellValues A B φ) :
    ∃ T ∈ jointNormalizedBellOperators A B, (φ T).re = r := by
  obtain ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩ := hr
  refine ⟨(1 / 2 : ℂ) • (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)),
    ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩, ?_⟩
  exact normalizedBellOperator_eval _ φ _

theorem normalizedBellOperator_state_upper (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (φ : StateSpace (jointAlgebra A B))
    {T : (jointAlgebra A B).toStarSubalgebra}
    (hT : T ∈ jointNormalizedBellOperators A B) : (φ.1 T).re ≤ Real.sqrt 2 := by
  have hv := le_csSup (jointSignedBellValues_bddAbove A B φ.1)
    (eval_mem_jointSignedBellValues_of_normalized A B φ.1 hT)
  exact hv.trans ((jointSignedBellCorrelation_le A B φ.1).trans
    (jointBellCorrelation_bounds A B hcomm φ).2)

theorem exists_universal_normal_Bell_sequence_of_faithful
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (ω : NormalStateSpace (jointAlgebra A B))
    (hf : ∀ a : (jointAlgebra A B).toStarSubalgebra,
      ω.1 (star a * a) = 0 → a = 0)
    (hmax : jointSignedBellCorrelation A B ω.1 = Real.sqrt 2) :
    ∃ T : ℕ → (jointAlgebra A B).toStarSubalgebra,
      (∀ n, T n ∈ jointNormalizedBellOperators A B) ∧
      ∀ φ : NormalStateSpace (jointAlgebra A B),
        Tendsto (fun n => (φ.1 (T n)).re) atTop (𝓝 (Real.sqrt 2)) := by
  obtain ⟨r, _, hr, hmem⟩ := exists_seq_tendsto_sSup
    (jointSignedBellValues_nonempty A B ω.1) (jointSignedBellValues_bddAbove A B ω.1)
  change Tendsto r atTop (𝓝 (jointSignedBellCorrelation A B ω.1)) at hr
  rw [hmax] at hr
  choose T hT he using fun n => exists_normalizedBellOperator_of_signed_value A B ω.1 (hmem n)
  refine ⟨T, hT, ?_⟩
  have hω : Tendsto (fun n => (ω.1 (T n)).re) atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [he] using hr
  exact normalState_evaluation_tendsto_upper_of_faithful (jointAlgebra A B) ω hf
    T (Real.sqrt 2) 2 (fun n => norm_le_two_of_mem_jointNormalizedBellOperators A B (hT n))
    (fun φ n => normalizedBellOperator_state_upper A B hcomm φ (hT n)) hω

/-- Every normal state has maximal supremum iff one sequence works for them
all. Separability is used to construct a faithful normal reference, not to
replace the original state space by a countable chosen family. -/
theorem all_normal_maximal_iff_universal_normal_Bell_sequence
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B) :
    (∀ φ : NormalStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B φ.1 = Real.sqrt 2) ↔
    ∃ T : ℕ → (jointAlgebra A B).toStarSubalgebra,
      (∀ n, T n ∈ jointNormalizedBellOperators A B) ∧
      ∀ φ : NormalStateSpace (jointAlgebra A B),
        Tendsto (fun n => (φ.1 (T n)).re) atTop (𝓝 (Real.sqrt 2)) := by
  constructor
  · intro h
    obtain ⟨ω, hf⟩ := exists_faithful_mem_normalStateSpace (jointAlgebra A B)
    exact exists_universal_normal_Bell_sequence_of_faithful A B hcomm ω hf (h ω)
  · rintro ⟨T, hT, hlim⟩ φ
    apply le_antisymm
    · exact (jointSignedBellCorrelation_le A B φ.1).trans
        (jointBellCorrelation_bounds A B hcomm ⟨φ.1, φ.2.1⟩).2
    · apply le_of_tendsto (hlim φ)
      exact Eventually.of_forall fun n => le_csSup (jointSignedBellValues_bddAbove A B φ.1)
        (eval_mem_jointSignedBellValues_of_normalized A B φ.1 (hT n))

end VacuumBellSeparation.Bipartite
