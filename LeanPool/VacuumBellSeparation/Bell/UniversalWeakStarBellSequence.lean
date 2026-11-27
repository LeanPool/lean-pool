/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalStateWeakConvergence
public import LeanPool.VacuumBellSeparation.Bell.UniversalNormalBellSequence
public import LeanPool.VacuumBellSeparation.Bell.CoefficientNormalStateSpace

/-!
The common normalized CHSH sequence converges to sqrt(2) times the identity
in the weak topology paired with the actual coefficient Banach predual.
The canonical homeomorphism exposes the same convergence in WeakDual.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 TopologicalSpace Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isSelfAdjoint_of_mem_jointNormalizedBellOperators
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    {T : (jointAlgebra A B).toStarSubalgebra}
    (hT : T ∈ jointNormalizedBellOperators A B) : IsSelfAdjoint T := by
  obtain ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩ := hT
  have hs : IsSelfAdjoint (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)) := by
    apply Subtype.ext
    exact (chshOp_isSelfAdjoint hcomm hX₀ hX₁ hY₀ hY₁).star_eq
  change star ((1 / 2 : ℂ) • _) = _
  rw [star_smul, hs.star_eq]
  norm_num

theorem state_scalar_one_real (M : VonNeumannAlgebra H)
    (φ : StateSpace M) (c : ℝ) : (φ.1 ((c : ℂ) • 1)).re = c := by
  obtain ⟨ψ, hψ, he⟩ := φ.2
  have h1 : φ.1 1 = 1 := (he 1).symm.trans hψ
  simp [h1]

theorem coefficientWeak_Bell_sequence_limit
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (T : ℕ → (jointAlgebra A B).toStarSubalgebra)
    (hT : ∀ n, T n ∈ jointNormalizedBellOperators A B)
    (hlim : ∀ φ : NormalStateSpace (jointAlgebra A B),
      Tendsto (fun n => (φ.1 (T n)).re) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (β := CoefficientWeakAlgebra (jointAlgebra A B)) (fun n => T n) atTop
      (nhds (X := CoefficientWeakAlgebra (jointAlgebra A B))
        (((Real.sqrt 2 : ℝ) : ℂ) • (1 : (jointAlgebra A B).toStarSubalgebra))) := by
  let M := jointAlgebra A B
  let L : M.toStarSubalgebra := ((Real.sqrt 2 : ℝ) : ℂ) • 1
  have hL : IsSelfAdjoint L := by
    change star (((Real.sqrt 2 : ℝ) : ℂ) • (1 : M.toStarSubalgebra)) = _
    simp only [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
    rfl
  have hroot : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hbL : ‖L‖ ≤ 2 := by
    have hOne : ‖(1 : M.toStarSubalgebra)‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    calc
      ‖L‖ = Real.sqrt 2 * ‖(1 : M.toStarSubalgebra)‖ := by
        dsimp only [L]
        rw [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
      _ ≤ Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left hOne (Real.sqrt_nonneg 2)
      _ ≤ 2 := by simpa only [mul_one] using hroot
  apply selfAdjoint_coefficientWeak_limit_of_normalState_real_limits M T L
    (fun n => isSelfAdjoint_of_mem_jointNormalizedBellOperators A B hcomm (hT n)) hL
    2 (fun n => norm_le_two_of_mem_jointNormalizedBellOperators A B (hT n)) hbL
  intro φ
  simpa only [L, state_scalar_one_real M ⟨φ.1, φ.2.1⟩] using hlim φ

theorem all_normal_maximal_iff_coefficientWeak_Bell_sequence
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B) :
    (∀ φ : NormalStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B φ.1 = Real.sqrt 2) ↔
    ∃ T : ℕ → (jointAlgebra A B).toStarSubalgebra,
      (∀ n, T n ∈ jointNormalizedBellOperators A B) ∧
      Tendsto (β := CoefficientWeakAlgebra (jointAlgebra A B)) (fun n => T n) atTop
        (nhds (X := CoefficientWeakAlgebra (jointAlgebra A B))
        (((Real.sqrt 2 : ℝ) : ℂ) • (1 : (jointAlgebra A B).toStarSubalgebra))) := by
  rw [all_normal_maximal_iff_universal_normal_Bell_sequence A B hcomm]
  constructor
  · rintro ⟨T, hT, hlim⟩
    exact ⟨T, hT, coefficientWeak_Bell_sequence_limit A B hcomm T hT hlim⟩
  · rintro ⟨T, hT, hlim⟩
    refine ⟨T, hT, ?_⟩
    intro φ
    have hc := continuous_coefficientWeak_of_mem (jointAlgebra A B) φ.1
      (normalState_mem_coefficientPredual _ φ)
    have he : Tendsto (fun n => (φ.1 (T n)).re) atTop
        (𝓝 (φ.1 (((Real.sqrt 2 : ℝ) : ℂ) •
          (1 : (jointAlgebra A B).toStarSubalgebra))).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp
        (hc.continuousAt.tendsto.comp hlim)
    simpa only [state_scalar_one_real _ ⟨φ.1, φ.2.1⟩] using he

/-- Actual WeakDual convergence through the proved canonical dual identification. -/
theorem exists_weakStar_Bell_sequence_of_all_normal_maximal
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (hmax : ∀ φ : NormalStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B φ.1 = Real.sqrt 2) :
    ∃ T : ℕ → (jointAlgebra A B).toStarSubalgebra,
      (∀ n, T n ∈ jointNormalizedBellOperators A B) ∧
      Tendsto (fun n => coefficientWeakDualHomeomorph (jointAlgebra A B) (T n)) atTop
        (𝓝 (coefficientWeakDualHomeomorph (jointAlgebra A B)
          (((Real.sqrt 2 : ℝ) : ℂ) •
            (1 : (jointAlgebra A B).toStarSubalgebra)))) := by
  obtain ⟨T, hT, hlim⟩ :=
    (all_normal_maximal_iff_coefficientWeak_Bell_sequence A B hcomm).mp hmax
  exact ⟨T, hT, (coefficientWeakDualHomeomorph (jointAlgebra A
    B)).continuous.continuousAt.tendsto.comp hlim⟩

end VacuumBellSeparation.Bipartite
