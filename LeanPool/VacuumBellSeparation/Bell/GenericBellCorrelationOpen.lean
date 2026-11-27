/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationDefs
public import LeanPool.VacuumBellSeparation.Bell.StateBound

/-!
Norm-openness for HC00's actual Bell-correlated vectors and joint normal states.
The proof extracts a strict CHSH witness from the bounded supremum, then keeps
that same witness on a neighborhood. No density, Schlieder, infinite-type or
normal-representation conclusion is used as a premise.
-/

@[expose] public section

universe u v
namespace VacuumBellSeparation.Bipartite.HC00

open scoped Topology InnerProductSpace ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The zero quadruple is always admissible, even for a nonlinear function f. -/
theorem jointBellValues_nonempty (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) :
    (jointBellValues A B f).Nonempty := by
  refine ⟨(1 / 2 : ℝ) * ‖f 0‖, 0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨A.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨A.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨B.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨B.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · simp

/-- Actual operator norm bounds, rather than a hypothesis on Bell correlation,
make the conditional real supremum legitimate. -/
theorem jointBellValues_bddAbove_of_bound (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ T, ‖f T‖ ≤ C * ‖T‖) : BddAbove (jointBellValues A B f) := by
  refine ⟨2 * C, ?_⟩
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  have hT : ‖X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)‖ ≤ 4 := by
    change ‖chshOp (X₀ : H →L[ℂ] H) (X₁ : H →L[ℂ] H)
      (Y₀ : H →L[ℂ] H) (Y₁ : H →L[ℂ] H)‖ ≤ 4
    exact norm_chshOp_le hX₀.2.2 hX₁.2.2 hY₀.2.2 hY₁.2.2
  have he := (hf (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁))).trans
    (mul_le_mul_of_nonneg_left hT hC)
  linarith

/-- A continuously varying evaluation with a bounded Bell-value set at each
point has an open strict-violation set. Only one fixed actual CHSH witness is
used in each neighborhood; no exchange of a supremum with a limit is assumed. -/
theorem isOpen_jointBellCorrelation_gt_one {X : Type v} [TopologicalSpace X]
    (A B : VonNeumannAlgebra H)
    (f : X → (jointAlgebra A B).toStarSubalgebra → ℂ)
    (hbound : ∀ x, BddAbove (jointBellValues A B (f x)))
    (hcont : ∀ T, Continuous (fun x => f x T)) :
    IsOpen {x | 1 < jointBellCorrelation A B (f x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change 1 < sSup (jointBellValues A B (f x)) at hx
  obtain ⟨r, hr, hlt⟩ :=
    exists_lt_of_lt_csSup (jointBellValues_nonempty A B (f x)) hx
  rcases hr with ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  let T : (jointAlgebra A B).toStarSubalgebra :=
    X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)
  have hc : Continuous (fun y : X => (1 / 2 : ℝ) * ‖f y T‖) :=
    continuous_const.mul (hcont T).norm
  have hopen : IsOpen {y : X | 1 < (1 / 2 : ℝ) * ‖f y T‖} :=
    isOpen_lt continuous_const hc
  have hn : {y : X | 1 < (1 / 2 : ℝ) * ‖f y T‖} ∈ 𝓝 x :=
    hopen.mem_nhds hlt
  apply Filter.mem_of_superset hn
  intro y hy
  change 1 < sSup (jointBellValues A B (f y))
  exact lt_csSup_of_lt (hbound y)
    ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩ hy

/-- HC00 p.3 openness in the norm topology of the full original unit sphere. -/
theorem isOpen_bellCorrelatedVectors (A B : VonNeumannAlgebra H) :
    IsOpen (bellCorrelatedVectors A B) := by
  change IsOpen {Ω : UnitSphere H |
    1 < jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) Ω.1)}
  apply isOpen_jointBellCorrelation_gt_one A B
    (fun Ω : UnitSphere H => vectorFunctional (jointAlgebra A B) Ω.1)
  · intro Ω
    apply jointBellValues_bddAbove_of_bound A B _ 1 zero_le_one
    intro T
    change ‖⟪Ω.1, (T : H →L[ℂ] H) Ω.1⟫_ℂ‖ ≤ 1 * ‖(T : H →L[ℂ] H)‖
    have h := (norm_inner_le_norm (𝕜 := ℂ) Ω.1 ((T : H →L[ℂ] H) Ω.1)).trans
      (mul_le_mul_of_nonneg_left ((T : H →L[ℂ] H).le_opNorm Ω.1)
        (norm_nonneg Ω.1))
    simpa only [Ω.2, one_mul, mul_one] using h
  · intro T
    change Continuous (fun Ω : UnitSphere H => ⟪Ω.1, (T : H →L[ℂ] H) Ω.1⟫_ℂ)
    exact continuous_subtype_val.inner
      ((T : H →L[ℂ] H).continuous.comp continuous_subtype_val)

/-- The same open set in all joint states, with their inherited dual norm. -/
theorem isOpen_bellCorrelatedStates (A B : VonNeumannAlgebra H) :
    IsOpen {φ : StateSpace (jointAlgebra A B) |
      1 < jointBellCorrelation A B φ.1} := by
  apply isOpen_jointBellCorrelation_gt_one A B
    (fun φ : StateSpace (jointAlgebra A B) => φ.1)
  · intro φ
    exact jointBellValues_bddAbove_of_bound A B φ.1 ‖φ.1‖ (norm_nonneg _)
      (fun T => φ.1.le_opNorm T)
  · intro T
    exact (continuous_subtype_val : Continuous
      (fun φ : StateSpace (jointAlgebra A B) => φ.1)).clm_apply continuous_const

/-- HC00 p.3 openness in ALL normal joint states, not just a vector-state image.
The topology is inherited from the normed continuous dual, and normality is
retained as a defining predicate on this full state subtype. -/
theorem isOpen_bellCorrelatedNormalStates (A B : VonNeumannAlgebra H) :
    IsOpen (bellCorrelatedNormalStates A B) := by
  change IsOpen {φ : NormalStateSpace (jointAlgebra A B) |
    1 < jointBellCorrelation A B φ.1}
  apply isOpen_jointBellCorrelation_gt_one A B
    (fun φ : NormalStateSpace (jointAlgebra A B) => φ.1)
  · intro φ
    exact jointBellValues_bddAbove_of_bound A B φ.1 ‖φ.1‖ (norm_nonneg _)
      (fun T => φ.1.le_opNorm T)
  · intro T
    exact (continuous_subtype_val : Continuous
      (fun φ : NormalStateSpace (jointAlgebra A B) => φ.1)).clm_apply continuous_const

end VacuumBellSeparation.Bipartite.HC00
