/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationContinuity

/-! Convexity of the literal joint-algebra Bell quantity. All terms are
estimated at the same actual CHSH observable before taking the supremum.
The boundedness hypotheses are explicit even for arbitrary nonlinear functions.
These lemmas do not supply faithful-state domination or normal-state density. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem jointBellCorrelation_nonneg_combination_le (A B : VonNeumannAlgebra H)
    (f g : (jointAlgebra A B).toStarSubalgebra → ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : BddAbove (jointBellValues A B f))
    (hg : BddAbove (jointBellValues A B g)) :
    jointBellCorrelation A B (a • f + b • g) ≤
      a * jointBellCorrelation A B f + b * jointBellCorrelation A B g := by
  apply csSup_le (jointBellValues_nonempty A B _)
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  let T : (jointAlgebra A B).toStarSubalgebra :=
    X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)
  have hfT : (1 / 2 : ℝ) * ‖f T‖ ≤ jointBellCorrelation A B f :=
    le_csSup hf ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  have hgT : (1 / 2 : ℝ) * ‖g T‖ ≤ jointBellCorrelation A B g :=
    le_csSup hg ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  have hn : ‖a • f T + b • g T‖ ≤ a * ‖f T‖ + b * ‖g T‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using
      norm_add_le (a • f T) (b • g T)
  change (1 / 2 : ℝ) * ‖a • f T + b • g T‖ ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * (a * ‖f T‖ + b * ‖g T‖) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = a * ((1 / 2 : ℝ) * ‖f T‖) + b * ((1 / 2 : ℝ) * ‖g T‖) := by ring
    _ ≤ a * jointBellCorrelation A B f + b * jointBellCorrelation A B g :=
      add_le_add (mul_le_mul_of_nonneg_left hfT ha) (mul_le_mul_of_nonneg_left hgT hb)

/-- Continuous dual functionals supply the required bounded value sets from
their actual operator norms; the same real scalar combination is retained. -/
theorem jointBellCorrelation_dual_nonneg_combination_le (A B : VonNeumannAlgebra H)
    (φ ψ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    jointBellCorrelation A B (a • φ + b • ψ) ≤
      a * jointBellCorrelation A B φ + b * jointBellCorrelation A B ψ := by
  exact jointBellCorrelation_nonneg_combination_le A B φ ψ a b ha hb
    (jointBellValues_bddAbove_of_bound A B φ ‖φ‖ (norm_nonneg _) (fun T => φ.le_opNorm T))
    (jointBellValues_bddAbove_of_bound A B ψ ‖ψ‖ (norm_nonneg _) (fun T => ψ.le_opNorm T))

/-- A nontrivial convex decomposition of a maximizer has maximal components
when both components satisfy the same upper bound. Endpoints t=0,1 are excluded. -/
theorem jointBellCorrelation_maximal_components (A B : VonNeumannAlgebra H)
    (f g : (jointAlgebra A B).toStarSubalgebra → ℂ)
    {t C : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hf : BddAbove (jointBellValues A B f))
    (hg : BddAbove (jointBellValues A B g))
    (hfC : jointBellCorrelation A B f ≤ C)
    (hgC : jointBellCorrelation A B g ≤ C)
    (hm : jointBellCorrelation A B (t • f + (1 - t) • g) = C) :
    jointBellCorrelation A B f = C ∧ jointBellCorrelation A B g = C := by
  have hmix := jointBellCorrelation_nonneg_combination_le A B f g t (1 - t)
    ht.le (sub_nonneg.mpr ht1.le) hf hg
  rw [hm] at hmix
  have hsum : t * C + (1 - t) * C = C := by ring
  constructor
  · apply le_antisymm hfC
    by_contra h
    have hlt : jointBellCorrelation A B f < C := lt_of_not_ge h
    have hs := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt ht)
      (mul_le_mul_of_nonneg_left hgC (sub_nonneg.mpr ht1.le))
    rw [hsum] at hs
    exact (not_lt_of_ge hmix) hs
  · apply le_antisymm hgC
    by_contra h
    have hlt : jointBellCorrelation A B g < C := lt_of_not_ge h
    have hs := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hfC ht.le)
      (mul_lt_mul_of_pos_left hlt (sub_pos.mpr ht1))
    rw [hsum] at hs
    exact (not_lt_of_ge hmix) hs

/-- Sharp intrinsic joint-state specialization, without a normality,
faithfulness or representation hypothesis hidden in either component. -/
theorem jointBellCorrelation_state_maximal_components (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (φ ψ : StateSpace (jointAlgebra A B))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hm : jointBellCorrelation A B
      (fun T => t • φ.1 T + (1 - t) • ψ.1 T) = Real.sqrt 2) :
    jointBellCorrelation A B φ.1 = Real.sqrt 2 ∧
      jointBellCorrelation A B ψ.1 = Real.sqrt 2 := by
  exact jointBellCorrelation_maximal_components A B φ.1 ψ.1 ht ht1
    (jointBellValues_bddAbove_of_bound A B φ.1 ‖φ.1‖ (norm_nonneg _) (fun T => φ.1.le_opNorm T))
    (jointBellValues_bddAbove_of_bound A B ψ.1 ‖ψ.1‖ (norm_nonneg _) (fun T => ψ.1.le_opNorm T))
    (jointBellCorrelation_bounds A B hcomm φ).2
    (jointBellCorrelation_bounds A B hcomm ψ).2 hm

end VacuumBellSeparation.Bipartite.HC00
