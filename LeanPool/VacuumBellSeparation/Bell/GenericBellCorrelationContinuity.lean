/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationCompatibility
public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationOpen

/-!
Norm continuity of HC00's intrinsic Bell quantity. The argument compares the
same actual CHSH observable in two functionals. A crude operator bound four
suffices for continuity; the sharp bound is transferred separately above.
-/

@[expose] public section

universe u
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A pointwise operator-norm bound on the evaluation difference controls the
whole supremum, without exchanging supremum and limit. -/
theorem jointBellCorrelation_le_add_of_bound (A B : VonNeumannAlgebra H)
    (f g : (jointAlgebra A B).toStarSubalgebra → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : BddAbove (jointBellValues A B g))
    (hfg : ∀ T, ‖f T - g T‖ ≤ C * ‖T‖) :
    jointBellCorrelation A B f ≤ jointBellCorrelation A B g + 2 * C := by
  apply csSup_le (jointBellValues_nonempty A B f)
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  let T : (jointAlgebra A B).toStarSubalgebra :=
    X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)
  have hT : ‖T‖ ≤ 4 := by
    change ‖chshOp (X₀ : H →L[ℂ] H) (X₁ : H →L[ℂ] H)
      (Y₀ : H →L[ℂ] H) (Y₁ : H →L[ℂ] H)‖ ≤ 4
    exact norm_chshOp_le hX₀.2.2 hX₁.2.2 hY₀.2.2 hY₁.2.2
  have hd := (hfg T).trans (mul_le_mul_of_nonneg_left hT hC)
  have hn := norm_sub_norm_le (f T) (g T)
  have hv : (1 / 2 : ℝ) * ‖g T‖ ≤ jointBellCorrelation A B g :=
    le_csSup hg ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  change (1 / 2 : ℝ) * ‖f T‖ ≤ jointBellCorrelation A B g + 2 * C
  linarith

theorem abs_jointBellCorrelation_sub_le_of_bound (A B : VonNeumannAlgebra H)
    (f g : (jointAlgebra A B).toStarSubalgebra → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : BddAbove (jointBellValues A B f))
    (hg : BddAbove (jointBellValues A B g))
    (hfg : ∀ T, ‖f T - g T‖ ≤ C * ‖T‖) :
    |jointBellCorrelation A B f - jointBellCorrelation A B g| ≤ 2 * C := by
  have hfg' := jointBellCorrelation_le_add_of_bound A B f g C hC hg hfg
  have hgf' := jointBellCorrelation_le_add_of_bound A B g f C hC hf
    (fun T => by simpa only [norm_sub_rev] using hfg T)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In particular the quantity is Lipschitz on the entire continuous dual,
before imposing positivity, unitality or normality. -/
theorem lipschitzWith_jointBellCorrelation (A B : VonNeumannAlgebra H) :
    LipschitzWith 2 (fun φ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra =>
      jointBellCorrelation A B φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro φ ψ
  simp only [dist_eq_norm]
  change |jointBellCorrelation A B φ - jointBellCorrelation A B ψ| ≤ 2 * ‖φ - ψ‖
  apply abs_jointBellCorrelation_sub_le_of_bound A B φ ψ ‖φ - ψ‖ (norm_nonneg _)
  · exact jointBellValues_bddAbove_of_bound A B φ ‖φ‖ (norm_nonneg _)
      (fun T => φ.le_opNorm T)
  · exact jointBellValues_bddAbove_of_bound A B ψ ‖ψ‖ (norm_nonneg _)
      (fun T => ψ.le_opNorm T)
  · intro T
    exact (φ - ψ).le_opNorm T

theorem norm_vectorFunctional_le_of_unit (M : VonNeumannAlgebra H) (x : UnitSphere H)
    (T : M.toStarSubalgebra) : ‖vectorFunctional M x.1 T‖ ≤ ‖T‖ := by
  have h := (norm_inner_le_norm (𝕜 := ℂ) x.1 ((T : H →L[ℂ] H) x.1)).trans
    (mul_le_mul_of_nonneg_left ((T : H →L[ℂ] H).le_opNorm x.1)
      (norm_nonneg x.1))
  change ‖inner ℂ x.1 ((T : H →L[ℂ] H) x.1)‖ ≤ ‖(T : H →L[ℂ] H)‖
  simpa only [x.2, one_mul, mul_one] using h

/-- A direct estimate on actual full-H vector evaluations. Neither vectors
nor operators are projected to a finite or cyclic subspace. -/
theorem norm_vectorFunctional_sub_le_of_unit (M : VonNeumannAlgebra H)
    (x y : UnitSphere H) (T : M.toStarSubalgebra) :
    ‖vectorFunctional M x.1 T - vectorFunctional M y.1 T‖ ≤
      (2 * ‖x.1 - y.1‖) * ‖T‖ := by
  let S : H →L[ℂ] H := T
  have he : ⟪x.1, S x.1⟫_ℂ - ⟪y.1, S y.1⟫_ℂ =
      ⟪x.1 - y.1, S x.1⟫_ℂ + ⟪y.1, S (x.1 - y.1)⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hx : ‖S x.1‖ ≤ ‖S‖ := by simpa only [x.2, mul_one] using S.le_opNorm x.1
  have h₁ : ‖⟪x.1 - y.1, S x.1⟫_ℂ‖ ≤ ‖x.1 - y.1‖ * ‖S‖ :=
    (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have h₂ : ‖⟪y.1, S (x.1 - y.1)⟫_ℂ‖ ≤ ‖S‖ * ‖x.1 - y.1‖ := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) y.1 (S (x.1 - y.1))).trans
      (mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg y.1))
    simpa only [y.2, one_mul] using h
  change ‖⟪x.1, S x.1⟫_ℂ - ⟪y.1, S y.1⟫_ℂ‖ ≤ (2 * ‖x.1 - y.1‖) * ‖S‖
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem lipschitzWith_vector_jointBellCorrelation (A B : VonNeumannAlgebra H) :
    LipschitzWith 4 (fun x : UnitSphere H =>
      jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) x.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := jointBellValues_bddAbove_of_bound A B
    (vectorFunctional (jointAlgebra A B) x.1) 1 zero_le_one
    (fun T => by simpa only [one_mul] using norm_vectorFunctional_le_of_unit _ x T)
  have hy := jointBellValues_bddAbove_of_bound A B
    (vectorFunctional (jointAlgebra A B) y.1) 1 zero_le_one
    (fun T => by simpa only [one_mul] using norm_vectorFunctional_le_of_unit _ y T)
  have h := abs_jointBellCorrelation_sub_le_of_bound A B
    (vectorFunctional (jointAlgebra A B) x.1) (vectorFunctional (jointAlgebra A B) y.1)
    (2 * ‖x.1 - y.1‖) (by positivity) hx hy
    (norm_vectorFunctional_sub_le_of_unit (jointAlgebra A B) x y)
  simp only [Subtype.dist_eq, dist_eq_norm]
  change |jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) x.1) -
    jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) y.1)| ≤
      4 * ‖x.1 - y.1‖
  nlinarith

/-- All-state norm continuity, the literal sharp bounds, and full unit-vector
norm continuity, exactly as specified. The two density obligations are separate. -/
theorem bellContinuityAndBounds_specification :
    BellContinuityAndBoundsSpecification (H := H) := by
  intro A B hcomm
  refine ⟨?_, jointBellCorrelation_bounds A B hcomm, ?_⟩
  · exact (lipschitzWith_jointBellCorrelation A B).continuous.comp continuous_subtype_val
  · exact (lipschitzWith_vector_jointBellCorrelation A B).continuous

end VacuumBellSeparation.Bipartite.HC00
