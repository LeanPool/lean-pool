/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceMomentVectors
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Actual moment vectors and their finite-dimensional degree ranges

The original joint source norm is used throughout. The proved weighted
moment theorem supplies genuine Riesz vectors; taking real parts removes
the auxiliary complexification without changing any real test moment.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped InnerProductSpace

/-- Two actual moment families in the original real source completion. -/
structure JointSourceMomentFamily {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) where
  /-- Spatial monomial moments in the field component of the real source space. -/
  field : (Fin 3 → ℕ) → SourceHilbert hμ U
  /-- Spatial monomial moments in the momentum component of the real source space. -/
  momentum : (Fin 3 → ℕ) → SourceHilbert hμ U
  field_pairing : ∀ α (u : SourceTestSpace hμ U),
    inner ℝ (u : SourceHilbert hμ U) (field α) = spatialRealTestMoment u.1.1 α
  momentum_pairing : ∀ α (u : SourceTestSpace hμ U),
    inner ℝ (u : SourceHilbert hμ U) (momentum α) = spatialRealTestMoment u.1.2 α

theorem exists_jointSourceMomentFamily {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : U ⊆ Metric.ball 0 T) :
    Nonempty (JointSourceMomentFamily hμ U) := by
  obtain ⟨C, hC, h⟩ := exists_weightedSource_moment_vectors
    (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl) (by norm_num : (1 / 2 : ℝ) < 1)
  have hv (α : Fin 3 → ℕ) : ∃ u v : SourceHilbert hμ U,
      (∀ x : SourceTestSpace hμ U,
        inner ℝ (x : SourceHilbert hμ U) u = spatialRealTestMoment x.1.1 α) ∧
      (∀ x : SourceTestSpace hμ U,
        inner ℝ (x : SourceHilbert hμ U) v = spatialRealTestMoment x.1.2 α) := by
    obtain ⟨u, v, _, _, hu, hv⟩ := h μ hμ T hT U hU α
    refine ⟨((sourceReserve hμ U ^ (1 / 2 : ℝ)) u).re,
      ((sourceReserve hμ U ^ (1 / 2 : ℝ)) v).re, ?_, ?_⟩
    · intro x
      have hx := congrArg Complex.re (hu x)
      simpa only [HilbertComplexification.inner_eq, ofReal_re, ofReal_im,
        inner_zero_left, add_zero, Complex.ofReal_re] using hx
    · intro x
      have hx := congrArg Complex.re (hv x)
      simpa only [HilbertComplexification.inner_eq, ofReal_re, ofReal_im,
        inner_zero_left, add_zero, Complex.ofReal_re] using hx
  choose u v hu hv using hv
  exact ⟨⟨u, v, hu, hv⟩⟩

/-- A canonical choice from the actual moment-vector existence theorem. -/
def jointSourceMomentFamily {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : U ⊆ Metric.ball 0 T) :
    JointSourceMomentFamily hμ U :=
  Classical.choice (exists_jointSourceMomentFamily hμ hT U hU)

section DegreeRange
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A coordinate degree box has only cubic cardinality. -/
def spatialMomentDegreeRange (v : (Fin 3 → ℕ) → E) (D : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun α : Fin 3 → Fin (D + 1) => v (fun i => (α i).val))

instance finiteDimensional_spatialMomentDegreeRange
    (v : (Fin 3 → ℕ) → E) (D : ℕ) :
    FiniteDimensional 𝕜 (spatialMomentDegreeRange (𝕜 := 𝕜) v D) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

theorem mem_spatialMomentDegreeRange (v : (Fin 3 → ℕ) → E) (D : ℕ)
    (α : Fin 3 → ℕ) (hα : ∀ i, α i ≤ D) :
    v α ∈ spatialMomentDegreeRange (𝕜 := 𝕜) v D := by
  apply Submodule.subset_span
  refine ⟨fun i => ⟨α i, Nat.lt_succ_of_le (hα i)⟩, rfl⟩

theorem finrank_spatialMomentDegreeRange_le (v : (Fin 3 → ℕ) → E) (D : ℕ) :
    Module.finrank 𝕜 (spatialMomentDegreeRange (𝕜 := 𝕜) v D) ≤ (D + 1) ^ 3 := by
  calc
    _ ≤ Fintype.card (Fin 3 → Fin (D + 1)) :=
      finrank_range_le_card (R := 𝕜)
        (fun α : Fin 3 → Fin (D + 1) => v (fun i => (α i).val))
    _ = (D + 1) ^ 3 := by simp only [Fintype.card_fun, Fintype.card_fin]

end DegreeRange
end VacuumBellSeparation
