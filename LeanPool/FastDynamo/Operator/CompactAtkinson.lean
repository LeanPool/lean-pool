/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Compact perturbations of the identity on a Hilbert space

This module supplies the compact-operator Fredholm step needed by the local
Ponomarenko reduction.  A compact map into a Hilbert space is approximated in
operator norm by projecting its image onto the span of finitely many centres
of a compact-image net.  The approximant has finite range.  Taking the error
smaller than one makes the identity minus that error invertible by the
Neumann lemma, and the finite-rank perturbation theorem then proves
that the identity minus the original compact map is Fredholm.

The approximation theorem is stated for a general normed domain and Hilbert
codomain.  Completeness of the ambient Hilbert space is needed only for the
final Fredholm theorem (through the Neumann inverse); each finite-dimensional
span used in the approximation is complete on its own.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Set
open scoped LinearMap.FiniteRangeSetoid

namespace CompactAtkinson

universe u v

variable {E : Type u} {H : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A compact continuous linear map into a complex Hilbert space admits
arbitrarily accurate finite-range approximations in operator norm.

The approximant is the orthogonal projection of the compact map onto the
span of a finite net for the image of the closed unit ball. -/
theorem exists_hasFiniteRange_norm_sub_lt
    {K : E →L[ℂ] H} (hK : IsCompactOperator K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ F : E →L[ℂ] H,
      F.toLinearMap.HasFiniteRange ∧ ‖K - F‖ < epsilon := by
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨t, ht_subset, ht_finite, ht_cover⟩ :=
    (hK.isCompact_closure_image_closedBall 1).finite_cover_balls hdelta
  let V : Submodule ℂ H := Submodule.span ℂ t
  let : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ ht_finite
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let F : E →L[ℂ] H := V.starProjection.comp K
  have hFfinite : F.toLinearMap.HasFiniteRange := by
    have hprojection : V.starProjection.toLinearMap.HasFiniteRange := by
      rw [LinearMap.hasFiniteRange_iff_range,
        Submodule.range_starProjection]
      exact (Submodule.fg_iff_finiteDimensional V).2 inferInstance
    exact hprojection.comp_right K.toLinearMap
  refine ⟨F, hFfinite, ?_⟩
  have hnorm : ‖K - F‖ ≤ delta := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hdelta.le
    intro x hx
    have hx_ball : x ∈ closedBall (0 : E) 1 := by
      simp [mem_closedBall, dist_zero_right, hx]
    have hKx_closure : K x ∈ closure (K '' closedBall (0 : E) 1) :=
      subset_closure ⟨x, hx_ball, rfl⟩
    have hcovered := ht_cover hKx_closure
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcovered
    obtain ⟨y, hyt, hy⟩ := hcovered
    have hyV : y ∈ V := Submodule.subset_span hyt
    have hbest : ‖K x - V.starProjection (K x)‖ ≤ ‖K x - y‖ := by
      rw [Submodule.starProjection_minimal]
      change (⨅ z : V, ‖K x - z‖) ≤ ‖K x - (⟨y, hyV⟩ : V)‖
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ _
    change ‖K x - V.starProjection (K x)‖ ≤ delta
    exact hbest.trans (by simpa [dist_eq_norm] using hy.le)
  exact hnorm.trans_lt (by dsimp [delta]; linarith)

/-- Atkinson's theorem for a compact endomorphism of a complex Hilbert space:
the identity minus the compact map is Fredholm. -/
theorem isFredholm_id_sub_of_isCompact
    [CompleteSpace H] {K : H →L[ℂ] H} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm (ContinuousLinearMap.id ℂ H - K) := by
  obtain ⟨F, hFfinite, herror⟩ :=
    exists_hasFiniteRange_norm_sub_lt hK (epsilon := (1 : ℝ)) zero_lt_one
  let U : H →L[ℂ] H :=
    ContinuousLinearMap.id ℂ H - (K - F)
  have hU : U.IsInvertible := by
    have hsmall : ‖-(K - F)‖ < 1 := by
      rw [norm_neg]
      exact herror
    have hinv := ContinuousLinearMap.isInvertible_id_add_of_norm_lt_one hsmall
    simpa [U, sub_eq_add_neg] using hinv
  apply FredholmIsolation.IsInvertible.isFredholm_of_hasFiniteRange_sub hU
  have heq :
      ((ContinuousLinearMap.id ℂ H - K) - U).toLinearMap =
        (-F).toLinearMap := by
    ext x
    simp [U]
  rw [heq]
  exact hFfinite.neg

end CompactAtkinson

end

end FastDynamo
