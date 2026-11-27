/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.StandardSourceSpace
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The actual densely defined source Tomita operator

Its domain is the literal complex source range, and its action is
κ z ↦ κ (conj z). Injectivity of κ makes this a genuine partial antilinear
map, rather than a multivalued relation. The graph description in closed
real source coordinates proves closedness without a bounded inverse of κ.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ClosedSubmodule
open Gaussian.HilbertComplexification
open scoped ComplexConjugate

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Linear equivalence between the source completion and its range in the one-particle space. -/
noncomputable def sourceRangeEquiv (hU : Bornology.IsBounded U) :
    ComplexSourceHilbert hm U ≃ₗ[ℂ] (complexSourceMap hm U).range :=
  LinearEquiv.ofInjective (complexSourceMap hm U).toLinearMap
    (complexSourceMap_injective hm U hU)

@[simp] theorem sourceRangeEquiv_apply (hU : Bornology.IsBounded U)
    (z : ComplexSourceHilbert hm U) :
    (sourceRangeEquiv hm U hU z : Lp ℂ 2 (oneParticleMeasure m)) = complexSourceMap hm U z := rfl

@[simp] theorem sourceRangeEquiv_symm_apply (hU : Bornology.IsBounded U)
    (x : (complexSourceMap hm U).range) :
    complexSourceMap hm U ((sourceRangeEquiv hm U hU).symm x) = x :=
  LinearEquiv.ofInjective_symm_apply _ _

/-- The actual antilinear partial operator on the physical one-particle Hilbert space. -/
noncomputable def sourceTomita (hU : Bornology.IsBounded U) :
    Lp ℂ 2 (oneParticleMeasure m) →ₛₗ.[starRingEnd ℂ] Lp ℂ 2 (oneParticleMeasure m) where
  domain := (complexSourceMap hm U).range
  toFun := (complexSourceMap hm U).toLinearMap.comp
    (conjugation.toLinearEquiv.toLinearMap.comp (sourceRangeEquiv hm U hU).symm.toLinearMap)

@[simp] theorem sourceTomita_source (hU : Bornology.IsBounded U)
    (z : ComplexSourceHilbert hm U) :
    sourceTomita hm U hU (sourceRangeEquiv hm U hU z) =
      complexSourceMap hm U (conjugation z) := by
  change complexSourceMap hm U
    (conjugation ((sourceRangeEquiv hm U hU).symm (sourceRangeEquiv hm U hU z))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem sourceTomita_dense_domain (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) :
    Dense ((sourceTomita hm U hU).domain : Set (Lp ℂ 2 (oneParticleMeasure m))) :=
  complexSourceMap_denseRange_of_open hm U hopen hne

/-- Actual graph of the antilinear operator, kept as a set to avoid treating it
as a complex-linear subspace of the ordinary product. -/
def sourceTomitaGraph : Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | ∃ z : ComplexSourceHilbert hm U,
    complexSourceMap hm U z = p.1 ∧ complexSourceMap hm U (conjugation z) = p.2}

theorem sourceTomitaGraph_iff (hU : Bornology.IsBounded U)
    (x y : Lp ℂ 2 (oneParticleMeasure m)) :
    (x, y) ∈ sourceTomitaGraph hm U ↔
      ∃ hx : x ∈ (sourceTomita hm U hU).domain, sourceTomita hm U hU ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨z, rfl, hy⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    exact (sourceTomita_source hm U hU z).trans hy
  · rintro ⟨hx, hy⟩
    refine ⟨(sourceRangeEquiv hm U hU).symm ⟨x, hx⟩, ?_, hy⟩
    exact sourceRangeEquiv_symm_apply hm U hU _

theorem sourceTomitaGraph_flip {x y : Lp ℂ 2 (oneParticleMeasure m)}
    (h : (x, y) ∈ sourceTomitaGraph hm U) : (y, x) ∈ sourceTomitaGraph hm U := by
  obtain ⟨z, hx, hy⟩ := h
  exact ⟨conjugation z, hy, by simpa only [conjugation_conjugation] using hx⟩

theorem sourceTomitaGraph_coordinates (x y : Lp ℂ 2 (oneParticleMeasure m)) :
    (x, y) ∈ sourceTomitaGraph hm U ↔
      (1 / 2 : ℝ) • (x + y) ∈ sourceRealSpace hm U ∧
      (-(Complex.I / 2)) • (x - y) ∈ sourceRealSpace hm U := by
  constructor
  · rintro ⟨z, rfl, rfl⟩
    have hplus : (1 / 2 : ℝ) •
        (complexSourceMap hm U z + complexSourceMap hm U (conjugation z)) =
          sourceEmbedding hm U z.re := by
      change (1 / 2 : ℝ) • ((sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im) +
        (sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U (-z.im))) = _
      simp only [map_neg, smul_neg, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      push_cast
      module
    have hminus : (-(Complex.I / 2)) •
        (complexSourceMap hm U z - complexSourceMap hm U (conjugation z)) =
          sourceEmbedding hm U z.im := by
      change (-(Complex.I / 2)) • ((sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U
        z.im) -
        (sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U (-z.im))) = _
      simp only [map_neg, smul_neg, smul_sub, smul_add, smul_smul]
      have hc : -(Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_sq
      rw [hc]
      module
    rw [hplus, hminus]
    exact ⟨⟨z.re, rfl⟩, ⟨z.im, rfl⟩⟩
  · rintro ⟨hu, hv⟩
    obtain ⟨u, hu⟩ := hu
    obtain ⟨v, hv⟩ := hv
    change sourceEmbedding hm U u = (1 / 2 : ℝ) • (x + y) at hu
    change sourceEmbedding hm U v = (-(Complex.I / 2)) • (x - y) at hv
    refine ⟨mk u v, ?_, ?_⟩
    · change sourceEmbedding hm U u + Complex.I • sourceEmbedding hm U v = x
      rw [hu, hv, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      have hc : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_sq
      rw [hc]
      push_cast
      module
    · change sourceEmbedding hm U u + Complex.I • sourceEmbedding hm U (-v) = y
      rw [map_neg, smul_neg, hu, hv, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      have hc : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_sq
      rw [hc]
      push_cast
      module

/-- Closedness of the actual graph, not closedness of the generally nonclosed domain. -/
theorem sourceTomitaGraph_isClosed : IsClosed (sourceTomitaGraph hm U) := by
  have heq : sourceTomitaGraph hm U =
      (fun p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) =>
        (1 / 2 : ℝ) • (p.1 + p.2)) ⁻¹' (sourceRealSpace hm U : Set _) ∩
      (fun p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) =>
        (-(Complex.I / 2)) • (p.1 - p.2)) ⁻¹' (sourceRealSpace hm U : Set _) := by
    ext p
    exact sourceTomitaGraph_coordinates hm U p.1 p.2
  rw [heq]
  exact ((sourceRealSpace hm U).isClosed.preimage (by fun_prop)).inter
    ((sourceRealSpace hm U).isClosed.preimage (by fun_prop))

end VacuumBellSeparation
