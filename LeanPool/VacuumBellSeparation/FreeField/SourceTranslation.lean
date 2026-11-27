/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestTranslation
public import LeanPool.VacuumBellSeparation.FreeField.SourceTomita
public import LeanPool.VacuumBellSeparation.FreeField.WedgeGeometry

/-!
# Translation covariance of the full original closed source spaces

Actual translated test pairs and continuity give covariance of the completed
real source ranges. The universal real-coordinate description of the Tomita
graph then gives covariance of its entire domain and graph.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ClosedSubmodule
open scoped InnerProductSpace

theorem oneParticleSpatialTranslation_neg_apply (m : ℝ)
    (a : EuclideanSpace ℝ (Fin 3)) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleSpatialTranslation m (-a) (oneParticleSpatialTranslation m a ψ) = ψ := by
  apply Lp.ext
  filter_upwards [oneParticleSpatialTranslation_ae m (-a) (oneParticleSpatialTranslation m a ψ),
    oneParticleSpatialTranslation_ae m a ψ] with p hneg hpos
  rw [hneg, hpos, ← mul_assoc, spatialTranslationPhase, spatialTranslationPhase,
    ← Complex.exp_add, inner_neg_right, Complex.ofReal_neg]
  have hz : -(Complex.I * -(⟪p, a⟫_ℝ : ℂ)) + -(Complex.I * (⟪p, a⟫_ℝ : ℂ)) = 0 := by ring
  rw [hz, Complex.exp_zero, one_mul]

theorem oneParticleSpatialTranslation_symm (m : ℝ) (a : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (oneParticleSpatialTranslation m a).symm ψ = oneParticleSpatialTranslation m (-a) ψ := by
  apply (oneParticleSpatialTranslation m a).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [neg_neg] using (oneParticleSpatialTranslation_neg_apply m (-a) ψ).symm

theorem spatialTestTranslate_support_subset {a : EuclideanSpace ℝ (Fin 3)}
    {U V : Set (EuclideanSpace ℝ (Fin 3))} (hUV : ∀ x ∈ U, x + a ∈ V)
    (f : SpatialTestFunction) (hf : tsupport f.1 ⊆ U) :
    tsupport (spatialTestTranslate a f).1 ⊆ V := by
  rw [tsupport_spatialTestTranslate]
  intro x hx
  have h := hUV (x - a) (hf hx)
  simpa only [sub_add_cancel] using h

theorem oneParticleSpatialTranslation_mem_sourceRealSpace {m : ℝ} (hm : 0 < m)
    (a : EuclideanSpace ℝ (Fin 3))
    {U V : Set (EuclideanSpace ℝ (Fin 3))} (hUV : ∀ x ∈ U, x + a ∈ V)
    {ψ : Lp ℂ 2 (oneParticleMeasure m)} (hψ : ψ ∈ sourceRealSpace hm U) :
    oneParticleSpatialTranslation m a ψ ∈ sourceRealSpace hm V := by
  have hs : Set.range (sourceTestMap hm U) ⊆
      (oneParticleSpatialTranslation m a) ⁻¹' (sourceRealSpace hm V : Set _) := by
    rintro _ ⟨u, rfl⟩
    let v : SourceTestSpace hm V := ⟨timeZeroTranslate a u.1,
      spatialTestTranslate_support_subset hUV u.1.1 u.2.1,
      spatialTestTranslate_support_subset hUV u.1.2 u.2.2⟩
    refine ⟨(v : SourceHilbert hm V), ?_⟩
    change sourceEmbedding hm V (v : SourceHilbert hm V) = _
    rw [sourceEmbedding_coe]
    exact timeZeroL2_translate hm a u.1
  have hc := closure_minimal hs
    ((sourceRealSpace hm V).isClosed.preimage (oneParticleSpatialTranslation m a).continuous)
  change ψ ∈ Set.range (sourceEmbedding hm U) at hψ
  rw [range_sourceEmbedding_eq_closure] at hψ
  exact hc hψ

theorem oneParticleSpatialTranslation_mem_sourceTomitaGraph {m : ℝ} (hm : 0 < m)
    (a : EuclideanSpace ℝ (Fin 3))
    {U V : Set (EuclideanSpace ℝ (Fin 3))} (hUV : ∀ x ∈ U, x + a ∈ V)
    {ψ χ : Lp ℂ 2 (oneParticleMeasure m)} (h : (ψ, χ) ∈ sourceTomitaGraph hm U) :
    (oneParticleSpatialTranslation m a ψ, oneParticleSpatialTranslation m a χ) ∈
      sourceTomitaGraph hm V := by
  rw [sourceTomitaGraph_coordinates] at h ⊢
  constructor
  · have hh := oneParticleSpatialTranslation_mem_sourceRealSpace hm a hUV h.1
    change (oneParticleSpatialTranslation m a).toLinearEquiv.toLinearMap.restrictScalars ℝ
      ((1 / 2 : ℝ) • (ψ + χ)) ∈ sourceRealSpace hm V at hh
    simp only [map_smul, map_add] at hh
    change (1 / 2 : ℝ) •
      (oneParticleSpatialTranslation m a ψ + oneParticleSpatialTranslation m a χ) ∈
        sourceRealSpace hm V at hh
    exact hh
  · have hh := oneParticleSpatialTranslation_mem_sourceRealSpace hm a hUV h.2
    simpa only [map_smul, map_sub] using hh

theorem leftWedgeTimeZero_add_edge (ℓ : ℝ) :
    ∀ x ∈ leftWedgeTimeZero 0, x + ℓ • e₁ ∈ leftWedgeTimeZero ℓ := by
  intro x hx
  change ⟪e₁, x + ℓ • e₁⟫_ℝ < ℓ
  rw [inner_e₁_add_smul]
  change ⟪e₁, x⟫_ℝ < 0 at hx
  linarith

theorem leftWedgeTimeZero_sub_edge (ℓ : ℝ) :
    ∀ x ∈ leftWedgeTimeZero ℓ, x + -(ℓ • e₁) ∈ leftWedgeTimeZero 0 := by
  intro x hx
  change ⟪e₁, x + -(ℓ • e₁)⟫_ℝ < 0
  rw [← neg_smul, inner_e₁_add_smul]
  change ⟪e₁, x⟫_ℝ < ℓ at hx
  linarith

/-- Exact translation covariance of the entire actual source Tomita graph. -/
theorem leftWedge_sourceTomitaGraph_translation {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (oneParticleSpatialTranslation m (ℓ • e₁) ψ,
      oneParticleSpatialTranslation m (ℓ • e₁) χ) ∈
        sourceTomitaGraph hm (leftWedgeTimeZero ℓ) ↔
      (ψ, χ) ∈ sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
  constructor
  · intro h
    have hh := oneParticleSpatialTranslation_mem_sourceTomitaGraph hm (-(ℓ • e₁))
      (leftWedgeTimeZero_sub_edge ℓ) h
    simpa only [oneParticleSpatialTranslation_neg_apply] using hh
  · exact oneParticleSpatialTranslation_mem_sourceTomitaGraph hm (ℓ • e₁)
      (leftWedgeTimeZero_add_edge ℓ)

end VacuumBellSeparation
