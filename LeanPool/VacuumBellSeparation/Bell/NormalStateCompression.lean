/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.PositiveStateCompression
public import LeanPool.VacuumBellSeparation.Bell.NormalStateMarginals
public import LeanPool.VacuumBellSeparation.Bell.StateExtension

/-!
# Compression preserves full order-normality

The normality predicate quantifies over every nonempty directed positive
set. The proof uses the actual strong limit of that set in the original
Hilbert space. No normal extension to all B(H), universal representation,
countable cofinal family or vector-state representation is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Concrete conjugation preserves the actual supremum of a directed positive set. -/
theorem isLUB_compression_image_positive (M : VonNeumannAlgebra H)
    (q : M.toStarSubalgebra) {s : Set M.toStarSubalgebra}
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ T ∈ s, 0 ≤ T)
    {X : M.toStarSubalgebra} (hX : IsLUB s X) :
    IsLUB ((compressionPositive q) '' s) (compressionPositive q X) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hdir.isDirectedOrder
  have ht (x : H) : Tendsto (fun i : s =>
      (compressionPositive q i.1 : H →L[ℂ] H) x) atTop
      (𝓝 ((compressionPositive q X : H →L[ℂ] H) x)) := by
    change Tendsto (fun i : s => (star (q : H →L[ℂ] H))
      ((i.1 : H →L[ℂ] H) ((q : H →L[ℂ] H) x))) atTop
      (𝓝 ((star (q : H →L[ℂ] H)) ((X : H →L[ℂ] H) ((q : H →L[ℂ] H) x))))
    exact (star (q : H →L[ℂ] H)).continuous.continuousAt.tendsto.comp
      (strong_tendsto_of_isLUB_positive M hs hdir hpos hX ((q : H →L[ℂ] H) x))
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact (compressionPositive q).monotone' (hX.1 hY)
  · intro Y hY
    change (compressionPositive q X : H →L[ℂ] H) ≤ (Y : H →L[ℂ] H)
    exact Gaussian.operator_le_of_strong_tendsto ht (fun _ => tendsto_const_nhds)
      (Filter.Eventually.of_forall fun i : s =>
        (show (compressionPositive q i.1 : H →L[ℂ] H) ≤ (Y : H →L[ℂ] H) from
          hY ⟨i.1, i.2, rfl⟩))

/-- Positive conjugation is normal for arbitrary, not just sequential, suprema. -/
theorem IsNormalFunctional.compression {M : VonNeumannAlgebra H}
    {f : M.toStarSubalgebra → ℂ} (hf : IsNormalFunctional M f)
    (q : M.toStarSubalgebra) :
    IsNormalFunctional M (fun X => f (star q * X * q)) := by
  intro s hs hdir hpos X hX
  let c := compressionPositive q
  have hd : DirectedOn (· ≤ ·) (c '' s) := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨Z, hZ, rfl⟩
    obtain ⟨W, hW, hYW, hZW⟩ := hdir Y hY Z hZ
    exact ⟨c W, ⟨W, hW, rfl⟩, c.monotone' hYW, c.monotone' hZW⟩
  have hp : ∀ Y ∈ c '' s, 0 ≤ Y := by
    rintro _ ⟨Y, hY, rfl⟩
    exact c.map_nonneg (hpos Y hY)
  have h := hf (c '' s) (hs.image c) hd hp (c X)
    (isLUB_compression_image_positive M q hs hdir hpos hX)
  simpa only [Set.image_image, Function.comp_def, c, compressionPositive_apply] using h

/-- Strictly positive real rescaling preserves the directed-supremum predicate. -/
theorem IsNormalFunctional.positive_smul {M : VonNeumannAlgebra H}
    {f : M.toStarSubalgebra → ℂ} (hf : IsNormalFunctional M f)
    (c : ℝ) (hc : 0 < c) : IsNormalFunctional M (fun X => c • f X) := by
  intro s hs hdir hpos X hX
  have h := hf s hs hdir hpos X hX
  simp only [Complex.smul_re, smul_eq_mul]
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact mul_le_mul_of_nonneg_left (h.1 ⟨Y, hY, rfl⟩) hc.le
  · intro r hr
    have hbound : (f X).re ≤ r / c := h.2 (by
      rintro _ ⟨Y, hY, rfl⟩
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hr ⟨Y, hY, rfl⟩)
    have hmul := (le_div_iff₀ hc).mp hbound
    simpa only [mul_comm] using hmul

/-- The normalized compressed functional is an actual normal state on M itself. -/
theorem normalizedCompression_isNormalState (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ) (q : M.toStarSubalgebra)
    (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) :
    IsNormalStateFunctional M (normalizedCompression φ q) := by
  refine ⟨⟨normalizedCompression φ q, normalizedCompression_one φ q hq hp,
    fun _ => rfl⟩, ?_⟩
  exact (hn.compression q).positive_smul ‖φ q‖⁻¹ (inv_pos.mpr hp)

/-- Full norm control and actual normality for an arbitrary original normal state. -/
theorem exists_normal_compressed_state (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (hn : IsNormalFunctional M φ) (q : M.toStarSubalgebra)
    (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) :
    ∃ ψ : StrongDual ℂ M.toStarSubalgebra,
      IsNormalStateFunctional M ψ ∧
      (∀ X, ψ X = ‖φ q‖⁻¹ • φ (q * X * q)) ∧
      ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap - ψ‖ ≤
        2 * Real.sqrt ‖φ (1 - q)‖ + ‖φ (1 - q)‖ := by
  refine ⟨(PositiveContinuousLinearMap.ofClass (normalizedCompression φ q)).toContinuousLinearMap,
    normalizedCompression_isNormalState M φ hn q hq hp, ?_,
    normalizedCompression_dual_error_le φ hφ q hq hp⟩
  intro X
  change ‖φ q‖⁻¹ • φ (star q * X * q) = _
  rw [hq.isSelfAdjoint.star_eq]

end VacuumBellSeparation.Bipartite
