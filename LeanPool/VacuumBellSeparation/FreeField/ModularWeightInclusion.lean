/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightNorm
public import LeanPool.VacuumBellSeparation.FreeField.PhysicalModularPowers

/-!
# Containing-region bounds for the actual completed source spaces

The source inclusion is the constructed isometry of the covariance
completions. Compression of its actual Gram identifies the normalized
commutation operator; the weighted-mean inequality then bounds the full
bounded source weight. For bounded nonempty open containing regions this
is transported to the physical modular power, with domain membership.
No wedge modular identification is claimed here.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap Gaussian MeasureTheory
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m)
variable {U W : Set (EuclideanSpace ℝ (Fin 3))} (hUW : U ⊆ W)

theorem sourceNormalizedCommutation_compression :
    compression (complexSourceInclusion hm hUW)
      (normalizedCommutation (complexSourceCommutation hm W)) =
        normalizedCommutation (complexSourceCommutation hm U) := by
  have heq (V : Set (EuclideanSpace ℝ (Fin 3))) :
      normalizedCommutation (complexSourceCommutation hm V) = sourceGram hm V - 1 := by
    rw [sourceGram_eq_normalized_commutation]
    change (Complex.I / 2) • complexSourceCommutation hm V =
      1 + (Complex.I / 2) • complexSourceCommutation hm V - 1
    abel
  rw [heq W, heq U, compression_sub, compression_one]
  congr 1
  exact sourceGram_compression hm hUW

/-- Bounded weight order, with no injectivity or spectral-gap hypothesis. -/
theorem sourceModularWeight_square_compression {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    compression (complexSourceInclusion hm hUW)
      ((sourceModularWeight hm W c).adjoint * sourceModularWeight hm W c) ≤
        (sourceModularWeight hm U c).adjoint * sourceModularWeight hm U c := by
  rw [sourceModularWeight_adjoint_mul hm W hc.le hc2,
    sourceModularWeight_adjoint_mul hm U hc.le hc2,
    ← sourceNormalizedCommutation_compression hm hUW]
  exact modularWeight_compression (complexSourceInclusion hm hUW)
    (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm W))
    (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm W))
    (by linarith) (by linarith)

/-- The exact bounded source inequality for every completed complex source vector. -/
theorem sourceModularWeight_inclusion_norm {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm U) :
    ‖sourceModularWeight hm W c (complexSourceInclusion hm hUW z)‖ ≤
      ‖sourceModularWeight hm U c z‖ := by
  let J := (complexSourceInclusion hm hUW).toContinuousLinearMap
  let A := sourceModularWeight hm W c
  let B := sourceModularWeight hm U c
  have hleft : ‖A (J z)‖ ^ 2 =
      (inner ℂ z (compression (complexSourceInclusion hm hUW) (A.adjoint * A) z)).re := by
    change ‖(A ∘L J) z‖ ^ 2 = _
    rw [(A ∘L J).apply_norm_sq_eq_inner_adjoint_right, adjoint_comp]
    rfl
  have hright : ‖B z‖ ^ 2 = (inner ℂ z ((B.adjoint * B) z)).re :=
    B.apply_norm_sq_eq_inner_adjoint_right z
  have hh := (nonneg_iff_isPositive.mp (sub_nonneg.mpr
    (sourceModularWeight_square_compression hm hUW hc hc2))).re_inner_nonneg_right z
  change 0 ≤ (inner ℂ z ((B.adjoint * B -
    compression (complexSourceInclusion hm hUW) (A.adjoint * A)) z)).re at hh
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hh
  rw [← hleft, ← hright] at hh
  change ‖A (J z)‖ ≤ ‖B z‖
  nlinarith [norm_nonneg (A (J z)), norm_nonneg (B z)]

include hUW in
/-- The physical containing-region estimate, including its actual unbounded domain.
The containing region is bounded, nonempty and open so that its constructed polar
source unitary exists. The containing-wedge case is proved in another module
(`physicalRapidityExponential_containing_leftWedge` in `FreeField/WedgeModularInclusion.lean`). -/
theorem physicalModularPower_containing_region
    (hW : Bornology.IsBounded W) (hopen : IsOpen W) (hne : W.Nonempty)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ hx : complexSourceMap hm U z ∈
        (physicalModularPower hm W hW hopen hne c hc.le (by linarith)).domain,
      ‖physicalModularPower hm W hW hopen hne c hc.le (by linarith)
        ⟨complexSourceMap hm U z, hx⟩‖ ≤ ‖sourceModularWeight hm U c z‖ := by
  have hmap : complexSourceMap hm W (complexSourceInclusion hm hUW z) = complexSourceMap hm U z :=
    DFunLike.congr_fun (complexSourceMap_comp_inclusion hm hUW) z
  obtain ⟨hx, hv⟩ := physicalModularPower_apply_source hm W hW hopen hne c hc.le hc2
    (complexSourceInclusion hm hUW z)
  have hh : ∃ hy : complexSourceMap hm W (complexSourceInclusion hm hUW z) ∈
      (physicalModularPower hm W hW hopen hne c hc.le (by linarith)).domain,
      ‖physicalModularPower hm W hW hopen hne c hc.le (by linarith)
        ⟨complexSourceMap hm W (complexSourceInclusion hm hUW z), hy⟩‖ ≤
          ‖sourceModularWeight hm U c z‖ := by
    refine ⟨hx, ?_⟩
    rw [hv, LinearIsometryEquiv.norm_map]
    exact sourceModularWeight_inclusion_norm hm hUW hc hc2 z
  simpa only [hmap] using hh

end VacuumBellSeparation
