/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCoordinates

/-! # Compactness of the literal normalized target, including mass zero -/

@[expose] public section

namespace VacuumBellSeparation

theorem continuous_euclidSq : Continuous euclidSq := by
  unfold euclidSq
  fun_prop

theorem continuous_reLorentzSq : Continuous reLorentzSq := by
  unfold reLorentzSq reSpatialSq
  fun_prop

theorem isClosed_normalizedTarget : IsClosed normalizedTarget := by
  have h0 : IsClosed {p : ℝ × ComplexSpacetime | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have h1 : IsClosed {p : ℝ × ComplexSpacetime | p.1 ≤ 1} :=
    isClosed_le continuous_fst continuous_const
  have hs : IsClosed {p : ℝ × ComplexSpacetime | p.2 ∈ complexShell p.1} := by
    change IsClosed {p : ℝ × ComplexSpacetime |
      p.2.1 ^ 2 - spatialDot p.2.2 p.2.2 = (p.1 : ℂ) ^ 2}
    apply isClosed_eq <;> (try simp only [spatialDot]) <;> fun_prop
  have he : IsClosed {p : ℝ × ComplexSpacetime | euclidSq p.2 ≤ 16 ^ 2} :=
    isClosed_le (continuous_euclidSq.comp continuous_snd) continuous_const
  have hr : IsClosed {p : ℝ × ComplexSpacetime | reLorentzSq p.2 ≤ -16} :=
    isClosed_le (continuous_reLorentzSq.comp continuous_snd) continuous_const
  exact h0.inter (h1.inter (hs.inter (he.inter hr)))

theorem normalizedTarget_euclidean_bound {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) : ‖complexSpacetimeEuclideanEquiv z‖ ≤ 16 := by
  have h := hz.2.2.2.1
  rw [← complexSpacetimeEuclideanEquiv_norm_sq] at h
  nlinarith [norm_nonneg (complexSpacetimeEuclideanEquiv z)]

theorem isCompact_normalizedTarget : IsCompact normalizedTarget := by
  let T : (ℝ × ComplexSpacetime) ≃ₜ (ℝ × ShellEuclideanAmbient) :=
    (Homeomorph.refl ℝ).prodCongr complexSpacetimeEuclideanEquiv.toHomeomorph
  have hc : IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ Metric.closedBall (0 : ShellEuclideanAmbient) 16) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  apply (hc.image T.symm.continuous).of_isClosed_subset isClosed_normalizedTarget
  intro p hp
  refine ⟨T p, ?_, T.symm_apply_apply p⟩
  refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
  change complexSpacetimeEuclideanEquiv p.2 ∈
    Metric.closedBall (0 : ShellEuclideanAmbient) 16
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    normalizedTarget_euclidean_bound hp

theorem normalizedTarget_finite_subcover {ι : Type*}
    (U : ι → Set (ℝ × ComplexSpacetime)) (hU : ∀ i, IsOpen (U i))
    (hcover : normalizedTarget ⊆ ⋃ i, U i) :
    ∃ s : Finset ι, normalizedTarget ⊆ ⋃ i ∈ s, U i :=
  isCompact_normalizedTarget.elim_finite_subcover U hU hcover

end VacuumBellSeparation
