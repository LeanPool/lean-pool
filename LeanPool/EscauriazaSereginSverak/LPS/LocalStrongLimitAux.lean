/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitGrad
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongShift
public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes

/-!
# Bookkeeping for the limit strong solution

Square integrability of the components of a good-time slice, scalar weak continuity from the vector
weak continuity of a Leray--Hopf solution, and the replacement of the specified gradient by an
almost everywhere equal field in the space-time weak derivatives and in the equation
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The components of a good-time slice are square integrable. -/
theorem lps_goodTime_memLp {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {t : ℝ} (h : ESS.IsLpsGoodTime u Du t) (i : Fin 3) :
    MemLp (fun x : Vec3 => u (x, t) i) 2 volume := by
  obtain ⟨h1, hfun, -⟩ := h.1 i
  have hmem : MemLp h1.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using h1.memL2
  simpa only [hfun] using hmem

/-- Scalar weak continuity of a vector field from its vector weak continuity. -/
theorem lps_weak_continuity_scalar {T : ℝ} {u : ParabolicPoint → Vec3}
    (h : ∀ w : Vec3 → Vec3, MemLp w (2 : ℝ≥0∞) volume →
      ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i) (Icc 0 T))
    (i : Fin 3) (w : Vec3 → ℝ) (hw : MemLp w 2 volume) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, u (x, t) i * w x) (Icc 0 T) := by
  classical
  have hvec : MemLp (fun x : Vec3 => (Pi.single i (w x) : Vec3)) (2 : ℝ≥0∞) volume := by
    refine memLp_pi_iff.2 fun k => ?_
    by_cases hk : k = i
    · subst hk
      simpa using hw
    · simp [Pi.single_eq_of_ne hk]
  refine (h _ hvec).congr fun t _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The space-time weak derivatives are unchanged when the specified gradient is replaced by an
almost everywhere equal square integrable field. -/
theorem lps_hasSpaceTimeWeakDerivs_congr_grad {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du Du' : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (h : CKN.HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) I u Du D2u Dtu)
    (hae : Du =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)] Du')
    (hmem : MemLp Du' 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I))) :
    CKN.HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) I u Du' D2u Dtu := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  refine ⟨h1, lps_locallyIntegrableOn_of_memLp hmem, h3, h4, fun φ hφ => ?_⟩
  obtain ⟨c1, c2, c3⟩ := h5 φ hφ
  refine ⟨fun i j => ?_, fun i j k => ?_, c3⟩
  · rw [c1 i j]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  · rw [← c2 i j k]
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]

/-- The `L²` norm of a vector-valued family tends to zero when its coordinates do. -/
theorem lps_vec3_norm_tendsto {S : Set ℝ} {t : ℝ} {v : ℝ → Vec3 → Vec3}
    (hmem : ∀ s ∈ S, MemLp (v s) 2 volume)
    (h : ∀ i : Fin 3, Tendsto (fun s => eLpNorm (fun x => v s x i) 2 volume)
      (nhdsWithin t S) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (v s) 2 volume) (nhdsWithin t S) (𝓝 0) := by
  have hsum : Tendsto (fun s => ∑ i : Fin 3, eLpNorm (fun x => v s x i) 2 volume)
      (nhdsWithin t S) (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => h i
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun s => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact lps_eLpNorm_vec3_le_sum_coordinates (hmem s hs)

/-- The `L²` norm of a matrix-valued family tends to zero when its coordinates do. -/
theorem lps_matrix_norm_tendsto {S : Set ℝ} {t : ℝ} {v : ℝ → Vec3 → Fin 3 → Vec3}
    (hmem : ∀ s ∈ S, MemLp (v s) 2 volume)
    (h : ∀ i j : Fin 3, Tendsto (fun s => eLpNorm (fun x => v s x i j) 2 volume)
      (nhdsWithin t S) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (v s) 2 volume) (nhdsWithin t S) (𝓝 0) := by
  have hsum : Tendsto (fun s => ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun x => v s x i j) 2 volume)
      (nhdsWithin t S) (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => h i j
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun s => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact lps_eLpNorm_matrix_le_sum_coordinates (hmem s hs)

end ESS.LPS

end
