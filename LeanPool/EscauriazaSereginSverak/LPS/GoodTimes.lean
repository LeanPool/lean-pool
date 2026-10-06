/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEstimate
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A positive-time slice in `H¹ ∩ J` with the specified weak gradient,
as in `lem:lps-good-times`. -/
@[expose] def IsLpsGoodTime (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) : Prop :=
  (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
    h.toFun = (fun x : Vec3 => u (x, t) i) ∧
    h.grad = (fun x : Vec3 => Du (x, t) i)) ∧
  IsInJ (fun x : Vec3 => u (x, t))

/-- Almost every positive-time slice of a Leray--Hopf field belongs to
`H¹ ∩ J`, with weak gradient `Du` (`lem:lps-good-times`). -/
theorem lps_good_times_ae
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T), IsLpsGoodTime u Du t := by
  have hSlices := serrin_slice_memLp_two_ae hLH
  rcases hLH with ⟨_hT, _hJ, _huMeas, _hDuMeas, _hSliceBound, _hJointBound,
    hWeakGradient, hDivergence, _hWeakContinuity, _hMomentum, _hEnergy,
    _hInitialTrace⟩
  filter_upwards [hSlices, hWeakGradient, hDivergence]
    with t ht hgrad hdiv
  change
    (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u (x, t) i) ∧
      h.grad = (fun x : Vec3 => Du (x, t) i)) ∧
    IsInJ (fun x : Vec3 => u (x, t))
  constructor
  · intro i
    let hi : H1Function (Set.univ : Set Vec3) := {
      toFun := fun x => u (x, t) i
      grad := fun x => Du (x, t) i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          ht.1.eval i
      gradMemL2 := by
        intro j
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (ht.2.eval i).eval j
      hasWeakGradient := hgrad i
    }
    exact ⟨hi, rfl, rfl⟩
  · exact weakDivFreeL2_isInJ ⟨ht.1, hdiv⟩

/-- Every nonempty interval inside `[0,T]` contains a time whose slice is in
`H¹ ∩ J` with weak gradient `Du` (`lem:lps-good-times`). -/
theorem lps_good_time_in_interval
    {T : ℝ} {a₀ : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a₀ u Du)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) :
    ∃ t, t ∈ Ioo a b ∧ IsLpsGoodTime u Du t := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 T)
  let G : Set ℝ := {t | IsLpsGoodTime u Du t}
  have hG : G ∈ ae μ := lps_good_times_ae hLH
  have hGnull : μ Gᶜ = 0 := mem_ae_iff.mp hG
  have hsub : Ioo a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
  have hμinterval : μ (Ioo a b) = volume (Ioo a b) := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    simp [inter_eq_left.mpr hsub]
  have hpositive : 0 < μ (Ioo a b) := by
    rw [hμinterval, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith only [hab])
  by_contra hnone
  have hnullsubset : Ioo a b ⊆ Gᶜ := by
    intro t ht
    by_contra hnot
    apply hnone
    refine ⟨t, ht, ?_⟩
    simpa [G] using not_not.mp hnot
  have hzero : μ (Ioo a b) = 0 :=
    le_antisymm ((measure_mono hnullsubset).trans_eq hGnull) bot_le
  exact (ne_of_gt hpositive) hzero

/-- Weak `L²` continuity of the prescribed slices and strong convergence to the
initial datum in `L²` along almost every positive-time slice. The strong trace
is the one in (LH5) of `def:leray-hopf`; this theorem gives its a.e.-slice
consequence, while `lem:lps-good-times` supplies the good slices. -/
theorem lps_weak_l2_continuity_and_initial_trace
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    (∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn
        (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)
        (Icc 0 T)) ∧
    Tendsto
      (fun t : ℝ => eLpNorm (fun x : Vec3 => u (x, t) - a x) 2 volume)
      (nhdsWithin 0 (Ioi 0) ⊓ ae (volume.restrict (Ioo 0 T))) (nhds 0) := by
  have hTrace := serrin_difference_initial_trace_l2_ae hLH
  rcases hLH with ⟨_hT, _hJ, _huMeas, _hDuMeas, _hSliceBound, _hJointBound,
    _hWeakGradient, _hDivergence, hWeakContinuity, _hMomentum, _hEnergy,
    _hInitialTrace⟩
  exact ⟨hWeakContinuity, hTrace⟩

end ESS
