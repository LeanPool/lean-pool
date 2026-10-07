/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSolution
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Restricting finite-energy weak solutions to shorter intervals

A finite-energy weak solution with pressure on `(0, T)` is one on every
shorter interval `(0, σ)`. The short-time comparison in `thm:ess-l5-unique`
applies `lem:pv-serrin-uniqueness` on such an interval.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Restriction of a finite-energy weak solution with pressure to a shorter
time interval. -/
theorem IsSerrinWeakSolution.restrict {T σ : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    (hσ : 0 < σ) (hσT : σ ≤ T) : IsSerrinWeakSolution σ a u Du p := by
  have hle := serrin_slab_restrict_le hσT
  have hsub : Ioo (0 : ℝ) σ ⊆ Ioo 0 T := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hσT⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := fun z hz => ⟨hz.1, hsub hz.2⟩
  refine ⟨hσ, hU.datum, hU.meas_u.mono_measure hle, hU.meas_Du.mono_measure hle, ?_, ?_,
    ae_restrict_of_ae_restrict_of_subset hsub hU.weak_grad,
    ae_restrict_of_ae_restrict_of_subset hsub hU.div_free, hU.pressure.mono_measure hle, ?_,
    fun ψ hψ hψc => (hU.weak_cont ψ hψ hψc).mono (Icc_subset_Icc_right hσT), hU.initial⟩
  · exact lt_of_le_of_lt (essSup_mono_measure' (Measure.restrict_mono hsub le_rfl))
      hU.slice_bound
  · exact lt_of_le_of_lt (lintegral_mono_set hQsub) hU.energy
  · intro φ hφ
    have hφT : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans hQsub⟩
    have h := hU.momentum φ hφT
    have hms : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hms hQsub] at h
    · exact h
    intro z hz
    let z' : Vec3 × ℝ := z
    let φ' : Vec3 × ℝ → Vec3 := φ
    have hzφ : z' ∉ tsupport φ' := fun hmem => hz.2 (hφ.2.2 hmem)
    have hcomp (i : Fin 3) : z' ∉ tsupport (fun y : Vec3 × ℝ => φ' y i) := by
      intro hmem
      apply hzφ
      refine closure_mono ?_ hmem
      intro y hy hzero
      apply hy
      simp [hzero]
    have hsm (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => φ' y i) :=
      contDiff_pi.mp hφ.1 i
    have ht (i : Fin 3) : timePartial (fun y => φ y i) z = 0 :=
      CKN.timePartial_zero_of_not_mem_tsupport_public (hsm i) (hcomp i)
    have hs (i j : Fin 3) : spatialPartial (fun y => φ y i) j z = 0 :=
      CKN.spatialPartial_zero_of_not_mem_tsupport_public (hsm i) (hcomp i) j
    have hφ0 : φ' z' = 0 := image_eq_zero_of_notMem_tsupport hzφ
    have hφ0' : φ z = 0 := hφ0
    simp [ht, hs, hφ0']

end ESS
