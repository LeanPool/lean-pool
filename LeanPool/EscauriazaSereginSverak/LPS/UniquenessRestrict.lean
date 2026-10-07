/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Restricting Leray–Hopf solutions to shorter intervals

A Leray–Hopf solution on `(0, T)` is one on every shorter interval `(0, σ)`
with the same datum (`def:leray-hopf`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Restriction of a Leray–Hopf solution to a shorter time interval. -/
theorem _root_.CKN.IsLerayHopfSolution.restrict {T σ : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du) (hσ : 0 < σ) (hσT : σ ≤ T) :
    IsLerayHopfSolution σ a u Du := by
  obtain ⟨-, hdatum, hmu, hmDu, hslice, henergy, hgrad, hdiv, hweak, hmom, hineq,
    hinit⟩ := hU
  have hle := serrin_slab_restrict_le hσT
  have hsub : Ioo (0 : ℝ) σ ⊆ Ioo 0 T := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hσT⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := fun z hz => ⟨hz.1, hsub hz.2⟩
  refine ⟨hσ, hdatum, hmu.mono_measure hle, hmDu.mono_measure hle, ?_, ?_,
    ae_restrict_of_ae_restrict_of_subset hsub hgrad,
    ae_restrict_of_ae_restrict_of_subset hsub hdiv,
    fun w hw => (hweak w hw).mono (Icc_subset_Icc_right hσT), ?_,
    fun t₀ ht₀ => hineq t₀ ⟨ht₀.1, ht₀.2.trans hσT⟩, hinit⟩
  · exact lt_of_le_of_lt (essSup_mono_measure' (Measure.restrict_mono hsub le_rfl)) hslice
  · exact lt_of_le_of_lt (lintegral_mono_set hQsub) henergy
  · intro φ hφ hφdiv
    have hφT : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans hQsub⟩
    have h := hmom φ hφT hφdiv
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
    simp [ht, hs]

end ESS

end
