/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszTimeSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution

public section

open CKN

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A globally integrable exterior tensor has a canonical Riesz pressure
whose spatial slices are harmonic on the interior for almost every time. -/
theorem blowup_rieszPressureSpaceTime_exterior_harmonic_slices
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (U : Set Vec3) (hU : IsOpen U)
    (hzero : ∀ i j z, z.1 ∈ U → F i j z = 0)
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      CKN.Foundation.Heat.WeaklyHarmonicOn U
        (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) F hF (x,t)) := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  let : Countable Q := hQcount.to_subtype
  let p : Vec3 × ℝ → ℝ := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  have hbump : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∀ q : Q × ℕ, Metric.closedBall (q.1 : Vec3) (CKN.sliceRadius q.2) ⊆ U →
        ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian
          (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius q.2)
            (CKN.sliceRadius_pos q.2) (z - (q.1 : Vec3))) x = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hball : Metric.closedBall (q.1 : Vec3) (CKN.sliceRadius q.2) ⊆ U
    · have hts : tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius q.2) (CKN.sliceRadius_pos q.2)
          (z - (q.1 : Vec3))) ⊆ U := by
        rw [CKN.tsupport_mollifier_sub_eq]
        exact hball
      filter_upwards [blowup_rieszPressure_exterior_slice_pairing_ae
        F hF U hzero (CKN.contDiff_mollifier_sub (CKN.sliceRadius_pos q.2)
          (q.1 : Vec3))
        (CKN.hasCompactSupport_mollifier_sub (CKN.sliceRadius_pos q.2)
          (q.1 : Vec3)) hts hab] with t ht _
      exact ht
    · filter_upwards [] with t ht
      exact absurd ht hball
  have hSlices := CKN.Leray.rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) F hF
  have hSlicesJ : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∃ hFt : ∀ i j, MemLp (fun x : Vec3 => F i j (x,t))
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3),
        (fun x : Vec3 => p (x,t)) =ᵐ[volume]
          fun x => CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
            (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y,t))) x :=
    ae_restrict_of_ae hSlices
  filter_upwards [hbump, hSlicesJ] with t ht ⟨hFt, hEq⟩
  have hMem : MemLp (fun x : Vec3 => p (x,t))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
    exact (Lp.memLp (CKN.Leray.rieszPressureSlice
      (3 / 2 : ℝ) (by norm_num)
      (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y,t))))).ae_eq hEq.symm
  have hLoc : LocallyIntegrableOn (fun x : Vec3 => p (x,t)) U volume :=
    (hMem.locallyIntegrable (by norm_num)).locallyIntegrableOn U
  apply blowup_harmonic_of_mollifier_bump_pairings hU hQdense hLoc
  intro y hy n hn
  have h := ht (⟨y, hy⟩, n) hn
  calc
    ∫ x in U, p (x,t) * CKN.spatialLaplacian
        (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
          (CKN.sliceRadius_pos n) (z - y)) x =
      ∫ x : Vec3, p (x,t) * CKN.spatialLaplacian
        (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
          (CKN.sliceRadius_pos n) (z - y)) x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hts : tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) ⊆ U := by
        rw [CKN.tsupport_mollifier_sub_eq]
        exact hn
      have hx' : x ∉ tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
          (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) :=
        fun hm => hx (hts hm)
      have hLap : CKN.spatialLaplacian
          (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
            (CKN.sliceRadius_pos n) (z - y)) x = 0 := by
        simp only [CKN.spatialLaplacian]
        apply Finset.sum_eq_zero
        intro i _
        have hsub : tsupport (CKN.spatialDeriv
            (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
              (CKN.sliceRadius_pos n) (z - y)) i) ⊆
            tsupport (fun z : Vec3 => CKN.mollifier (d := 3)
              (CKN.sliceRadius n) (CKN.sliceRadius_pos n) (z - y)) :=
          tsupport_fderiv_apply_subset ℝ (CKN.basisVec i)
        exact by
          rw [CKN.spatialDeriv]
          simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hm => hx' (hsub hm))]
      simp [hLap]
    _ = 0 := h

end ESS
