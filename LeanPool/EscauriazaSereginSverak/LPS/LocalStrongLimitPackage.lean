/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitDerivs
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongShift

/-!
# The compactness limit with all its space-time weak derivatives

The compactness limit of the regularized velocities, with its Leray--Hopf gradient, the weak limit
of the Hessians, and the weak limit of the time derivatives, satisfies the space-time weak
derivative relations of `HasSpaceTimeWeakDerivs` with square integrable fields
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The compactness limit, its gradient, the weak limit of the Hessians and the weak limit of the
time derivatives have the space-time weak derivative relations and are square integrable on the
slab (`prop:lps-local-strong`). -/
theorem lps_strong_limit_weak_derivatives
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧ CKN.IsInJ b)
    (T M : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hUniformBounds :
      ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hb.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => Uε y i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j =>
          fun k => spatialPartial
            (fun y => spatialPartial (fun x => Uε x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M) :
    ∃ σ₀ : ℕ → ℕ, StrictMono σ₀ ∧
      ∃ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtu : ParabolicPoint → Vec3),
        (∀ x : Vec3, u (x, 0) = b x) ∧
        CKN.IsLerayHopfSolution T b u Du ∧
        CKN.HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo 0 T) u Du D2u Dtu ∧
        MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3, MemLp w 2 volume →
          Tendsto
            (fun n => ∫ x : Vec3, ∑ i : Fin 3,
              CKN.Leray.regR12Uε ρ b hb.2
                ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ₀ n)) (x, t) i * w x i)
            atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y => CKN.Leray.regR12Uε ρ b hb.2
                ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ₀ n))
                (parabolicHomeomorph.symm y)) σ₀ z) := by
  obtain ⟨σ, hσ, u, Du, htrace, hLH, huMem, hDuMem, hUconv, hDweak, D2u, hD2mem, hD2weak,
    σ₀, hσ₀, hweakSlice, hrep⟩ :=
    lps_strong_limit_hessian_weak_compactness ρ b Db hb T M hT hM hUniformBounds
  obtain ⟨Dtu, hDtmem, hDtid⟩ :=
    lps_strong_limit_time_derivative ρ b Db hb T M hT hUniformBounds huMem hUconv
  refine ⟨σ₀, hσ₀, u, Du, D2u, Dtu, htrace, hLH, ⟨lps_locallyIntegrableOn_of_memLp huMem,
    lps_locallyIntegrableOn_of_memLp hDuMem, lps_locallyIntegrableOn_of_memLp hD2mem,
    lps_locallyIntegrableOn_of_memLp hDtmem, ?_⟩, huMem, hDuMem, hD2mem, hDtmem, hweakSlice,
    hrep⟩
  intro φ hφ
  refine ⟨fun i j => ?_, fun i j k => ?_, fun i => hDtid φ hφ i⟩
  · -- first derivative, from the weak gradients of the time slices
    have hslice := hLH.2.2.2.2.2.2.1
    have hsub : ∀ a' b' : ℝ, 0 < a' → b' < T → vlSlab a' b' ⊆ vlSlab 0 T := fun a' b' ha hb' z hz =>
      ⟨hz.1, ⟨by linarith only [ha, hz.2.1], by linarith only [hb', hz.2.2]⟩⟩
    refine lps_slab_spatial_weak_of_slices hT j
      (F := fun z : Vec3 × ℝ => u z i) (G := fun z : Vec3 × ℝ => Du z i j) ?_ ?_ ?_ hφ
    · filter_upwards [hslice] with s hs
      exact hs i j
    · intro a' b' ha hab hb'
      exact ((memLp_pi_iff.1 huMem) i).mono_measure (Measure.restrict_mono (hsub a' b' ha hb')
        le_rfl)
    · intro a' b' ha hab hb'
      exact ((memLp_pi_iff.1 ((memLp_pi_iff.1 hDuMem) i)) j).mono_measure
        (Measure.restrict_mono (hsub a' b' ha hb') le_rfl)
  · -- second derivative, from the weak limits along the compactness subsequence
    have hφ2 : MemLp φ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      (lps_test_memLp_slab hφ 0).1
    have hφk : MemLp (fun z => spatialPartial φ k z) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      (lps_test_memLp_slab hφ k).2.1
    have h1 := hDweak i j (fun z => spatialPartial φ k z) hφk
    have h2 := hD2weak i j k φ hφ2
    have hEq : ∀ n : ℕ,
        (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          spatialPartial (fun y => CKN.Leray.regR12Uε ρ b hb.2
            ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) y i) j z * spatialPartial φ k z) =
        -∫ z, spatialPartial (fun y => spatialPartial
          (fun x => CKN.Leray.regR12Velocity ρ (1 / ((σ n : ℝ) + 1)) (by positivity) b hb.2 x i)
            j y) k z * φ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
      intro n
      have hεp : 0 < ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) := by positivity
      have hU : CKN.Leray.regR12Uε ρ b hb.2 ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) =
          fun z => lpsRegU ρ ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) hεp b hb.2 z := by
        unfold CKN.Leray.regR12Uε
        exact dite_eq_left_of_eq_true (eq_true hεp)
      simp only [hU]
      exact lps_regR12_hessian_ibp ρ _ hεp b hb.2 hT i j k hφ
    have h3 := h2.neg
    have h4 := tendsto_nhds_unique h1 (h3.congr fun n => (hEq n).symm)
    rw [h4]

end ESS.LPS

end
