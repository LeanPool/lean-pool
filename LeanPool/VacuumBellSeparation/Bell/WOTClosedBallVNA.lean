/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.KaplanskyContractions
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The actual double commutant from a WOT-closed unit ball

Kaplansky approximation supplies bounded self-adjoint nets in the original
star-subalgebra. Closedness of its literal WOT unit ball captures their
limits. Rescaling and real/imaginary decomposition recover every element
of the double commutant. No normal representation theorem is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_starSubalgebra_of_wot_closed_unitBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    (hu : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S ∧ ‖T.toCLM‖ ≤ 1})
    {A : H →L[ℂ] H} (hA : A ∈ generatedVNA (S : Set (H →L[ℂ] H))) : A ∈ S := by
  classical
  have hsa (T : H →L[ℂ] H)
      (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H)))
      (ht : IsSelfAdjoint T) : T ∈ S := by
    let c : ℝ := ‖T‖ + 1
    have hc : 0 < c := by dsimp only [c]; positivity
    let B : H →L[ℂ] H := c⁻¹ • T
    have hB : B ∈ generatedVNA (S : Set (H →L[ℂ] H)) :=
      starSubalgebra_real_smul_mem
        (generatedVNA (S : Set (H →L[ℂ] H))).toStarSubalgebra hT _
    have hBs : IsSelfAdjoint B := (IsSelfAdjoint.all (c⁻¹)).smul ht
    have hBn : ‖B‖ ≤ 1 := by
      change ‖c⁻¹ • T‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      exact (inv_mul_le_one₀ hc).mpr (by dsimp only [c]; linarith)
    obtain ⟨As, hAs, hlim⟩ := exists_saContraction_strong_approximation S hfc hB hBs hBn
    have hw : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (As i)) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM B)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro x y
      exact tendsto_const_nhds.inner (hlim x)
    have hbmem : B ∈ S :=
      (hu.mem_of_tendsto hw (Eventually.of_forall fun i => ⟨(hAs i).1, (hAs i).2.2⟩)).1
    have hm := starSubalgebra_real_smul_mem S hbmem c
    simpa only [B, smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using hm
  let N := (generatedVNA (S : Set (H →L[ℂ] H))).toStarSubalgebra
  have hr : (realPart A : H →L[ℂ] H) ∈ N := by
    rw [realPart_apply_coe]
    exact starSubalgebra_real_smul_mem N (N.add_mem hA (N.star_mem' hA)) _
  have hi : (imaginaryPart A : H →L[ℂ] H) ∈ N := by
    rw [imaginaryPart_apply_coe]
    exact N.smul_mem
      (starSubalgebra_real_smul_mem N (N.sub_mem hA (N.star_mem' hA)) _) _
  have hrS := hsa _ hr (realPart A).2
  have hiS := hsa _ hi (imaginaryPart A).2
  rw [← realPart_add_I_smul_imaginaryPart A]
  exact S.add_mem hrS (S.smul_mem hiS _)

/-- Norm closedness supplies CFC stability; the resulting VNA has exactly
the original carrier, not a larger replacement carrier. -/
theorem exists_vna_eq_starSubalgebra_of_wot_closed_unitBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    (hu : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S ∧ ‖T.toCLM‖ ≤ 1}) :
    ∃ N : VonNeumannAlgebra H, N.toStarSubalgebra = S := by
  let : IsClosed (S : Set (H →L[ℂ] H)) := hS
  refine ⟨generatedVNA (S : Set (H →L[ℂ] H)), ?_⟩
  apply SetLike.ext
  intro T
  constructor
  · intro hT
    exact mem_starSubalgebra_of_wot_closed_unitBall S
      (fun f A hA => cfc_mem (𝕜' := ℂ) f hA) hu hT
  · intro hT
    change T ∈ (commutantOf (S : Set (H →L[ℂ] H))).commutant
    rw [VonNeumannAlgebra.mem_commutant_iff]
    intro B hB
    exact ((mem_commutantOf_starSubalgebra_iff S B).mp hB T hT).symm

end VacuumBellSeparation
