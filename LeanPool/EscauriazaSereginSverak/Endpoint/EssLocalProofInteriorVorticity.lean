/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalTimeProjection

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A CKN regular point has a neighborhood on which the velocity is essentially bounded. -/
theorem essLocal_regularPoint_velocityBound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint}
    (hreg : IsRegularPoint Ω I u z₀) :
    ∃ N : Set ParabolicPoint, IsOpen N ∧ z₀ ∈ N ∧
      N ⊆ spaceTimeSet Ω I ∧ ∃ M : ℝ, 0 ≤ M ∧
        ∀ᵐ z ∂(volume.restrict N), vec3EuclideanNorm (u z) ≤ M := by
  rcases hreg with ⟨_, N, hNopen, hzN, hNsub, _, _, _, w, hAE, hHolder⟩
  rcases hHolder with ⟨M, _, hM, _, hbound, _⟩
  refine ⟨N, hNopen, hzN, hNsub, M, hM, ?_⟩
  filter_upwards [hAE.symm, ae_restrict_mem hNopen.measurableSet] with z hzu hzN
  rw [hzu]
  exact hbound z hzN

/-- At almost every time supplied by the projection theorem, every spatial point
has a neighborhood with an essential velocity bound. -/
theorem essLocal_regularTimes_localVelocityBound
    {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hregular : ∀ᵐ t ∂volume, t ∈ I → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ > 0,
        closure (vec3Ball (0 : Vec3) ρ) ×ˢ Ioo (t - δ) (t + δ) ⊆
          regularPointLocus I u) :
    ∀ᵐ t ∂volume, t ∈ I → ∀ x : Vec3,
      ∃ N : Set ParabolicPoint, IsOpen N ∧ (x, t) ∈ N ∧
        N ⊆ spaceTimeSet Set.univ I ∧ ∃ M : ℝ, 0 ≤ M ∧
          ∀ᵐ z ∂(volume.restrict N), vec3EuclideanNorm (u z) ≤ M := by
  filter_upwards [hregular] with t ht
  intro htI x
  let ρ : ℝ := vec3EuclideanNorm x + 1
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x) (by norm_num)
  obtain ⟨δ, hδ, htube⟩ := ht htI ρ hρ
  have hx : x ∈ closure (vec3Ball (0 : Vec3) ρ) := by
    rw [closure_vec3Ball hρ]
    change vec3EuclideanNorm (x - 0) ≤ ρ
    rw [sub_zero]
    dsimp [ρ]
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  have htime : t ∈ Ioo (t - δ) (t + δ) := by
    constructor <;> linarith only [hδ]
  let z : ParabolicPoint := (x, t)
  have hz : z ∈ closure (vec3Ball (0 : Vec3) ρ) ×ˢ Ioo (t - δ) (t + δ) :=
    ⟨hx, htime⟩
  have hreg : IsRegularPoint Set.univ I u z := by
    have h := htube hz
    change IsRegularPoint Set.univ I u z at h
    exact h
  obtain ⟨N, hNopen, hzt, hNsub, M, hM, hbound⟩ :=
    essLocal_regularPoint_velocityBound hreg
  exact ⟨N, hNopen, hzt, hNsub, M, hM, hbound⟩

/-- A compact subset of the regular-point locus has one essential velocity bound. -/
theorem essLocal_regularCompact_velocityBound
    {I : Set ℝ} {u : ParabolicPoint → Vec3} {K : Set ParabolicPoint}
    (hK : IsCompact K) (hKreg : K ⊆ regularPointLocus I u) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ z ∂(volume.restrict K), vec3EuclideanNorm (u z) ≤ M := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨0, le_rfl, ?_⟩
    simp [hKempty]
  · have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    let Index := {z : ParabolicPoint // z ∈ K}
    choose N hNopen hzN hNsub M hM hbound using
      fun z : Index => essLocal_regularPoint_velocityBound (hKreg z.2)
    have hcover : K ⊆ ⋃ z : Index, N z := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzN ⟨z, hz⟩⟩
    obtain ⟨s, hscover⟩ := hK.elim_finite_subcover N hNopen hcover
    have hsne : s.Nonempty := by
      obtain ⟨z, hz⟩ := hKne
      rcases Set.mem_iUnion₂.mp (hscover hz) with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    let M₀ : ℝ := s.sup' hsne (fun i => M i)
    have hM₀ : 0 ≤ M₀ := by
      obtain ⟨i, hi⟩ := hsne
      exact (hM i).trans (Finset.le_sup' (fun j => M j) hi)
    have hVeq : (⋃ i ∈ s, K ∩ N i) = K := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion₂.mp hz with ⟨i, hi, hz⟩
        exact hz.1
      · intro hz
        rcases Set.mem_iUnion₂.mp (hscover hz) with ⟨i, hi, hzi⟩
        exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hz, hzi⟩⟩
    have hAE : ∀ᵐ z ∂(volume.restrict (⋃ i ∈ s, K ∩ N i)),
        vec3EuclideanNorm (u z) ≤ M₀ := by
      rw [ae_restrict_biUnion_finset_iff]
      intro i hi
      have hlocal : ∀ᵐ z ∂(volume.restrict (K ∩ N i)),
          vec3EuclideanNorm (u z) ≤ M i :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hbound i)
      exact hlocal.mono fun z hz => le_trans hz (Finset.le_sup' (fun j => M j) hi)
    rw [hVeq] at hAE
    exact ⟨M₀, hM₀, hAE⟩

end ESS
