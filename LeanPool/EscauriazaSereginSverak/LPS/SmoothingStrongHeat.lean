/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingStrongFamily
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTestLp
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainLeibniz

/-!
# The heat equation with source for a strong solution

`prop:lps-smoothing`: with `G = ∂ₜu - Δu` (in `L²`), each velocity component of a strong
solution is a distributional solution of `∂ₜ uᵢ - Δ uᵢ = Gᵢ` on the slab.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Each velocity component of a strong solution solves the heat equation with source
`Dtu - Δu` in distributions on the slab (`prop:lps-smoothing`). -/
theorem lps_strong_isHeatSolution {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (i : Fin 3) :
    IsHeatSolutionOn (Set.univ : Set Vec3) (Ioo t₀ T) (fun z => u z i)
      (fun z => Dtu z i - ∑ j : Fin 3, D2u z i j j) := by
  obtain ⟨-, -, -, -, hweak⟩ := hderiv
  intro ψ hψ hψc hψI
  set μ : Measure (Vec3 × ℝ) :=
    volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T) with hμ
  have hui : MemLp (fun z : ParabolicPoint => u z i) 2 μ := memLp_pi_iff.mp hu i
  have hDtui : MemLp (fun z : ParabolicPoint => Dtu z i) 2 μ := memLp_pi_iff.mp hDtu i
  have hψt : ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T) :=
    ⟨hψ, hψc, hψI⟩
  -- the first spatial partial of the test is again a test
  have hdt : ∀ j : Fin 3, (fun z : ParabolicPoint => spatialPartial (fun p : ParabolicPoint => ψ p) j z) ∈
      spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T) := by
    intro j
    refine ⟨vorticityHeatSmooth_spatialPartial_contDiff hψ j,
      hasCompactSupport_spatialPartial hψc j, ?_⟩
    exact (tsupport_spatialPartial_subset j).trans hψI
  have hψtime : MemLp (timePartial (fun p : ParabolicPoint => ψ p)) 2 μ :=
    (lps_spaceTimeTest_spatial_memLp_two (CKN.contDiff_timePartial hψ)
      (CKN.hasCompactSupport_timePartial hψc) (Ioo t₀ T)).1
  have hψ2 : ∀ j : Fin 3, MemLp (fun z : ParabolicPoint =>
      spatialSecondPartial (fun p : ParabolicPoint => ψ p) j j z) 2 μ := fun j =>
    (lps_spaceTimeTest_spatial_memLp_two (vorticityHeatSmooth_spatialPartial_contDiff hψ j)
      (hasCompactSupport_spatialPartial hψc j) (Ioo t₀ T)).2 j
  have hψ0 : MemLp (fun p : ParabolicPoint => ψ p) 2 μ :=
    (lps_spaceTimeTest_spatial_memLp_two hψ hψc (Ioo t₀ T)).1
  have hψ1 : ∀ j : Fin 3, MemLp (fun z : ParabolicPoint =>
      spatialPartial (fun p : ParabolicPoint => ψ p) j z) 2 μ := fun j =>
    (lps_spaceTimeTest_spatial_memLp_two hψ hψc (Ioo t₀ T)).2 j
  -- weak identities
  have ht := (hweak ψ hψt).2.2 i
  have hj : ∀ j : Fin 3,
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
          u z i * spatialSecondPartial (fun p : ParabolicPoint => ψ p) j j z) =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), D2u z i j j * ψ z := by
    intro j
    have h1 := (hweak _ (hdt j)).1 i j
    have h2 := (hweak ψ hψt).2.1 i j j
    change (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        u z i * spatialPartial (fun w => spatialPartial (fun p : ParabolicPoint => ψ p) j w) j z) = _
    rw [h1]
    have h3 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        Du z i j * spatialPartial (fun p : ParabolicPoint => ψ p) j z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), D2u z i j j * ψ z := h2
    rw [h3, neg_neg]
  have hDu2 : ∀ j : Fin 3, MemLp (fun z : ParabolicPoint => D2u z i j j) 2 μ := fun j =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp hD2u i) j) j
  change (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, u z i * (-timePartial ψ z -
      ∑ j : Fin 3, spatialSecondPartial ψ j j z)) =
    ∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, (Dtu z i - ∑ j : Fin 3, D2u z i j j) * ψ z
  have hL1 : Integrable (fun z : Vec3 × ℝ => -(u z i * timePartial ψ z)) μ :=
    (hui.integrable_mul hψtime).neg
  have hL2 : ∀ j : Fin 3, Integrable (fun z : Vec3 × ℝ =>
      u z i * spatialSecondPartial ψ j j z) μ := fun j => hui.integrable_mul (hψ2 j)
  have hR1 : Integrable (fun z : Vec3 × ℝ => Dtu z i * ψ z) μ := hDtui.integrable_mul hψ0
  have hR2 : ∀ j : Fin 3, Integrable (fun z : Vec3 × ℝ => D2u z i j j * ψ z) μ :=
    fun j => (hDu2 j).integrable_mul hψ0
  have hlhs : (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, u z i * (-timePartial ψ z -
      ∑ j : Fin 3, spatialSecondPartial ψ j j z)) =
      -(∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, u z i * timePartial ψ z) -
        ∑ j : Fin 3, ∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T,
          u z i * spatialSecondPartial ψ j j z := by
    have : ∀ z : Vec3 × ℝ, u z i * (-timePartial ψ z -
        ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -(u z i * timePartial ψ z) - ∑ j : Fin 3, u z i * spatialSecondPartial ψ j j z := by
      intro z
      rw [mul_sub, Finset.mul_sum]
      ring
    rw [integral_congr_ae (ae_of_all _ this)]
    rw [integral_sub hL1 (integrable_finsetSum _ fun j _ => hL2 j), integral_neg,
      integral_finsetSum _ fun j _ => hL2 j]
  have hrhs : (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, (Dtu z i - ∑ j : Fin 3, D2u z i j j) * ψ z) =
      (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, Dtu z i * ψ z) -
        ∑ j : Fin 3, ∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, D2u z i j j * ψ z := by
    have : ∀ z : Vec3 × ℝ, (Dtu z i - ∑ j : Fin 3, D2u z i j j) * ψ z =
        Dtu z i * ψ z - ∑ j : Fin 3, D2u z i j j * ψ z := by
      intro z
      rw [sub_mul, Finset.sum_mul]
    rw [integral_congr_ae (ae_of_all _ this)]
    rw [integral_sub hR1 (integrable_finsetSum _ fun j _ => hR2 j),
      integral_finsetSum _ fun j _ => hR2 j]
  rw [hlhs, hrhs]
  have hj' : ∀ j : Fin 3, (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T,
      u z i * spatialSecondPartial ψ j j z) =
      ∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, D2u z i j j * ψ z := hj
  simp_rw [hj']
  have ht' : (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, u z i * timePartial ψ z) =
      -∫ z in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, Dtu z i * ψ z := ht
  rw [ht', neg_neg]

end ESS
