/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSliceGrad
public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalTenThirds

/-!
# The rough forced heat response in the finite-energy class

For a tensor `G ∈ L^{5/2} ∩ L²` supported in the slab `ℝ³ × (0, τ)`, the forced
heat response `Z = forcedHeat G` has square integrable time slices with a
uniform bound, lies in `L²` of the slab, and has a spatial gradient `DZ ∈ L²`
of the slab which is the weak gradient of almost every time slice and with
which `Z` solves `∂_t Z_i - ΔZ_i = ∑_j ∂_j G_ij` weakly. These are the
properties of the forced part of the Duhamel fixed point used in
`prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Square integrability in terms of the integral of the squared norm. -/
theorem memLp_two_iff_lintegral_enorm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top hf
  rw [ENNReal.toReal_ofNat] at h
  rw [memLp_iff]
  exact h

/-- The time slices of the rough forced heat response are square integrable,
with a bound uniform in almost every time of the slab. -/
theorem forcedHeat_rough_slice_energy {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG52 : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      MemLp (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ∧
        ∫⁻ x, ‖forcedHeat G (x, t)‖ₑ ^ (2 : ℝ) ≤ K := by
  obtain ⟨C, _, hest⟩ := forcedHeat_rough_estimates
  obtain ⟨-, -, -, -, -, hslice, -⟩ := hest τ hτ G hG52 hG2 hGsupp
  set B : ℝ≥0∞ := ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
    (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))
  have hGm : MemLp (fun z => fun i j => G i j z) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
    memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => (hG2 i j).restrict _
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGm.eLpNorm_ne_top
  refine ⟨B ^ (2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB, ?_⟩
  filter_upwards [hslice] with t ht
  have hm : AEStronglyMeasurable (fun x : Vec3 => forcedHeat G (x, t)) volume :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top hB ht)
  refine ⟨memLp_iff.2 (lt_of_le_of_lt ht hB.lt_top), ?_⟩
  rw [lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) hm, ENNReal.ofReal_ofNat]
  exact ENNReal.rpow_le_rpow ht (by norm_num)

/-- The rough forced heat response is square integrable on the slab. -/
theorem forcedHeat_rough_memLp_two {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG52 : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    MemLp (forcedHeat G) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  obtain ⟨C, _, hest⟩ := forcedHeat_rough_estimates
  obtain ⟨h5, -⟩ := hest τ hτ G hG52 hG2 hGsupp
  obtain ⟨K, hK, hslice⟩ := forcedHeat_rough_slice_energy hτ hG52 hG2 hGsupp
  have hm := h5.aestronglyMeasurable
  rw [memLp_two_iff_lintegral_enorm_sq hm,
    lintegral_spaceTimeSet_univ_eq (hm.enorm.pow_const _)]
  calc
    ∫⁻ t in Ioo 0 τ, ∫⁻ x, ‖forcedHeat G (x, t)‖ₑ ^ (2 : ℝ) ≤ ∫⁻ _ in Ioo 0 τ, K :=
      lintegral_mono_ae (hslice.mono fun t ht => ht.2)
    _ = K * volume (Ioo 0 τ) := setLIntegral_const _ _
    _ < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top

/-- The rough forced heat response has a square integrable spatial gradient on
the slab, which is the weak gradient of almost every time slice, and with which
it solves `∂_t Z_i - ΔZ_i = ∑_j ∂_j G_ij` weakly on the slab. -/
theorem forcedHeat_rough_solution {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG52 : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    ∃ DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (DZ i j) 2
        (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ i : Fin 3,
        CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcedHeat G (x, s) i)
          (fun x => fun j => DZ i j (x, s))) ∧
      ∀ φ : ParabolicPoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p) →
        HasCompactSupport (fun p : Vec3 × ℝ => φ p) →
        tsupport (fun p : Vec3 × ℝ => φ p) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ →
        ∀ i, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
          (-(forcedHeat G z i * CKN.timePartial φ z) +
            ∑ j : Fin 3, DZ i j z * CKN.spatialPartial φ j z +
            ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z) = 0 := by
  obtain ⟨C, _, hgrad⟩ := forcedHeat_rough_gradient
  obtain ⟨Gs, DZ, hGs, hGsc, hGspos, hGsconv, hDZsmem, hDZmem, hDZlim, -⟩ :=
    hgrad τ hτ G hG52 hG2 hGsupp
  exact ⟨DZ, hDZmem, forcedHeat_slice_weakGradient_of_approx hτ hG2 hGsupp hGs hGsc hGspos
    hGsconv hDZmem hDZlim, fun φ hφ hφc hφQ => (forcedHeat_rough_weak_of_gradient hτ hG2 hGsupp
      hGs hGsc hGspos hGsconv hDZsmem hDZmem hDZlim φ hφ hφc hφQ).2⟩

end ESS

end
