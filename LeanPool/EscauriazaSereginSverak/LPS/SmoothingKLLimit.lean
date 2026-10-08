/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeJensen
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest

/-!
# The time derivative of a strong solution is bounded in `L²` on positive-time slices

`prop:lps-smoothing`: a uniform `L²` bound on the time-difference quotients transfers to the weak
time derivative for almost every time, since the pairings of the quotients converge to the pairing
of the derivative at almost every time.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Slices of a square-integrable slab field are square integrable for almost every time. -/
theorem lps_ae_slice_memLp_of_slab {a b : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b))) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), MemLp (fun x : Vec3 => F (x, t)) 2 volume := by
  have hspaceTime : MemLp F 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hF
  have hsq : Integrable (fun q => ‖F q‖ ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    (memLp_two_iff_integrable_sq_norm hspaceTime.aestronglyMeasurable).1 hspaceTime
  filter_upwards [hspaceTime.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae]
    with t hmeas hint
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hint

/-- A uniform `L²` bound on the time-difference quotients of a strong solution on `[t₁, T - h]`
for all small `h` bounds the weak time derivative in `L²` at almost every time of `(t₁, T)`
(`prop:lps-smoothing`). -/
theorem lps_dtu_slice_bound_of_difference_bound {t₀ T t₁ B h₀ : ℝ} (hT : t₀ < T)
    (ht₁ : t₀ ≤ t₁) {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    (hB : 0 ≤ B) (hh₀ : 0 < h₀)
    (hbound : ∀ h ∈ Ioo 0 h₀, ∀ t ∈ Icc t₁ (T - h), ∀ i : Fin 3,
      ∫ x : Vec3, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2 ≤ B) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₁ T)), ∀ i : Fin 3, ∫ x : Vec3, (Dtu (x, t) i) ^ 2 ≤ B := by
  have hlim := lps_slice_pairing_ae_tendsto_slope hT hu hDt htime hslice hcont
  have hDtsl : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      MemLp (fun x : Vec3 => Dtu (x, t) i) 2 volume := fun i =>
    lps_ae_slice_memLp_of_slab (F := fun z => Dtu z i) (memLp_pi_iff.mp hDt i)
  have hDtall : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i : Fin 3,
      MemLp (fun x : Vec3 => Dtu (x, t) i) 2 volume := ae_all_iff.mpr hDtsl
  have hsub : Ioo t₁ T ⊆ Ioo t₀ T := Ioo_subset_Ioo_left ht₁
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hlim,
    ae_restrict_of_ae_restrict_of_subset hsub hDtall, ae_restrict_mem measurableSet_Ioo]
    with t ht hDtt htmem i
  refine lps_integral_sq_le_of_test_pairing_le (hDtt i) (Real.sqrt_nonneg B) ?_ |>.trans
    (le_of_eq (Real.sq_sqrt hB))
  intro ψ hψ hψc
  have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have htI : t ∈ Icc t₀ T := ⟨(ht₁.trans htmem.1.le), htmem.2.le⟩
  have hquot := ht ψ hψ hψc i
  have hnorm : Tendsto (fun h : ℝ =>
      |(1 / h) * ((∫ x, u (x, t + h) i * ψ x) - ∫ x, u (x, t) i * ψ x)|) (𝓝[>] 0)
      (𝓝 |∫ x, Dtu (x, t) i * ψ x|) := hquot.abs
  refine le_of_tendsto hnorm ?_
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (min h₀ (T - t)) := by
    have hpos : (0 : ℝ) < min h₀ (T - t) := lt_min hh₀ (by linarith only [htmem.2])
    exact Ioo_mem_nhdsGT hpos
  filter_upwards [hev] with h hh
  have hh0 : 0 < h := hh.1
  have hhh₀ : h < h₀ := hh.2.trans_le (min_le_left _ _)
  have hhT : h < T - t := hh.2.trans_le (min_le_right _ _)
  have ht1 : t + h ∈ Icc t₀ T := ⟨by linarith only [htI.1, hh0], by linarith only [hhT]⟩
  have hbd := hbound h ⟨hh0, hhh₀⟩ t ⟨htmem.1.le, by linarith only [hhT]⟩ i
  have hv : MemLp (fun x => (1 / h) * (u (x, t + h) i - u (x, t) i)) 2 volume :=
    (((hslice (t + h) ht1).eval i).sub ((hslice t htI).eval i)).const_mul (1 / h)
  have heq : (1 / h) * ((∫ x, u (x, t + h) i * ψ x) - ∫ x, u (x, t) i * ψ x) =
      ∫ x, ((1 / h) * (u (x, t + h) i - u (x, t) i)) * ψ x := by
    have i1 : Integrable (fun x => u (x, t + h) i * ψ x) volume :=
      ((hslice (t + h) ht1).eval i).integrable_mul hψL
    have i2 : Integrable (fun x => u (x, t) i * ψ x) volume :=
      ((hslice t htI).eval i).integrable_mul hψL
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [heq]
  calc |∫ x, ((1 / h) * (u (x, t + h) i - u (x, t) i)) * ψ x|
      ≤ Real.sqrt (∫ x, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2) *
          Real.sqrt (∫ x, ψ x ^ 2) := lps_abs_integral_pairing_le _ _ hv hψL
    _ ≤ Real.sqrt B * Real.sqrt (∫ x, ψ x ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbd) (Real.sqrt_nonneg _)

end ESS
