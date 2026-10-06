/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundSource
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Spatial tails of the velocity–pressure energy

Under the critical bound u ∈ L^∞_t L³_x and p ∈ L^∞_t L^{3/2}_x on a finite
slab, the density |u|³ + |p|^{3/2} is integrable on the slab, so its integral
over {|x| ≥ ρ} × (0, T) tends to zero as ρ → ∞. Consequently the
velocity–pressure energy of every backward cylinder inside the slab and far
enough from the origin is uniformly small, as used in `lem:pv-positive-bound`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The velocity–pressure energy density is integrable on the finite slab. -/
theorem pv_energyDensity_slab_lt_top {T : ℝ} {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    (hPMixed : essSup
      (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) < ⊤ := by
  have hUm : AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hU).aemeasurable)
  have hPm : AEMeasurable (fun z => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have h : AEMeasurable (fun z => ‖p z‖ₑ ^ (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hp.enorm
    simpa only [Function.comp_def, Real.enorm_eq_ofReal_abs] using h
  have hUb := pv_setLIntegral_slab_le hUm
    (ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)))
  have hPb := pv_setLIntegral_slab_le hPm
    (K := essSup (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T))) (by
    have h := ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
    simpa only [Real.enorm_eq_ofReal_abs] using h)
  have hvol : volume (Ioo (0 : ℝ) T) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  rw [lintegral_add_left' hUm]
  exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt hUb (ENNReal.mul_lt_top hvol hL3),
    lt_of_le_of_lt hPb (ENNReal.mul_lt_top hvol hPMixed)⟩

/-- Backward cylinders inside the slab and far from the origin have uniformly
small velocity–pressure energy. -/
theorem pv_tail_goodPointEnergy_small {T : ℝ} {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ}
    (hfin : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ρ : ℝ, ∀ (x₀ : Vec3) (t₀ r : ℝ), ρ + r ≤ vec3EuclideanNorm x₀ →
      r ^ 2 ≤ t₀ → t₀ ≤ T → goodPointEnergy u p x₀ t₀ r ≤ ε := by
  let H : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) + ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)
  let s : ℕ → Set ParabolicPoint := fun n =>
    spaceTimeSet {x : Vec3 | (n : ℝ) ≤ vec3EuclideanNorm x} (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.withDensity H
  have hmeas : ∀ n, MeasurableSet (s n) := fun n =>
    (measurableSet_le measurable_const CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable).prod
      measurableSet_Ioo
  have hanti : Antitone s := by
    intro n m hnm z hz
    exact ⟨show (n : ℝ) ≤ vec3EuclideanNorm z.1 from
      le_trans (Nat.cast_le.mpr hnm) hz.1, hz.2⟩
  have hμs : ∀ n, μ (s n) = ∫⁻ z in s n, H z := fun n => withDensity_apply _ (hmeas n)
  have hfin0 : μ (s 0) ≠ ⊤ := by
    rw [hμs]
    refine ne_top_of_le_ne_top hfin.ne (lintegral_mono_set ?_)
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hinter : ⋂ n, s n = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    refine ⟨⌈vec3EuclideanNorm z.1⌉₊ + 1, fun hz => ?_⟩
    have h1 := hz.1
    have h2 := Nat.le_ceil (vec3EuclideanNorm z.1)
    change ((⌈vec3EuclideanNorm z.1⌉₊ + 1 : ℕ) : ℝ) ≤ vec3EuclideanNorm z.1 at h1
    push_cast at h1
    linarith only [h1, h2]
  have ht := tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet)
    hanti ⟨0, hfin0⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp ht ε hε
  refine ⟨N, fun x₀ t₀ r hx hr ht₀ => ?_⟩
  have hsub : goodPointPastCylinder x₀ t₀ r ⊆ s N := by
    rintro ⟨y, t⟩ ⟨hy, htI⟩
    have hy' : vec3EuclideanNorm (y - x₀) < r := hy
    have htri := vec3EuclideanNorm_sub_le y (y - x₀)
    rw [sub_sub_cancel] at htri
    refine ⟨?_, ?_, ?_⟩
    · change (N : ℝ) ≤ vec3EuclideanNorm y
      linarith only [hx, htri, hy']
    · linarith only [htI.1, hr]
    · linarith only [htI.2, ht₀]
  rw [goodPointEnergy_eq_open_top]
  calc
    _ ≤ ∫⁻ z in s N, H z := lintegral_mono_set hsub
    _ = μ (s N) := (hμs N).symm
    _ ≤ ε := hN N le_rfl

end ESS
