/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHilbertEnergyBridge
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallySquareIntegrableForce
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniform energy bounds for the forced regularized solutions

`lem:forced-energy-bounds`: the forced energy inequality `eq:reg-energy-forced`
with `2 f·u ≤ |f|² + |u|²` and Grönwall's inequality bound the kinetic energy
on `[0,T]` by `E_T = e^T (‖a‖₂² + ‖f‖²_{L²((0,T)×ℝ³)})`, and substitution back
into the same inequality bounds the dissipation on `(0,T)` by
`G_T² = (‖a‖₂² + ‖f‖²_{L²((0,T)×ℝ³)} + T E_T) / 2`. Both constants are
independent of the regularization parameter.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Grönwall's inequality in integral form: a function continuous on `[0,T]`
with `y t ≤ K + ∫₀ᵗ y` there satisfies `y t ≤ K e^t` there. -/
private theorem forcedLerayLimit_gronwall (y : ℝ → ℝ) (K T : ℝ) (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, y t ≤ K + ∫ s in (0 : ℝ)..t, y s) :
    ∀ t ∈ Icc 0 T, y t ≤ K * Real.exp t := by
  let c : ℝ → ℝ := fun t => max 0 (min t T)
  have hcmem : ∀ t, c t ∈ Icc 0 T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hc : ∀ t ∈ Icc 0 T, c t = t := fun t ht => by
    simp only [c, min_eq_left ht.2, max_eq_right ht.1]
  let yt : ℝ → ℝ := fun t => y (c t)
  have hytc : Continuous yt :=
    hy.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hcmem
  have hyt : ∀ t ∈ Icc 0 T, yt t = y t := fun t ht => by
    simp only [yt, hc t ht]
  have hint : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, yt s) = ∫ s in (0 : ℝ)..t, y s := by
    intro t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact hyt s ⟨hs.1, hs.2.trans ht.2⟩
  let Y : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, yt s
  have hderiv : ∀ x, HasDerivAt Y (yt x) x := fun x =>
    (hytc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun x =>
    (hderiv x).continuousAt
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := Y) (f' := yt)
    (δ := 0) (K := 1) (ε := K) (a := 0) (b := T) hYc.continuousOn
    (fun x _ _ hr => (hderiv x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [Y])
    (fun x hx => by
      have h1 := hbound x ⟨hx.1, hx.2.le⟩
      rw [← hint x ⟨hx.1, hx.2.le⟩] at h1
      rw [hyt x ⟨hx.1, hx.2.le⟩, one_mul]
      linarith only [h1])
  intro t ht
  have hY := hgron t ht
  rw [gronwallBound_of_K_ne_0 one_ne_zero, sub_zero] at hY
  have h1 := hbound t ht
  rw [← hint t ht] at h1
  change Y t ≤ 0 * Real.exp (1 * t) + K / 1 * (Real.exp (1 * t) - 1) at hY
  rw [zero_mul, zero_add, one_mul, div_one] at hY
  linarith only [h1, hY]

/-- `lem:forced-energy-bounds`: a velocity with continuous `L²` slices, a
square-integrable weak gradient on finite slabs and the forced energy
inequality `eq:reg-energy-forced` satisfies, on every `[0,T]`, the kinetic
bound `‖u(t)‖₂² ≤ E_T` and the dissipation bound `2 ∫₀ᵀ ‖Du‖₂² ≤ 2 G_T²`,
with `E_T` and `G_T` depending only on `T`, `‖a‖₂` and the `L²` norm of `f`
on `(0,T)`. -/
theorem forcedLerayLimit_energy_bounds
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : Continuous (fun t : Set.Ici (0 : ℝ) =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    (hu : ∀ T : ℝ, 0 < T →
      MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : ∀ T : ℝ, 0 < T →
      MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (henergy : ∀ t : ℝ, 0 ≤ t →
      (eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation u Du t).toReal ≤
        (eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^
          (2 : ℕ)).toReal +
        2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ i : Fin 3, f z i * u z i)
    (T : ℝ) (hT : 0 < T) :
    (∀ t ∈ Icc 0 T, ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i ^ 2 ≤
      Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
        ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)) ∧
    2 * (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Du z i j ^ 2) ≤
      (∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
        (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
        T * (Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
          ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)) := by
  let slab : ℝ → Set ParabolicPoint := fun t => spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)
  let A : ℝ := ∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2
  let F : ℝ := ∑ i : Fin 3, ∫ z in slab T, f z i ^ 2
  let K : ℝ := A + F
  let y : ℝ → ℝ := fun t => ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i ^ 2
  have hy0 : ∀ t, 0 ≤ y t := fun t =>
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => setIntegral_nonneg
    (MeasurableSet.univ.prod measurableSet_Ioo) fun z _ => sq_nonneg _
  have hK0 : 0 ≤ K := add_nonneg hA0 hF0
  have hslabLE : ∀ t ∈ Icc 0 T, volume.restrict (slab t) ≤ volume.restrict (slab T) :=
    fun t ht => Measure.restrict_mono_set volume
      (Set.prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2))
  -- continuity of the kinetic energy
  have hycont : ContinuousOn y (Ici 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Ici (0 : ℝ)).domRestrict y = fun t : Set.Ici (0 : ℝ) =>
        ‖realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1))
          (hSlice t.1 t.2)‖ ^ 2 := by
      funext t
      exact (realVectorL2OfCoordinateFunction_norm_sq _ (hSlice t.1 t.2)).symm
    rw [heq]
    exact (continuous_norm.comp hcont).pow 2
  -- the kinetic energy integrates to the slab mass
  have hG : Integrable (fun z : ParabolicPoint => ∑ i : Fin 3, u z i ^ 2)
      (volume.restrict (slab T)) :=
    integrable_finsetSum _ fun i _ => ((hu T hT).eval i).integrable_sq
  have hmass : ∀ t ∈ Icc 0 T,
      ∫ z in slab t, ∑ i : Fin 3, u z i ^ 2 = ∫ s in (0 : ℝ)..t, y s := by
    intro t ht
    rw [forcedHopf_setIntegral_slab_eq_intervalIntegral Set.univ T _ hG t ht]
    have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ T := by
      rw [ae_iff]
      simp
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with τ hτT hτ
    rw [uIoc_of_le ht.1] at hτ
    have hτmem : τ ∈ Ioo 0 T := ⟨hτ.1, lt_of_le_of_ne (hτ.2.trans ht.2) hτT⟩
    rw [indicator_of_mem hτmem, Measure.restrict_univ]
    exact integral_finsetSum _ fun i _ =>
      ((hSlice τ hτmem.1.le).eval i).integrable_sq
  -- the energy inequality in real form, with the work bounded
  have hreal : ∀ t ∈ Icc 0 T, y t + 2 * (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in slab t, Du z i j ^ 2) ≤ K + ∫ s in (0 : ℝ)..t, y s := by
    intro t ht
    have hDt : MemLp Du 2 (volume.restrict (slab t)) :=
      (hDu T hT).mono_measure (hslabLE t ht)
    have hut : MemLp u 2 (volume.restrict (slab t)) :=
      (hu T hT).mono_measure (hslabLE t ht)
    have hft : MemLp f 2 (volume.restrict (slab t)) :=
      (hf T hT).mono_measure (hslabLE t ht)
    have hE := forcedHopf_energy_real_of_regularised ρ ε hε a ha u f Du t
      (hSlice t ht.1) hDt (henergy t ht.1)
    have hfu : ∀ i : Fin 3, Integrable (fun z => f z i * u z i) (volume.restrict (slab t)) :=
      fun i => (hft.eval i).integrable_mul (hut.eval i)
    have hf2 : ∀ i : Fin 3, Integrable (fun z => f z i ^ 2) (volume.restrict (slab t)) :=
      fun i => (hft.eval i).integrable_sq
    have hu2 : ∀ i : Fin 3, Integrable (fun z => u z i ^ 2) (volume.restrict (slab t)) :=
      fun i => (hut.eval i).integrable_sq
    have hwork : 2 * ∫ z in slab t, ∑ i : Fin 3, f z i * u z i ≤
        (∑ i : Fin 3, ∫ z in slab t, f z i ^ 2) + ∫ z in slab t, ∑ i : Fin 3, u z i ^ 2 := by
      rw [← integral_finsetSum _ fun i _ => hf2 i, ← integral_const_mul,
        ← integral_add (integrable_finsetSum _ fun i _ => hf2 i)
          (integrable_finsetSum _ fun i _ => hu2 i)]
      refine integral_mono ((integrable_finsetSum _ fun i _ => hfu i).const_mul 2)
        ((integrable_finsetSum _ fun i _ => hf2 i).add
          (integrable_finsetSum _ fun i _ => hu2 i)) fun z => ?_
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith only [sq_nonneg (f z i - u z i)]
    have hFt : (∑ i : Fin 3, ∫ z in slab t, f z i ^ 2) ≤ F := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact setIntegral_mono_set ((hf T hT).eval i).integrable_sq
        (Eventually.of_forall fun z => sq_nonneg _)
        (Eventually.of_forall (Set.prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2)))
    rw [hmass t ht] at hwork
    change y t + _ ≤ A + _ at hE
    linarith only [hE, hwork, hFt]
  have hG0 : ∀ t, 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in slab t, Du z i j ^ 2 := fun t =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => setIntegral_nonneg
      (MeasurableSet.univ.prod measurableSet_Ioo) fun z _ => sq_nonneg _
  have hkin : ∀ t ∈ Icc 0 T, y t ≤ K * Real.exp t :=
    forcedLerayLimit_gronwall y K T hT.le (hycont.mono Icc_subset_Ici_self)
      fun t ht => by
        have h := hreal t ht
        have h0 := hG0 t
        linarith only [h, h0]
  have hkinT : ∀ t ∈ Icc 0 T, y t ≤ Real.exp T * K := fun t ht => by
    have h := hkin t ht
    have hexp : Real.exp t ≤ Real.exp T := Real.exp_le_exp.2 ht.2
    have := mul_le_mul_of_nonneg_left hexp hK0
    linarith only [h, this]
  refine ⟨hkinT, ?_⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hint : ∫ s in (0 : ℝ)..T, y s ≤ T * (Real.exp T * K) := by
    have h := intervalIntegral.integral_mono_on hT.le
      ((hycont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hT.le)
      (intervalIntegrable_const (μ := (volume : Measure ℝ)) (c := Real.exp T * K)) hkinT
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    exact h
  have h := hreal T hTmem
  have hy := hy0 T
  change y T + 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∫ z in slab T, Du z i j ^ 2) ≤ A + F + _ at h
  change 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∫ z in slab T, Du z i j ^ 2) ≤ A + F + T * (Real.exp T * K)
  linarith only [h, hy, hint]

end CKN.Leray

end
