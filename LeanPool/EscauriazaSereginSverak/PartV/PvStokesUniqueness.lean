/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyComponent
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyGronwall
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergySum

/-!
# Uniqueness for the zero-data heat system

The uniqueness clause of `lem:pv-stokes`: a square-integrable distributional
solution of the homogeneous heat system on `ℝ³ × (0, τ)` with zero initial trace
vanishes. The energy estimate for the linear heat equation with square-integrable
data (the energy argument of `lem:localized-vorticity-energy`) bounds the
squared norm of the continuous `L²` representative by its own time integral, and
Grönwall's inequality forces it to vanish.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped ENNReal Topology


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- A square-integrable distributional solution of `∂ₜw - Δw = 0` on
`ℝ³ × (0, τ)` whose pairings with test functions are continuous on `[0, τ]` and
vanish at `t = 0` vanishes almost everywhere. -/
theorem pvStokes_scalar_heat_unique {τ : ℝ} (hτ : 0 < τ) {w : Vec3 × ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (vlSlab 0 τ)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo 0 τ),
      ∫ p in vlSlab 0 τ, w p * (-CKN.timePartial φ p -
        ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) = 0)
    (htrace : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, w (x, t) * ψ x) :
    w =ᵐ[volume.restrict (vlSlab 0 τ)] 0 := by
  set w' : Vec3 × ℝ → ℝ := hw.aestronglyMeasurable.mk w with hw'def
  have hww' : w =ᵐ[volume.restrict (vlSlab 0 τ)] w' := hw.aestronglyMeasurable.ae_eq_mk
  have hw'm : StronglyMeasurable w' := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hslice := vlSlab_slice_ae_eq hww'
  have sol : VlHeatSolution 0 τ w' (fun _ _ => 0) (fun _ => 0) (fun _ => 0) :=
    { lt := hτ
      w_meas := hw'm
      H_meas := fun _ => stronglyMeasurable_const
      f_meas := stronglyMeasurable_const
      w_L2 := (memLp_congr_ae hww').1 hw
      H_L2 := fun _ => MemLp.zero
      f_L2 := MemLp.zero
      w₀_L2 := MemLp.zero
      weak := by
        intro φ hφ
        have hc : (fun p => w' p * (-CKN.timePartial φ p -
            ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p)) =ᵐ[volume.restrict (vlSlab 0 τ)]
            fun p => w p * (-CKN.timePartial φ p -
              ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) :=
          hww'.mono fun p hp => by simp only [hp]
        rw [integral_congr_ae hc, hweak φ hφ]
        simp
      trace := by
        intro ψ hψ hψc
        obtain ⟨c, hc, hc0, hct⟩ := htrace ψ hψ hψc
        refine ⟨c, hc, by simp [hc0], ?_⟩
        filter_upwards [hct, hslice] with t ht hst
        rw [ht]
        exact integral_congr_ae (hst.mono fun x hx => by simp only [hx]) }
  obtain ⟨Z, D, hZc, -, hZw, -, -, hE⟩ := vlHeat_energy sol
  let e : ℝ → ℝ := fun t => if h : t ∈ Icc 0 τ then ‖Z ⟨t, h⟩‖ ^ 2 else 0
  have he (t : ℝ) (ht : t ∈ Icc 0 τ) : e t = ‖Z ⟨t, ht⟩‖ ^ 2 := by
    change (if h : t ∈ Icc 0 τ then ‖Z ⟨t, h⟩‖ ^ 2 else 0) = _
    split_ifs
    rfl
  have hec : ContinuousOn e (Icc 0 τ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : (Icc 0 τ).domRestrict e = fun t => ‖Z t‖ ^ 2 := by
      funext t
      exact he t.1 t.2
    rw [h]
    exact (hZc.norm).pow 2
  have he0 (t : ℝ) (ht : t ∈ Icc 0 τ) : 0 ≤ e t := by
    rw [he t ht]
    positivity
  have hslice_sq : ∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), (∫ x, (w' (x, s)) ^ 2) = e s := by
    filter_upwards [hZw, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsI' : s ∈ Icc 0 τ := Ioo_subset_Icc_self hsI
    rw [he s hsI', vl_Lp_norm_sq]
    exact integral_congr_ae ((hs hsI').mono fun x hx => by simp only [hx])
  have hineq (t : ℝ) (ht : t ∈ Icc 0 τ) : e t + 0 ≤ 0 + 1 * ∫ s in Ioo 0 t, e s := by
    have h := hE ⟨t, ht⟩
    simp only [vlDataEnergy, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, integral_zero, Finset.sum_const_zero, zero_add, add_zero] at h
    have hDnn : 0 ≤ ∑ j : Fin 3, ∫ p in vlSlab 0 t, (D j p) ^ 2 :=
      Finset.sum_nonneg fun j _ => integral_nonneg fun p => sq_nonneg _
    have hcongr : (∫ s in Ioo 0 t, ∫ x, (w' (x, s)) ^ 2) = ∫ s in Ioo 0 t, e s := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      have hsub : volume.restrict (Ioo 0 t) ≤ volume.restrict (Ioo (0 : ℝ) τ) :=
        Measure.restrict_mono (Ioo_subset_Ioo_right ht.2) le_rfl
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (ae_mono hsub hslice_sq)] with s hs hsI
      exact hs hsI
    rw [he t ht, one_mul, zero_add, add_zero, ← hcongr]
    linarith only [h, hDnn]
  have hg := vl_gronwall hτ.le one_pos hec he0 (fun _ _ => le_rfl) hineq
  have hZ0 (t : ℝ) (ht : t ∈ Icc 0 τ) : Z ⟨t, ht⟩ = 0 := by
    have h1 := hg t ht
    rw [zero_mul, add_zero, he t ht] at h1
    have h2 : ‖Z ⟨t, ht⟩‖ = 0 := by nlinarith only [h1, norm_nonneg (Z ⟨t, ht⟩)]
    exact norm_eq_zero.1 h2
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), ∀ᵐ x ∂(volume : Measure Vec3), w' (x, t) = 0 := by
    filter_upwards [hZw, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have htI' : t ∈ Icc 0 τ := Ioo_subset_Icc_self htI
    have h := ht htI'
    rw [hZ0 t htI'] at h
    filter_upwards [h, Lp.coeFn_zero ℝ 2 (volume : Measure Vec3)] with x hx h0
    rw [← hx, h0]
    rfl
  have hmeasSet : MeasurableSet {q : Vec3 × ℝ | w' (q.1, q.2) = 0} :=
    hw'm.measurable (measurableSet_singleton 0)
  have hprod : ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo (0 : ℝ) τ))),
      w' q = 0 := by
    rw [Measure.ae_prod_iff_ae_ae hmeasSet]
    exact (Measure.ae_ae_comm hmeasSet).2 hae
  rw [← vlSlab_measure] at hprod
  filter_upwards [hww', hprod] with q h1 h2
  rw [h1, h2]
  rfl

/-- The vector form: a square-integrable distributional solution of the
homogeneous heat system on `ℝ³ × (0, τ)` with zero initial trace vanishes. -/
theorem pvStokes_heat_unique {τ : ℝ} (hτ : 0 < τ) {w : Vec3 × ℝ → Vec3}
    (hw : MemLp w 2 (volume.restrict (vlSlab 0 τ)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo 0 τ),
      ∫ p in vlSlab 0 τ, ∑ i : Fin 3, w p i *
        (-CKN.timePartial (fun q => φ q i) p -
          ∑ j : Fin 3, CKN.spatialSecondPartial (fun q => φ q i) j j p) = 0)
    (htrace : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, w (x, t) i * ψ x i) :
    w =ᵐ[volume.restrict (vlSlab 0 τ)] 0 := by
  have hcomp (i : Fin 3) : (fun p => w p i) =ᵐ[volume.restrict (vlSlab 0 τ)] 0 := by
    refine pvStokes_scalar_heat_unique hτ (memLp_pi_iff.1 hw i) (fun φ hφ => ?_) ?_
    · have h := vlVectorWeak_component (a := 0) (τ := τ) (z := w) (v := 0) (g₀ := 0)
        (F := fun _ _ _ => 0) (G := fun _ _ _ => 0) ?_ i hφ
      · rw [h]
        simp
      · intro ψ hψ
        exact (hweak ψ hψ).trans (Eq.symm (by simp))
    · intro ψ hψ hψc
      obtain ⟨c, hc, hca, hct⟩ := vlVectorTrace_component (a := 0) (τ := τ) (z := w)
        (z₀ := 0) (fun ψ hψ hψc => by
          obtain ⟨c, hc, hc0, hct⟩ := htrace ψ hψ hψc
          exact ⟨c, hc, by simp [hc0], hct⟩) i hψ hψc
      exact ⟨c, hc, by simp [hca], hct⟩
  filter_upwards [hcomp 0, hcomp 1, hcomp 2] with p h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end ESS

end
