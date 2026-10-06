/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticPairing
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticDiv
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.SelfTransportFour
public import LeanPool.EscauriazaSereginSverak.LPS.OverlapStrongSerrin

/-!
# The kinetic energy identity of a strong solution

The mollified equation, paired with the mollified velocity, passes to the
limit on almost every time slice, where the transport and pressure terms vanish
and the Laplacian pairs to minus the squared gradient
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Almost every time slice of a square-integrable slab field is square
integrable, for fields that are only almost everywhere strongly measurable. -/
theorem lps_slab_slice_memLp_aem {a b : ℝ} {f : Vec3 × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (vlSlab a b))) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), MemLp (fun x => f (x, t)) 2 volume := by
  have hsq := hf.integrable_sq
  have hm := hf.aestronglyMeasurable
  rw [vlSlab_measure] at hsq hm
  filter_upwards [hm.prodMk_right, hsq.prod_left_ae] with t hmeas hint
  exact (memLp_two_iff_integrable_sq hmeas).2 hint

/-- Every closed-interval slice of a strong solution is a Serrin slice, and
its velocity is in `L⁴`. -/
theorem lps_strong_slice_serrin {t₀ T t : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) (ht : t ∈ Icc t₀ T) :
    SerrinSlice (fun x : Vec3 => u (x, t)) (fun x => Du (x, t)) ∧
      MemLp (fun x : Vec3 => u (x, t)) (ENNReal.ofReal 4) volume := by
  obtain ⟨hw2, hDw2, hH1⟩ := lps_strong_solution_slice_h1 hU ht
  have hdiv := lps_strong_solution_slice_weak_div_free hU ht
  have hgrad := lps_strong_solution_slice_weak_gradient hU ht
  refine ⟨⟨hw2, hDw2, hgrad, lps_weak_gradient_trace_zero hdiv hDw2 hgrad⟩, ?_⟩
  have h6 := ESS.LPS.lps_regularised_h1_vector_six_bound hw2 hDw2 hH1
  have hSob : (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm (fun x : Vec3 => Du (x, t)) 2
      volume < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
      (lt_top_iff_ne_top.2 CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top))
      hDw2.eLpNorm_lt_top
  have hu6 : MemLp (fun x : Vec3 => u (x, t)) 6 volume := lt_of_le_of_lt h6 hSob
  have h2 : MemLp (fun x : Vec3 => u (x, t)) 2 volume := hw2
  have hle2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal 4 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hle6 : ENNReal.ofReal 4 ≤ (6 : ℝ≥0∞) := by
    rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact serrin_memLp_interpolate (p := 2) (q := 6) (r := ENNReal.ofReal 4) (by norm_num)
    (by norm_num) hle2 hle6 h2 hu6

/-- On almost every time slice, the pairing of the time derivative with the
velocity is minus the squared gradient (`prop:lps-local-strong`). -/
theorem lps_strong_kinetic_slice
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hp : MemLp p 2 (volume.restrict (vlSlab t₀ T))) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      ∑ i : Fin 3, ∫ x : Vec3, Dtu (x, t) i * u (x, t) i =
        -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, (Du (x, t) i j) ^ 2 := by
  have hweak := hDerivs.2.2.2.2
  have hsliceDt : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i : Fin 3,
      MemLp (fun x : Vec3 => Dtu (x, t) i) 2 volume :=
    ae_all_iff.2 fun i => lps_slab_slice_memLp_aem (hDt i)
  have hsliceD2 : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => D2u (x, t) i j j) 2 volume :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => lps_slab_slice_memLp_aem (hD2 i j)
  have hsliceP := lps_slab_slice_memLp_aem hp
  have hM : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ (n : ℕ) (i : Fin 3), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlMoll n) (fun y : Vec3 => Dtu (y, t) i) x +
        ∑ j : Fin 3, vlConv (vlDeriv (vlMoll n) j)
          (fun y : Vec3 => u (y, t) i * u (y, t) j) x -
        ∑ j : Fin 3, vlConv (vlMoll n) (fun y : Vec3 => D2u (y, t) i j j) x +
        vlConv (vlDeriv (vlMoll n) i) (fun y : Vec3 => p (y, t)) x = 0 :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i =>
      lps_strong_mollified_equation_slice hU hDerivs hu hDu hD2 hDt hp i (vlMoll_kernel n)
  have hG1 : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ (n : ℕ) (i j : Fin 3),
      ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv (vlMoll n) j) (fun y : Vec3 => u (y, t) i) x =
        vlConv (vlMoll n) (fun y : Vec3 => Du (y, t) i j) x :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      lps_conv_first_deriv_ae_aem j (hu i) (hDu i j)
        (fun φ hφ => (hweak φ hφ).1 i j) (vlMoll_kernel n)
  have hH1 : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ (n : ℕ) (i j : Fin 3),
      ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv (vlMoll n) j) (fun y : Vec3 => Du (y, t) i j) x =
        vlConv (vlMoll n) (fun y : Vec3 => D2u (y, t) i j j) x :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      lps_conv_first_deriv_ae_aem j (hDu i j) (hD2 i j)
        (fun φ hφ => (hweak φ hφ).2.1 i j j) (vlMoll_kernel n)
  filter_upwards [hsliceDt, hsliceD2, hsliceP, hM, hG1, hH1,
    ae_restrict_mem measurableSet_Ioo] with t hW hH hP hMt hG1t hH1t htI
  have ht : t ∈ Icc t₀ T := Ioo_subset_Icc_self htI
  obtain ⟨hSerrin, hu4⟩ := lps_strong_slice_serrin hU ht
  have hUi : ∀ i : Fin 3, MemLp (fun x : Vec3 => u (x, t) i) 2 volume :=
    fun i => memLp_pi_iff.1 hSerrin.mem2 i
  have hGij : ∀ i j : Fin 3, MemLp (fun x : Vec3 => Du (x, t) i j) 2 volume :=
    fun i j => memLp_pi_iff.1 (memLp_pi_iff.1 hSerrin.grad2 i) j
  have hFij : ∀ i j : Fin 3, MemLp (fun x : Vec3 => u (x, t) i * u (x, t) j) 2 volume := by
    intro i j
    have _ : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4) (ENNReal.ofReal 2) :=
      serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h : MemLp (fun x : Vec3 => u (x, t) i * u (x, t) j) (ENNReal.ofReal 2) volume :=
      (hu4.eval i).mul (hu4.eval j)
    simpa using h
  have hdiv := lps_strong_solution_slice_weak_div_free hU ht
  have hmain := lps_slice_energy_limit (U := fun i x => u (x, t) i)
    (W := fun i x => Dtu (x, t) i) (G := fun i j x => Du (x, t) i j)
    (H := fun i j x => D2u (x, t) i j j) (F := fun i j x => u (x, t) i * u (x, t) j)
    (P := fun x => p (x, t)) hUi hW hGij hH hFij hP hMt hG1t hH1t
    (fun n => Eventually.of_forall fun x => lps_conv_div_free hdiv (vlMoll_kernel n) x)
  have htrans : ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, u (x, t) i * u (x, t) j * Du (x, t) i j = 0 := by
    have h := lps_slice_self_transport_four hSerrin hu4
    have hint : ∀ i j : Fin 3, Integrable
        (fun x : Vec3 => u (x, t) i * u (x, t) j * Du (x, t) i j) volume :=
      fun i j => (hFij i j).integrable_mul (hGij i j)
    have hrw : (fun x : Vec3 => ∑ k : Fin 3, u (x, t) k * ∑ j : Fin 3, u (x, t) j * Du (x, t) k j) =
        fun x => ∑ i : Fin 3, ∑ j : Fin 3, u (x, t) i * u (x, t) j * Du (x, t) i j := by
      funext x
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrw] at h
    rw [← h, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint i j).symm
  have hmain' : ∑ i : Fin 3, ∫ x : Vec3, Dtu (x, t) i * u (x, t) i =
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, u (x, t) i * u (x, t) j * Du (x, t) i j) -
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, (Du (x, t) i j) ^ 2 := hmain
  rw [htrans] at hmain'
  linarith only [hmain']

end ESS.LPS

end
