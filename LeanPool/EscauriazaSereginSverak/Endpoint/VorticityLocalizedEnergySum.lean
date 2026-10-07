/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyGronwall

/-!
# Summing the component energies

The data energies of the three component heat equations of the localized
vorticity equation sum to at most
`‖z₀‖² + 3‖F‖² + 3‖G‖² + ‖g₀‖² + (36 M² + 1) ∫ₐᵗ ‖z(s)‖² ds`, since the drift flux
satisfies `|vⱼ zᵢ - zⱼ vᵢ| ≤ M (|zᵢ| + |zⱼ|)` (`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- The squared `L²` norm of an element of `L²`. -/
theorem vl_Lp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ((f : α → ℝ) x) ^ 2 ∂μ := by
  have h := vl_norm_toLp_sq (Lp.memLp f)
  rwa [Lp.toLp_coeFn] at h

private theorem vl_sq_three (x y b : ℝ) : (x + y - b) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * b ^ 2 := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (x + b), sq_nonneg (y + b)]

private theorem vl_flux_sq_le {M : ℝ} {v z : Vec3} (hv : vec3EuclideanNorm v ≤ M) (i j : Fin 3) :
    (v j * z i - z j * v i) ^ 2 ≤ 2 * M ^ 2 * (z i) ^ 2 + 2 * M ^ 2 * (z j) ^ 2 := by
  have h := vl_flux_abs_le (z := z) hv i j
  have h0 : 0 ≤ |v j * z i - z j * v i| := abs_nonneg _
  have hsq := pow_le_pow_left₀ h0 h 2
  rw [sq_abs] at hsq
  have hM : (M * |z i| + M * |z j|) ^ 2 ≤ 2 * M ^ 2 * (z i) ^ 2 + 2 * M ^ 2 * (z j) ^ 2 := by
    nlinarith only [sq_nonneg (M * |z i| - M * |z j|), sq_abs (z i), sq_abs (z j)]
  exact hsq.trans hM

/-- The pointwise bound on the component fluxes. -/
theorem vl_flux_total_le {M : ℝ} {v z : Vec3} {F G : Fin 3 → Fin 3 → ℝ}
    (hv : vec3EuclideanNorm v ≤ M) :
    ∑ i : Fin 3, ∑ j : Fin 3, (F j i + G j i - (v j * z i - z j * v i)) ^ 2 ≤
      3 * (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) + 3 * (∑ j : Fin 3, ∑ i : Fin 3, (G j i) ^ 2) +
        36 * M ^ 2 * ∑ i : Fin 3, (z i) ^ 2 := by
  have h1 : ∀ i j : Fin 3, (F j i + G j i - (v j * z i - z j * v i)) ^ 2 ≤
      3 * (F j i) ^ 2 + 3 * (G j i) ^ 2 +
        (6 * M ^ 2 * (z i) ^ 2 + 6 * M ^ 2 * (z j) ^ 2) := fun i j => by
    have h3 := vl_sq_three (F j i) (G j i) (v j * z i - z j * v i)
    have hf := vl_flux_sq_le (z := z) hv i j
    linarith only [h3, hf]
  calc
    ∑ i : Fin 3, ∑ j : Fin 3, (F j i + G j i - (v j * z i - z j * v i)) ^ 2 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, (3 * (F j i) ^ 2 + 3 * (G j i) ^ 2 +
          (6 * M ^ 2 * (z i) ^ 2 + 6 * M ^ 2 * (z j) ^ 2)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = 3 * (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) +
        3 * (∑ j : Fin 3, ∑ i : Fin 3, (G j i) ^ 2) +
        36 * M ^ 2 * ∑ i : Fin 3, (z i) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring

/-- The component flux of the localized vorticity equation. -/
@[expose] def vlCompFlux (z v : Vec3 × ℝ → Vec3) (F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    Fin 3 → Vec3 × ℝ → ℝ :=
  fun j p => F p j i + G p j i - (v p j * z p i - z p j * v p i)

/-- The data energy of a heat solution as slab integrals. -/
theorem vlDataEnergy_eq_slab {a τ t : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    {w₀ : Vec3 → ℝ} (sol : VlHeatSolution a τ w H f w₀) (ht : t ∈ Icc a τ) :
    vlDataEnergy w₀ w H f a t = (∫ x, (w₀ x) ^ 2) +
      ((∑ j : Fin 3, ∫ p in vlSlab a t, (H j p) ^ 2) + (∫ p in vlSlab a t, (w p) ^ 2) +
        ∫ p in vlSlab a t, (f p) ^ 2) := by
  have hwt := vlSlab_memLp_mono ht.2 sol.w_L2
  have hHt := fun j => vlSlab_memLp_mono ht.2 (sol.H_L2 j)
  have hft := vlSlab_memLp_mono ht.2 sol.f_L2
  have hIH : ∀ j : Fin 3, IntegrableOn (fun s => ∫ x, (H j (x, s)) ^ 2) (Ioo a t) volume :=
    fun j => vlSlab_sliceSq_integrableOn (hHt j)
  have hIw := vlSlab_sliceSq_integrableOn hwt
  have hIf := vlSlab_sliceSq_integrableOn hft
  have hsum : IntegrableOn (fun s => ∑ j : Fin 3, ∫ x, (H j (x, s)) ^ 2) (Ioo a t) volume :=
    integrable_finsetSum _ fun j _ => hIH j
  have hsw : IntegrableOn (fun s => (∑ j : Fin 3, ∫ x, (H j (x, s)) ^ 2) +
      ∫ x, (w (x, s)) ^ 2) (Ioo a t) volume := hsum.add hIw
  unfold vlDataEnergy
  rw [integral_add hsw hIf, integral_add hsum hIw, integral_finsetSum _ fun j _ => hIH j,
    vlSlab_integral_sq hwt, vlSlab_integral_sq hft]
  congr 3
  exact Finset.sum_congr rfl fun j _ => (vlSlab_integral_sq (hHt j)).symm

/-- The sum of the component data energies. -/
theorem vl_dataEnergy_sum_le {a τ M t : ℝ} {z v g₀ : Vec3 × ℝ → Vec3}
    {F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ} {z₀ : Vec3 → Vec3}
    (sol : ∀ i, VlHeatSolution a τ (fun p => z p i) (vlCompFlux z v F G i) (fun p => g₀ p i)
      (fun x => z₀ x i))
    (hF : ∀ j i, MemLp (fun p => F p j i) 2 (volume.restrict (vlSlab a τ)))
    (hG : ∀ j i, MemLp (fun p => G p j i) 2 (volume.restrict (vlSlab a τ)))
    (hv : ∀ᵐ p ∂(volume.restrict (vlSlab a τ)), vec3EuclideanNorm (v p) ≤ M)
    (ht : t ∈ Icc a τ) :
    ∑ i : Fin 3, vlDataEnergy (fun x => z₀ x i) (fun p => z p i) (vlCompFlux z v F G i)
        (fun p => g₀ p i) a t ≤
      (∑ i : Fin 3, ∫ x, (z₀ x i) ^ 2) +
        3 * (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2) +
        3 * (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2) +
        (∫ p in vlSlab a τ, ∑ i : Fin 3, (g₀ p i) ^ 2) +
        (36 * M ^ 2 + 1) * ∫ p in vlSlab a t, ∑ i : Fin 3, (z p i) ^ 2 := by
  set μt := (volume : Measure (Vec3 × ℝ)).restrict (vlSlab a t) with hμt
  set μQ := (volume : Measure (Vec3 × ℝ)).restrict (vlSlab a τ) with hμQ
  have hsub : vlSlab a t ⊆ vlSlab a τ := prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2)
  have hμ : μt ≤ μQ := Measure.restrict_mono hsub le_rfl
  have hHt : ∀ i j, MemLp (vlCompFlux z v F G i j) 2 μt := fun i j =>
    vlSlab_memLp_mono ht.2 ((sol i).H_L2 j)
  have hzt : ∀ i, MemLp (fun p => z p i) 2 μt := fun i => vlSlab_memLp_mono ht.2 (sol i).w_L2
  have hgt : ∀ i, MemLp (fun p => g₀ p i) 2 μt := fun i => vlSlab_memLp_mono ht.2 (sol i).f_L2
  have hFt : ∀ j i, MemLp (fun p => F p j i) 2 μt := fun j i => vlSlab_memLp_mono ht.2 (hF j i)
  have hGt : ∀ j i, MemLp (fun p => G p j i) 2 μt := fun j i => vlSlab_memLp_mono ht.2 (hG j i)
  -- integrability of the summed squares
  have iH : ∀ i, Integrable (fun p => ∑ j : Fin 3, (vlCompFlux z v F G i j p) ^ 2) μt :=
    fun i => integrable_finsetSum _ fun j _ => (hHt i j).integrable_sq
  have iHH : Integrable (fun p => ∑ i : Fin 3, ∑ j : Fin 3, (vlCompFlux z v F G i j p) ^ 2) μt :=
    integrable_finsetSum _ fun i _ => iH i
  have iFQ : Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2) μQ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hF j i).integrable_sq
  have iGQ : Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2) μQ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hG j i).integrable_sq
  have igQ : Integrable (fun p => ∑ i : Fin 3, (g₀ p i) ^ 2) μQ :=
    integrable_finsetSum _ fun i _ => (sol i).f_L2.integrable_sq
  have iz : Integrable (fun p => ∑ i : Fin 3, (z p i) ^ 2) μt :=
    integrable_finsetSum _ fun i _ => (hzt i).integrable_sq
  have ig : Integrable (fun p => ∑ i : Fin 3, (g₀ p i) ^ 2) μt := igQ.mono_measure hμ
  have iF : Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2) μt := iFQ.mono_measure hμ
  have iG : Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2) μt := iGQ.mono_measure hμ
  -- rewrite each component energy
  have hcomp : ∀ i, vlDataEnergy (fun x => z₀ x i) (fun p => z p i) (vlCompFlux z v F G i)
      (fun p => g₀ p i) a t = (∫ x, (z₀ x i) ^ 2) +
        ((∫ p, ∑ j : Fin 3, (vlCompFlux z v F G i j p) ^ 2 ∂μt) + (∫ p, (z p i) ^ 2 ∂μt) +
          ∫ p, (g₀ p i) ^ 2 ∂μt) := by
    intro i
    rw [vlDataEnergy_eq_slab (sol i) ht, integral_finsetSum _ fun j _ => (hHt i j).integrable_sq]
  simp_rw [hcomp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← integral_finsetSum _ fun i _ => iH i, ← integral_finsetSum _ fun i _ => (hzt i).integrable_sq,
    ← integral_finsetSum _ fun i _ => (hgt i).integrable_sq]
  -- the flux bound
  have hbound : ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (vlCompFlux z v F G i j p) ^ 2 ∂μt ≤
      3 * (∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 ∂μt) +
        3 * (∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 ∂μt) +
        36 * M ^ 2 * ∫ p, ∑ i : Fin 3, (z p i) ^ 2 ∂μt := by
    have i1 : Integrable (fun p => 3 * ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 +
        3 * ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2) μt := (iF.const_mul 3).add (iG.const_mul 3)
    have i2 : Integrable (fun p => 36 * M ^ 2 * ∑ i : Fin 3, (z p i) ^ 2) μt := iz.const_mul _
    have i12 : Integrable (fun p => 3 * ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 +
        3 * ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 +
        36 * M ^ 2 * ∑ i : Fin 3, (z p i) ^ 2) μt := i1.add i2
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iF.const_mul 3) (iG.const_mul 3), ← integral_add i1 i2]
    refine integral_mono_ae iHH i12 ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hv] with p hp
    exact vl_flux_total_le hp
  have hmonoF : ∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 ∂μt ≤
      ∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 ∂μQ :=
    setIntegral_mono_set iFQ (Eventually.of_forall fun p =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hmonoG : ∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 ∂μt ≤
      ∫ p, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 ∂μQ :=
    setIntegral_mono_set iGQ (Eventually.of_forall fun p =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hmonog : ∫ p, ∑ i : Fin 3, (g₀ p i) ^ 2 ∂μt ≤ ∫ p, ∑ i : Fin 3, (g₀ p i) ^ 2 ∂μQ :=
    setIntegral_mono_set igQ (Eventually.of_forall fun p =>
      Finset.sum_nonneg fun i _ => sq_nonneg _) (Eventually.of_forall hsub)
  linarith only [hbound, hmonoF, hmonoG, hmonog]

end ESS

end
