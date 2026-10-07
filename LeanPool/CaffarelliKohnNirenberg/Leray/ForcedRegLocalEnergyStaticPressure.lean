/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyStatic

/-!
# Pressure and divergence identities for the local energy inequality

For a weakly divergence-free square-integrable velocity slice `u` with weak
gradient `D`, the trace `∑ₖ D_kk` vanishes almost everywhere, and a locally
integrable pressure `p` with square-integrable weak gradient `G` satisfies
`∑ₖ ∫ u_k ψ Gₖ = -∑ₖ ∫ u_k p ∂ₖψ` against a smooth compactly supported weight
`ψ`. A pressure in `L⁶` restricted by a bounded compactly supported factor is
square integrable. These are the pressure identities of
`eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN.Leray

/-- An `L⁶` function times a bounded factor supported in a set of finite
measure is square integrable. -/
theorem eLpNorm_mul_le_of_six {p h : Vec3 → ℝ} (hp : AEStronglyMeasurable p volume)
    (hh : AEStronglyMeasurable h volume) {K : Set Vec3} (hK : MeasurableSet K) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) (hhK : ∀ x ∉ K, h x = 0) :
    eLpNorm (fun x => p x * h x) 2 volume ≤
      ENNReal.ofReal M * (eLpNorm p (ENNReal.ofReal 6) volume * volume K ^ (1 / 3 : ℝ)) := by
  have h1 : eLpNorm (fun x => p x * h x) 2 volume ≤
      ENNReal.ofReal M * eLpNorm (K.indicator p) 2 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hp.mul hh) (Eventually.of_forall fun x => ?_) 2
    change ‖p x * h x‖ ≤ M * ‖K.indicator p x‖
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, norm_mul, mul_comm, Real.norm_eq_abs (h x)]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    · rw [hhK x hx, mul_zero, norm_zero]
      exact mul_nonneg ((abs_nonneg _).trans (hM x)) (norm_nonneg _)
  have h2 : eLpNorm (K.indicator p) 2 volume ≤
      eLpNorm p (ENNReal.ofReal 6) volume * volume K ^ (1 / 3 : ℝ) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hK]
    have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K)
      (p := 2) (q := ENNReal.ofReal 6) (by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal (by norm_num)) hp.restrict
    rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal (by norm_num)] at h3
    have e : (1 / (2 : ℝ≥0∞).toReal - 1 / 6 : ℝ) = 1 / 3 := by
      rw [ENNReal.toReal_ofNat]
      norm_num
    rw [e] at h3
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_right
      (eLpNorm_mono_measure (μ := volume) (ν := volume.restrict K) p Measure.restrict_le_self)
      zero_le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)

section Pressure

variable {u : Vec3 → Vec3} (hdf : CKN.IsWeakDivFreeL2 u)

include hdf in
/-- The trace of the weak gradient of a weakly divergence-free field vanishes. -/
theorem ae_sum_diag_eq_zero {D : Vec3 → Fin 3 → Vec3}
    (hD : ∀ k, MemLp (fun x => D x k k) 2 volume)
    (hweak : ∀ k, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u x k) (fun x => D x k)) :
    ∀ᵐ x, ∑ k : Fin 3, D x k k = 0 := by
  have hloc : LocallyIntegrable (fun x => ∑ k : Fin 3, D x k k) volume :=
    (memLp_finsetSum _ fun k _ => hD k).locallyIntegrable (by norm_num)
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => ?_
  have hdg : ∀ k, Continuous fun x => fderiv ℝ g x (CKN.basisVec k) := fun k =>
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgc : ∀ k, HasCompactSupport fun x => fderiv ℝ g x (CKN.basisVec k) := fun k =>
    hgc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
  have i1 : ∀ k, Integrable fun x => D x k k * g x := fun k =>
    ((hD k).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hg.continuous hgc
  have i2 : ∀ k, Integrable fun x => u x k * fderiv ℝ g x (CKN.basisVec k) := fun k =>
    ((hdf.1.eval k).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (hdg k) (hdgc k)
  have hk : ∀ k, ∫ x, D x k k * g x = -∫ x, u x k * fderiv ℝ g x (CKN.basisVec k) := by
    intro k
    have h := hweak k k g hg hgc (subset_univ _)
    simp only [Measure.restrict_univ] at h
    rw [h, neg_neg]
  let φ : CKN.WeakTestFunction (Set.univ : Set Vec3) := ⟨g, hg, hgc, subset_univ _⟩
  have hdiv := hdf.2 φ
  have e : ∀ x, g x • ∑ k : Fin 3, D x k k = ∑ k : Fin 3, D x k k * g x := fun x => by
    rw [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => i1 k]
  simp_rw [hk]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun k _ => i2 k]
  change -∫ x, ∑ k : Fin 3, u x k * φ.partialDeriv k x = 0
  rw [hdiv, neg_zero]

include hdf in
/-- The pressure identity `∑ₖ ∫ u_k ψ Gₖ = -∑ₖ ∫ u_k p ∂ₖψ`. -/
theorem sum_integral_pressure_eq {p : Vec3 → ℝ} (hpl : LocallyIntegrable p volume)
    {G : Vec3 → Vec3} (hG : ∀ k, MemLp (fun x => G x k) 2 volume)
    (hpG : CKN.HasWeakGradientOn (Set.univ : Set Vec3) p G) {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hpψ : ∀ k, MemLp (fun x => p x * fderiv ℝ ψ x (CKN.basisVec k)) 2 volume) :
    ∑ k : Fin 3, ∫ x, u x k * (ψ x * G x k) =
      -∑ k : Fin 3, ∫ x, u x k * (p x * fderiv ℝ ψ x (CKN.basisVec k)) := by
  have hu : ∀ k, MemLp (fun x => u x k) 2 volume := fun k => hdf.1.eval k
  obtain ⟨Mψ, hMψ⟩ := Continuous.bounded_above_of_compact_support hψ.continuous hψc
  have hψG : ∀ k, MemLp (fun x => ψ x * G x k) 2 volume := fun k =>
    ((hG k).of_le_mul (c := Mψ) (hψ.continuous.aestronglyMeasurable.mul (hG k).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hMψ x) (norm_nonneg _)))
  have hdelta : ∀ n, ∑ k : Fin 3, ∫ x, leConv (leMol n) (fun y => u y k) x * (ψ x * G x k) =
      -∑ k : Fin 3, ∫ x, leConv (leMol n) (fun y => u y k) x *
        (p x * fderiv ℝ ψ x (CKN.basisVec k)) := by
    intro n
    have hw : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (leConv (leMol n) (fun y => u y k)) := fun k =>
      leConv_leMol_contDiff (hu k) n
    have hdw : ∀ k, Continuous (leConv (CKN.spatialDeriv (leMol n) k) (fun y => u y k)) :=
      fun k => (leConv_contDiff (CKN.contDiff_spatialDeriv_smooth (leMol_contDiff n) k)
        (CKN.hasCompactSupport_spatialDeriv (leMol_hasCompactSupport n) k)
        ((hu k).locallyIntegrable (by norm_num))).continuous
    have hdψ : ∀ k, Continuous fun x => fderiv ℝ ψ x (CKN.basisVec k) := fun k =>
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψc : ∀ k, HasCompactSupport fun x => fderiv ℝ ψ x (CKN.basisVec k) := fun k =>
      hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
    have ia : ∀ k, Integrable fun x =>
        p x * (leConv (CKN.spatialDeriv (leMol n) k) (fun y => u y k) x * ψ x) := fun k =>
      hpl.integrable_smul_right_of_hasCompactSupport ((hdw k).mul hψ.continuous) hψc.mul_left
    have ib : ∀ k, Integrable fun x =>
        p x * (leConv (leMol n) (fun y => u y k) x * fderiv ℝ ψ x (CKN.basisVec k)) := fun k =>
      hpl.integrable_smul_right_of_hasCompactSupport ((hw k).continuous.mul (hdψ k))
        (hdψc k).mul_left
    have hk : ∀ k, ∫ x, leConv (leMol n) (fun y => u y k) x * (ψ x * G x k) =
        -((∫ x, p x * (leConv (CKN.spatialDeriv (leMol n) k) (fun y => u y k) x * ψ x)) +
          ∫ x, p x * (leConv (leMol n) (fun y => u y k) x * fderiv ℝ ψ x (CKN.basisVec k))) := by
      intro k
      have h := hpG k (fun x => leConv (leMol n) (fun y => u y k) x * ψ x) ((hw k).mul hψ)
        hψc.mul_left (subset_univ _)
      simp only [Measure.restrict_univ] at h
      simp_rw [fderiv_leConv_mul (leMol_contDiff n) (leMol_hasCompactSupport n) (hu k) hψ _ k,
        mul_add] at h
      rw [integral_add (ia k) (ib k)] at h
      rw [h, neg_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    simp_rw [hk]
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← integral_finsetSum _ fun k _ => ia k]
    have h0 : ∫ x, ∑ k : Fin 3, p x * (leConv (CKN.spatialDeriv (leMol n) k)
        (fun y => u y k) x * ψ x) = 0 := by
      have e : ∀ x, ∑ k : Fin 3, p x * (leConv (CKN.spatialDeriv (leMol n) k)
          (fun y => u y k) x * ψ x) = 0 := fun x => by
        rw [show ∑ k : Fin 3, p x * (leConv (CKN.spatialDeriv (leMol n) k)
            (fun y => u y k) x * ψ x) = p x * ψ x * ∑ k : Fin 3,
              leConv (CKN.spatialDeriv (leMol n) k) (fun y => u y k) x by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring,
          sum_leConv_spatialDeriv_eq_zero (leMol_contDiff n) (leMol_hasCompactSupport n) hdf x,
          mul_zero]
      simp_rw [e, integral_zero]
    rw [h0, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hconst : ∀ Y : Vec3 → ℝ, Tendsto (fun _ : ℕ => eLpNorm (Y - Y) 2 volume) atTop (𝓝 0) :=
    fun Y => by
      simp only [sub_self, eLpNorm_zero]
      exact tendsto_const_nhds
  have hL : Tendsto (fun n => ∑ k : Fin 3, ∫ x, leConv (leMol n) (fun y => u y k) x *
      (ψ x * G x k)) atTop (𝓝 (∑ k : Fin 3, ∫ x, u x k * (ψ x * G x k))) :=
    tendsto_finsetSum _ fun k _ => tendsto_integral_leConv_mul (hu k) (fun _ => hψG k) (hψG k)
      (hconst _)
  have hR := (tendsto_finsetSum Finset.univ fun k _ => tendsto_integral_leConv_mul (hu k)
    (fun _ => hpψ k) (hpψ k) (hconst _)).neg
  simp_rw [hdelta] at hL
  exact tendsto_nhds_unique hL hR

end Pressure

end CKN.Leray

end
