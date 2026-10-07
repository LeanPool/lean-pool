/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedBounds

/-!
# The mollified cross identity

For two Leray–Hopf solutions with pressures, the cutoff-weighted pairing of
their mollifications changes in time by the integrated tested fluxes. This is
the regularized cross-testing identity of `lem:pv-serrin-uniqueness`; the
mollification and cutoff are removed afterwards.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem serrinMol_continuousOn {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (k : Fin 3) (y : Vec3) :
    ContinuousOn (fun τ => serrinMol u ρ k y τ) (Icc 0 T) := by
  have h := hU.weak_cont _ (serrinKernelTest_contDiff hρ k y)
    (serrinKernelTest_hasCompactSupport hρc k y)
  have hfun : (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i *
      serrinKernelTest ρ k y x i) = fun τ => serrinMol u ρ k y τ := by
    funext τ
    simp only [serrinMol, serrinPairing_kernelTest]
  rwa [hfun] at h

/-- The cutoff-weighted pairing of two mollified solutions changes in time by
the integrated tested fluxes. -/
theorem serrinMol_cross_identity
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    {η : Vec3 → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ y, η y * ((∑ k : Fin 3, serrinMol v ρ k y t * serrinMol u ρ k y t) -
        ∑ k : Fin 3, serrinMol v ρ k y 0 * serrinMol u ρ k y 0)) =
      ∫ τ in (0 : ℝ)..t, ∫ y, η y * ∑ k : Fin 3,
        (serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
          serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ) := by
  let H : Vec3 → ℝ → ℝ := fun y τ => ∑ k : Fin 3,
    (serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
      serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ)
  let K : Set Vec3 := tsupport η
  have hK : IsCompact K := hηc.isCompact
  obtain ⟨Bu, hBu⟩ := serrinMol_bound_ae hU hρ.continuous hρc
  obtain ⟨Bv, hBv⟩ := serrinMol_bound_ae hV hρ.continuous hρc
  obtain ⟨mu, hmu, hmuB⟩ := serrinMolFlux_bound_ae hU hρ hρc hK
  obtain ⟨mv, hmv, hmvB⟩ := serrinMolFlux_bound_ae hV hρ hρc hK
  -- the pointwise identity at each mollification point
  have hpoint : ∀ y, (∑ k : Fin 3, serrinMol v ρ k y t * serrinMol u ρ k y t) -
      ∑ k : Fin 3, serrinMol v ρ k y 0 * serrinMol u ρ k y 0 =
      ∫ τ in (0 : ℝ)..t, H y τ := by
    intro y
    have hterm (k : Fin 3) : IntervalIntegrable
        (fun τ => serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
          serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ) volume 0 t := by
      have hsub : Ι (0 : ℝ) t ⊆ Icc 0 T := by
        rw [uIoc_of_le ht.1]
        exact fun τ hτ => ⟨hτ.1.le, hτ.2.trans ht.2⟩
      have hle : volume.restrict (Ι (0 : ℝ) t) ≤ volume.restrict (Ioo 0 T) := by
        calc
          volume.restrict (Ι (0 : ℝ) t) ≤ volume.restrict (Ioc 0 T) := by
            apply Measure.restrict_mono _ le_rfl
            rw [uIoc_of_le ht.1]
            exact Ioc_subset_Ioc_right ht.2
          _ = volume.restrict (Ioo 0 T) := Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
      have hvf := (serrinMol_slab hV hρ hρc k y).1
      have huf := (serrinMol_slab hU hρ hρc k y).1
      have hucont := (serrinMol_continuousOn hU hρ hρc k y).mono hsub
      have hvcont := (serrinMol_continuousOn hV hρ hρc k y).mono hsub
      rw [intervalIntegrable_iff]
      refine Integrable.add ?_ ?_
      · refine (Integrable.mono_measure hvf hle).mul_bdd (c := Bu)
          (hucont.aestronglyMeasurable measurableSet_uIoc) ?_
        filter_upwards [ae_mono hle hBu] with τ hτ
        exact hτ k y
      · refine (Integrable.mono_measure huf hle).bdd_mul (c := Bv)
          (hvcont.aestronglyMeasurable measurableSet_uIoc) ?_
        filter_upwards [ae_mono hle hBv] with τ hτ
        exact hτ k y
    have hprod (k : Fin 3) := serrinMol_product hU hV hρ hρc k y ht
    rw [intervalIntegral.integral_finsetSum fun k _ => hterm k]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hprod k]
    ring
  have hleft : (fun y => η y * ((∑ k : Fin 3, serrinMol v ρ k y t * serrinMol u ρ k y t) -
      ∑ k : Fin 3, serrinMol v ρ k y 0 * serrinMol u ρ k y 0)) =
      fun y => η y * ∫ τ in (0 : ℝ)..t, H y τ := by
    funext y
    rw [hpoint y]
  rw [hleft]
  -- measurability of the exchanged density
  have hUm := hU.meas_u
  have hDUm := hU.meas_Du
  have hVm := hV.meas_u
  have hDVm := hV.meas_Du
  have hpu := hU.pressure
  have hpv := hV.pressure
  have hHm : AEStronglyMeasurable (fun z : ℝ × Vec3 => H z.2 z.1)
      ((volume.restrict (Ioo 0 T)).prod volume) := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    exact ((serrinMolFlux_aestronglyMeasurable hVm hDVm hpv.aestronglyMeasurable hρ k).mul
      (serrinMol_aestronglyMeasurable hUm hρ.continuous k)).add
      ((serrinMol_aestronglyMeasurable hVm hρ.continuous k).mul
        (serrinMolFlux_aestronglyMeasurable hUm hDUm hpu.aestronglyMeasurable hρ k))
  have hm : IntegrableOn (fun τ => 3 * (mv τ * |Bu| + |Bv| * mu τ)) (Ioo 0 T) :=
    ((hmv.mul_const |Bu|).add (hmu.const_mul |Bv|)).const_mul 3
  have hbd : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ∀ y ∈ K,
      |H y τ| ≤ 3 * (mv τ * |Bu| + |Bv| * mu τ) := by
    filter_upwards [hBu, hBv, hmuB, hmvB] with τ hu hv hfu hfv y hy
    have hterm (k : Fin 3) :
        |serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
          serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ| ≤
          mv τ * |Bu| + |Bv| * mu τ := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have hmvnn : 0 ≤ mv τ := (abs_nonneg _).trans (hfv y hy k)
      exact add_le_add
        (mul_le_mul (hfv y hy k) ((hu k y).trans (le_abs_self _)) (abs_nonneg _) hmvnn)
        (mul_le_mul ((hv k y).trans (le_abs_self _)) (hfu y hy k) (abs_nonneg _)
          (abs_nonneg _))
    calc
      |H y τ| ≤ ∑ k : Fin 3, |serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
          serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, (mv τ * |Bu| + |Bv| * mu τ) :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = 3 * (mv τ * |Bu| + |Bv| * mu τ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
  obtain ⟨Cη, hCη⟩ := hηc.exists_bound_of_continuous hη
  exact serrin_cutoff_fubini ht hK (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    hη.stronglyMeasurable (fun y => (hCη y).trans_eq' (Real.norm_eq_abs _).symm) hHm hm hbd

end ESS
