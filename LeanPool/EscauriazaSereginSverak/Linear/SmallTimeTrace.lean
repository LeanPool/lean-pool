/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.EscauriazaSereginSverak.Linear.SpaceTimeTimeDerivative
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

public section

open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

private theorem vec3EuclideanNorm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]

private theorem section_small_time_bound {τ t : ℝ} (hτ : 0 < τ)
    (ht : 0 < t) (htτ : t < τ) {x : Vec3}
    {w Dtw : ParabolicPoint → Vec3}
    (hwcont : ContinuousOn (fun s => w ((show ParabolicPoint from (x, s)))) (Ico 0 τ))
    (hwzero : w ((show ParabolicPoint from (x, 0))) = 0)
    (hweak : ∀ i : Fin 3,
      HasWeakDerivOn (Ioo 0 τ) (fun s => w ((show ParabolicPoint from (x, s))) i) (fun s => Dtw ((show ParabolicPoint from (x, s))) i))
    (hDtwL2 : MemLp (fun s => Dtw ((show ParabolicPoint from (x, s)))) 2 (volume.restrict (Ioo 0 τ))) :
    vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2 ≤
      t * ∫ s in 0..t, vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2 := by
  have hcoord (i : Fin 3) :
      |w ((show ParabolicPoint from (x, t))) i| ^ 2 ≤ t * ∫ s in 0..t, |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2 := by
    have hconti : ContinuousOn (fun s => w ((show ParabolicPoint from (x, s))) i) (Ico 0 τ) := by
      exact (continuous_apply i).comp_continuousOn hwcont
    have hzeroi : w ((show ParabolicPoint from (x, 0))) i = 0 := congrArg (fun v : Vec3 => v i) hwzero
    have hcoordLp : MemLp (fun s => Dtw ((show ParabolicPoint from (x, s))) i) 2
        (volume.restrict (Ioo 0 τ)) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        hDtwL2.continuousLinearMap_comp
          (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    exact abs_sq_le_time_integral_sq_of_continuous_weakDeriv hτ hconti hzeroi
      hcoordLp (hweak i) t ht htτ
  calc
    vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2 = ∑ i : Fin 3, |w ((show ParabolicPoint from (x, t))) i| ^ 2 := by
      rw [vec3EuclideanNorm_sq]
      exact Finset.sum_congr rfl (fun i _ => (sq_abs _).symm)
    _ ≤ ∑ i : Fin 3, t * ∫ s in 0..t, |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = t * ∫ s in 0..t, ∑ i : Fin 3, |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply intervalIntegral.integral_finsetSum
      intro i hi
      have hiLp : MemLp (fun s => Dtw ((show ParabolicPoint from (x, s))) i) 2
          (volume.restrict (Ioo 0 τ)) := by
        simpa only [ContinuousLinearMap.proj_apply] using
          hDtwL2.continuousLinearMap_comp
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
      have hiInt := hiLp.integrable_sq
      have hiIntAbs : Integrable (fun s => |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2)
          (volume.restrict (Ioo 0 τ)) := by
        simpa [sq_abs] using hiInt
      have hiIntOn : IntegrableOn (fun s => |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2)
          (Ioo 0 τ) volume := hiIntAbs
      have hiInterval : IntervalIntegrable (fun s => |Dtw ((show ParabolicPoint from (x, s))) i| ^ 2)
          volume 0 t := by
        apply intervalIntegrable_iff.mpr
        apply hiIntOn.mono_set
        intro s hs
        have hs' : s ∈ Ioc 0 t := by simpa [uIoc, ht.le] using hs
        exact ⟨hs'.1, lt_of_le_of_lt hs'.2 htτ⟩
      exact hiInterval
    _ = t * ∫ s in 0..t, vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2 := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [vec3EuclideanNorm_sq]
      exact Finset.sum_congr rfl (fun i _ => sq_abs _)

/-- The small-time trace estimate from manuscript label `lem:ftc-small-time`.
The space-time time derivative identity gives the a.e. sectionwise weak
derivative through `hasSectionwiseTimeWeakDeriv_of_hasSpaceTimeWeakDerivs`.
The spacetime `L²` hypothesis uses the product volume. The nested right-hand
lintegral places space outside time; Tonelli's theorem identifies it with the
manuscript's time-outside-space order. -/
theorem ftc_small_time {B : Set Vec3} {τ : ℝ}
    (hB : IsOpen B) (hτ : 0 < τ) {w Dtw : ParabolicPoint → Vec3}
    (hwcont : ContinuousOn w (spaceTimeSet B (Ico 0 τ)))
    (hwzero : ∀ x ∈ B, w ((show ParabolicPoint from (x, 0))) = 0)
    (hDtwL2 : MemLp Dtw 2
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs B (Ioo 0 τ) w Dw D2w Dtw) :
    ∀ t, 0 < t → t < τ →
      (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2)
        ∂(volume.restrict B)) ≤
        ENNReal.ofReal t * ∫⁻ x, ∫⁻ s,
          ENNReal.ofReal (vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2)
            ∂(volume.restrict (Ioc 0 t)) ∂(volume.restrict B) := by
  have hweak := hasSectionwiseTimeWeakDeriv_of_hasSpaceTimeWeakDerivs
    hB hτ hwcont hDtwL2 hderiv
  intro t ht htτ
  have hspaceMeas : MeasurableSet B := hB.measurableSet
  have hDtwSq : Integrable (fun z : ParabolicPoint => ‖Dtw z‖ ^ 2)
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))) :=
    hDtwL2.integrable_norm_pow (p := 2) (by norm_num)
  have hDtwAEMeas := hDtwL2.aestronglyMeasurable
  have hDtwSectionMeas := hDtwAEMeas.prodMk_left
  have hDtwSectionSq := hDtwSq.prod_right_ae
  have hsection : ∀ᵐ x ∂(volume.restrict B),
      (∀ i : Fin 3,
        HasWeakDerivOn (Ioo 0 τ) (fun s => w ((show ParabolicPoint from (x, s))) i) (fun s => Dtw ((show ParabolicPoint from (x, s))) i)) ∧
      MemLp (fun s => Dtw ((show ParabolicPoint from (x, s)))) 2 (volume.restrict (Ioo 0 τ)) := by
    filter_upwards [hweak, hDtwSectionMeas, hDtwSectionSq] with x hxweak hxmeas hxsq
    exact ⟨hxweak, (memLp_two_iff_integrable_sq_norm hxmeas).2 hxsq⟩
  have hpoint : ∀ᵐ x ∂(volume.restrict B),
      vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2 ≤
        t * ∫ s in 0..t, vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2 := by
    filter_upwards [hsection, ae_restrict_mem hspaceMeas] with x hx hxB
    have hmap : Continuous (fun s : ℝ => (show ParabolicPoint from (x, s))) := by
      exact CKN.Foundation.Parabolic.continuous_prod_to_parabolicPoint.comp
        (continuous_const.prodMk continuous_id)
    have hcontx : ContinuousOn (fun s => w ((show ParabolicPoint from (x, s)))) (Ico 0 τ) := by
      exact hwcont.comp hmap.continuousOn (by
        intro s hs
        exact ⟨hxB, hs⟩)
    exact section_small_time_bound hτ ht htτ hcontx (hwzero x hxB) hx.1 hx.2
  have hpointENN : ∀ᵐ x ∂(volume.restrict B),
      ENNReal.ofReal (vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2) ≤
        ENNReal.ofReal t * ENNReal.ofReal
          (∫ s in 0..t, vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2) := by
    filter_upwards [hpoint] with x hx
    calc
      ENNReal.ofReal (vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2) ≤
          ENNReal.ofReal (t * ∫ s in 0..t,
            vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2) := ENNReal.ofReal_le_ofReal hx
      _ = ENNReal.ofReal t * ENNReal.ofReal
          (∫ s in 0..t, vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2) :=
        ENNReal.ofReal_mul (le_of_lt ht)
  have htimeConv : ∀ᵐ x ∂(volume.restrict B),
      ENNReal.ofReal (∫ s in 0..t,
        vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2) =
      ∫⁻ s, ENNReal.ofReal (vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2)
        ∂(volume.restrict (Ioc 0 t)) := by
    filter_upwards [hsection] with x hx
    let g := fun s : ℝ => vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s))))
    have hmeas : AEStronglyMeasurable g (volume.restrict (Ioo 0 τ)) := by
      exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hx.2.aestronglyMeasurable
    have hmajor : MemLp (fun s : ℝ => Real.sqrt 3 * ‖Dtw ((show ParabolicPoint from (x, s)))‖)
        2 (volume.restrict (Ioo 0 τ)) :=
      hx.2.norm.const_mul (Real.sqrt 3)
    have hgLp : MemLp g 2 (volume.restrict (Ioo 0 τ)) := by
      apply hmajor.of_le hmeas
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
    have hgSq := hgLp.integrable_sq
    have hsub : Ioc 0 t ⊆ Ioo 0 τ := by
      intro s hs
      exact ⟨hs.1, lt_of_le_of_lt hs.2 htτ⟩
    have hgSqOn : Integrable (fun s => g s ^ 2)
        (volume.restrict (Ioc 0 t)) :=
      hgSq.mono_measure (Measure.restrict_mono_set volume hsub)
    have hinterval : (∫ s in 0..t, g s ^ 2) =
        ∫ s, g s ^ 2 ∂(volume.restrict (Ioc 0 t)) := by
      calc
        (∫ s in 0..t, g s ^ 2) = ∫ s in Ioc 0 t, g s ^ 2 :=
          intervalIntegral.integral_of_le ht.le
        _ = ∫ s, g s ^ 2 ∂(volume.restrict (Ioc 0 t)) := rfl
    rw [hinterval]
    exact ofReal_integral_eq_lintegral_ofReal hgSqOn
      (Filter.Eventually.of_forall fun s => sq_nonneg (g s))
  calc
    (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (w ((show ParabolicPoint from (x, t)))) ^ 2)
      ∂(volume.restrict B)) ≤
      ∫⁻ x, ENNReal.ofReal t *
        (∫⁻ s, ENNReal.ofReal (vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2)
          ∂(volume.restrict (Ioc 0 t))) ∂(volume.restrict B) := by
      apply lintegral_mono_ae
      filter_upwards [hpointENN, htimeConv] with x hx hconv
      rw [← hconv]
      exact hx
    _ = ENNReal.ofReal t * ∫⁻ x, ∫⁻ s,
        ENNReal.ofReal (vec3EuclideanNorm (Dtw ((show ParabolicPoint from (x, s)))) ^ 2)
          ∂(volume.restrict (Ioc 0 t)) ∂(volume.restrict B) :=
      lintegral_const_mul' (ENNReal.ofReal t) _ (by simp)

end ESS
