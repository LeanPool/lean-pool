/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Time slices of finite-energy weak solutions

Almost every time slice of a space-time `L^q` field is in `L^q`, and almost
every slice of a finite-energy weak solution has a square-integrable weak
gradient with vanishing trace. These are the fixed-time inputs of the
cross-testing identity in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost every time slice of a space-time `L^q` field on the slab is in `L^q`. -/
theorem serrin_slice_memLp_ae {E : Type} [NormedAddCommGroup E] {T : ℝ}
    {f : ParabolicPoint → E} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ⊤)
    (hf : MemLp f q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), MemLp (fun x : Vec3 => f (x, s)) q volume := by
  rw [serrin_slab_measure_eq] at hf
  set r : ℝ := q.toReal
  have hr : 0 < r := ENNReal.toReal_pos hq0 hqtop
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have hfm : AEStronglyMeasurable (fun z : Vec3 × ℝ => f z) ν := hf.aestronglyMeasurable
  have hgm : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ r) ν := hfm.enorm.pow_const r
  have hfin : (∫⁻ z, ‖f z‖ₑ ^ r ∂ν) ≠ ⊤ := by
    have h1 := hf.eLpNorm_lt_top
    have hfm' : AEStronglyMeasurable f ν := hfm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hfm'] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).mp h1 |>.ne
  have hGm : AEMeasurable (fun s => ∫⁻ x, ‖f (x, s)‖ₑ ^ r ∂volume)
      (volume.restrict (Ioo 0 T)) := hgm.lintegral_prod_left'
  have hGfin : (∫⁻ s, ∫⁻ x, ‖f (x, s)‖ₑ ^ r ∂volume ∂(volume.restrict (Ioo 0 T))) ≠ ⊤ := by
    rw [← lintegral_prod_symm _ hgm]
    exact hfin
  filter_upwards [hfm.prodMk_right, ae_lt_top' hGm hGfin] with s hs hlt
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hs]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne

/-- A square-integrable weakly differentiable field that is weakly
divergence free has an almost everywhere vanishing gradient trace. -/
theorem serrin_trace_zero_of_divFree {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw : MemLp w 2 volume) (hDw : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i))
    (hdiv : ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, w x i * ψ.partialDeriv i x = 0) :
    ∀ᵐ x ∂volume, ∑ i : Fin 3, Dw x i i = 0 := by
  have hloc : LocallyIntegrable (fun x => ∑ i : Fin 3, Dw x i i) volume := by
    have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        LocallyIntegrable (fun x => Dw x i i) volume :=
      fun i _ => ((hDw.eval i).eval i).locallyIntegrable (by norm_num)
    simpa using locallyIntegrable_finsetSum _ h
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => ?_
  let ψ : WeakTestFunction (Set.univ : Set Vec3) :=
    ⟨g, hg, hgc, Set.subset_univ _⟩
  have hψ2 (i : Fin 3) : MemLp (fun x => ψ.partialDeriv i x) 2 volume := by
    have hc : Continuous (fun x => ψ.partialDeriv i x) :=
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => ψ.partialDeriv i x) :=
      hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hc.memLp_of_hasCompactSupport hcs
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hsplit : (∫ x : Vec3, ∑ i : Fin 3, w x i * ψ.partialDeriv i x) =
      ∑ i : Fin 3, ∫ x : Vec3, w x i * ψ.partialDeriv i x :=
    integral_finsetSum _ fun i _ => (hw.eval i).integrable_mul (hψ2 i)
  have hweak (i : Fin 3) : (∫ x : Vec3, w x i * ψ.partialDeriv i x) =
      -∫ x : Vec3, Dw x i i * g x := by
    have h := hgrad i i g hg hgc (Set.subset_univ _)
    simp only [Measure.restrict_univ] at h
    exact h
  have hzero := hdiv ψ
  rw [hsplit] at hzero
  simp only [hweak, Finset.sum_neg_distrib, neg_eq_zero] at hzero
  have hint (i : Fin 3) : Integrable (fun x => Dw x i i * g x) volume :=
    ((hDw.eval i).eval i).integrable_mul hg2
  rw [← integral_finsetSum _ fun i _ => hint i] at hzero
  rw [← hzero]
  congr 1
  funext x
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Almost every time slice of a finite-energy weak solution is square
integrable with a square-integrable weak gradient of vanishing trace, and its
pressure slice is locally integrable. -/
theorem serrinWeak_slices_ae {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p) :
    ∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => u (x, s)) 2 volume ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 volume ∧
      (∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, s) i) (fun x => Du (x, s) i)) ∧
      (∀ᵐ x ∂volume, ∑ i : Fin 3, Du (x, s) i i = 0) ∧
      LocallyIntegrable (fun x : Vec3 => p (x, s)) volume := by
  have hu := serrin_slice_memLp_ae (by norm_num) (by norm_num)
    (serrinWeak_velocity_memLp_two hU)
  have hDu := serrin_slice_memLp_ae (by norm_num) (by norm_num)
    (serrinWeak_gradient_memLp_two hU)
  have hp := serrin_slice_memLp_ae (by simp) ENNReal.ofReal_ne_top hU.pressure
  filter_upwards [hu, hDu, hp, hU.weak_grad, hU.div_free] with s hus hDus hps hgs hds
  refine ⟨hus, hDus, hgs, serrin_trace_zero_of_divFree hus hDus hgs hds, ?_⟩
  exact hps.locallyIntegrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num))

end ESS
