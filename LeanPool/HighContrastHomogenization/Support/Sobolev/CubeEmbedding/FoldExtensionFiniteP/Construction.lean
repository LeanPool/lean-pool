/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FoldExtensionFiniteP.Basic

/-!
# Even-fold Sobolev extension construction

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.

The construction uses the geometry, approximation and transport estimates from
the companion basic module.
-/

public section

namespace HCPolySupport

open MeasureTheory Filter Topology HCPolySupport
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The finite-`p` even-fold extension of a Sobolev function on an open axis
box. -/
@[expose]
def foldExtensionFiniteP {m : ℕ} (lo hi : Vec (m + 1)) (hlt : ∀ k, lo k < hi k)
    (p : FiniteLpExponent) (u : W1pFunction (Box lo hi) p.exponent) :
    FoldExtensionFiniteP lo hi p u := by
  classical
  set lo3 : Vec (m + 1) := fun k => 2 * lo k - hi k with hlo3
  set hi3 : Vec (m + 1) := fun k => 2 * hi k - lo k with hhi3
  have hlt3 : ∀ k, lo3 k < hi3 k := fun k => by
    simp only [hlo3, hhi3]
    linarith [hlt k]
  have hbox3 : Box3 lo hi = Box lo3 hi3 := rfl
  have hU : IsOpenBoundedConvexDomain (Box lo hi) := isOpenBoundedConvexDomain_Box lo hi
  have hFold_cont : Continuous (Fold lo hi) := continuous_Fold lo hi (fun k => (hlt k).le)
  have hFold_meas : Measurable (Fold lo hi) := hFold_cont.measurable
  set Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) with hCd
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg
      (one_div_nonneg.mpr (finiteLpExponent_toReal_pos' p).le)
      (ENNReal.pow_ne_top (by simp))
  have hg_asm : AEStronglyMeasurable u.toFun (volume.restrict (Box lo hi)) :=
    u.memLp.aestronglyMeasurable
  set g : Vec (m + 1) → ℝ := hg_asm.mk u.toFun with hg_def
  have hg_meas : Measurable g := hg_asm.stronglyMeasurable_mk.measurable
  have hg_ae : u.toFun =ᵐ[volume.restrict (Box lo hi)] g := hg_asm.ae_eq_mk
  have hgi_asm : ∀ i, AEStronglyMeasurable (fun x => u.grad x i)
      (volume.restrict (Box lo hi)) := fun i => (u.grad_memLp i).aestronglyMeasurable
  set gi : Fin (m + 1) → Vec (m + 1) → ℝ :=
    fun i => (hgi_asm i).mk (fun x => u.grad x i) with hgi_def
  have hgi_meas : ∀ i, Measurable (gi i) :=
    fun i => (hgi_asm i).stronglyMeasurable_mk.measurable
  have hgi_ae : ∀ i, (fun x => u.grad x i) =ᵐ[volume.restrict (Box lo hi)] gi i :=
    fun i => (hgi_asm i).ae_eq_mk
  set x0 : Vec (m + 1) := fun k => (lo k + hi k) / 2 with hx0
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun k => hi k - lo k) with hδ
  have hδ_pos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff Finset.univ_nonempty]
    exact fun k _ => by linarith [hlt k]
  set r : ℝ := δ / 3 with hrdef
  have hr : 0 < r := by
    rw [hrdef]
    linarith
  have hball : Metric.closedBall x0 r ⊆ Box lo hi := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    have hxk : dist (x k) (x0 k) ≤ r := hx k
    rw [Real.dist_eq, abs_le] at hxk
    have hmk : δ ≤ hi k - lo k := Finset.inf'_le _ (Finset.mem_univ k)
    simp only [hx0, hrdef] at hxk
    exact ⟨by nlinarith [hxk.1], by nlinarith [hxk.2]⟩
  set A : ℕ → W1pFunction (Box lo hi) p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr with hA
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n).toFun := by
    intro n
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel) p.one_lt.le u.memLp hr
      (W1pFunction.unitConvexApproxScale_pos n)
  have hφ_grad : ∀ n x i, (A n).grad x i = fderiv ℝ ((A n).toFun) x (basisVec i) := by
    intro n x i
    simp [A, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
  set χ : Vec (m + 1) → ℝ := boxCutoff lo3 hi3 1 with hχ
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_cptsupp : HasCompactSupport χ := by
    apply HasCompactSupport.intro (K := Set.Icc (fun k => lo3 k - 1) (fun k => hi3 k + 1))
      isCompact_Icc
    intro x hx
    exact boxCutoff_eq_zero (by norm_num) hx
  have hχ_one : ∀ x ∈ Set.Icc lo3 hi3, χ x = 1 :=
    fun x hx => boxCutoff_eq_one (by norm_num) hx
  have hBox_Icc : ∀ x ∈ Box lo hi, x ∈ Set.Icc lo3 hi3 := by
    intro x hx
    have hx' := Set.mem_univ_pi.1 hx
    refine Set.mem_Icc.2 ⟨fun k => ?_, fun k => ?_⟩
    · have := (hx' k).1
      simp only [hlo3]
      linarith [hlt k]
    · have := (hx' k).2
      simp only [hhi3]
      linarith [hlt k]
  set wn : ℕ → Vec (m + 1) → ℝ := fun n x => χ x * (A n).toFun x with hwn
  have hw_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (wn n) :=
    fun n => hχ_smooth.mul (hφ_smooth n)
  have hw_cont : ∀ n, Continuous (wn n) := fun n => (hw_smooth n).continuous
  have hw_meas : ∀ n, Measurable (wn n) := fun n => (hw_cont n).measurable
  have hw_cptsupp : ∀ n, HasCompactSupport (wn n) := fun n => hχ_cptsupp.mul_right
  have hw_eq_φ : ∀ n, ∀ x ∈ Set.Icc lo3 hi3, wn n x = (A n).toFun x := by
    intro n x hx
    simp only [hwn, hχ_one x hx, one_mul]
  have hfderiv_eq : ∀ n, ∀ y ∈ Box lo hi,
      fderiv ℝ (wn n) y = fderiv ℝ ((A n).toFun) y := by
    intro n y hy
    have hy3 : y ∈ Box3 lo hi := by
      rw [hbox3]
      refine Set.mem_univ_pi.2 fun k => ?_
      have hyk := Set.mem_univ_pi.1 hy k
      exact ⟨by
        simp only [hlo3]
        linarith [hyk.1, hlt k], by
        simp only [hhi3]
        linarith [hyk.2, hlt k]⟩
    have hnbhd : Box3 lo hi ∈ 𝓝 y :=
      (by rw [hbox3]; exact isOpen_Box lo3 hi3 : IsOpen (Box3 lo hi)).mem_nhds hy3
    have heq : wn n =ᶠ[𝓝 y] (A n).toFun := by
      refine eventuallyEq_of_mem hnbhd fun x hx => ?_
      refine hw_eq_φ n x ?_
      rw [hbox3] at hx
      have hx' := Set.mem_univ_pi.1 hx
      exact Set.mem_Icc.2 ⟨fun k => (hx' k).1.le, fun k => (hx' k).2.le⟩
    exact heq.fderiv_eq
  have hEu_mem : MemLp (fun x => g (Fold lo hi x)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    refine memLp_iff.2 ?_
    rw [eLpNorm_foldComp_finiteLp p hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae]
    exact ENNReal.mul_lt_top hCd_lt u.memLp.eLpNorm_lt_top
  have hEu_grad_mem : ∀ i, MemLp
      (fun x => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    intro i
    refine memLp_iff.2 ?_
    refine lt_of_le_of_lt
      (eLpNorm_foldComp_mul_foldSign_le_finiteLp p (hgi_meas i) lo hi hlt i) ?_
    rw [← eLpNorm_congr_ae (hgi_ae i)]
    exact ENNReal.mul_lt_top hCd_lt (u.grad_memLp i).eLpNorm_lt_top
  have hEn_mem : ∀ n, MemLp (fun x => wn n (Fold lo hi x)) p.exponent
      (volume.restrict (Box3 lo hi)) := by
    intro n
    refine memLp_iff.2 ?_
    rw [eLpNorm_foldComp_finiteLp p (hw_meas n) lo hi hlt]
    have hmem : MemLp (wn n) p.exponent (volume.restrict (Box lo hi)) :=
      ((hw_cont n).memLp_of_hasCompactSupport (hw_cptsupp n)).restrict _
    exact ENNReal.mul_lt_top hCd_lt hmem.eLpNorm_lt_top
  have hDEn_mem : ∀ n, GradMemLpOn (Box3 lo hi) p.exponent
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
        foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have hcont : Continuous (fun y => fderiv ℝ (wn n) y (basisVec i)) :=
      (((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv
        (by simp)).clm_apply continuous_const
    refine memLp_iff.2 ?_
    refine lt_of_le_of_lt
      (eLpNorm_foldComp_mul_foldSign_le_finiteLp p hcont.measurable lo hi hlt i) ?_
    have hmem : MemLp (fun y => fderiv ℝ (wn n) y (basisVec i)) p.exponent
        (volume.restrict (Box lo hi)) :=
      (hcont.memLp_of_hasCompactSupport
        ((hw_cptsupp n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict _
    exact ENNReal.mul_lt_top hCd_lt hmem.eLpNorm_lt_top
  have hweak : ∀ n, HasWeakGradientOn (Box3 lo hi) (fun x => wn n (Fold lo hi x))
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
        foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have huniv := hasWeakPartialDerivOn_univ_foldComp
      ((hw_smooth n).of_le (by exact_mod_cast le_top)) (hw_cptsupp n) lo hi
      (fun k => (hlt k).le) i
    exact huniv.restrict (by rw [hbox3]; exact isOpen_Box lo3 hi3) (Set.subset_univ _)
  have htend_u : Tendsto (fun n => eLpNorm
      (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) p.exponent
        (volume.restrict (Box3 lo hi))) atTop (nhds 0) := by
    have heq : ∀ n, eLpNorm (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) p.exponent
        (volume.restrict (Box3 lo hi))
        = Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) p.exponent
          (volume.restrict (Box lo hi)) := by
      intro n
      rw [show (fun x => wn n (Fold lo hi x) - g (Fold lo hi x))
          = fun x => (wn n - g) (Fold lo hi x) from rfl,
        eLpNorm_foldComp_finiteLp p ((hw_meas n).sub hg_meas) lo hi hlt]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
      have hχ1 : χ x = 1 := hχ_one x (hBox_Icc x hxU)
      simp only [Pi.sub_apply, hwn, hχ1, one_mul, hgx]
    have hmul : Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) p.exponent
          (volume.restrict (Box lo hi))) atTop (nhds (Cd * 0)) :=
      ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_convexApproxSmoothW1p hU p u hball hr) (Or.inr hCd_lt.ne)
    rw [mul_zero] at hmul
    exact hmul.congr (fun n => (heq n).symm)
  have htend_Du : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
          foldSign (lo i) (hi i) (x i) -
        gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
      p.exponent (volume.restrict (Box3 lo hi))) atTop (nhds 0) := by
    intro i
    have hbound : ∀ n, eLpNorm
        (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
            foldSign (lo i) (hi i) (x i) -
          gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
        p.exponent (volume.restrict (Box3 lo hi))
        ≤ Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
          (volume.restrict (Box lo hi)) := by
      intro n
      rw [show (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) *
              foldSign (lo i) (hi i) (x i) -
            gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
          = fun x => (fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) -
              gi i (Fold lo hi x)) * foldSign (lo i) (hi i) (x i) by
              funext x
              ring]
      calc
        eLpNorm (fun x => (fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) -
            gi i (Fold lo hi x)) * foldSign (lo i) (hi i) (x i)) p.exponent
            (volume.restrict (Box3 lo hi))
            ≤ Cd * eLpNorm (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y)
              p.exponent (volume.restrict (Box lo hi)) :=
              eLpNorm_foldComp_mul_foldSign_le_finiteLp p
                ((((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv
                  (by simp)).clm_apply continuous_const |>.measurable.sub (hgi_meas i)) lo hi hlt i
        _ = Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
              (volume.restrict (Box lo hi)) := by
              congr 1
              refine eLpNorm_congr_ae ?_
              filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
                with x hxU hgix
              rw [hfderiv_eq n x hxU, ← hφ_grad n x i, ← hgix]
    have hrhs : Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) p.exponent
          (volume.restrict (Box lo hi))) atTop (nhds 0) := by
      have hmul := ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_grad_convexApproxSmoothW1p hU p u hball hr i)
        (Or.inr hCd_lt.ne)
      simpa using hmul
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => zero_le) hbound
  exact
    { Eu :=
        { toFun := fun x => g (Fold lo hi x)
          grad := fun x i => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)
          memLp := hEu_mem
          gradMemLp := hEu_grad_mem
          hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp p
            hEu_mem hEu_grad_mem hEn_mem hDEn_mem hweak htend_u htend_Du }
      toFun_ae := by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le,
            (Set.mem_univ_pi.1 hxU k).2.le⟩
        show g (Fold lo hi x) = u.toFun x
        rw [hfold, hgx]
      grad_ae := fun i => by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
          with x hxU hgix
        have hxk := Set.mem_univ_pi.1 hxU i
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le,
            (Set.mem_univ_pi.1 hxU k).2.le⟩
        have hsign : foldSign (lo i) (hi i) (x i) = 1 := by
          unfold foldSign
          rw [ite_eq_right (not_lt.mpr hxk.1.le), ite_eq_right (not_lt.mpr hxk.2.le)]
        show gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i) = u.grad x i
        rw [hfold, hsign, mul_one, hgix]
      eLpNorm_le := le_of_eq (by
        rw [eLpNorm_foldComp_finiteLp p hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae])
      grad_eLpNorm_le := fun i => by
        calc
          eLpNorm (fun x => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
              p.exponent (volume.restrict (Box3 lo hi))
              ≤ ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) *
                eLpNorm (gi i) p.exponent (volume.restrict (Box lo hi)) :=
                eLpNorm_foldComp_mul_foldSign_le_finiteLp p (hgi_meas i) lo hi hlt i
          _ = ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) *
                eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box lo hi)) := by
                congr 1
                rw [← eLpNorm_congr_ae (hgi_ae i)] }

end

end HCPolySupport
