/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.Extension
public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FoldNormFiniteP
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareW1p.ConvexApproxTendsto
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Coarse-graining support: Support.Sobolev.CubeEmbedding.FoldExtensionFiniteP

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Finite-`p` even-fold extension on an axis box

The `W^{1,p}` companion to `foldExtension`.  Smooth convex-domain
approximants are cut off outside the tripled box, transported by the fold, and
closed using finite-exponent Hölder pairings against compactly supported test
functions.
-/

namespace HCPolySupport

open MeasureTheory Filter Topology HCPolySupport
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

private theorem finiteLpExponent_ne_zero' (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

theorem tendsto_eLpNorm_convexApproxSmoothW1p {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (p : FiniteLpExponent)
    (u : W1pFunction U p.exponent) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto
      (fun n => eLpNorm
        (fun x => (W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr n).toFun x -
          u.toFun x) p.exponent (volume.restrict U))
      atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      fun _ hn => hn)
  have hraw :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => convexApproxSmoothing ρ u.toFun x0 r (unitConvexApproxScale n) x -
            u.toFun x) p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ p.one_lt.le p.lt_top.ne u.memLp hball hr
        tendsto_unitConvexApproxScale_zero
        (Eventually.of_forall W1pFunction.unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => convexApproxSmoothRepresentative U ρ u.toFun x0 r
              (unitConvexApproxScale n) x - u.toFun x)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u.toFun) hU hρ hx hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with x
  simp [ρ, W1pFunction.convexApproxSmoothW1p,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

theorem tendsto_eLpNorm_grad_convexApproxSmoothW1p {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (p : FiniteLpExponent)
    (u : W1pFunction U p.exponent) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (i : Fin d) :
    Tendsto
      (fun n => eLpNorm
        (fun x => (W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr n).grad x i -
          u.grad x i) p.exponent (volume.restrict U))
      atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p.exponent :=
    W1pFunction.convexApproxSmoothW1p hU p.one_lt.le u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      fun _ hn => hn)
  have hraw :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => (1 - unitConvexApproxScale n) *
              convexApproxSmoothing ρ (fun y => u.grad y i) x0 r
                (unitConvexApproxScale n) x - u.grad x i)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ p.one_lt.le p.lt_top.ne (u.grad_memLp i) hball hr
        tendsto_unitConvexApproxScale_zero
        (Eventually.of_forall W1pFunction.unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun x => (fderiv ℝ
              (convexApproxSmoothRepresentative U ρ u.toFun x0 r
                (unitConvexApproxScale n)) x) (basisVec i) - u.grad x i)
          p.exponent (volume.restrict U))
        atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply eLpNorm_congr_ae
    have hbridge := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
      (U := U) (ρ := ρ) (u := u.toFun) (gi := fun y => u.grad y i)
      (i := i) (p := p.exponent) hU hρ p.one_lt.le u.memLp (u.grad_memLp i)
      (u.hasWeakPartialDerivOn i) hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one
    filter_upwards [hbridge, ae_restrict_mem hU.isOpen.measurableSet] with x hxbridge hxU
    rw [hxbridge]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := fun y => u.grad y i) hU hρ hxU hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with x
  simp [ρ, W1pFunction.convexApproxSmoothW1p,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent) {h : Vec d → ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h p.conjugate.exponent (volume.restrict U))
    (hf : ∀ n, MemLp (f n) p.exponent (volume.restrict U))
    (hg : MemLp g p.exponent (volume.restrict U))
    (htend : Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in U, f n x * h x ∂volume)
      atTop (nhds (∫ x in U, g x * h x ∂volume)) := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
  let : ENNReal.HolderConjugate p.conjugate.exponent p.exponent := inferInstance
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp ((hf n).fun_mul (r := 1) hh))
  have hgh_int : Integrable (fun x => g x * h x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hg.fun_mul (r := 1) hh))
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ)
        = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) p.exponent μ *
      eLpNorm h p.conjugate.exponent μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h p.conjugate.exponent μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.eLpNorm_lt_top.ne)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p.exponent) (q := p.conjugate.exponent) (r := 1)
      (fun a b => a * b) 1 continuous_mul
      ((hf n).sub hg).aestronglyMeasurable hh.aestronglyMeasurable hbound
    simpa [B] using! h
  have hmeas : AEStronglyMeasurable (fun x => (f n x - g x) * h x) μ :=
    ((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable
  calc
    ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hmeas]
      simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
      apply ENNReal.toReal_mono _ hHolder
      exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_lt_top.ne hh.eLpNorm_lt_top.ne

private theorem HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent) {i : Fin d}
    {u gi : Vec d → ℝ} {u_n g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hgi : MemLp gi p.exponent (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) p.exponent (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_g : Tendsto
      (fun n => eLpNorm (fun x => g_n n x - gi x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) p.conjugate.exponent
      (volume.restrict U) := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφ_compact.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hφmem : MemLp φ p.conjugate.exponent (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
  have hlhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp p hDφ hu_n hu htend_u
  have hrhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp p hφmem hg_n hgi htend_g
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
        = -(∫ x in U, g_n n x * φ x ∂volume) :=
    fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Tendsto
      (fun n => -(∫ x in U, g_n n x * φ x ∂volume))
      atTop (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n
    rw [heq_n n]
  exact tendsto_nhds_unique hlhs' hrhs.neg

theorem HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp
    {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {u_n : ℕ → Vec d → ℝ} {Du_n : ℕ → Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hDu_n : ∀ n, GradMemLpOn U p.exponent (Du_n n))
    (hweak : ∀ n, HasWeakGradientOn U (u_n n) (Du_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => Du_n n x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakGradientOn U u Du := by
  intro i
  exact HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp p hu (hDu i)
    hu_n (fun n => hDu_n n i) (fun n => hweak n i) htend_u (htend_Du i)

/-- Data of the finite-`p` even-fold extension. -/
structure FoldExtensionFiniteP (lo hi : Vec d) (p : FiniteLpExponent)
    (u : W1pFunction (Box lo hi) p.exponent) where
  Eu : W1pFunction (Box3 lo hi) p.exponent
  toFun_ae : Eu.toFun =ᵐ[volume.restrict (Box lo hi)] u.toFun
  grad_ae : ∀ i, (fun x => Eu.grad x i) =ᵐ[volume.restrict (Box lo hi)]
    fun x => u.grad x i
  eLpNorm_le : eLpNorm Eu.toFun p.exponent (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
      eLpNorm u.toFun p.exponent (volume.restrict (Box lo hi))
  grad_eLpNorm_le : ∀ i,
    eLpNorm (fun x => Eu.grad x i) p.exponent (volume.restrict (Box3 lo hi))
      ≤ ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box lo hi))

theorem finiteLpExponent_toReal_pos' (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_ne_zero' p) p.lt_top.ne
end

end HCPolySupport
