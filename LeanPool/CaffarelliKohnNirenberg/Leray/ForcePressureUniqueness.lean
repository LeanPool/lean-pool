/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Uniqueness of the force pressure

An L⁶ function on ℝ³ with zero weak gradient vanishes almost everywhere:
its mollifications are constant, a constant in L⁶(ℝ³) is zero, and the
mollifications converge in L⁶. Hence two L⁶ functions with the same weak
gradient agree almost everywhere, which is the uniqueness statement of
`lem:force-pressure`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem forcePressure_mollify_zero {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    mollify (fun _ : Vec3 => (0 : ℝ)) ε hε x = 0 := by
  simp [mollify, convolution]

private theorem forcePressure_mollify_const_of_weakGradient_zero {q : Vec3 → ℝ}
    (hqloc : LocallyIntegrable q volume)
    (hgrad : HasWeakGradientOn (Set.univ : Set Vec3) q (fun _ => 0))
    {ε : ℝ} (hε : 0 < ε) (x y : Vec3) :
    mollify q ε hε x = mollify q ε hε y := by
  have hdiff : Differentiable ℝ (mollify q ε hε) :=
    (mollify_contDiff (n := 1) hε hqloc).differentiable (by simp)
  apply is_const_of_fderiv_eq_zero hdiff
  intro z
  have hbasis (i : Fin 3) : fderiv ℝ (mollify q ε hε) z (basisVec i) = 0 := by
    rw [fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ hqloc
      (locallyIntegrable_const 0) (hgrad i) hε (Set.subset_univ _)]
    exact forcePressure_mollify_zero hε z
  have hnorm := opNorm_eq_sum_abs_basis (fderiv ℝ (mollify q ε hε) z)
  simp only [hbasis, abs_zero, Finset.sum_const_zero] at hnorm
  exact norm_eq_zero.1 hnorm

/-- An L⁶ function on ℝ³ whose weak gradient vanishes is zero almost
everywhere. -/
theorem ae_eq_zero_of_memLp_six_of_hasWeakGradientOn_zero {q : Vec3 → ℝ}
    (hq : MemLp q 6 volume)
    (hgrad : HasWeakGradientOn (Set.univ : Set Vec3) q (fun _ => 0)) :
    q =ᵐ[volume] 0 := by
  have hqloc : LocallyIntegrable q volume := hq.locallyIntegrable (by norm_num)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hL6 := tendsto_eLpNorm_sub_zero_mollify (p := 6) (by norm_num) (by norm_num)
    hq hε hεpos
  have hfin : ∀ᶠ n in atTop,
      eLpNorm (fun x => mollify q (ε n) (hεpos n) x - q x) 6 volume < ⊤ :=
    (tendsto_order.1 hL6).2 ⊤ ENNReal.zero_lt_top
  have hvol : (volume : Measure Vec3) Set.univ = ⊤ :=
    measure_univ_of_isAddLeftInvariant volume
  have heq : ∀ᶠ n in atTop,
      eLpNorm (fun x => mollify q (ε n) (hεpos n) x - q x) 6 volume =
        eLpNorm q 6 volume := by
    filter_upwards [hfin] with n hn
    set c := mollify q (ε n) (hεpos n) 0
    have hconst : mollify q (ε n) (hεpos n) = fun _ => c := by
      funext x
      exact forcePressure_mollify_const_of_weakGradient_zero hqloc hgrad (hεpos n) x 0
    have hdiffMem : MemLp (fun x => mollify q (ε n) (hεpos n) x - q x) 6 volume :=
      hn
    have hcMem : MemLp (fun _ : Vec3 => c) 6 volume := by
      have hsum := hdiffMem.add hq
      have hfun : ((fun x => mollify q (ε n) (hεpos n) x - q x) + q) = fun _ => c := by
        funext x
        rw [hconst]
        simp
      rwa [hfun] at hsum
    have hc : c = 0 := by
      by_contra hc
      have htop := hcMem.eLpNorm_lt_top
      rw [eLpNorm_const c (by norm_num) (NeZero.ne volume), hvol,
        ENNReal.top_rpow_of_pos (by norm_num)] at htop
      have hcne : ‖c‖ₑ ≠ 0 := by simpa using hc
      rw [ENNReal.mul_top hcne] at htop
      exact lt_irrefl _ htop
    rw [hconst, hc]
    simp only [zero_sub]
    exact eLpNorm_neg (f := q) (p := 6) (μ := volume)
  have hzero : eLpNorm q 6 volume = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)) hL6
  exact (eLpNorm_eq_zero_iff (by norm_num)).1 hzero

/-- The uniqueness statement of `lem:force-pressure`: two L⁶ functions on
ℝ³ with the same weak gradient agree almost everywhere. -/
theorem ae_eq_of_memLp_six_of_hasWeakGradientOn {p₁ p₂ : Vec3 → ℝ} {G : Vec3 → Vec3}
    (h₁ : MemLp p₁ 6 volume) (h₂ : MemLp p₂ 6 volume)
    (hG₁ : HasWeakGradientOn (Set.univ : Set Vec3) p₁ G)
    (hG₂ : HasWeakGradientOn (Set.univ : Set Vec3) p₂ G) :
    p₁ =ᵐ[volume] p₂ := by
  have hloc₁ : LocallyIntegrable p₁ volume := h₁.locallyIntegrable (by norm_num)
  have hloc₂ : LocallyIntegrable p₂ volume := h₂.locallyIntegrable (by norm_num)
  have hgrad : HasWeakGradientOn (Set.univ : Set Vec3) (fun x => p₁ x - p₂ x)
      (fun _ => 0) := by
    intro i
    rw [hasWeakPartialDerivOn_iff_forall_testFunction]
    intro ψ
    have e₁ := (hasWeakPartialDerivOn_iff_forall_testFunction.1 (hG₁ i)) ψ
    have e₂ := (hasWeakPartialDerivOn_iff_forall_testFunction.1 (hG₂ i)) ψ
    simp only [setIntegral_univ] at e₁ e₂ ⊢
    have hψd : Continuous fun x => ψ.partialDeriv i x :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport fun x => ψ.partialDeriv i x :=
      ψ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left
        (g := fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (by simp)
    have hi₁ : Integrable (fun x => p₁ x * ψ.partialDeriv i x) volume :=
      hloc₁.integrable_smul_right_of_hasCompactSupport hψd hψdc
    have hi₂ : Integrable (fun x => p₂ x * ψ.partialDeriv i x) volume :=
      hloc₂.integrable_smul_right_of_hasCompactSupport hψd hψdc
    simp only [sub_mul, Pi.zero_apply, zero_mul, integral_zero, neg_zero]
    rw [integral_sub hi₁ hi₂, e₁, e₂, sub_self]
  have h := ae_eq_zero_of_memLp_six_of_hasWeakGradientOn_zero (h₁.sub h₂) hgrad
  filter_upwards [h] with x hx
  exact sub_eq_zero.1 hx

end CKN.Leray
