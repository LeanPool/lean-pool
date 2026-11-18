/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Tensor
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate

/-!
# Integration by parts and the Bochner formula for tensor fields of temperate growth

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), eqs. (15) and (16) for tensor fields: `u, v ∈ 𝒜` with
values in a finite-dimensional real inner product space `F`, the generator acting componentwise.
With orthonormal bases `(e_i)` of `E` and `(b_α)` of `F`:
`∫ ⟪ℒu, v⟫ dμ = -∫ ∑_i ⟪Du(e_i), Dv(e_i)⟫ dμ` and
`∫ ‖ℒu‖² dμ = ∫ ∑_{i,j} ‖∇²u(e_i, e_j)‖² dμ + ∫ ∑_{i,j} ∇²V(e_i, e_j) ⟪Du(e_i), Du(e_j)⟫ dμ`,
so `∇²V ≥ ρ` gives `∫ ∑_{i,j} ‖∇²u(e_i, e_j)‖² + ρ ∫ ∑_i ‖Du(e_i)‖² ≤ ∫ ‖ℒu‖²`, the inequality of
Lemma 3.4 for the tensor-valued iterates. The proofs sum the scalar identities over the components
`⟪b_α, u⟫`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ F] in
/-- Components of a temperate tensor field are temperate. -/
theorem hasTemperateGrowth_inner_left_comp {f : E → F} (hf : f.HasTemperateGrowth) (c : F) :
    (fun x => ⟪c, f x⟫).HasTemperateGrowth := by
  have h :=
    ContinuousLinearMap.bilinear_hasTemperateGrowth (innerSL ℝ)
      (Function.HasTemperateGrowth.const c) hf
  have heq : (fun x => ⟪c, f x⟫) = (innerSL ℝ c) ∘ f := by
    funext x
    change ⟪c, f x⟫ = (innerSL ℝ c) (f x)
    rw [innerSL_apply_apply]
  rw [heq]
  exact h

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
private theorem inner_weightedLaplacianVec_inner (V : E → ℝ) {f : E → F}
    (hf : ContDiff ℝ 2 f) (c : F) (x : E) :
    ⟪weightedLaplacianVec V f x, c⟫ =
      weightedLaplacian V (fun y => ⟪c, f y⟫) x := by
  calc
    ⟪weightedLaplacianVec V f x, c⟫ =
        ⟪c, weightedLaplacianVec V f x⟫ := real_inner_comm _ _
    _ = (innerSL ℝ c) (weightedLaplacianVec V f x) := by
      rw [innerSL_apply_apply]
    _ = weightedLaplacian V (fun y => (innerSL ℝ c) (f y)) x :=
      clm_apply_weightedLaplacianVec V hf (innerSL ℝ c) x
    _ = weightedLaplacian V (fun y => ⟪c, f y⟫) x := by
      simp only [innerSL_apply_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `⟪ℒu, v⟫ = ∑_α ℒ(u_α) v_α` in an orthonormal basis of `F`. -/
theorem inner_weightedLaplacianVec_eq_sum (V : E → ℝ) {f : E → F} (hf : ContDiff ℝ 2 f)
    (g : E → F) (x : E) :
    ⟪weightedLaplacianVec V f x, g x⟫ =
      ∑ α, weightedLaplacian V (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x *
        ⟪stdOrthonormalBasis ℝ F α, g x⟫ := by
    rw [← (stdOrthonormalBasis ℝ F).sum_inner_mul_inner
      (weightedLaplacianVec V f x) (g x)]
    refine Finset.sum_congr rfl ?_
    intro α hα
    rw [inner_weightedLaplacianVec_inner V hf (stdOrthonormalBasis ℝ F α) x]

section GradientComponents

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
private lemma inner_gradient_component
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (c : F) (v : E) :
    ⟪gradient (fun y => ⟪c, f y⟫) x, v⟫ =
      ⟪c, fderiv ℝ f x v⟫ := by
  have h :=
    congrArg (fun z => ⟪z, v⟫) (gradient_clm_comp hf (innerSL ℝ c))
  simpa [Function.comp_def, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_symm_apply, real_inner_comm] using h

private lemma inner_component_gradient
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (c : F) (v : E) :
    ⟪c, fderiv ℝ f x v⟫ =
      ⟪v, gradient (fun y => ⟪c, f y⟫) x⟫ := by
  calc
    ⟪c, fderiv ℝ f x v⟫ =
        ⟪gradient (fun y => ⟪c, f y⟫) x, v⟫ :=
      (inner_gradient_component hf c v).symm
    _ = ⟪v, gradient (fun y => ⟪c, f y⟫) x⟫ :=
      real_inner_comm _ _

end GradientComponents

omit [MeasurableSpace E] [BorelSpace E] in
/-- `∑_i ⟪Du(e_i), Dv(e_i)⟫ = ∑_α ⟪∇u_α, ∇v_α⟫`. -/
theorem sum_inner_fderiv_eq_sum_inner_gradient {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∑ i, ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i), fderiv ℝ g x (stdOrthonormalBasis ℝ E i)⟫ =
      ∑ α, ⟪gradient (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x,
        gradient (fun y => ⟪stdOrthonormalBasis ℝ F α, g y⟫) x⟫ := by
    classical
    let e := stdOrthonormalBasis ℝ E
    let b := stdOrthonormalBasis ℝ F
    calc
      ∑ i, ⟪fderiv ℝ f x (e i), fderiv ℝ g x (e i)⟫ =
          ∑ i, ∑ α, ⟪b α, fderiv ℝ f x (e i)⟫ *
            ⟪b α, fderiv ℝ g x (e i)⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ⟪fderiv ℝ f x (e i), fderiv ℝ g x (e i)⟫ =
              ∑ α, ⟪fderiv ℝ f x (e i), b α⟫ *
                ⟪b α, fderiv ℝ g x (e i)⟫ :=
            (b.sum_inner_mul_inner _ _).symm
          _ = ∑ α, ⟪b α, fderiv ℝ f x (e i)⟫ *
                ⟪b α, fderiv ℝ g x (e i)⟫ := by
            apply Finset.sum_congr rfl
            intro α hα
            rw [real_inner_comm (fderiv ℝ f x (e i)) (b α)]
      _ = ∑ α, ∑ i, ⟪b α, fderiv ℝ f x (e i)⟫ *
            ⟪b α, fderiv ℝ g x (e i)⟫ := by
        rw [Finset.sum_comm]
      _ = ∑ α, ⟪gradient (fun y => ⟪b α, f y⟫) x,
            gradient (fun y => ⟪b α, g y⟫) x⟫ := by
        apply Finset.sum_congr rfl
        intro α hα
        calc
          ∑ i, ⟪b α, fderiv ℝ f x (e i)⟫ *
              ⟪b α, fderiv ℝ g x (e i)⟫ =
              ∑ i, ⟪gradient (fun y => ⟪b α, f y⟫) x, e i⟫ *
                ⟪e i, gradient (fun y => ⟪b α, g y⟫) x⟫ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [inner_gradient_component hf, inner_component_gradient hg]
          _ = ⟪gradient (fun y => ⟪b α, f y⟫) x,
                gradient (fun y => ⟪b α, g y⟫) x⟫ :=
            e.sum_inner_mul_inner _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ F] in
private theorem inner_iteratedFDeriv_two_component {f : E → F} (hf : ContDiff ℝ 2 f) (c : F)
    (x v w : E) :
    ⟪c, iteratedFDeriv ℝ 2 f x ![v, w]⟫ =
      bilinearIteratedFDerivTwo ℝ (fun y => ⟪c, f y⟫) x v w := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  have h :=
    ContinuousLinearMap.iteratedFDeriv_comp_left (f := f) (g := innerSL ℝ c) (x := x) (i := 2)
      hf.contDiffAt (by norm_num)
  simpa [Function.comp_def, innerSL_apply_apply] using (congrArg (fun L => L ![v, w]) h).symm

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- `∑_{i,j} ‖∇²u(e_i, e_j)‖² = ∑_α ‖∇²u_α‖²_HS`. -/
theorem sum_norm_sq_iteratedFDeriv_two_eq {f : E → F} (hf : ContDiff ℝ 2 f) (x : E) :
    ∑ i, ∑ j, ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^ 2 =
      ∑ α, hessianSqStdBasis (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x := by
    classical
    let e := stdOrthonormalBasis ℝ E
    let b := stdOrthonormalBasis ℝ F
    have hparseval (z : F) : ‖z‖ ^ 2 = ∑ α, ⟪b α, z⟫ ^ 2 := by
      calc
        ‖z‖ ^ 2 = ⟪z, z⟫ := (real_inner_self_eq_norm_sq z).symm
        _ = ∑ α, ⟪z, b α⟫ * ⟪b α, z⟫ :=
          (b.sum_inner_mul_inner z z).symm
        _ = ∑ α, ⟪b α, z⟫ ^ 2 := by
          apply Finset.sum_congr rfl
          intro α hα
          rw [real_inner_comm z (b α)]
          ring
    calc
      ∑ i, ∑ j, ‖iteratedFDeriv ℝ 2 f x ![e i, e j]‖ ^ 2 =
          ∑ i, ∑ j, ∑ α,
            ⟪b α, iteratedFDeriv ℝ 2 f x ![e i, e j]⟫ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hparseval]
      _ = ∑ i, ∑ α, ∑ j,
            ⟪b α, iteratedFDeriv ℝ 2 f x ![e i, e j]⟫ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ α, ∑ i, ∑ j,
            ⟪b α, iteratedFDeriv ℝ 2 f x ![e i, e j]⟫ ^ 2 := by
        exact Finset.sum_comm
      _ = ∑ α, hessianSqStdBasis (fun y => ⟪b α, f y⟫) x := by
        apply Finset.sum_congr rfl
        intro α hα
        simp only [hessianSqStdBasis]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [inner_iteratedFDeriv_two_component hf]

private theorem tensorCurv_parseval (v w : F) :
    ⟪v, w⟫ = ∑ α,
      ⟪stdOrthonormalBasis ℝ F α, v⟫ * ⟪stdOrthonormalBasis ℝ F α, w⟫ := by
  classical
  calc
    ⟪v, w⟫ = ∑ α,
        ⟪v, stdOrthonormalBasis ℝ F α⟫ * ⟪stdOrthonormalBasis ℝ F α, w⟫ :=
      ((stdOrthonormalBasis ℝ F).sum_inner_mul_inner v w).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      rw [real_inner_comm v]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem tensorCurv_expand (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v : E) :
    B v v = ∑ i, ∑ j,
      B (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) *
        (⟪v, stdOrthonormalBasis ℝ E i⟫ * ⟪v, stdOrthonormalBasis ℝ E j⟫) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  calc
    B v v = B (∑ i, ⟪e i, v⟫ • e i) (∑ j, ⟪e j, v⟫ • e j) := by
      rw [e.sum_repr']
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [real_inner_comm v]
      dsimp [e]
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- `∑_{i,j} ∇²V(e_i, e_j) ⟪Du(e_i), Du(e_j)⟫ = ∑_α ∇²V(∇u_α, ∇u_α)`. -/
theorem sum_hessian_inner_fderiv_eq {V : E → ℝ} {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    ∑ i,
        ∑ j,
          bilinearIteratedFDerivTwo ℝ V x (stdOrthonormalBasis ℝ E i)
              (stdOrthonormalBasis ℝ E j) *
            ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
              fderiv ℝ f x (stdOrthonormalBasis ℝ E j)⟫ =
      ∑ α,
        bilinearIteratedFDerivTwo ℝ V x (gradient (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x)
          (gradient (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x) := by
  classical
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [tensorCurv_parseval, Finset.mul_sum]
  simp_rw [← inner_gradient_component hf]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  exact
    (tensorCurv_expand (bilinearIteratedFDerivTwo ℝ V x)
        (gradient (fun y => ⟪stdOrthonormalBasis ℝ F α, f y⟫) x)).symm

variable (m : Measure E) [m.IsAddHaarMeasure]

omit [m.IsAddHaarMeasure] in
private theorem tensorIBP_integrable_product {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ}
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ s : ℝ, Integrable (fun x => Real.exp (s * ‖x‖)) (m.tilted (-V))) {q r : E → ℝ}
    (hq : q.HasTemperateGrowth) (hr : r.HasTemperateGrowth) :
    Integrable (fun x => weightedLaplacian V q x * r x) (m.tilted (-V)) := by
  obtain ⟨kq, Cq, hCq, hbq⟩ := hq.norm_iteratedFDeriv_le_uniform 1
  obtain ⟨kr, Cr, hCr, hbr⟩ := hr.norm_iteratedFDeriv_le_uniform 0
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simpa using (norm_nonneg (gradient V 0)).trans h
  have hqg : ∀ x, ‖gradient q x‖ ≤ Cq * (1 + ‖x‖) ^ kq := by
    intro x
    simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hbq 1 le_rfl x
  have hrv : ∀ x, ‖r x‖ ≤ Cr * (1 + ‖x‖) ^ kr := by
    intro x
    simpa only [norm_iteratedFDeriv_zero] using hbr 0 le_rfl x
  have hDi : Integrable (fun x => ⟪gradient V x, gradient q x⟫ * r x) (m.tilted (-V)) := by
    apply
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _ hexp
        (((continuous_gradient hV).inner
                (continuous_gradient (hq.1.of_le (WithTop.coe_le_coe.mpr le_top)))).mul
            hr.1.continuous).aestronglyMeasurable
        (C := CV * Cq * Cr) (k := kV + kq + kr)
    intro x
    calc
      ‖⟪gradient V x, gradient q x⟫ * r x‖ ≤ ‖gradient V x‖ * ‖gradient q x‖ * ‖r x‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ (CV * (1 + ‖x‖) ^ kV) * (Cq * (1 + ‖x‖) ^ kq) * (Cr * (1 + ‖x‖) ^ kr) := by
        gcongr
        · exact hVg x
        · exact hqg x
        · exact hrv x
      _ = (CV * Cq * Cr) * (1 + ‖x‖) ^ (kV + kq + kr) := by
        rw [pow_add, pow_add]
        ring
  have hEq :
    (fun x => weightedLaplacian V q x * r x) =
      (fun x => Laplacian.laplacian q x * r x - ⟪gradient V x, gradient q x⟫ * r x) := by
    funext x
    rw [weightedLaplacian_apply, sub_mul]
  rw [hEq]
  exact
    (FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
          ((hasTemperateGrowth_laplacian hq).mul hr)).sub
      hDi

/-- **BKL (15)** for tensor fields of temperate growth. -/
theorem integral_inner_weightedLaplacianVec_eq_neg {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ}
    {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {f g : E → F}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, ⟪weightedLaplacianVec V f x, g x⟫ ∂(m.tilted (-V)) =
      -∫ x,
          ∑ i,
            ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
              fderiv ℝ g x (stdOrthonormalBasis ℝ E i)⟫ ∂(m.tilted (-V)) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let c := fun α (x : E) => ⟪b α, f x⟫
  let d := fun α (x : E) => ⟪b α, g x⟫
  have hc : ∀ α, (c α).HasTemperateGrowth := fun α =>
    (innerSL ℝ (b α)).hasTemperateGrowth.comp hf
  have hd : ∀ α, (d α).HasTemperateGrowth := fun α =>
    (innerSL ℝ (b α)).hasTemperateGrowth.comp hg
  have hLi : ∀ α, Integrable (fun x => weightedLaplacian V (c α) x * d α x) (m.tilted (-V)) :=
    fun α => tensorIBP_integrable_product m hV hVg hexp (hc α) (hd α)
  have hGi : ∀ α, Integrable (fun x => ⟪gradient (c α) x, gradient (d α) x⟫) (m.tilted (-V)) :=
    fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (hasTemperateGrowth_gamma (hc α) (hd α))
  have hLeft :
    (fun x => ⟪weightedLaplacianVec V f x, g x⟫) =
      (fun x => ∑ α, weightedLaplacian V (c α) x * d α x) := by
    funext x
    rw [← b.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro α _
    rw [real_inner_comm (b α)]
    congr 1
    exact
      clm_apply_weightedLaplacianVec V (hf.1.of_le (WithTop.coe_le_coe.mpr le_top))
        (innerSL ℝ (b α)) x
  have hRight :
    (fun x =>
        ∑ i,
          ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
            fderiv ℝ g x (stdOrthonormalBasis ℝ E i)⟫) =
      (fun x => ∑ α, ⟪gradient (c α) x, gradient (d α) x⟫) := by
    funext x
    exact
      sum_inner_fderiv_eq_sum_inner_gradient (hf.1.differentiable (by simp) x)
        (hg.1.differentiable (by simp) x)
  rw [hLeft, hRight, integral_finsetSum _ (fun α _ => hLi α),
    integral_finsetSum _ (fun α _ => hGi α)]
  simp_rw [integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth m hV hVg hexp (hc _)
      (hd _)]
  simp only [Finset.sum_neg_distrib]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem tensorEq_hessian_growth {q : E → ℝ} (hq : q.HasTemperateGrowth)
    {g h : E → E} (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    (fun x => bilinearIteratedFDerivTwo ℝ q x (g x) (h x)).HasTemperateGrowth := by
  have hdd := hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hq)
  have h1 : (fun x => fderiv ℝ (fderiv ℝ q) x (g x)).HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).bilinear_hasTemperateGrowth hg hdd
  exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hh h1

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem tensorEq_hessianSq_growth {q : E → ℝ} (hq : q.HasTemperateGrowth) :
    (hessianSqStdBasis q).HasTemperateGrowth := by
  unfold hessianSqStdBasis
  apply Function.HasTemperateGrowth.sum
  intro i _
  apply Function.HasTemperateGrowth.sum
  intro j _
  exact (tensorEq_hessian_growth hq
    (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E i))
    (Function.HasTemperateGrowth.const (stdOrthonormalBasis ℝ E j))).pow 2

/-- **BKL (16)** for tensor fields of temperate growth. -/
theorem integral_norm_sq_weightedLaplacianVec_eq {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {f : E → F}
    (hf : f.HasTemperateGrowth) :
    ∫ x, ‖weightedLaplacianVec V f x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x,
          ∑ i,
            ∑ j,
              ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
                2 ∂(m.tilted (-V)) +
        ∫ x,
          ∑ i,
            ∑ j,
              bilinearIteratedFDerivTwo ℝ V x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E j) *
                ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
                  fderiv ℝ f x (stdOrthonormalBasis ℝ E j)⟫ ∂(m.tilted (-V)) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let c := fun α (x : E) => ⟪b α, f x⟫
  have hc : ∀ α, (c α).HasTemperateGrowth := fun α =>
    (innerSL ℝ (b α)).hasTemperateGrowth.comp hf
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hL : ∀ x, ‖weightedLaplacianVec V f x‖ ^ 2 = ∑ α, weightedLaplacian V (c α) x ^ 2 := by
    intro x
    rw [← b.sum_sq_inner_right]
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    exact clm_apply_weightedLaplacianVec V hf2 (innerSL ℝ (b α)) x
  have hLi : ∀ α, Integrable (fun x => weightedLaplacian V (c α) x ^ 2) (m.tilted (-V)) :=
    fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      ((hasTemperateGrowth_weightedLaplacian hV (hc α)).pow 2)
  have hHi : ∀ α, Integrable (hessianSqStdBasis (c α)) (m.tilted (-V)) := fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (tensorEq_hessianSq_growth (hc α))
  have hBi :
    ∀ α,
      Integrable
        (fun x => bilinearIteratedFDerivTwo ℝ V x (gradient (c α) x) (gradient (c α) x))
        (m.tilted (-V)) :=
    fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (tensorEq_hessian_growth hV (hasTemperateGrowth_gradient (hc α))
        (hasTemperateGrowth_gradient (hc α)))
  have hHess :
    (fun x =>
        ∑ i,
          ∑ j,
            ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
              2) =
      (fun x => ∑ α, hessianSqStdBasis (c α) x) := by
    funext x
    exact sum_norm_sq_iteratedFDeriv_two_eq hf2 x
  have hCurv :
    (fun x =>
        ∑ i,
          ∑ j,
            bilinearIteratedFDerivTwo ℝ V x (stdOrthonormalBasis ℝ E i)
                (stdOrthonormalBasis ℝ E j) *
              ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i),
                fderiv ℝ f x (stdOrthonormalBasis ℝ E j)⟫) =
      (fun x => ∑ α, bilinearIteratedFDerivTwo ℝ V x (gradient (c α) x) (gradient (c α) x)) := by
    funext x
    exact sum_hessian_inner_fderiv_eq (hf.1.differentiable (by simp) x)
  simp_rw [hL]
  rw [hHess, hCurv]
  rw [integral_finsetSum _ (fun α _ => hLi α), integral_finsetSum _ (fun α _ => hHi α),
    integral_finsetSum _ (fun α _ => hBi α)]
  simp_rw [integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth m hV hexp (hc _)]
  exact Finset.sum_add_distrib

/-- The curvature form of (16) for tensor fields (the inequality in BKL Lemma 3.4). -/
theorem integral_hessian_add_le_norm_sq_weightedLaplacianVec {V : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {f : E → F}
    (hf : f.HasTemperateGrowth) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) :
    ∫ x,
          ∑ i,
            ∑ j,
              ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
                2 ∂(m.tilted (-V)) +
        ρ * ∫ x, ∑ i, ‖fderiv ℝ f x (stdOrthonormalBasis ℝ E i)‖ ^ 2 ∂(m.tilted (-V)) ≤
      ∫ x, ‖weightedLaplacianVec V f x‖ ^ 2 ∂(m.tilted (-V)) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let c := fun α (x : E) => ⟪b α, f x⟫
  have hc : ∀ α, (c α).HasTemperateGrowth := fun α =>
    (innerSL ℝ (b α)).hasTemperateGrowth.comp hf
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hL : ∀ x, ‖weightedLaplacianVec V f x‖ ^ 2 = ∑ α, weightedLaplacian V (c α) x ^ 2 := by
    intro x
    rw [← b.sum_sq_inner_right]
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    exact clm_apply_weightedLaplacianVec V hf2 (innerSL ℝ (b α)) x
  have hLi : ∀ α, Integrable (fun x => weightedLaplacian V (c α) x ^ 2) (m.tilted (-V)) :=
    fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      ((hasTemperateGrowth_weightedLaplacian hV (hc α)).pow 2)
  have hHi : ∀ α, Integrable (hessianSqStdBasis (c α)) (m.tilted (-V)) := fun α =>
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (tensorEq_hessianSq_growth (hc α))
  have hGi : ∀ α, Integrable (fun x => ‖gradient (c α) x‖ ^ 2) (m.tilted (-V)) := by
    intro α
    rw [← gamma_self_fun (c α)]
    exact
      FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
        (hasTemperateGrowth_gamma (hc α) (hc α))
  have hHess :
    (fun x =>
        ∑ i,
          ∑ j,
            ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
              2) =
      (fun x => ∑ α, hessianSqStdBasis (c α) x) := by
    funext x
    exact sum_norm_sq_iteratedFDeriv_two_eq hf2 x
  have hGrad :
    (fun x => ∑ i, ‖fderiv ℝ f x (stdOrthonormalBasis ℝ E i)‖ ^ 2) =
      (fun x => ∑ α, ‖gradient (c α) x‖ ^ 2) := by
    funext x
    simpa only [real_inner_self_eq_norm_sq] using
      (sum_inner_fderiv_eq_sum_inner_gradient (hf.1.differentiable (by simp) x)
        (hf.1.differentiable (by simp) x))
  rw [hHess, hGrad]
  simp_rw [hL]
  rw [integral_finsetSum _ (fun α _ => hHi α), integral_finsetSum _ (fun α _ => hGi α),
    integral_finsetSum _ (fun α _ => hLi α), Finset.mul_sum, ← Finset.sum_add_distrib]
  exact
    Finset.sum_le_sum
      (fun α _ => integral_hessianSq_add_le_of_hasTemperateGrowth m hV hexp (hc α) hH)

end FunctionalInequalities.Analysis.BakryEmery
