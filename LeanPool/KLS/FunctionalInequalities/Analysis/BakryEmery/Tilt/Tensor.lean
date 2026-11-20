/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate

/-!
# Lemma 3.6 for tensor-valued functions, and Corollary 3.7

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.6 for `u ∈ 𝒜` with values in a
finite-dimensional real normed space `F` (a tensor space): the generator acts componentwise,
`ℒu = Δu - Du(∇V)`, the tilt average of `−ℒu` at `z` is `F_{Du}(z) z`, `T_1(−ℒu) = ∫ Du dμ` and
`T_{d+1}(−ℒu) = S_{d+1} T_d(Du)`, where `T_d(Du)` is an `F`-valued `(d+1)`-linear map with the
original (derivative) index after the `d` Taylor indices and `S_{d+1}` symmetrizes these `d + 1`
arguments while the trailing indices carried by `F` are not permuted. The proof reduces to the
scalar case through continuous linear functionals on `F`. Corollary 3.7 follows for every pair of
tensor fields satisfying the relation (30) `-ℒh_{i+1} = α_{i+1} ∇₀h_i` defining the iterates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The weighted Laplacian of a vector-valued function, `ℒu = Δu - Du(∇V)`, acting componentwise. -/
def weightedLaplacianVec (V : E → ℝ) (f : E → F) (x : E) : F :=
  Laplacian.laplacian f x - fderiv ℝ f x (gradient V x)

omit [MeasurableSpace E] [BorelSpace E] in
/-- For real-valued functions the vector weighted Laplacian is the weighted Laplacian. -/
theorem weightedLaplacianVec_eq_weightedLaplacian (V f : E → ℝ) (x : E) :
    weightedLaplacianVec V f x = weightedLaplacian V f x := by
    unfold weightedLaplacianVec
    rw [weightedLaplacian_apply]
    congr 1
    rw [real_inner_comm]
    simpa only [gradient] using
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)).symm

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
/-- Continuous linear functionals commute with the weighted Laplacian. -/
theorem clm_apply_weightedLaplacianVec (V : E → ℝ) {f : E → F} (hf : ContDiff ℝ 2 f)
    (ℓ : F →L[ℝ] ℝ) (x : E) :
    ℓ (weightedLaplacianVec V f x) = weightedLaplacian V (fun y => ℓ (f y)) x := by
    have hfd : DifferentiableAt ℝ f x :=
      hf.contDiffAt.differentiableAt (by norm_num)
    have hLap :
        Laplacian.laplacian (fun y => ℓ (f y)) x =
          ℓ (Laplacian.laplacian f x) := by
      change Laplacian.laplacian (ℓ ∘ f) x =
        ℓ (Laplacian.laplacian f x)
      exact hf.contDiffAt.laplacian_CLM_comp_left
    have hderiv :
        fderiv ℝ (fun y => ℓ (f y)) x =
          ℓ.comp (fderiv ℝ f x) := by
      change fderiv ℝ (ℓ ∘ f) x =
        ℓ.comp (fderiv ℝ f x)
      exact (ℓ.hasFDerivAt.comp x hfd.hasFDerivAt).fderiv
    have hgrad :
        gradient (fun y => ℓ (f y)) x =
          (InnerProductSpace.toDual ℝ E).symm
            (ℓ.comp (fderiv ℝ f x)) := by
      change
        (InnerProductSpace.toDual ℝ E).symm
            (fderiv ℝ (fun y => ℓ (f y)) x) =
          (InnerProductSpace.toDual ℝ E).symm
            (ℓ.comp (fderiv ℝ f x))
      rw [hderiv]
    have hinner :
        ⟪gradient V x, gradient (fun y => ℓ (f y)) x⟫ =
          ℓ (fderiv ℝ f x (gradient V x)) := by
      rw [hgrad, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
      rfl
    unfold weightedLaplacianVec
    rw [weightedLaplacian_apply, map_sub, hLap, hinner]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
/-- The gradient of `ℓ ∘ f` is the Riesz representative of `ℓ ∘ Df`. -/
theorem gradient_clm_comp {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (ℓ : F →L[ℝ] ℝ) :
    gradient (fun y => ℓ (f y)) x =
      (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (fderiv ℝ f x)) := by
  apply congrArg (InnerProductSpace.toDual ℝ E).symm
  simpa [Function.comp_def] using (ℓ.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

variable (m : Measure E) [m.IsAddHaarMeasure]

section NormedSpace

variable {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [CompleteSpace E] [m.IsAddHaarMeasure] in
/-- Functions of temperate growth are integrable for every exponential tilt of a law with all
exponential moments. -/
theorem integrable_expTilt_of_hasTemperateGrowth {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} (hg : g.HasTemperateGrowth) (z : E) :
    Integrable g (expTilt (m.tilted (-V)) z) := by
    rcases hg.2 0 with ⟨k, C, hC⟩
    refine FunctionalInequalities.Probability.integrable_of_norm_le_pow (k := k) (C := C)
      (expTilt (m.tilted (-V)) z) ?_ ?_ ?_
    · exact integrable_exp_mul_norm_expTilt m hexp z
    · exact hg.1.continuous.aestronglyMeasurable
    · simpa only [norm_iteratedFDeriv_zero] using hC

section NormedSpace

variable {G H : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

section LinearTransport

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
/-- Tilt averages commute with continuous linear maps (for integrable functions). -/
theorem clm_apply_tiltAverage (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (L : G →L[ℝ] H) :
    (fun z => L (tiltAverage μ g z)) = tiltAverage μ (fun x => L (g x)) := by
    funext z
    unfold tiltAverage
    exact (L.integral_comp_comm (hg z)).symm

/-- Taylor tensors commute with continuous linear maps. -/
theorem clm_comp_taylorTensor (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (hF : ContDiff ℝ ∞ (tiltAverage μ g))
    (L : G →L[ℝ] H) (d : ℕ) :
    L.compContinuousMultilinearMap (taylorTensor μ g d) = taylorTensor μ (fun x => L (g x)) d := by
  have heq := clm_apply_tiltAverage μ hg L
  have hd : iteratedFDeriv ℝ d (fun z => L (tiltAverage μ g z)) 0 =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ d (tiltAverage μ g) 0) :=
    L.iteratedFDeriv_comp_left hF.contDiffAt
      (show (d : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [heq] at hd
  ext v
  simp [taylorTensor, hd]

end LinearTransport

end NormedSpace

omit [CompleteSpace E] [FiniteDimensional ℝ F] [m.IsAddHaarMeasure] in
private theorem tensorTilt_integrable_laplacian {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {f : E → F}
    (hf : f.HasTemperateGrowth) (z : E) :
    Integrable (Laplacian.laplacian f) (expTilt (m.tilted (-V)) z) := by
  classical
  obtain ⟨k, C, hb⟩ := hf.2 2
  have h₂ : Integrable (iteratedFDeriv ℝ 2 f) (expTilt (m.tilted (-V)) z) :=
    FunctionalInequalities.Probability.integrable_of_norm_le_pow _
      (integrable_exp_mul_norm_expTilt m hexp z)
      (hf.1.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).aestronglyMeasurable hb
  have heq :
    Laplacian.laplacian f = fun x =>
      ∑ i, iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] := by
    exact InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f
  rw [heq]
  apply integrable_finsetSum
  intro i hi
  exact
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F
          ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]).integrable_comp
      h₂

omit [FiniteDimensional ℝ E] [m.IsAddHaarMeasure] in
private theorem tensorTilt_integrable_drift {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ}
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {f : E → F}
    (hf : f.HasTemperateGrowth) (z : E) :
    Integrable (fun x => fderiv ℝ f x (gradient V x)) (expTilt (m.tilted (-V)) z) := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  apply
    FunctionalInequalities.Probability.integrable_of_norm_le_pow _
      (integrable_exp_mul_norm_expTilt m hexp z)
      ((hf.1.continuous_fderiv (by simp)).clm_apply
          (continuous_gradient hV)).aestronglyMeasurable
      (C := C * CV) (k := k + kV)
  intro x
  have hdf : ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [norm_iteratedFDeriv_one] using hb 1 le_rfl x
  calc
    ‖fderiv ℝ f x (gradient V x)‖ ≤ ‖fderiv ℝ f x‖ * ‖gradient V x‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ ≤ (C * (1 + ‖x‖) ^ k) * (CV * (1 + ‖x‖) ^ kV) := by
      exact mul_le_mul hdf (hVg x) (norm_nonneg _) (by positivity)
    _ = (C * CV) * (1 + ‖x‖) ^ (k + kV) := by
      rw [pow_add]
      ring

/-- **BKL (48)** for `F`-valued `u ∈ 𝒜`: `F_{−ℒu}(z) = F_{Du}(z) z`. -/
theorem tiltAverage_neg_weightedLaplacianVec {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ}
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {f : E → F} (hf : f.HasTemperateGrowth) (z : E) :
    tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacianVec V f x) z =
      tiltAverage (m.tilted (-V)) (fderiv ℝ f) z z := by
  let : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  let μ : Measure E := m.tilted (-V)
  have hdf := hasTemperateGrowth_fderiv hf
  have hDi := integrable_expTilt_of_hasTemperateGrowth m hexp hdf z
  have hLi : Integrable (fun x => -weightedLaplacianVec V f x) (expTilt μ z) :=
    ((tensorTilt_integrable_laplacian m hexp hf z).sub
      (tensorTilt_integrable_drift m hV hVg hexp hf z)).neg
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro ℓ
  let R : (E →L[ℝ] F) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ E F ℝ) ℓ)
  have hscalar : (fun x => ℓ (f x)).HasTemperateGrowth :=
    ℓ.hasTemperateGrowth.comp hf
  have hgrad : gradient (fun x => ℓ (f x)) = fun x => R (fderiv ℝ f x) := by
    funext x
    exact gradient_clm_comp (hf.1.differentiable (by simp) x) ℓ
  have hAvg : tiltAverage μ (gradient (fun x => ℓ (f x))) z =
      R (tiltAverage μ (fderiv ℝ f) z) := by
    rw [hgrad]
    exact R.integral_comp_comm hDi
  calc
    ℓ (tiltAverage μ (fun x => -weightedLaplacianVec V f x) z) =
        ∫ x, ℓ (-weightedLaplacianVec V f x) ∂(expTilt μ z) :=
      (ℓ.integral_comp_comm hLi).symm
    _ = tiltAverage μ (fun x => -weightedLaplacian V (fun y => ℓ (f y)) x) z := by
      apply integral_congr_ae
      filter_upwards with x
      rw [map_neg, clm_apply_weightedLaplacianVec V
        (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)) ℓ x]
    _ = ⟪z, tiltAverage μ (gradient (fun x => ℓ (f x))) z⟫ :=
      tiltAverage_neg_weightedLaplacian_of_hasTemperateGrowth m hV hVg hexp hscalar z
    _ = ℓ (tiltAverage μ (fderiv ℝ f) z z) := by
      rw [hAvg, real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)

omit [CompleteSpace E] in
private theorem tensorTaylor_smooth_average [CompleteSpace G] {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} (hg : g.HasTemperateGrowth) :
    ContDiff ℝ ∞ (tiltAverage (m.tilted (-V)) g) := by
  by_cases hi : Integrable (fun x => Real.exp ((-V) x)) m
  · let := isProbabilityMeasure_tilted hi
    obtain ⟨k, C, hb⟩ := hg.2 0
    apply contDiff_tiltAverage_of_norm_le_pow (m.tilted (-V)) hexp
      hg.1.continuous.aestronglyMeasurable (M := C) (k := k)
    intro x
    simpa only [norm_iteratedFDeriv_zero] using hb x
  · have hzero := tilted_of_not_integrable hi
    have heq : tiltAverage (m.tilted (-V)) g = fun _ => (0 : G) := by
      funext z
      simp [tiltAverage, expTilt, hzero]
    rw [heq]
    exact contDiff_const

end NormedSpace

/-- **BKL Lemma 3.6, (50)**, for `F`-valued `u ∈ 𝒜`: `T_{d+1}(−ℒu) = S_{d+1} T_d(Du)`, with the
derivative index of `T_d(Du)` placed after its `d` Taylor indices. -/
theorem taylorTensor_neg_weightedLaplacianVec {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ}
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {f : E → F} (hf : f.HasTemperateGrowth) (d : ℕ) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacianVec V f x) (d + 1) =
      symmetrizeML (taylorTensor (m.tilted (-V)) (fderiv ℝ f) d).uncurryRight := by
  let : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  let μ : Measure E := m.tilted (-V)
  have hdf := hasTemperateGrowth_fderiv hf
  have hD := tensorTaylor_smooth_average m hexp hdf
  have hEq : tiltAverage μ (fun x => -weightedLaplacianVec V f x) =
      fun z => tiltAverage μ (fderiv ℝ f) z z := by
    funext z
    exact tiltAverage_neg_weightedLaplacianVec m hV hVg hexp hf z
  have hN : ContDiff ℝ ∞ (tiltAverage μ (fun x => -weightedLaplacianVec V f x)) := by
    rw [hEq]
    exact hD.clm_apply contDiff_id
  ext v
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro ℓ
  let R : (E →L[ℝ] F) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ E F ℝ) ℓ)
  have hscalar : (fun x => ℓ (f x)).HasTemperateGrowth :=
    ℓ.hasTemperateGrowth.comp hf
  have hgrad : gradient (fun x => ℓ (f x)) = fun x => R (fderiv ℝ f x) := by
    funext x
    exact gradient_clm_comp (hf.1.differentiable (by simp) x) ℓ
  have hAvg : tiltAverage μ (gradient (fun x => ℓ (f x))) =
      fun z => R (tiltAverage μ (fderiv ℝ f) z) := by
    rw [hgrad]
    exact (clm_apply_tiltAverage μ
      (integrable_expTilt_of_hasTemperateGrowth m hexp hdf) R).symm
  have hfun : (fun z => ℓ (tiltAverage μ (fun x => -weightedLaplacianVec V f x) z)) =
      tiltAverage μ (fun x => -weightedLaplacian V (fun y => ℓ (f y)) x) := by
    funext z
    rw [hEq, tiltAverage_neg_weightedLaplacian_of_hasTemperateGrowth m hV hVg hexp hscalar,
      hAvg, real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
      (y := ℓ.comp (tiltAverage μ (fderiv ℝ f) z)) (x := z)).symm
  have hd : iteratedFDeriv ℝ (d + 1)
      (fun z => ℓ (tiltAverage μ (fun x => -weightedLaplacianVec V f x) z)) 0 =
      ℓ.compContinuousMultilinearMap
        (iteratedFDeriv ℝ (d + 1) (tiltAverage μ (fun x => -weightedLaplacianVec V f x)) 0) :=
    ℓ.iteratedFDeriv_comp_left hN.contDiffAt
      (show ((d + 1 : ℕ) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [hfun] at hd
  have hleft : ℓ (taylorTensor μ (fun x => -weightedLaplacianVec V f x) (d + 1) v) =
      taylorTensor μ (fun x => -weightedLaplacian V (fun y => ℓ (f y)) x) (d + 1) v := by
    simp [taylorTensor, hd]
  have hR : R.compContinuousMultilinearMap (taylorTensor μ (fderiv ℝ f) d) =
      taylorTensor μ (gradient (fun x => ℓ (f x))) d := by
    rw [hgrad]
    exact clm_comp_taylorTensor μ (integrable_expTilt_of_hasTemperateGrowth m hexp hdf) hD R d
  rw [hleft, taylorTensor_neg_weightedLaplacian_of_hasTemperateGrowth m hV hVg hexp hscalar]
  have hp : appendInner (taylorTensor μ (gradient (fun x => ℓ (f x))) d) =
      ℓ.compContinuousMultilinearMap (taylorTensor μ (fderiv ℝ f) d).uncurryRight := by
    rw [← hR]
    ext w
    simp only [appendInner, ContinuousMultilinearMap.uncurryRight_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
  rw [hp, ← clm_comp_symmetrizeML]
  rfl

/-- **BKL Lemma 3.6, (49)**, for `F`-valued `u ∈ 𝒜`: `T_1(−ℒu)(h) = (∫ Du dμ)(h₀)`. -/
theorem taylorTensor_one_neg_weightedLaplacianVec {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ}
    {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {f : E → F} (hf : f.HasTemperateGrowth) (h : Fin 1 → E) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacianVec V f x) 1 h =
      (∫ x, fderiv ℝ f x ∂(m.tilted (-V))) (h 0) := by
    classical
    have hmain :=
      taylorTensor_neg_weightedLaplacianVec (m := m) hV hVg hexp hf 0
    have hmain' := congrArg (fun T => T h) hmain
    simpa [taylorTensor, symmetrizeML,
      ContinuousMultilinearMap.uncurryRight_apply, tiltAverage, expTilt] using hmain'

section Corollary

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The centered derivative `∇₀u = Du - ∫ Du dμ` (BKL (22)). -/
def centeredFDeriv (μ : Measure E) (f : E → G) (x : E) : E →L[ℝ] G :=
  fderiv ℝ f x - ∫ y, fderiv ℝ f y ∂μ

section NormedSpace

variable {H : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem cor37_iteratedFDeriv_sub_const (F : E → H) (c : H) {d : ℕ} (hd : 1 ≤ d) :
    iteratedFDeriv ℝ d (fun x => F x - c) = iteratedFDeriv ℝ d F := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  funext x
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_sub_const]

section CompleteSpace

variable [CompleteSpace H]

omit [CompleteSpace E] in
/-- Taylor tensors of degree `d ≥ 1` do not see constants: `T_d(f - c) = T_d f`. -/
theorem taylorTensor_sub_const {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {f : E → H} (hf : f.HasTemperateGrowth) (c : H) {d : ℕ} (hd : 1 ≤ d) :
    taylorTensor (m.tilted (-V)) (fun x => f x - c) d = taylorTensor (m.tilted (-V)) f d := by
  by_cases hi : Integrable (fun x => Real.exp ((-V) x)) m
  · let := isProbabilityMeasure_tilted hi
    have hprob : ∀ z : E, IsProbabilityMeasure (expTilt (m.tilted (-V)) z) := by
      intro z
      apply isProbabilityMeasure_tilted
      refine (hexp ‖z‖).mono'
        (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    have havg : tiltAverage (m.tilted (-V)) (fun x => f x - c) =
        fun z => tiltAverage (m.tilted (-V)) f z - c := by
      funext z
      let := hprob z
      simp only [tiltAverage]
      rw [integral_sub (integrable_expTilt_of_hasTemperateGrowth m hexp hf z)
        (integrable_const c), integral_const]
      simp
    unfold taylorTensor
    rw [havg, cor37_iteratedFDeriv_sub_const _ _ hd]
  · have hzero := tilted_of_not_integrable hi
    have hz (q : E → H) : tiltAverage (m.tilted (-V)) q = fun _ => (0 : H) := by
      funext z
      simp [tiltAverage, expTilt, hzero]
    simp only [taylorTensor, hz]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
omit [CompleteSpace H] in
/-- Taylor tensors are homogeneous for vector-valued functions. -/
theorem taylorTensor_const_smul (μ : Measure E) (a : ℝ) (f : E → H) (d : ℕ) :
    taylorTensor μ (fun x => a • f x) d = a • taylorTensor μ f d := by
    have havg :
        tiltAverage μ (fun x => a • f x) =
          (fun x => a • tiltAverage μ f x) := by
      funext x
      simp [tiltAverage, integral_smul]
    by_cases ha : a = 0
    · subst a
      have hz :
          tiltAverage μ (fun x => (0 : ℝ) • f x) = (0 : E → H) := by
        funext x
        simp [tiltAverage]
      unfold taylorTensor
      rw [hz]
      simp
    · let L : H →L[ℝ] H := a • ContinuousLinearMap.id ℝ H
      let L' : H →L[ℝ] H := a⁻¹ • ContinuousLinearMap.id ℝ H
      let e : H ≃L[ℝ] H :=
        ContinuousLinearEquiv.equivOfInverse L L'
          (by
            intro x
            simp [L, L', ha])
          (by
            intro x
            simp [L, L', ha])
      have he : ∀ x : H, e x = a • x := by
        intro x
        change L x = a • x
        simp [L]
      unfold taylorTensor
      rw [havg]
      have hcomp :
          (fun x => a • tiltAverage μ f x) =
            e ∘ tiltAverage μ f := by
        funext x
        change a • tiltAverage μ f x = e (tiltAverage μ f x)
        rw [he]
      rw [hcomp, e.iteratedFDeriv_comp_left]
      have hmap :
          (e : H →L[ℝ] H).compContinuousMultilinearMap
              (iteratedFDeriv ℝ d (tiltAverage μ f) 0) =
            a • iteratedFDeriv ℝ d (tiltAverage μ f) 0 := by
        ext x
        change e ((iteratedFDeriv ℝ d (tiltAverage μ f) 0) x) =
          a • (iteratedFDeriv ℝ d (tiltAverage μ f) 0) x
        exact he _
      rw [hmap]
      simp only [smul_smul]
      rw [mul_comm]

end CompleteSpace

end NormedSpace

/-- **BKL Corollary 3.7.** If `h` is a tensor field of temperate growth and `g` a tensor field with
`-ℒh = α ∇₀g` (the relation (30) defining `h = h_{i+1}` from `g = h_i`), then for `d ≥ 1`
`S_{d+1} T_d(∇₀h) = T_{d+1}(-ℒh) = α T_{d+1}(∇₀g)`. -/
theorem symmetrizeML_taylorTensor_centeredFDeriv {V : E → ℝ} (hV : ContDiff ℝ 1 V) {CV : ℝ}
    {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} {h : E → (E →L[ℝ] G)} (hh : h.HasTemperateGrowth)
    {α : ℝ} (hrel : ∀ x, -weightedLaplacianVec V h x = α • centeredFDeriv (m.tilted (-V)) g x)
    {d : ℕ} (hd : 1 ≤ d) :
    symmetrizeML (taylorTensor (m.tilted (-V)) (centeredFDeriv (m.tilted (-V)) h) d).uncurryRight =
        taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacianVec V h x) (d + 1) ∧
      taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacianVec V h x) (d + 1) =
        α • taylorTensor (m.tilted (-V)) (centeredFDeriv (m.tilted (-V)) g) (d + 1) := by
    have hcenter :
        taylorTensor (m.tilted (-V)) (centeredFDeriv (m.tilted (-V)) h) d =
          taylorTensor (m.tilted (-V)) (fderiv ℝ h) d := by
      change
        taylorTensor (m.tilted (-V))
            (fun x => fderiv ℝ h x -
              ∫ y, fderiv ℝ h y ∂(m.tilted (-V))) d =
          taylorTensor (m.tilted (-V)) (fderiv ℝ h) d
      exact
        taylorTensor_sub_const (m := m) (V := V) hexp
          (hasTemperateGrowth_fderiv hh)
          (∫ y, fderiv ℝ h y ∂(m.tilted (-V))) hd
    have hneg :=
      taylorTensor_neg_weightedLaplacianVec m hV hVg hexp hh d
    have hfun :
        (fun x => -weightedLaplacianVec V h x) =
          (fun x => α • centeredFDeriv (m.tilted (-V)) g x) :=
      funext hrel
    constructor
    · rw [hcenter]
      exact hneg.symm
    · calc
        taylorTensor (m.tilted (-V))
            (fun x => -weightedLaplacianVec V h x) (d + 1) =
            taylorTensor (m.tilted (-V))
              (fun x => α • centeredFDeriv (m.tilted (-V)) g x) (d + 1) := by
          exact congrArg
            (fun f => taylorTensor (m.tilted (-V)) f (d + 1)) hfun
        _ = α •
            taylorTensor (m.tilted (-V))
              (centeredFDeriv (m.tilted (-V)) g) (d + 1) := by
          exact
            taylorTensor_const_smul (m.tilted (-V)) α
              (centeredFDeriv (m.tilted (-V)) g) (d + 1)

end Corollary

end FunctionalInequalities.Analysis.BakryEmery
