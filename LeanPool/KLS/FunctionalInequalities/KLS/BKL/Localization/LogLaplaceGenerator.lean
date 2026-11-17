/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.LogPartition
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
/-!
# BKL (71) in generator form

For every `z`, the generator of the localization equations (67) applied to the posterior log-Laplace
transform
`Λ_p(z) = ψ(c + z, Q) − ψ(c, Q)` equals `−½ ⟪v, A⁻¹ v⟫` with `v = a(c + z, Q) − a(c, Q)`
(`generator_logLaplace_posterior`): `∫ e^{⟪z,x⟫} dμ_p = e^{Λ_p(z)}` has zero generator by the
generator cancellation
of the posterior, and the chain rule for `exp` gives the formula. Includes partial-derivative
helpers on the parameter
space.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open scoped ContDiff

section Bridges

variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup L]
  [NormedSpace ℝ L]

/--
The joint derivative in a first-factor direction is the partial derivative in the first factor. -/
theorem fderiv_fst_dir (H : E × L → ℝ) (p : E × L) (hH : DifferentiableAt ℝ H p) (u : E) :
    fderiv ℝ H p (u, 0) = fderiv ℝ (fun y => H (y, p.2)) p.1 u := by
  have h := hH.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  have h' :
    fderiv ℝ (fun y => H (y, p.2)) p.1 = (fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ E L) :=
    h.fderiv
  rw [h']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The joint derivative in a second-factor direction is the derivative along the line `Q + t M`. -/
theorem fderiv_snd_dir (H : E × L → ℝ) (p : E × L) (hH : DifferentiableAt ℝ H p) (M : L) :
    fderiv ℝ H p (0, M) = deriv (fun t : ℝ => H (p.1, p.2 + t • M)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p.2 + t • M) M 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const M).const_add p.2
  have hγ : HasDerivAt (fun t : ℝ => (p.1, p.2 + t • M)) ((0 : E), M) 0 :=
    (hasDerivAt_const (0 : ℝ) p.1).prodMk h1
  have h := hH.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  exact (h.deriv).symm

/-- Joint derivative along `(b, M)` splits into the two partial derivatives. -/
theorem fderiv_prod_split (H : E × L → ℝ) (p : E × L) (hH : DifferentiableAt ℝ H p) (b : E)
    (M : L) :
    fderiv ℝ H p (b, M) =
      fderiv ℝ (fun y => H (y, p.2)) p.1 b + deriv (fun t : ℝ => H (p.1, p.2 + t • M)) 0 := by
  rw [← fderiv_fst_dir H p hH b, ← fderiv_snd_dir H p hH M, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end Bridges

section SecondBridge

variable {E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- The joint second derivative along a first-factor direction is the `c`-Hessian of the
restriction. -/
theorem fderiv_fderiv_fst_dir (H : E × L → ℝ) (hH : ContDiff ℝ 2 H) (p : E × L) (u : E) :
    fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) =
      bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1 u u := by
  have hH1 : ContDiff ℝ (1 + 1) H := by
    convert hH using 1; norm_num
  have hHf : ContDiff ℝ 1 (fderiv ℝ H) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := H) (n := 1)).mp hH1 |>.2.2
  have hHfd : Differentiable ℝ (fderiv ℝ H) := hHf.differentiable_one
  have hHd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hrestr : ContDiff ℝ 2 (fun y => H (y, p.2)) :=
    hH.comp (contDiff_id.prodMk contDiff_const)
  rw [BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hrestr]
  have h1 : fderiv ℝ (fun y => fderiv ℝ H y (u, 0)) p (u, 0) =
      fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) := by
    rw [((hHfd p).hasFDerivAt.clm_apply (hasFDerivAt_const (u, 0) p)).fderiv]
    simp
  rw [← h1]
  have h2 : (fun y => fderiv ℝ (fun y' => H (y', p.2)) y u) =
      fun y => fderiv ℝ H (y, p.2) (u, 0) := by
    funext y
    exact (fderiv_fst_dir H (y, p.2) (hHd _) u).symm
  rw [h2]
  have hK : DifferentiableAt ℝ (fun y => fderiv ℝ H y (u, 0)) p :=
    (hHfd p).clm_apply (differentiableAt_const _)
  exact fderiv_fst_dir (fun y => fderiv ℝ H y (u, 0)) p hK u

end SecondBridge

section Trace

variable {n : ℕ}

/-- Trace rearrangement `Σ_k B(σ e_k, σ e_k) = Σ_i B(σ σ e_i, e_i)` for a self-adjoint `σ`. -/
theorem sum_bilin_inverseSqrt_eq
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
    (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) :
    ∑ k, B (σ (EuclideanSpace.single k 1)) (σ (EuclideanSpace.single k 1)) =
      ∑ i, B (σ (σ (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he : ∀ i, EuclideanSpace.single i (1 : ℝ) = e i := fun i =>
    (EuclideanSpace.basisFun_apply (Fin n) ℝ i).symm
  simp only [he]
  have hσe : ∀ i, σ (e i) = ∑ k, ⟪e i, σ (e k)⟫ • e k := by
    intro i
    conv_lhs => rw [← e.sum_repr' (σ (e i))]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [← hσ (e i) (e k), real_inner_comm]
  calc
    ∑ k, B (σ (e k)) (σ (e k)) = ∑ k, B (σ (e k)) (∑ i, ⟪e i, σ (e k)⟫ • e i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [e.sum_repr' (σ (e k))]
    _ = ∑ k, ∑ i, ⟪e i, σ (e k)⟫ * B (σ (e k)) (e i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul]
    _ = ∑ i, ∑ k, ⟪e i, σ (e k)⟫ * B (σ (e k)) (e i) := Finset.sum_comm
    _ = ∑ i, B (σ (∑ k, ⟪e i, σ (e k)⟫ • e k)) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum, map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i, B (σ (σ (e i))) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hσe i]

/-- `Σ_k ⟪σ e_k, v⟫² = ⟪v, σ σ v⟫` for a self-adjoint `σ`. -/
theorem sum_inner_inverseSqrt_sq (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) (v : EuclideanSpace ℝ (Fin n)) :
    ∑ k, ⟪σ (EuclideanSpace.single k 1), v⟫ * ⟪σ (EuclideanSpace.single k 1), v⟫ =
      ⟪v, σ (σ v)⟫ := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he : ∀ i, EuclideanSpace.single i (1 : ℝ) = e i := fun i =>
    (EuclideanSpace.basisFun_apply (Fin n) ℝ i).symm
  simp only [he]
  calc
    ∑ k, ⟪σ (e k), v⟫ * ⟪σ (e k), v⟫ = ∑ k, ⟪σ v, e k⟫ * ⟪e k, σ v⟫ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hσ, real_inner_comm (e k) (σ v)]
    _ = ⟪σ v, σ v⟫ := e.sum_inner_mul_inner (σ v) (σ v)
    _ = ⟪v, σ (σ v)⟫ := by rw [real_inner_comm, hσ]

end Trace

section ExpDeriv

theorem fderiv_exp_apply' (t u : ℝ) : fderiv ℝ Real.exp t u = Real.exp t * u := by
  rw [(Real.hasDerivAt_exp t).hasFDerivAt.fderiv]
  simp [mul_comm]

theorem fderiv_fderiv_exp_apply (t u v : ℝ) :
    fderiv ℝ (fderiv ℝ Real.exp) t u v = Real.exp t * u * v := by
  have h2 : fderiv ℝ Real.exp = fun s => Real.exp s • (1 : ℝ →L[ℝ] ℝ) := by
    funext s
    refine ContinuousLinearMap.ext fun w => ?_
    rw [fderiv_exp_apply']
    simp
  have h3 : HasFDerivAt (fun s => Real.exp s • (1 : ℝ →L[ℝ] ℝ))
      ((fderiv ℝ Real.exp t).smulRight (1 : ℝ →L[ℝ] ℝ)) t :=
    Real.differentiableAt_exp.hasFDerivAt.smul_const (1 : ℝ →L[ℝ] ℝ)
  rw [h2, h3.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
  rw [fderiv_exp_apply']

end ExpDeriv

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- Self-adjointness and the square identity of the diffusion coefficient `σ = A(p)^{-1/2}`. -/
theorem inverseSqrt_cov_props (hiso : KLS.Isotropic μ) (p : Param n) :
    (∀ u v, ⟪inverseSqrt (cov μ hc p) u, v⟫ = ⟪u, inverseSqrt (cov μ hc p) v⟫) ∧
      ∀ v, inverseSqrt (cov μ hc p) (inverseSqrt (cov μ hc p) v) = Ring.inverse (cov μ hc p) v := by
  have hspec := Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2
  dsimp only at hspec
  obtain ⟨hsa, -, -, hsq, -, -, -⟩ := hspec
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) u v
  · change (inverseSqrt (cov μ hc p) * inverseSqrt (cov μ hc p)) v = _
    exact congrArg (fun T => T v) hsq

/-- The generator of (67) in partial-derivative form for a jointly `C²` observable:
`𝓛H = D_cH[A⁻¹a] + ∂_QH[A⁻¹] + ½ Σ_i D²_cH[A⁻¹e_i, e_i]`. -/
theorem generator_eq_partial (hiso : KLS.Isotropic μ) (H : Param n → ℝ) (hH : ContDiff ℝ 2 H)
    (p : Param n) :
    generator μ hc H p =
      fderiv ℝ (fun y => H (y, p.2)) p.1
          (Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2)) +
        deriv (fun t : ℝ => H (p.1, p.2 + t • Ring.inverse (cov μ hc p))) 0 +
        (1 / 2 : ℝ) * ∑ i, bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1
          (Ring.inverse (cov μ hc p) (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) := by
  obtain ⟨hσ, hM⟩ := inverseSqrt_cov_props μ hc hiso p
  have hd : DifferentiableAt ℝ H p := (hH.differentiable (by norm_num)) p
  unfold generator diffusionGenerator drift noise
  rw [fderiv_prod_split H p hd]
  simp_rw [fderiv_fderiv_fst_dir H hH p]
  rw [sum_bilin_inverseSqrt_eq (bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1)
    (inverseSqrt (cov μ hc p)) hσ]
  simp only [hM]

/-- The generator of (67) kills the posterior expectation of `e^{⟪z,·⟫}` (joint form of the
cancellation lemma). -/
theorem generator_posteriorExpectation_exp_inner (hiso : KLS.Isotropic μ)
    (z : EuclideanSpace ℝ (Fin n)) (p : Param n) :
    generator μ hc
      (fun q : Param n => posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) p = 0 := by
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪z, x⟫) := by fun_prop
  obtain ⟨C, hC, hCb⟩ := exists_bound_on_support_of_compact μ hc
    (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪z, x⟫))
  have hsm : ContDiff ℝ 2
      (fun q : Param n => posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) :=
    (contDiff_posteriorExpectation_joint μ hc hf hCb).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [generator_eq_partial μ hc hiso _ hsm p]
  have hcancel := Isotropic.compactPosterior_generator_cancellation μ hc hiso hf hC hCb p.1 p.2
    (EuclideanSpace.basisFun (Fin n) ℝ)
  dsimp only at hcancel
  simp only [EuclideanSpace.basisFun_apply] at hcancel
  exact hcancel

include hc in
/-- The posterior expectation of `e^{⟪z,·⟫}` is `exp (ψ(c + z, Q) − ψ(c, Q))`. -/
theorem posteriorExpectation_exp_inner_eq_exp (z : EuclideanSpace ℝ (Fin n)) (q : Param n) :
    posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫) =
      Real.exp (logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) := by
  have hpos :
    ∀ (c : EuclideanSpace ℝ (Fin n))
      (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      0 < ∫ x, Real.exp (quadraticExponent c Q x) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun c Q =>
    integral_exp_pos
      (integrable_exp_of_compact μ hc
        (by
          unfold quadraticExponent
          fun_prop))
  have heq :
    (fun x : EuclideanSpace ℝ (Fin n) =>
        Real.exp (quadraticExponent q.1 q.2 x) * Real.exp ⟪z, x⟫) =
      fun x => Real.exp (quadraticExponent (q.1 + z) q.2 x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [quadraticExponent, inner_add_left]
    ring
  unfold posteriorExpectation logPartition
  rw [integral_tilted_eq_div, heq, Real.exp_sub, Real.exp_log (hpos _ _),
    Real.exp_log (hpos _ _)]

include hc in
/-- Joint smoothness of the log-Laplace transform `Λ(q) = ψ(q.1 + z, q.2) − ψ(q.1, q.2)`. -/
theorem contDiff_logLaplace_joint (z : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞
      (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) := by
  have hjoint := contDiff_logPartition_joint μ hc
  have hmap : ContDiff ℝ ∞ (fun q : Param n => ((q.1 + z, q.2) : Param n)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have h1 := hjoint.comp hmap
  have h1' : ContDiff ℝ ∞ (fun q : Param n => logPartition μ (q.1 + z) q.2) := by
    convert h1 using 1
    rfl
  exact h1'.sub hjoint

include hc in
/--
`D_c Λ[u] = ⟪u, a(c + z, Q) − a(c, Q)⟫` for the log-Laplace transform `Λ(q) = ψ(q.1 + z, q.2) −
ψ(q.1, q.2)`. -/
theorem fderiv_logLaplace_fst_dir (z : EuclideanSpace ℝ (Fin n)) (p : Param n)
    (u : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) p
        (u, 0) =
      ⟪u, posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2⟫ := by
  have hjoint := contDiff_logPartition_joint μ hc
  have hψ : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => logPartition μ y p.2) := by
    have hmap : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ((y, p.2) : Param n)) :=
      contDiff_id.prodMk contDiff_const
    have h := hjoint.comp hmap
    convert h using 1
    rfl
  have hψz : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => logPartition μ (y + z) p.2) := by
    have hmap : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => y + z) :=
      contDiff_id.add contDiff_const
    have h := hψ.comp hmap
    convert h using 1
    rfl
  have hΛ := contDiff_logLaplace_joint μ hc z
  rw [fderiv_fst_dir _ p (hΛ.differentiable (by norm_num) p) u]
  change
    fderiv ℝ
        (fun y : EuclideanSpace ℝ (Fin n) => logPartition μ (y + z) p.2 - logPartition μ y p.2)
        p.1 u =
      _
  rw [fderiv_fun_sub (hψz.differentiable (by norm_num) p.1)
      (hψ.differentiable (by norm_num) p.1),
    sub_apply,
    fderiv_comp_add_right (f := fun y : EuclideanSpace ℝ (Fin n) => logPartition μ y p.2) z,
    fderiv_logPartition_c_apply μ hc, fderiv_logPartition_c_apply μ hc, inner_sub_right]

/--
**BKL (71) in generator form**: for every `z`, the generator of (67) applied to the log-Laplace
transform of the posterior, `Λ_p(z) = ψ(c + z, Q) − ψ(c, Q)`, is `−½ ⟪v, A⁻¹ v⟫` with
`v = a(c + z, Q) − a(c, Q)` (the drift of `dΛ_t(z)` in (71)); every parameter `p`, isotropic compact
prior. -/
theorem generator_logLaplace_posterior (hiso : KLS.Isotropic μ) (z : EuclideanSpace ℝ (Fin n))
    (p : Param n) :
    generator μ hc (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2)
        p =
      -(1 / 2 : ℝ) *
        ⟪posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2,
          Ring.inverse (cov μ hc p)
            (posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2)⟫ := by
  obtain ⟨hσ, hM⟩ := inverseSqrt_cov_props μ hc hiso p
  set Λ : Param n → ℝ := fun q => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2 with
    hΛdef
  set v := posteriorMean μ (p.1 + z) p.2 - posteriorMean μ p.1 p.2 with hvdef
  have hΛ : ContDiff ℝ ∞ Λ := contDiff_logLaplace_joint μ hc z
  have hΛ2 : ContDiff ℝ 2 Λ := hΛ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF :
    (fun q : Param n => posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) =
      Real.exp ∘ Λ := by
    funext q
    exact posteriorExpectation_exp_inner_eq_exp μ hc z q
  have hzero := generator_posteriorExpectation_exp_inner μ hc hiso z p
  rw [hF] at hzero
  unfold generator at hzero
  rw [diffusionGenerator_comp _ _ Real.exp Λ p Real.contDiff_exp hΛ2] at hzero
  simp only [fderiv_exp_apply', fderiv_fderiv_exp_apply, smul_eq_mul] at hzero
  have hd :
    ∀ k,
      fderiv ℝ Λ p (noise μ hc p k) =
        ⟪inverseSqrt (cov μ hc p) (EuclideanSpace.single k 1), v⟫ := by
    intro k
    exact fderiv_logLaplace_fst_dir μ hc z p _
  have hsum :
    ∑ k, fderiv ℝ Λ p (noise μ hc p k) * fderiv ℝ Λ p (noise μ hc p k) =
      ⟪v, Ring.inverse (cov μ hc p) v⟫ := by
    simp only [hd]
    rw [sum_inner_inverseSqrt_sq _ hσ v, hM]
  have hS :
    ∑ k, Real.exp (Λ p) * fderiv ℝ Λ p (noise μ hc p k) * fderiv ℝ Λ p (noise μ hc p k) =
      Real.exp (Λ p) * ⟪v, Ring.inverse (cov μ hc p) v⟫ := by
    rw [← hsum, Finset.mul_sum]
    simp only [mul_assoc]
  rw [hS] at hzero
  have hexp : Real.exp (Λ p) ≠ 0 := (Real.exp_pos _).ne'
  unfold generator diffusionGenerator
  apply mul_left_cancel₀ hexp
  linear_combination hzero

end FunctionalInequalities.KLS.BKL.Localization
