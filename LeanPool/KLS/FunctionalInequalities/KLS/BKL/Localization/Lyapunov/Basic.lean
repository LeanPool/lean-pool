/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.NoiseBound
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.HilbertSchmidt
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.VectorGenerator
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.InverseCalculus
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Regularity
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator

/-!
# The Lyapunov function and its exact generator calculus
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

private abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

private def entryMap {n : ℕ} (x y : Vec n) : Op n →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ (Vec n) y)

private theorem entryMap_apply {n : ℕ} (x y : Vec n) (M : Op n) :
    entryMap x y M = ⟪x, M y⟫ := rfl

private def traceMap {n : ℕ} : Op n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    entryMap (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i)

private theorem traceMap_apply {n : ℕ} (M : Op n) :
    traceMap M = stdTrace M := by
  simp [traceMap, entryMap, stdTrace]

private theorem norm_sq_first {n : ℕ} (x u : Vec n) :
    fderiv ℝ (fun y : Vec n => ‖y‖ ^ 2) x u = 2 * ⟪x, u⟫ := by
  rw [fderiv_norm_sq]
  simp

private theorem norm_sq_second {n : ℕ} (x u v : Vec n) :
    bilinearIteratedFDerivTwo ℝ (fun y : Vec n => ‖y‖ ^ 2) x u v =
      2 * ⟪u, v⟫ := by
  have he :
      fderiv ℝ (fun y : Vec n => ‖y‖ ^ 2) = ⇑(2 • innerSL ℝ) :=
    fderiv_norm_sq
  change fderiv ℝ (fderiv ℝ (fun y : Vec n => ‖y‖ ^ 2)) x u v = _
  rw [he, ContinuousLinearMap.fderiv]
  simp only [smul_apply]
  change (2 : ℕ) • ⟪u, v⟫ = _
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

private theorem hsNormSq_path_deriv {n : ℕ} (Q R : Op n) :
    HasDerivAt (fun t : ℝ => hsNormSq (Q + t • R))
      (2 *
        ∑ j, ⟪Q (EuclideanSpace.basisFun (Fin n) ℝ j), R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫)
      0 := by
  have hj (e : Vec n) : HasDerivAt (fun t : ℝ => ‖(Q + t • R) e‖ ^ 2) (2 * ⟪Q e, R e⟫) 0 := by
    have hp :=
      (hasDerivAt_const (0 : ℝ) (Q e)).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const (R e))
    convert hp.norm_sq using 1 <;> simp [add_apply, smul_apply]
  have hh :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun (j : Fin n) _ => hj (EuclideanSpace.basisFun (Fin n) ℝ j))
  simpa only [← hsNormSq_eq_sum_norm_sq, ← Finset.mul_sum] using hh

private theorem sandwich_inner {n : ℕ} (S R H : Op n)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hSS : S * S = R) (e : Vec n) :
    ⟪e, (R * H * R) e⟫ = ⟪S e, (S * H * S) (S e)⟫ := by
  have heq : R * H * R = S * (S * H * S) * S := by
    rw [← hSS]
    simp only [mul_assoc]
  rw [heq]
  change ⟪e, S ((S * H * S) (S e))⟫ = _
  exact (hS e _).symm

private theorem sandwich_norm {n : ℕ} (S R H : Op n)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hSS : S * S = R) (e : Vec n) :
    ⟪e, (R * H * R * H * R) e⟫ = ‖(S * H * S) (S e)‖ ^ 2 := by
  let T := S * H * S
  have hT : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫ := by
    intro x y
    change ⟪S (H (S x)), y⟫ = ⟪x, S (H (S y))⟫
    rw [hS, hH, hS]
  have heq : R * H * R * H * R = S * T * T * S := by
    dsimp only [T]
    rw [← hSS]
    simp only [mul_assoc]
  rw [heq]
  change ⟪e, S (T (T (S e)))⟫ = ‖T (S e)‖ ^ 2
  rw [← hS, ← hT, real_inner_self_eq_norm_sq]

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

private theorem cov_smooth_two : ContDiff ℝ 2 (cov μ hc) := by
  have h : ContDiff ℝ ∞ (cov μ hc) :=
    contDiff_posteriorCovariance_joint μ hc
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

private theorem inverse_cov_smooth_two (hiso : KLS.Isotropic μ) :
    ContDiff ℝ 2 (fun q : Param n => Ring.inverse (cov μ hc q)) := by
  have h :
      ContDiff ℝ ∞ (fun q : Param n => Ring.inverse (cov μ hc q)) :=
    Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

private theorem cov_derivative_symmetric (p v : Param n) (x y : Vec n) :
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
      ⟪x, fderiv ℝ (cov μ hc) p v y⟫ := by
  have hA : DifferentiableAt ℝ (cov μ hc) p :=
    (cov_smooth_two μ hc).differentiable (by norm_num) p
  have hf :
      (fun q : Param n => entryMap y x (cov μ hc q)) =
        (fun q : Param n => entryMap x y (cov μ hc q)) := by
    funext q
    change ⟪y, cov μ hc q x⟫ = ⟪x, cov μ hc q y⟫
    rw [← real_inner_comm y (cov μ hc q x)]
    exact
      (Covariance.operator_isSelfAdjoint
        (compactPosterior μ hc q.1 q.2 : Measure (Vec n))).isSymmetric x y
  calc
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
        entryMap y x (fderiv ℝ (cov μ hc) p v) :=
      real_inner_comm _ _
    _ = fderiv ℝ (fun q : Param n => entryMap y x (cov μ hc q)) p v :=
      (fderiv_clm_comp_apply_vec (entryMap y x) hA v).symm
    _ = fderiv ℝ (fun q : Param n => entryMap x y (cov μ hc q)) p v := by
      rw [hf]
    _ = entryMap x y (fderiv ℝ (cov μ hc) p v) :=
      fderiv_clm_comp_apply_vec (entryMap x y) hA v
    _ = ⟪x, fderiv ℝ (cov μ hc) p v y⟫ := rfl

private theorem cov_vector_generator (hiso : KLS.Isotropic μ) (p : Param n) :
    vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p =
      -(cov μ hc p) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  let ℓ : Op n →L[ℝ] ℝ := entryMap y x
  have hf :
      (fun q : Param n => ℓ (cov μ hc q)) =
        (fun q : Param n => ⟪cov μ hc q x, y⟫) := by
    funext q
    exact (real_inner_comm y (cov μ hc q x)).symm
  have hg :
      vectorGenerator (drift μ hc) (noise μ hc)
        (fun q : Param n => ℓ (cov μ hc q)) p =
          -⟪cov μ hc p x, y⟫ := by
    rw [hf]
    have h := generator_inner_cov μ hc hiso p x y
    change
      diffusionGenerator (drift μ hc) (noise μ hc)
        (fun q : Param n => ⟪cov μ hc q x, y⟫) p =
          -⟪cov μ hc p x, y⟫ at h
    rw [diffusionGenerator_eq_vectorGenerator] at h
    exact h
  rw [vectorGenerator_clm_comp (drift μ hc) (noise μ hc) ℓ
    (cov_smooth_two μ hc).contDiffAt] at hg
  have hh :
      ⟪y, vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p x⟫ =
        -⟪cov μ hc p x, y⟫ := hg
  rw [← real_inner_comm y
    (vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p x)] at hh
  simpa only [neg_apply, inner_neg_left] using hh

/--
The Lyapunov function `𝒱(c, Q) = 1 + ‖c‖² + ‖Q‖²_HS + (tr A(p)⁻¹)²` of the localization (67)
(non-explosion of
the cutoff Eldan processes, uniformly in the cutoff). -/
def lyapunov (p : Param n) : ℝ :=
  1 + ‖p.1‖ ^ 2 + hsNormSq p.2 + stdTrace (Ring.inverse (cov μ hc p)) ^ 2

theorem one_le_lyapunov (p : Param n) : 1 ≤ lyapunov μ hc p := by
  unfold lyapunov
  have h₁ := sq_nonneg ‖p.1‖
  have h₂ := hsNormSq_nonneg p.2
  have h₃ := sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))
  linarith

theorem contDiff_lyapunov (hiso : KLS.Isotropic μ) : ContDiff ℝ ∞ (lyapunov μ hc) := by
  have hR :
      ContDiff ℝ ∞ (fun p : Param n => Ring.inverse (cov μ hc p)) :=
    Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
  have ht :
      ContDiff ℝ ∞
        (fun p : Param n => stdTrace (Ring.inverse (cov μ hc p))) := by
    unfold stdTrace
    apply ContDiff.sum
    intro i _
    exact ContDiff.inner ℝ contDiff_const (hR.clm_apply contDiff_const)
  have hcpart : ContDiff ℝ ∞ (fun p : Param n => ‖p.1‖ ^ 2) := by
    have hfst : ContDiff ℝ ∞ (fun p : Param n => p.1) := contDiff_fst
    simpa only [real_inner_self_eq_norm_sq] using
      (ContDiff.inner ℝ hfst hfst)
  have hqpart : ContDiff ℝ ∞ (fun p : Param n => hsNormSq p.2) := by
    unfold hsNormSq
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact
      (ContDiff.inner ℝ contDiff_const
        (contDiff_snd.clm_apply contDiff_const)).pow 2
  unfold lyapunov
  exact ((contDiff_const.add hcpart).add hqpart).add (ht.pow 2)

/-- Sublevel sets are bounded: `‖p‖² ≤ 𝒱(p)`. -/
theorem norm_sq_le_lyapunov (p : Param n) : ‖p‖ ^ 2 ≤ lyapunov μ hc p := by
  unfold lyapunov
  rw [Prod.norm_def]
  have hq := opNorm_sq_le_hsNormSq p.2
  by_cases h : ‖p.1‖ ≤ ‖p.2‖
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖p.1‖,
      sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))]
  · rw [max_eq_left (le_of_not_ge h)]
    nlinarith [hsNormSq_nonneg p.2,
      sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))]

/-- `‖A(p)⁻¹‖² ≤ 𝒱(p)`. -/
theorem opNorm_sq_ringInverse_cov_le_lyapunov (hiso : KLS.Isotropic μ) (p : Param n) :
    ‖Ring.inverse (cov μ hc p)‖ ^ 2 ≤ lyapunov μ hc p := by
  have hs :=
    Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2
  have hpos : (Ring.inverse (cov μ hc p)).IsPositive := by
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hs.2.2.1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      change 0 ≤
        ⟪Ring.inverse (cov μ hc p) (0 : Vec n), (0 : Vec n)⟫
      simp
    · exact (hs.2.2.2 v hv).le
  have h₁ := opNorm_sq_le_hsNormSq (Ring.inverse (cov μ hc p))
  have h₂ := hsNormSq_le_stdTrace_sq hpos
  unfold lyapunov
  nlinarith [sq_nonneg ‖p.1‖, hsNormSq_nonneg p.2]

/-- `𝓛 ‖c‖² = 2⟪c, A⁻¹ a⟫ + tr A⁻¹`. -/
theorem generator_norm_sq_fst (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => ‖q.1‖ ^ 2) p =
      2 * ⟪p.1, Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2)⟫ +
        stdTrace (Ring.inverse (cov μ hc p)) := by
  have hH : ContDiff ℝ 2 (fun q : Param n => ‖q.1‖ ^ 2) := by
    have hf : (fun q : Param n => ‖q.1‖ ^ 2) = (fun q : Param n => ⟪q.1, q.1⟫) :=
      funext fun q => (real_inner_self_eq_norm_sq q.1).symm
    rw [hf]
    exact ContDiff.inner ℝ contDiff_fst contDiff_fst
  have htr :
    (∑ i : Fin n,
        ⟪Ring.inverse (cov μ hc p) (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫) =
      stdTrace (Ring.inverse (cov μ hc p)) := by
    unfold stdTrace
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply]
    exact real_inner_comm _ _
  rw [generator_eq_partial μ hc hiso _ hH p]
  dsimp only [Prod.fst]
  rw [norm_sq_first, deriv_const]
  simp_rw [norm_sq_second]
  rw [← Finset.mul_sum, htr]
  ring

/-- `𝓛 ‖Q‖²_HS = 2 Σ_j ⟪Q e_j, A⁻¹ e_j⟫` (no noise acts on `Q`). -/
theorem generator_hsNormSq_snd (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => hsNormSq q.2) p =
      2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
        Ring.inverse (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  have hH : ContDiff ℝ 2 (fun q : Param n => hsNormSq q.2) := by
    unfold hsNormSq
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact
      (ContDiff.inner ℝ contDiff_const
        (contDiff_snd.clm_apply contDiff_const)).pow 2
  have hf : fderiv ℝ (fun _ : Vec n => hsNormSq p.2) = 0 :=
    fderiv_const _
  have hz (u v : Vec n) :
      bilinearIteratedFDerivTwo ℝ
        (fun _ : Vec n => hsNormSq p.2) p.1 u v = 0 := by
    change
      fderiv ℝ (fderiv ℝ (fun _ : Vec n => hsNormSq p.2)) p.1 u v = 0
    rw [hf, fderiv_zero]
    rfl
  have hsum :
      (∑ i : Fin n,
        bilinearIteratedFDerivTwo ℝ
          (fun _ : Vec n => hsNormSq p.2) p.1
          (Ring.inverse (cov μ hc p) (EuclideanSpace.single i 1))
          (EuclideanSpace.single i 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => hz _ _
  rw [generator_eq_partial μ hc hiso _ hH p]
  rw [show
    fderiv ℝ (fun _ : Vec n => hsNormSq p.2) p.1
      (Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2)) = 0 by
        rw [hf]
        rfl]
  rw [hsum]
  have hd := (hsNormSq_path_deriv p.2 (Ring.inverse (cov μ hc p))).deriv
  rw [hd]
  ring

/-- The noise derivative of `tr A⁻¹`: `D(tr A⁻¹)[σ e_k] = −Σ_i ⟪σ e_i, Htilde_k σ e_i⟫` with
`Htilde_k = σ (D_cA[σ e_k]) σ`. -/
theorem fderiv_stdTrace_ringInverse_cov_noise (hiso : KLS.Isotropic μ) (p : Param n)
    (k : Fin n) :
    fderiv ℝ (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p (noise μ hc p k) =
      -∑ i,
          ⟪inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i),
            (inverseSqrt (cov μ hc p) * fderiv ℝ (cov μ hc) p (noise μ hc p k) *
                inverseSqrt (cov μ hc p))
              (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ := by
  have hA : DifferentiableAt ℝ (cov μ hc) p :=
    (cov_smooth_two μ hc).differentiable (by norm_num) p
  have hR : DifferentiableAt ℝ (fun q : Param n => Ring.inverse (cov μ hc q)) p :=
    (inverse_cov_smooth_two μ hc hiso).differentiable (by norm_num) p
  have hu : IsUnit (cov μ hc p) :=
    Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hfun :
    (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) =
      (fun q : Param n => traceMap (Ring.inverse (cov μ hc q))) :=
    funext fun q => (traceMap_apply (Ring.inverse (cov μ hc q))).symm
  have hSS : inverseSqrt (cov μ hc p) * inverseSqrt (cov μ hc p) = Ring.inverse (cov μ hc p) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (inverseSqrt_cov_props μ hc hiso p).2 v
  rw [hfun, fderiv_clm_comp_apply_vec traceMap hR (noise μ hc p k)]
  rw [FunctionalInequalities.Probability.Diffusion.fderiv_ringInverse_comp_apply (cov μ hc) hA
      hu (noise μ hc p k)]
  rw [map_neg, traceMap_apply]
  apply congrArg Neg.neg
  unfold stdTrace
  apply Finset.sum_congr rfl
  intro i _
  exact
    sandwich_inner (inverseSqrt (cov μ hc p)) (Ring.inverse (cov μ hc p))
      (fderiv ℝ (cov μ hc) p (noise μ hc p k)) (inverseSqrt_cov_props μ hc hiso p).1 hSS
      (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- `𝓛 tr A⁻¹ = tr A⁻¹ + Σ_k Σ_i ‖Htilde_k σ e_i‖²` (BKL (69) and the inverse calculus). -/
theorem generator_stdTrace_ringInverse_cov (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p =
      stdTrace (Ring.inverse (cov μ hc p)) +
        ∑ k,
          ∑ i,
            ‖(inverseSqrt (cov μ hc p) * fderiv ℝ (cov μ hc) p (noise μ hc p k) *
                    inverseSqrt (cov μ hc p))
                  (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^
              2 := by
  let R : Op n := Ring.inverse (cov μ hc p)
  let S : Op n := inverseSqrt (cov μ hc p)
  let H : Fin n → Op n := fun k => fderiv ℝ (cov μ hc) p (noise μ hc p k)
  have hu : IsUnit (cov μ hc p) :=
    Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hSS : S * S = R := by
    apply ContinuousLinearMap.ext
    intro v
    exact (inverseSqrt_cov_props μ hc hiso p).2 v
  have hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫ := (inverseSqrt_cov_props μ hc hiso p).1
  have hcancel : -(R * (-(cov μ hc p)) * R) = R := by
    have hRA : R * cov μ hc p = 1 := Ring.inverse_mul_cancel (cov μ hc p) hu
    calc
      -(R * (-(cov μ hc p)) * R) = (R * cov μ hc p) * R := by
        apply ContinuousLinearMap.ext
        intro v
        change -(R (-(cov μ hc p (R v)))) = R (cov μ hc p (R v))
        rw [map_neg, neg_neg]
      _ = R := by rw [hRA, one_mul]
  have hLG :
    vectorGenerator (drift μ hc) (noise μ hc) (fun q : Param n => Ring.inverse (cov μ hc q)) p =
      R + ∑ k, R * H k * R * H k * R := by
    have hi :=
      FunctionalInequalities.Probability.Diffusion.generator_ringInverse_comp (drift μ hc)
        (noise μ hc) (cov μ hc) (cov_smooth_two μ hc).contDiffAt hu
    change
      vectorGenerator (drift μ hc) (noise μ hc) (fun q : Param n => Ring.inverse (cov μ hc q))
          p =
        -(R * vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p * R) +
          ∑ k, R * H k * R * H k * R at hi
    rw [cov_vector_generator μ hc hiso p, hcancel] at hi
    exact hi
  have hfun :
    (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) =
      (fun q : Param n => traceMap (Ring.inverse (cov μ hc q))) :=
    funext fun q => (traceMap_apply (Ring.inverse (cov μ hc q))).symm
  rw [hfun]
  unfold generator
  rw [diffusionGenerator_eq_vectorGenerator,
    vectorGenerator_clm_comp (drift μ hc) (noise μ hc) traceMap
      (inverse_cov_smooth_two μ hc hiso).contDiffAt,
    hLG, map_add, map_sum, traceMap_apply]
  apply congrArg (fun z : ℝ => stdTrace R + z)
  apply Finset.sum_congr rfl
  intro k _
  rw [traceMap_apply]
  unfold stdTrace
  apply Finset.sum_congr rfl
  intro i _
  exact
    sandwich_norm S R (H k) hS (cov_derivative_symmetric μ hc p (noise μ hc p k)) hSS
      (EuclideanSpace.basisFun (Fin n) ℝ i)

end FunctionalInequalities.KLS.BKL.Localization
