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
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Generator
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Regularity
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator

/-!
# Generator bounds for the localization Lyapunov function
-/

@[expose] public section

noncomputable section
section LyapunovBound

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor

/-! Generator bound `𝓛𝒱 ≤ K𝒱` on symmetric positive semidefinite `Q` under `CumulantBoundCompact 2
8`. -/

namespace FunctionalInequalities.KLS.BKL.Localization

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

private theorem ringInverse_isPositive (hiso : KLS.Isotropic μ) (p : Param n) :
    (Ring.inverse (cov μ hc p)).IsPositive := by
  have hs :=
    Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hs.2.2.1, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    change 0 ≤
      ⟪Ring.inverse (cov μ hc p) (0 : EuclideanSpace ℝ (Fin n)),
        (0 : EuclideanSpace ℝ (Fin n))⟫
    simp
  · exact (hs.2.2.2 v hv).le

section NormedSpace

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem diffusionGenerator_add_local {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y + v y) x =
      diffusionGenerator b σ u x + diffusionGenerator b σ v x := by
  have hu' : DifferentiableAt ℝ u x :=
    hu.differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x :=
    hv.differentiableAt (by norm_num)
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond (a c : V) :
      fderiv ℝ (fderiv ℝ (fun y => u y + v y)) x a c =
        fderiv ℝ (fderiv ℝ u) x a c +
          fderiv ℝ (fderiv ℝ v) x a c := by
    have h :
        (fun y => fderiv ℝ (fun z => u z + v z) y) =ᶠ[nhds x]
          (fun y => fderiv ℝ u y + fderiv ℝ v y) := by
      filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
      rw [fderiv_fun_add (hyu.differentiableAt (by norm_num))
        (hyv.differentiableAt (by norm_num))]
    rw [h.fderiv_eq, fderiv_fun_add hfu hfv]
    simp only [add_apply]
  unfold diffusionGenerator
  rw [fderiv_fun_add hu' hv']
  simp_rw [hsecond]
  simp only [add_apply, Finset.sum_add_distrib]
  ring

private theorem diffusionGenerator_const_local {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) (c : ℝ) (x : V) :
    diffusionGenerator b σ (fun _ : V => c) x = 0 := by
  unfold diffusionGenerator
  change
    (fderiv ℝ (Function.const V c) x) (b x) +
        1 / 2 * ∑ k,
          ((fderiv ℝ (fderiv ℝ (Function.const V c)) x) (σ x k)) (σ x k) = 0
  simp

end NormedSpace

theorem sum_hsNormSq_conjugatedNoiseOperator_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) ≤ 8 * n := by
  classical
  have hmatrix (k : Fin n) :
      hsNormSq (conjugatedNoiseOperator μ hc p k) =
        ∑ a, ∑ b, (conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
    have h :=
      congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ => ∑ a, ∑ b, M a b ^ 2)
        (stdMatrix_conjugatedNoiseOperator μ hc hiso p k)
    simpa [hsNormSq, stdMatrix, Matrix.of_apply] using h
  have hsingle (k a b : Fin n) :
      ∑ j, conjugatedNoiseMatrix μ hc p k a j *
          (Pi.single b (1 : ℝ) : Fin n → ℝ) j =
        conjugatedNoiseMatrix μ hc p k a b := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro j hj hne
      simp [hne]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  have hcolumn (b : Fin n) :
      ∑ k, ∑ a, (conjugatedNoiseMatrix μ hc p k a b) ^ 2 ≤ 8 := by
    have h :=
      sum_sq_conjugatedNoiseMatrix_mulVec_le μ hc hiso hLC h8 p hSym hQ
        (Pi.single b (1 : ℝ))
    simp_rw [hsingle] at h
    simpa [Pi.single_apply] using h
  calc
    ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) =
        ∑ k, ∑ a, ∑ b, (conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hmatrix k]
    _ = ∑ k, ∑ b, ∑ a, (conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ k, ∑ a, (conjugatedNoiseMatrix μ hc p k a b) ^ 2 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b, 8 := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcolumn b
    _ = 8 * n := by
      simp
      ring

theorem generator_stdTrace_ringInverse_cov_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    generator μ hc (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p ≤
      (1 + 8 * n) * stdTrace (Ring.inverse (cov μ hc p)) := by
  let R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Ring.inverse (cov μ hc p)
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    inverseSqrt (cov μ hc p)
  let G : ℝ := stdTrace R
  have hRpos : R.IsPositive := by
    simpa [R] using ringInverse_isPositive μ hc hiso p
  have hG : 0 ≤ G := by
    simpa [G] using stdTrace_nonneg hRpos
  have hSS : S * S = R := by
    apply ContinuousLinearMap.ext
    intro v
    simpa [R, S] using
      (inverseSqrt_cov_props μ hc hiso p).2 v
  have hSself : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫ :=
    (inverseSqrt_cov_props μ hc hiso p).1
  have htrace :
      ∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 = G := by
    calc
      ∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 =
          ∑ i, ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
            S (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          S (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hSself _ _
      _ = ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          R (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_apply_eq_comp, hSS]
      _ = G := rfl
  have hterm (k : Fin n) :
      ∑ i, ‖(conjugatedNoiseOperator μ hc p k)
          (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2 ≤
        hsNormSq (conjugatedNoiseOperator μ hc p k) * G := by
    calc
      ∑ i, ‖(conjugatedNoiseOperator μ hc p k)
          (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2 ≤
          ∑ i, hsNormSq (conjugatedNoiseOperator μ hc p k) *
            ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_apply_sq_le_hsNormSq_mul
          (conjugatedNoiseOperator μ hc p k)
          (S (EuclideanSpace.basisFun (Fin n) ℝ i))
      _ = hsNormSq (conjugatedNoiseOperator μ hc p k) *
          ∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ = hsNormSq (conjugatedNoiseOperator μ hc p k) * G := by
        rw [htrace]
  rw [generator_stdTrace_ringInverse_cov μ hc hiso p]
  change G + ∑ k, ∑ i, ‖(conjugatedNoiseOperator μ hc p k)
      (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2 ≤ (1 + 8 * n) * G
  calc
    G + ∑ k, ∑ i, ‖(conjugatedNoiseOperator μ hc p k)
        (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2 ≤
        G + ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) * G :=
      add_le_add (le_refl G) (Finset.sum_le_sum fun k hk => hterm k)
    _ = G + (∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k)) * G := by
      rw [Finset.sum_mul]
    _ ≤ G + (8 * n) * G := by
      gcongr
      exact sum_hsNormSq_conjugatedNoiseOperator_le μ hc hiso hLC h8 p hSym hQ
    _ = (1 + 8 * n) * G := by ring

theorem sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le (hiso : KLS.Isotropic μ)
    (hLC : KLS.LogConcave μ) (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) :
    ∑ k,
        (fderiv ℝ (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
            (noise μ hc p k)) ^
          2 ≤
      8 * n * stdTrace (Ring.inverse (cov μ hc p)) ^ 2 := by
  classical
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := inverseSqrt (cov μ hc p)
  let R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := Ring.inverse (cov μ hc p)
  let G : ℝ := stdTrace R
  have hRpos : R.IsPositive := by simpa [R] using ringInverse_isPositive μ hc hiso p
  have hG : 0 ≤ G := by simpa [G] using stdTrace_nonneg hRpos
  have hSS : S * S = R := by
    apply ContinuousLinearMap.ext
    intro v
    simpa [R, S] using (inverseSqrt_cov_props μ hc hiso p).2 v
  have hSself : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫ := (inverseSqrt_cov_props μ hc hiso p).1
  have htrace : ∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 = G := by
    calc
      ∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 =
          ∑ i,
            ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
              S (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (real_inner_self_eq_norm_sq _).symm
      _ =
          ∑ i,
            ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
              S (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hSself _ _
      _ = ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, R (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_apply_eq_comp, hSS]
      _ = G := rfl
  have hterm (k : Fin n) :
    (∑ i,
          ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
            (conjugatedNoiseOperator μ hc p k) (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫) ^
        2 ≤
      hsNormSq (conjugatedNoiseOperator μ hc p k) * G ^ 2 := by
    let T := conjugatedNoiseOperator μ hc p k
    let B : ℝ :=
      ∑ i,
        ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ *
          ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖
    let W : ℝ := ∑ i, ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2
    let A : ℝ :=
      ∑ i,
        ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i), T (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫
    have hW : W ≤ hsNormSq T * G := by
      calc
        W ≤ ∑ i, hsNormSq T * ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_apply_sq_le_hsNormSq_mul T (S (EuclideanSpace.basisFun (Fin n) ℝ i))
        _ = hsNormSq T * G := by rw [← Finset.mul_sum, htrace]
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      exact Finset.sum_nonneg fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hBcs : B ≤ Real.sqrt G * Real.sqrt W := by
      dsimp [B, W]
      calc
        (∑ i,
              ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ *
                ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖) ≤
            Real.sqrt (∑ i, ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) *
              Real.sqrt (∑ i, ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
            (fun i => ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖)
            (fun i => ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖)
        _ = Real.sqrt G * Real.sqrt W := by rw [htrace]
    have hWnonneg : 0 ≤ W := by
      dsimp [W]
      exact Finset.sum_nonneg fun i hi => sq_nonneg _
    have hBsq : B ^ 2 ≤ G * W := by
      have hprod : 0 ≤ Real.sqrt G * Real.sqrt W :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc
        B ^ 2 ≤ (Real.sqrt G * Real.sqrt W) ^ 2 := (sq_le_sq₀ hBnonneg hprod).mpr hBcs
        _ = G * W := by rw [mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hWnonneg]
    have hupper : A ≤ B := by
      dsimp [A, B]
      exact Finset.sum_le_sum fun i hi => real_inner_le_norm _ _
    have hlower : -B ≤ A := by
      have h :
        ∑ i,
            -(‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ *
                ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖) ≤
          ∑ i,
            ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
              T (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ := by
        apply Finset.sum_le_sum
        intro i hi
        have h' :=
          real_inner_le_norm (-(S (EuclideanSpace.basisFun (Fin n) ℝ i)))
            (T (S (EuclideanSpace.basisFun (Fin n) ℝ i)))
        have h'' :
          -⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
                T (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ ≤
            ‖S (EuclideanSpace.basisFun (Fin n) ℝ i)‖ *
              ‖T (S (EuclideanSpace.basisFun (Fin n) ℝ i))‖ := by
          simpa only [inner_neg_left, norm_neg] using h'
        have h''' := neg_le_neg h''
        simpa only [neg_neg] using h'''
      simpa only [B, A, Finset.sum_neg_distrib] using h
    have habs : |A| ≤ B := abs_le.mpr ⟨hlower, hupper⟩
    have hA_sq : A ^ 2 ≤ B ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg A) hBnonneg).mpr habs
      simpa only [sq_abs] using h
    have hAsq : A ^ 2 ≤ hsNormSq T * G ^ 2 := by
      calc
        A ^ 2 ≤ B ^ 2 := hA_sq
        _ ≤ G * W := hBsq
        _ ≤ G * (hsNormSq T * G) := mul_le_mul_of_nonneg_left hW hG
        _ = hsNormSq T * G ^ 2 := by ring
    simpa [A, T] using hAsq
  calc
    ∑ k,
          (fderiv ℝ (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
              (noise μ hc p k)) ^
            2 =
        ∑ k,
          (∑ i,
              ⟪S (EuclideanSpace.basisFun (Fin n) ℝ i),
                (conjugatedNoiseOperator μ hc p k) (S (EuclideanSpace.basisFun (Fin n) ℝ i))⟫) ^
            2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fderiv_stdTrace_ringInverse_cov_noise μ hc hiso p k]
      simp only [neg_sq]
      rfl
    _ ≤ ∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k) * G ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k
    _ = (∑ k, hsNormSq (conjugatedNoiseOperator μ hc p k)) * G ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (8 * n) * G ^ 2 := by
      gcongr
      exact sum_hsNormSq_conjugatedNoiseOperator_le μ hc hiso hLC h8 p hSym hQ
    _ = 8 * n * stdTrace (Ring.inverse (cov μ hc p)) ^ 2 := by
      ring_nf
      rfl

private theorem generator_resolvent_trace_sq
    {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (p : Param n)
    (hG : 0 ≤ stdTrace (Ring.inverse (cov μ hc p)))
    (hGgen : generator μ hc (fun q => stdTrace (Ring.inverse (cov μ hc q))) p ≤ (1 + 8 *
      (n : ℝ)) * stdTrace (Ring.inverse (cov μ hc p)))
    (hGcarre : ∑ k, (fderiv ℝ (fun q => stdTrace (Ring.inverse (cov μ hc q))) p)
      (noise μ hc p k) ^ 2 ≤ 8 * (n : ℝ) * stdTrace (Ring.inverse (cov μ hc p)) ^ 2)
    (hGdiff : ContDiff ℝ 2 fun q => stdTrace (Ring.inverse (cov μ hc q))) :
    generator μ hc
        (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) p ≤
      (2 * (1 + 8 * n) + 8 * n) * stdTrace (Ring.inverse (cov μ hc p)) ^ 2 := by
  classical
  let G := stdTrace (Ring.inverse (cov μ hc p))
  have hmul :=
    diffusionGenerator_mul (drift μ hc) (noise μ hc) (x := p)
      hGdiff.contDiffAt hGdiff.contDiffAt
  have hfirst :
      2 * G *
          generator μ hc
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p ≤
        2 * (1 + 8 * n) * G ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hGgen (by positivity : 0 ≤ 2 * G)
    calc
      2 * G *
          generator μ hc
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p ≤
          2 * G * ((1 + 8 * n) * G) := h
      _ = 2 * (1 + 8 * n) * G ^ 2 := by ring
  change diffusionGenerator (drift μ hc) (noise μ hc)
      (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) p ≤ _
  rw [show
      (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) =
        (fun q => stdTrace (Ring.inverse (cov μ hc q)) *
          stdTrace (Ring.inverse (cov μ hc q))) by
    funext q
    rw [pow_two]]
  rw [hmul]
  change
    G * generator μ hc
          (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p +
        G * generator μ hc
          (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p +
        ∑ k, (fderiv ℝ
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
            (noise μ hc p k)) *
          (fderiv ℝ
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
            (noise μ hc p k)) ≤ _
  calc
    _ = 2 * G *
          generator μ hc
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p +
          ∑ k, (fderiv ℝ
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
            (noise μ hc p k)) ^ 2 := by
      simp only [pow_two]
      ring
    _ ≤ 2 * (1 + 8 * n) * G ^ 2 + 8 * n * G ^ 2 :=
      add_le_add hfirst hGcarre
    _ = (2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by ring

theorem exists_generator_lyapunov_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) p ≤ K * lyapunov μ hc p := by
  let K : ℝ := 1 + r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro p hSym hQ
    -- Control the resolvent and the posterior mean.
    let R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      Ring.inverse (cov μ hc p)
    let G : ℝ := stdTrace R
    have hRpos : R.IsPositive := by
      simpa [R] using ringInverse_isPositive μ hc hiso p
    have hG : 0 ≤ G := by
      simpa [G] using stdTrace_nonneg hRpos
    have hmean : ‖posteriorMean μ p.1 p.2‖ ≤ r :=
      norm_posteriorMean_le μ hr hsupp p
    have hop : ‖R‖ ^ 2 ≤ G ^ 2 := by
      have h1 := opNorm_sq_le_hsNormSq R
      have h2 := hsNormSq_le_stdTrace_sq hRpos
      simpa [G] using le_trans h1 h2
    have hRnorm : ‖R‖ ≤ G :=
      (sq_le_sq₀ (norm_nonneg _) hG).mp hop
    have hRa : ‖R (posteriorMean μ p.1 p.2)‖ ≤ ‖R‖ * r := by
      calc
        ‖R (posteriorMean μ p.1 p.2)‖ ≤
            ‖R‖ * ‖posteriorMean μ p.1 p.2‖ :=
          R.le_opNorm _
        _ ≤ ‖R‖ * r :=
          mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
    have hRG : ‖R‖ * r ≤ r * G := by
      calc
        ‖R‖ * r = r * ‖R‖ := by ring
        _ ≤ r * G := mul_le_mul_of_nonneg_left hRnorm hr
    have hfst :
        2 * ⟪p.1, R (posteriorMean μ p.1 p.2)⟫ ≤
          ‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 := by
      have hi :
          ⟪p.1, R (posteriorMean μ p.1 p.2)⟫ ≤
            ‖p.1‖ * ‖R (posteriorMean μ p.1 p.2)‖ :=
        real_inner_le_norm _ _
      have h₁ :
          2 * ⟪p.1, R (posteriorMean μ p.1 p.2)⟫ ≤
            2 * (‖p.1‖ * ‖R (posteriorMean μ p.1 p.2)‖) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      have h₂ :
          2 * (‖p.1‖ * ‖R (posteriorMean μ p.1 p.2)‖) ≤
            2 * (‖p.1‖ * (‖R‖ * r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRa (norm_nonneg _)) (by norm_num)
      have h₃ :
          2 * (‖p.1‖ * (‖R‖ * r)) ≤
            2 * (‖p.1‖ * (r * G)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRG (norm_nonneg _)) (by norm_num)
      calc
        2 * ⟪p.1, R (posteriorMean μ p.1 p.2)⟫ ≤
            2 * (‖p.1‖ * ‖R (posteriorMean μ p.1 p.2)‖) := h₁
        _ ≤ 2 * (‖p.1‖ * (‖R‖ * r)) := h₂
        _ ≤ 2 * (‖p.1‖ * (r * G)) := h₃
        _ ≤ ‖p.1‖ ^ 2 + (r * G) ^ 2 := by
          simpa only [mul_assoc] using two_mul_le_add_sq ‖p.1‖ (r * G)
        _ = ‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 := by ring
    have hq :
        2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
          R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
          hsNormSq p.2 + G ^ 2 := by
      have hcs := sum_inner_apply_le_sqrt_hsNormSq_mul p.2 R
      have hsR : hsNormSq R ≤ G ^ 2 :=
        hsNormSq_le_stdTrace_sq hRpos
      have hsqrtR : Real.sqrt (hsNormSq R) ≤ G := by
        calc
          Real.sqrt (hsNormSq R) ≤ Real.sqrt (G ^ 2) :=
            Real.sqrt_le_sqrt hsR
          _ = G := by
            simpa [abs_of_nonneg hG] using Real.sqrt_sq_eq_abs G
      calc
        2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
            R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
            2 * (Real.sqrt (hsNormSq p.2) * Real.sqrt (hsNormSq R)) :=
          mul_le_mul_of_nonneg_left hcs (by norm_num)
        _ ≤ 2 * (Real.sqrt (hsNormSq p.2) * G) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsqrtR (Real.sqrt_nonneg _)) (by norm_num)
        _ ≤ Real.sqrt (hsNormSq p.2) ^ 2 + G ^ 2 := by
          simpa only [mul_assoc] using
            two_mul_le_add_sq (Real.sqrt (hsNormSq p.2)) G
        _ = hsNormSq p.2 + G ^ 2 := by
          rw [Real.sq_sqrt (hsNormSq_nonneg p.2)]
    have hGgen :
        generator μ hc (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p ≤
          (1 + 8 * n) * G := by
      simpa [G, R] using
        generator_stdTrace_ringInverse_cov_le μ hc hiso hLC h8 p hSym hQ
    have hGcarre :
        ∑ k, (fderiv ℝ
          (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p
          (noise μ hc p k)) ^ 2 ≤
          8 * n * G ^ 2 := by
      simpa [G, R] using
        sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le μ hc hiso hLC h8 p hSym hQ
    -- Compute the generator on the remaining coordinate terms.
    have hC : ContDiff ℝ 2 (fun q : Param n => ‖q.1‖ ^ 2) := by
      have hf : ContDiff ℝ 2 (fun q : Param n => q.1) := contDiff_fst
      simpa only [real_inner_self_eq_norm_sq] using ContDiff.inner ℝ hf hf
    have hQdiff : ContDiff ℝ 2 (fun q : Param n => hsNormSq q.2) := by
      have hR : ContDiff ℝ ∞ (fun q : Param n => hsNormSq q.2) := by
        unfold hsNormSq
        apply ContDiff.sum
        intro i hi
        apply ContDiff.sum
        intro j hj
        exact
          (ContDiff.inner ℝ contDiff_const
            (contDiff_snd.clm_apply contDiff_const)).pow 2
      exact hR.of_le (WithTop.coe_le_coe.mpr le_top)
    have hGdiff :
        ContDiff ℝ 2
          (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) := by
      have hR :
          ContDiff ℝ ∞
            (fun q : Param n => Ring.inverse (cov μ hc q)) :=
        Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
      have hT :
          ContDiff ℝ ∞
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) := by
        unfold stdTrace
        apply ContDiff.sum
        intro i hi
        exact ContDiff.inner ℝ contDiff_const (hR.clm_apply contDiff_const)
      exact hT.of_le (WithTop.coe_le_coe.mpr le_top)
    have hOne : ContDiff ℝ 2 (fun _ : Param n => (1 : ℝ)) := contDiff_const
    have hdecomp :
        generator μ hc (lyapunov μ hc) p =
          generator μ hc (fun _ : Param n => 1) p +
            generator μ hc (fun q : Param n => ‖q.1‖ ^ 2) p +
            generator μ hc (fun q : Param n => hsNormSq q.2) p +
            generator μ hc
              (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) p := by
      unfold generator lyapunov
      rw [diffusionGenerator_add_local
        (drift μ hc) (noise μ hc)
        ((hOne.add hC).add hQdiff).contDiffAt
        (hGdiff.pow 2).contDiffAt]
      rw [diffusionGenerator_add_local
        (drift μ hc) (noise μ hc)
        (hOne.add hC).contDiffAt hQdiff.contDiffAt]
      rw [diffusionGenerator_add_local
        (drift μ hc) (noise μ hc)
        hOne.contDiffAt hC.contDiffAt]
    have hsquare :
        generator μ hc
            (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) p ≤
          (2 * (1 + 8 * n) + 8 * n) * G ^ 2 :=
      generator_resolvent_trace_sq μ hc p hG hGgen hGcarre hGdiff
    -- Combine the bounds under a single Lyapunov constant.
    have hbound :
        generator μ hc (lyapunov μ hc) p ≤
          ‖p.1‖ ^ 2 + hsNormSq p.2 + 1 +
            (r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
      rw [hdecomp]
      rw [generator_norm_sq_fst μ hc hiso p, generator_hsNormSq_snd μ hc hiso p]
      have hconst : generator μ hc (fun _ : Param n => 1) p = 0 :=
        diffusionGenerator_const_local (drift μ hc) (noise μ hc) 1 p
      rw [hconst]
      have hGle : G ≤ 1 + G ^ 2 := by
        nlinarith [sq_nonneg (G - 1)]
      calc
        0 +
              (2 * ⟪p.1, R (posteriorMean μ p.1 p.2)⟫ + G) +
              2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
                R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ +
              generator μ hc
                (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q)) ^ 2) p ≤
            (‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 + G) +
              (hsNormSq p.2 + G ^ 2) +
              (2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
          linarith [hfst, hq, hsquare]
        _ ≤ ‖p.1‖ ^ 2 + hsNormSq p.2 + 1 +
            (r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
          nlinarith
    have hK1 : 1 ≤ K := by
      dsimp [K]
      nlinarith [sq_nonneg r, Nat.cast_nonneg (α := ℝ) n]
    have hKB : r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n ≤ K := by
      dsimp [K]
      linarith
    have hrest : 0 ≤ 1 + ‖p.1‖ ^ 2 + hsNormSq p.2 := by
      have hq0 := hsNormSq_nonneg p.2
      positivity
    have hdom := mul_le_mul_of_nonneg_right hK1 hrest
    have hdom₂ := mul_le_mul_of_nonneg_right hKB (sq_nonneg G)
    have hV :
        lyapunov μ hc p = 1 + ‖p.1‖ ^ 2 + hsNormSq p.2 + G ^ 2 := rfl
    rw [hV]
    nlinarith only [hbound, hdom, hdom₂]

end FunctionalInequalities.KLS.BKL.Localization

end LyapunovBound
