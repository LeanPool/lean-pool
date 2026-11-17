/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Testing

/-!
# Directional Hessian subsolutions and rough square tests

Weak supporting identities for Letwin arXiv:2607.24164v1 Lemma 2.4 (2.6).
Given weak Hessian and inverse-derivative inputs, local integrability and
test-class qualifications are retained explicitly. No source regularity
or mathematical completion is inferred.
-/

@[expose] public section

noncomputable section

section DirectionalWeakSubsolution
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities.Analysis

/-- Reordering of a fourfold finite sum `(i, j, a, b) ↦ (a, b, i, j)`. -/
private theorem sum_four_comm {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ =>
      (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

/--
**Directional weak subsolution** of the weighted weak Hessian evolution: under the hypotheses of
`integral_exp_neg_hessian_flux_eq_curvature_gram`, with `W` convex and `∇²u` positive definite a.e.,
for every direction `v`
and every nonnegative compactly supported C1 `ψ`, `h_v = vᵀ ∇²u v` satisfies
`∫ e^{-u} Σₐ (Σ_b (∇²u)⁻¹_{ba} ∂_b h_v) ∂ₐψ ≤ ∫ e^{-u} h_v ψ` with `∂_b h_v = Σᵢⱼ vᵢ vⱼ T_{bij}`:
the curvature and Gram
forcing plus `∇²u` is positive semidefinite, and the matrix identity is contracted with `v`. -/
theorem integral_directional_hessian_flux_le {n : ℕ} {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G LF : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst :
      ∀ i : Fin n,
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    (hconvW : ConvexOn ℝ Set.univ W)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (v : Fin n → ℝ) (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψnonneg : ∀ x, 0 ≤ ψ x) :
    (∫ x,
        Real.exp (-u x) *
          (∑ a : Fin n,
            (∑ b : Fin n,
                (hessianMatrix u x)⁻¹ b a * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
              fderiv ℝ ψ x
                (EuclideanSpace.basisFun (Fin n) ℝ
                  a)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      ∫ x,
        Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
          ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hident :=
    integral_exp_neg_hessian_flux_eq_curvature_gram hu hL hG hW hF hdet T hT hInv hFirst
  dsimp only at hident
  set e : Fin n → EuclideanSpace ℝ (Fin n) := fun a => EuclideanSpace.basisFun (Fin n) ℝ a with
    he
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hu.continuous.neg
  have hdψ (a : Fin n) : Continuous fun x => fderiv ℝ ψ x (e a) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  -- the three matrix fields absorbing the weight and the test
  let Fm : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j =>
      Real.exp (-u x) *
        (∑ a : Fin n, (∑ b : Fin n, (hessianMatrix u x)⁻¹ b a * T x b i j) * fderiv ℝ ψ x (e a))
  let Em : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j =>
      Real.exp (-u x) *
          (-hessianMatrix u x i j +
              (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) * (hessianMatrix u x)⁻¹ *
                (Matrix.of fun a b => T x j a b)).trace) *
        ψ x
  let Hm : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j => Real.exp (-u x) * hessianMatrix u x i j * ψ x
  have hFint (i j : Fin n) : Integrable (fun x => Fm x i j) volume := by
    have hterm (a : Fin n) :
      Integrable
        (fun x =>
          (Real.exp (-u x) * fderiv ℝ ψ x (e a)) *
            ∑ b : Fin n, (hessianMatrix u x)⁻¹ b a * T x b i j)
        volume := by
      have h :=
        (locallyIntegrable_of_compact_local_memLp_two
              ((hident i j).1 a)).integrable_smul_left_of_hasCompactSupport
          (hρc.mul (hdψ a)) ((hψc.fderiv_apply (𝕜 := ℝ) (e a)).mul_left)
      simp only [smul_eq_mul, Pi.mul_apply] at h
      exact h
    refine (integrable_finsetSum Finset.univ fun a _ => hterm a).congr (ae_of_all _ fun x => ?_)
    simp only [Fm, Matrix.of_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hEint (i j : Fin n) : Integrable (fun x => Em x i j) volume := by
    refine
      ((hident i j).2.2.1.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc).congr
        (ae_of_all _ fun x => ?_)
    simp only [Em, Matrix.of_apply, smul_eq_mul]
    ring
  have hHint (i j : Fin n) : Integrable (fun x => Hm x i j) volume := by
    have h :=
      (locallyIntegrable_of_compact_local_memLp_two
            (fun S hS =>
              memLp_hessianMatrix_entry_of_isCompact hG i j
                hS)).integrable_smul_left_of_hasCompactSupport
        (hρc.mul hψ.continuous) hψc.mul_left
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Hm, Matrix.of_apply, smul_eq_mul, Pi.mul_apply]
    ring
  have hflux (i j : Fin n) : (∫ x, Fm x i j) = -(∫ x, Em x i j) := by
    simpa only [Fm, Em, Matrix.of_apply, he] using (hident i j).2.2.2 ψ hψ hψc
  have hsym := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  have hpos : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (Em x + Hm x).PosSemidef := by
    filter_upwards [hPD, hsym] with x hx hs
    have hHW : (hessianMatrix W (gradient u x)).PosSemidef := by
      change (hessianMatrixIn W (EuclideanSpace.basisFun (Fin n) ℝ) (gradient u x)).PosSemidef
      exact
        hessianMatrixIn_posSemidef _ hW.contDiffAt
          (fun w => bilinearIteratedFDerivTwo_nonneg_of_convexOn hW hconvW _ w)
    have hcurv :
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x).PosSemidef := by
      simpa only [hx.isHermitian.eq] using hHW.mul_mul_conjTranspose_same (hessianMatrix u x)
    have hgram :=
      traceGram_posSemidef ((hessianMatrix u x)⁻¹) hx.posSemidef.inv
        (fun a => Matrix.of fun c d => T x a c d)
        (fun a =>
          Matrix.IsSymm.ext fun c d => by
            simpa only [Matrix.of_apply] using ((hs a c d).2).symm)
    have heq :
      Em x + Hm x =
        (Real.exp (-u x) * ψ x) •
          (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x +
            Matrix.of fun a b =>
              ((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x a c d) *
                    (hessianMatrix u x)⁻¹ *
                  (Matrix.of fun c d => T x b c d)).trace) := by
      ext i j
      simp only [Em, Hm, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      ring
    rw [heq]
    exact (hcurv.add hgram).smul (mul_nonneg (Real.exp_pos _).le (hψnonneg x))
  have hmain :=
    integral_quadratic_flux_le_of_posSemidef volume Fm Em Hm v hFint hEint hHint hflux hpos
  have hleft :
    (fun x => dotProduct v ((Fm x).mulVec v)) = fun x =>
      Real.exp (-u x) *
        (∑ a : Fin n,
          (∑ b : Fin n,
              (hessianMatrix u x)⁻¹ b a * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
            fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
    funext x
    simp only [Fm, dotProduct, Matrix.mulVec, Matrix.of_apply, he, Finset.mul_sum,
      Finset.sum_mul]
    rw [sum_four_comm]
    refine
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hright :
    (fun x => dotProduct v ((Hm x).mulVec v)) = fun x =>
      Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * ψ x := by
    funext x
    simp only [Hm, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hleft, hright] at hmain
  exact hmain

/--
**Directional weak subsolution against bounded weak tests, convexity on the gradient range**: as
`integral_directional_hessian_flux_le_of_bounded_weak_test`, with `W` convex only on an open set `Ω`
containing every gradient value `∇u x`; the convexity enters only through the positive semidefinite
Hessian of `W` at the points `∇u x`. -/
theorem integral_directional_hessian_flux_le_of_bounded_weak_test_on_range {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst :
      ∀ i : Fin n,
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω) (hconvW : ConvexOn ℝ Ω W)
    (hΩ : ∀ x, gradient u x ∈ Ω)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (v : Fin n → ℝ) {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (hdηc : ∀ k : Fin n, HasCompactSupport (dη k))
    (hdη2 : ∀ k : Fin n, MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) :
    Integrable
        (fun x =>
          Real.exp (-u x) *
            (∑ k : Fin n,
              (∑ b : Fin n,
                  (hessianMatrix u x)⁻¹ b k *
                    (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                dη k x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
              η x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x,
            (fun x =>
                Real.exp (-u x) *
                  (∑ k : Fin n,
                    (∑ b : Fin n,
                        (hessianMatrix u x)⁻¹ b k *
                          (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                      dη k x))
              x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          ∫ x,
            (fun x =>
                Real.exp (-u x) *
                    (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                  η x)
              x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hident :=
    integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test hu hL hG hW hF hdet T
      hT hInv hFirst hη hbound hηc hweak hdηc hdη2
  dsimp only at hident
  have hρc : Continuous (fun x => Real.exp (-u x)) :=
    Real.continuous_exp.comp
      hu.continuous.neg
  -- the three matrix fields absorbing the weight and the test
  let Fm : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j =>
      Real.exp (-u x) *
        (∑ a : Fin n, (∑ b : Fin n, (hessianMatrix u x)⁻¹ b a * T x b i j) * dη a x)
  let Em : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j =>
      Real.exp (-u x) *
          (-hessianMatrix u x i j +
              (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) * (hessianMatrix u x)⁻¹ *
                (Matrix.of fun a b => T x j a b)).trace) *
        η x
  let Hm : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x =>
    Matrix.of fun i j => Real.exp (-u x) * hessianMatrix u x i j * η x
  have hFint (i j : Fin n) : Integrable (fun x => Fm x i j) volume := by
    have hp (a : Fin n) :
      Integrable
        (fun x =>
          Real.exp (-u x) * (∑ b : Fin n, (hessianMatrix u x)⁻¹ b a * T x b i j) * dη a x)
        volume :=
      (hident i j).1 a
    refine (integrable_finsetSum Finset.univ fun a _ => hp a).congr (ae_of_all _ fun x => ?_)
    simp only [Fm, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hEint (i j : Fin n) : Integrable (fun x => Em x i j) volume := by
    simpa only [Em, Matrix.of_apply] using (hident i j).2.1
  have hHint (i j : Fin n) : Integrable (fun x => Hm x i j) volume := by
    have hloc : LocallyIntegrable (fun x => Real.exp (-u x) * hessianMatrix u x i j) volume :=
      LocallyIntegrable.continuous_mul hρc
        (locallyIntegrable_of_compact_local_memLp_two
          (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS))
    simpa only [Hm, Matrix.of_apply] using
      (compact_bounded_test_domination hloc hηc.isCompact hη.aestronglyMeasurable
            (subset_tsupport η) hbound).2.2
  have hflux (i j : Fin n) : (∫ x, Fm x i j) = -(∫ x, Em x i j) := by
    simpa only [Fm, Em, Matrix.of_apply] using (hident i j).2.2
  have hsym := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  have hpos : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (Em x + Hm x).PosSemidef := by
    filter_upwards [hPD, hsym, hηnonneg] with x hx hs hnx
    have hHW : (hessianMatrix W (gradient u x)).PosSemidef := by
      change (hessianMatrixIn W (EuclideanSpace.basisFun (Fin n) ℝ) (gradient u x)).PosSemidef
      exact
        hessianMatrixIn_posSemidef _ hW.contDiffAt
          (fun w =>
            bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open hΩo hW.contDiffOn hconvW
              (hΩ x) w)
    have hcurv :
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x).PosSemidef := by
      simpa only [hx.isHermitian.eq] using hHW.mul_mul_conjTranspose_same (hessianMatrix u x)
    have hgram :=
      traceGram_posSemidef ((hessianMatrix u x)⁻¹) hx.posSemidef.inv
        (fun a => Matrix.of fun c d => T x a c d)
        (fun a =>
          Matrix.IsSymm.ext fun c d => by
            simpa only [Matrix.of_apply] using ((hs a c d).2).symm)
    have heq :
      Em x + Hm x =
        (Real.exp (-u x) * η x) •
          (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x +
            Matrix.of fun a b =>
              ((hessianMatrix u x)⁻¹ * (Matrix.of fun c d => T x a c d) *
                    (hessianMatrix u x)⁻¹ *
                  (Matrix.of fun c d => T x b c d)).trace) := by
      ext i j
      simp only [Em, Hm, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      ring
    rw [heq]
    exact (hcurv.add hgram).smul (mul_nonneg (Real.exp_pos _).le hnx)
  have hmain :=
    integral_quadratic_flux_le_of_posSemidef volume Fm Em Hm v hFint hEint hHint hflux hpos
  have hleft :
    (fun x => dotProduct v ((Fm x).mulVec v)) = fun x =>
      Real.exp (-u x) *
        (∑ a : Fin n,
          (∑ b : Fin n,
              (hessianMatrix u x)⁻¹ b a * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
            dη a x) := by
    funext x
    simp only [Fm, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [sum_four_comm]
    refine
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hright :
    (fun x => dotProduct v ((Hm x).mulVec v)) = fun x =>
      Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x := by
    funext x
    simp only [Hm, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, Integrable (fun x => A x i j) volume) :
    Integrable (fun x => dotProduct v ((A x).mulVec v)) volume := by
    change Integrable (fun x => ∑ i, v i * ∑ j, A x i j * v j) volume
    exact
      integrable_finsetSum Finset.univ fun i _ =>
        (integrable_finsetSum Finset.univ fun j _ => (hA i j).mul_const (v j)).const_mul (v i)
  have hleftInt := hint Fm hFint
  have hrightInt := hint Hm hHint
  rw [hleft] at hleftInt
  rw [hright] at hrightInt
  rw [hleft, hright] at hmain
  exact ⟨hleftInt, hrightInt, hmain⟩


/-- **Directional weak subsolution against bounded weak tests**: under the hypotheses of
`integral_directional_hessian_flux_le`, for a bounded compactly supported locally integrable `η ≥ 0`
a.e. whose coordinate
weak derivatives `dη k` are compactly supported and globally L², both scalar pairings are integrable
and
`∫ e^{-u} Σ_k (Σ_b (∇²u)⁻¹_{bk} ∂_b h_v) dη_k ≤ ∫ e^{-u} h_v η`. No C1 test or positivity-preserving
approximation. -/
theorem integral_directional_hessian_flux_le_of_bounded_weak_test {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst :
      ∀ i : Fin n,
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    (hconvW : ConvexOn ℝ Set.univ W)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (v : Fin n → ℝ) {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (hdηc : ∀ k : Fin n, HasCompactSupport (dη k))
    (hdη2 : ∀ k : Fin n, MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) :
    Integrable
        (fun x =>
          Real.exp (-u x) *
            (∑ k : Fin n,
              (∑ b : Fin n,
                  (hessianMatrix u x)⁻¹ b k *
                    (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                dη k x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
              η x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x,
            (fun x =>
                Real.exp (-u x) *
                  (∑ k : Fin n,
                    (∑ b : Fin n,
                        (hessianMatrix u x)⁻¹ b k *
                          (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                      dη k x))
              x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          ∫ x,
            (fun x =>
                Real.exp (-u x) *
                    (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                  η x)
              x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  integral_directional_hessian_flux_le_of_bounded_weak_test_on_range hu hL hG hW hF hdet T hT
    hInv hFirst isOpen_univ hconvW (fun x => mem_univ (gradient u x)) hPD v hη hbound hηc hweak
    hdηc hdη2 hηnonneg

/--
**Rough square test** `η = (χ · vᵀ∇²u v)²`: under the hypotheses of the bounded directional theorem
and a compactly
supported C1 cutoff `χ`, `η` has weak derivatives `a_k b + b a_k` (with `b = χ h_v`, `a_k` from
`directional_cutoff_data`),
compactly supported and globally L², is compactly supported, bounded and nonnegative, and satisfies
the directional weak
subsolution inequality with both pairings integrable. -/
theorem rough_square_test_of_weak_data {n : ℕ} {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G LF : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst :
      ∀ i : Fin n,
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    (hconvW : ConvexOn ℝ Set.univ W)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (v : Fin n → ℝ) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    let e := fun k : Fin n => EuclideanSpace.basisFun (Fin n) ℝ k
    let hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
    let tv := fun (k : Fin n) x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j
    let b := fun x => χ x * hv x
    let ab := fun (k : Fin n) x => χ x * tv k x + fderiv ℝ χ x (e k) * hv x
    let η := fun x => b x * b x
    let dη := fun (k : Fin n) x => ab k x * b x + b x * ab k x
    (∀ k : Fin n,
        HasWeakDerivAlong η (dη k) (e k) ∧
          HasCompactSupport (dη k) ∧
            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      HasCompactSupport η ∧
        (∃ Cη : ℝ, ∀ x, ‖η x‖ ≤ Cη) ∧
          (∀ x, 0 ≤ η x) ∧
            Integrable
                (fun x =>
                  Real.exp (-u x) *
                    (∑ k : Fin n,
                      (∑ b : Fin n,
                          (hessianMatrix u x)⁻¹ b k *
                            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                        dη k x))
                (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
              Integrable
                  (fun x =>
                    Real.exp (-u x) *
                        (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                      η x)
                  (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                (∫ x,
                    Real.exp (-u x) *
                      (∑ k : Fin n,
                        (∑ b : Fin n,
                            (hessianMatrix u x)⁻¹ b k *
                              (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                          dη k x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                  ∫ x,
                    Real.exp (-u x) *
                        (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                      η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro e hv tv b ab η dη
  classical
  obtain ⟨hbm, hbc, ⟨B, -, hbb⟩, hbd⟩ := directional_cutoff_data hG T hT v hχ hχc
  have htop (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (B : ℝ)
    (hfB : ∀ x, ‖f x‖ ≤ B) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S →
        MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    fun S _ => memLp_top_of_bound hf.aestronglyMeasurable.restrict B (ae_of_all _ hfB)
  have hweakb (k : Fin n) : HasWeakDerivAlong b (ab k) (e k) := (hbd k).1
  have habc (k : Fin n) : HasCompactSupport (ab k) := (hbd k).2.1
  have hab2 (k : Fin n) : MemLp (ab k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hbd k).2.2
  have hbtop :=
    htop b hbm B
      hbb
  -- the square η = b², by the bounded weak product rule
  have hsq (k : Fin n) : HasWeakDerivAlong η (dη k) (e k) :=
    ((hweakb k).mul_of_locally_bounded (hweakb k) hbtop hbtop (fun S _ => (hab2 k).restrict S)
        (fun S _ => (hab2 k).restrict S)).1
  have hdηc (k : Fin n) : HasCompactSupport (dη k) := (habc k).mul_right.add (habc k).mul_left
  have hdη2 (k : Fin n) : MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h1 : MemLp (fun x => ab k x * b x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (hab2 k).of_le_mul ((hab2 k).aestronglyMeasurable.mul hbm.aestronglyMeasurable)
        (ae_of_all _ fun x => by
          rw [norm_mul, mul_comm];
          exact mul_le_mul_of_nonneg_right (hbb x) (norm_nonneg _))
    have h2 : MemLp (fun x => b x * ab k x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (hab2 k).of_le_mul (hbm.aestronglyMeasurable.mul (hab2 k).aestronglyMeasurable)
        (ae_of_all _ fun x => by
          rw [norm_mul];
          exact mul_le_mul_of_nonneg_right (hbb x) (norm_nonneg _))
    exact h1.add h2
  have hηc : HasCompactSupport η := hbc.mul_right
  have hηb (x : EuclideanSpace ℝ (Fin n)) : ‖η x‖ ≤ B * B := by
    simp only [η, norm_mul];
    exact mul_le_mul (hbb x) (hbb x) (norm_nonneg _) ((norm_nonneg _).trans (hbb x))
  have hηloc : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (htop η (hbm.mul hbm) _ hηb K hK).integrable le_top
  obtain ⟨h1, h2, h3⟩ :=
    integral_directional_hessian_flux_le_of_bounded_weak_test hu hL hG hW hF hdet T hT hInv
      hFirst hconvW hPD v hηloc hηb hηc hsq hdηc hdη2
      (ae_of_all _ fun x => mul_self_nonneg (b x))
  exact
    ⟨fun k => ⟨hsq k, hdηc k, hdη2 k⟩, hηc, ⟨_, hηb⟩, fun x => mul_self_nonneg (b x), h1, h2,
      h3⟩

end FunctionalInequalities.Analysis
end DirectionalWeakSubsolution
