/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Flux

/-!
# Weighted Hessian evolution with curvature and Gram forcing

Weak supporting identities for Letwin arXiv:2607.24164v1 Lemma 2.4 (2.6).
Given weak Hessian and inverse-derivative inputs, local integrability and
test-class qualifications are retained explicitly. No source regularity
or mathematical completion is inferred.
-/

@[expose] public section

noncomputable section

section WeightedWeakHessianEvolution
open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff
open scoped BigOperators
namespace FunctionalInequalities.Analysis

/-- Closed scalar contraction form of the negative trace product. -/
private theorem sum_entry_mul_neg_eq_neg_trace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, B a b * (-(A b a))) = -(A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- The inverse-derivative contraction has the standard Gram trace order;
only trace cyclicity is used, never commutation of the matrices. -/
private theorem sum_inverse_derivative_contraction_eq_neg_gram {n : ℕ}
    (R Ti Tj : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, Ti a b * (-((R * Tj * R) b a))) =
      -(R * Ti * R * Tj).trace := by
  rw [sum_entry_mul_neg_eq_neg_trace]
  have hCyclic : (R * Tj * R * Ti).trace = (R * Ti * R * Tj).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (R * Tj) (R * Ti)
  rw [hCyclic]

/-- The coordinate curvature expression before Hessian symmetry is applied. -/
private theorem sum_curvature_eq_mul_transpose {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) =
      (H * Aᵀ * Hᵀ) i j := by
  rw [Matrix.mul_mul_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun t : ℝ => H i a * t)
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

/-- The actual symmetric Hessian data identify the standard H A H entry. -/
private theorem sum_curvature_eq_mul_of_symm {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ = H) (hA : Aᵀ = A)
    (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) = (H * A * H) i j := by
  rw [sum_curvature_eq_mul_transpose, hH, hA]

/-- Row inverse/gradient cancellation in the Piola drift term. -/
private theorem sum_row_mul_neg_add_hessian_eq {n : ℕ}
    (R H : Matrix (Fin n) (Fin n) ℝ) (hRH : R * H = 1)
    (v w : Fin n → ℝ) (b : Fin n) :
    (∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)) =
      -(∑ a : Fin n, R b a * v a) + w b := by
  have hVec : R.mulVec (-v + H.mulVec w) = -(R.mulVec v) + w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hRH, Matrix.one_mulVec]
  have hEntry := congrFun hVec b
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.neg_apply] using hEntry

/-- Closed row/trace algebra after the actual curl identity, before weighting. -/
private theorem sum_weak_hessian_divergence_minus_drift_eq {n : ℕ}
    (R H A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : Hᵀ = H) (hA : Aᵀ = A) (hRH : R * H = 1)
    (hT : ∀ k i j : Fin n, T k i j = T i k j ∧ T k i j = T k j i)
    (v w : Fin n → ℝ)
    (hrow : ∀ b : Fin n,
      (∑ a : Fin n, -((R * T a * R) b a)) =
        -(∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)))
    (i j : Fin n) :
    let D := fun k b a => -((R * T k * R) b a)
    let J := fun a => ∑ b : Fin n, R b a * T b i j
    let Q := -H j i + ∑ a : Fin n,
      (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
    Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
        (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
        (∑ a : Fin n, J a * v a) =
      -H i j + (H * A * H) i j + (R * T i * R * T j).trace := by
  dsimp only
  let D := fun k b a => -((R * T k * R) b a)
  let J := fun a => ∑ b : Fin n, R b a * T b i j
  let Q := -H j i + ∑ a : Fin n,
    (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
  change Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
      (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
      (∑ a : Fin n, J a * v a) = _
  have hHij : H j i = H i j := congrFun (congrFun hH i) j
  have hTperm (a : Fin n) : T j i a = T a i j :=
    (hT j i a).1.trans ((hT i j a).2.trans (hT i a j).1)
  have hQ : Q = -H i j + (H * A * H) i j + ∑ a : Fin n, T a i j * w a := by
    dsimp [Q]
    rw [Finset.sum_add_distrib, sum_curvature_eq_mul_of_symm H A hH hA i j, hHij]
    simp_rw [hTperm]
    ring
  have hGram : (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) =
      -(R * T i * R * T j).trace :=
    sum_inverse_derivative_contraction_eq_neg_gram R (T i) (T j)
  have hrow' (b : Fin n) : (∑ a : Fin n, D a b a) =
      (∑ a : Fin n, R b a * v a) - w b := by
    change (∑ a : Fin n, -((R * T a * R) b a)) = _
    rw [hrow b, sum_row_mul_neg_add_hessian_eq R H hRH v w b]
    ring
  have hRowTerm : (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) =
      (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) -
      (∑ b : Fin n, T b i j * w b) := by
    simp_rw [hrow']
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hcancel : (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) =
      ∑ a : Fin n, J a * v a := by
    simp only [J, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hQ, hGram, hRowTerm, hcancel]
  ring


private theorem ae_hessian_flux_forcing_minus_drift {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
      (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
        hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
          hessianMatrix W (gradient u x) b a)
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
        (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
      -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x *
          (Matrix.of fun a b => T x j a b)).trace := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  have hrow₀ := ae_inverse_hessian_row_divergence_of_weak_derivative hu hG hF hdet T hInv
  have hrows : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ b : Fin n, (∑ a : Fin n, D x a b a) =
        -(∑ a : Fin n, R x b a *
          fderiv ℝ (fun y => -u y + W (gradient u y)) x (e a)) :=
    ae_all_iff.mpr (fun b => (hrow₀ b).2)
  have hchain := ae_fderiv_mongeAmpere_exponent hu hG (hW.of_le one_le_two)
  have hsymm := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  filter_upwards [hrows, hchain, hsymm, hdet, hG.ae_differentiableAt (μ := volume)]
    with x hrow hc hs hd hx
  intro i j
  have hH : (hessianMatrix u x)ᵀ = hessianMatrix u x := by
    have hh := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx
    ext a b
    simpa only [Matrix.transpose_apply, star_trivial] using hh.apply a b
  have hWsym : (hessianMatrix W (gradient u x))ᵀ = hessianMatrix W (gradient u x) := by
    ext a b
    exact BakryEmery.bilinearIteratedFDerivTwo_symm hW (gradient u x) (e b) (e a)
  have hRH : R x * hessianMatrix u x = 1 := by
    apply Matrix.nonsing_inv_mul
    apply isUnit_iff_ne_zero.mpr
    rw [hd]
    exact Real.exp_ne_zero _
  have hrow' (b : Fin n) : (∑ a : Fin n, D x a b a) =
      -(∑ a : Fin n, R x b a *
        (-fderiv ℝ u x (e a) + ∑ c : Fin n, hessianMatrix u x a c *
          fderiv ℝ W (gradient u x) (e c))) := by
    rw [hrow b]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc a]
  exact sum_weak_hessian_divergence_minus_drift_eq
    (R x) (hessianMatrix u x) (hessianMatrix W (gradient u x))
    (fun k => Matrix.of fun a b => T x k a b) hH hWsym hRH hs
    (fun a => fderiv ℝ u x (e a))
    (fun a => fderiv ℝ W (gradient u x) (e a)) hrow' i j



/-- Closed C1 multiplication by exp(-u) in a compact-test divergence identity. -/
private theorem integral_exp_neg_flux_of_unweighted {n : ℕ}
    {u c : EuclideanSpace ℝ (Fin n) → ℝ}
    {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    LocallyIntegrable
      (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let weight := fun x => Real.exp (-u x)
  have hweight : ContDiff ℝ 1 weight := hu.neg.exp
  have hdu (a : Fin n) : Continuous (fun x => fderiv ℝ u x (e a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let d := fun x => ∑ a : Fin n, J x a * fderiv ℝ u x (e a)
  have hd : LocallyIntegrable d (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => (hJ a).mul_continuous (hdu a))
  refine ⟨?_, ?_⟩
  · change LocallyIntegrable (fun x => weight x * (c x - d x)) volume
    simpa only [Pi.sub_apply] using
      LocallyIntegrable.continuous_mul hweight.continuous (hc.sub hd)
  · intro ψ hψ hψc
    let A := fun x => weight x * (∑ a : Fin n, J x a * fderiv ℝ ψ x (e a))
    let B := fun x => weight x * ψ x * d x
    let E := fun x => c x * (weight x * ψ x)
    have hdψ (a : Fin n) : Continuous (fun x => fderiv ℝ ψ x (e a)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdψc (a : Fin n) : HasCompactSupport (fun x => fderiv ℝ ψ x (e a)) :=
      hψc.fderiv_apply ℝ (e a)
    have hAi (a : Fin n) : Integrable (fun x => weight x * (J x a * fderiv ℝ ψ x (e a)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := (hJ a).integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul (hdψ a)) ((hdψc a).mul_left)
      convert hi using 1
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hA : Integrable A (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [A, Finset.mul_sum] using
        integrable_finsetSum Finset.univ (fun a _ => hAi a)
    have hB : Integrable B (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [B, smul_eq_mul, Pi.mul_apply] using
        hd.integrable_smul_left_of_hasCompactSupport
          (hweight.continuous.mul hψ.continuous) hψc.mul_left
    have hE : Integrable E (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := hc.integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul hψ.continuous) hψc.mul_left
      simpa only [E, smul_eq_mul, Pi.mul_apply, mul_comm] using hi
    have hderiv (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
        fderiv ℝ (fun y => weight y * ψ y) x (e a) =
          weight x * fderiv ℝ ψ x (e a) - weight x * ψ x * fderiv ℝ u x (e a) := by
      have hux := (hu.differentiable one_ne_zero).differentiableAt (x := x)
      have hψx := (hψ.differentiable one_ne_zero).differentiableAt (x := x)
      have he := ((hux.hasFDerivAt.neg.exp).mul hψx.hasFDerivAt).fderiv
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x (e a) = _
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x = _ at he
      rw [he]
      simp only [_root_.add_apply, _root_.smul_apply,
        _root_.neg_apply, smul_eq_mul, Pi.neg_apply]
      dsimp [weight]
      ring
    have hleft (x : EuclideanSpace ℝ (Fin n)) :
        (∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          A x - B x := by
      simp only [hderiv]
      calc
        _ = ∑ a : Fin n, (weight x * (J x a * fderiv ℝ ψ x (e a)) -
            (weight x * ψ x) * (J x a * fderiv ℝ u x (e a))) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hid := hId (fun y => weight y * ψ y) (hweight.mul hψ) hψc.mul_left
    have hleftfun :
        (fun x => ∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          (fun x => A x - B x) := funext hleft
    have hab : (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
        (∫ x, B x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, E x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      change (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ (fun y => weight y * ψ y) x (e a)) = -(∫ x, E x) at hid
      rw [hleftfun, integral_sub hA hB] at hid
      exact hid
    have hrhs : (fun x => weight x * (c x - d x) * ψ x) =
        (fun x => E x - B x) := by
      funext x
      dsimp [E, B]
      ring
    change (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, weight x * (c x - d x) * ψ x)
    rw [hrhs, integral_sub hE hB]
    linarith only [hab]


/--
Weighted weak Hessian evolution (weak Letwin (2.6)): the flux `J` is compact-local L2, the curvature
and Gram forcing `E = -H + H ∇²W(∇u) H + tr(H⁻¹Tᵢ H⁻¹Tⱼ)` and `e^{-u} E` are locally integrable, and
`∫ e^{-u} Σₐ Jᵢⱼₐ ∂ₐψ = -∫ e^{-u} Eᵢⱼ ψ` for every compactly supported C1 `ψ`. -/
theorem integral_exp_neg_hessian_flux_eq_curvature_gram {n : ℕ}
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
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j =>
      -hessianMatrix u x i j +
          (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x * (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n,
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => J x i j a) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        LocallyIntegrable (fun x => E x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
              ContDiff ℝ 1 ψ →
                HasCompactSupport ψ →
                  (∫ x,
                      Real.exp (-u x) *
                        (∑ a : Fin n,
                          J x i j a *
                            fderiv ℝ ψ x
                              (EuclideanSpace.basisFun (Fin n) ℝ
                                a)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
                    -(∫ x,
                        Real.exp (-u x) * E x i j *
                          ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  dsimp only
  intro i j
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let Q := fun x i j =>
    -hessianMatrix u x j i +
      ∑ a : Fin n,
        (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
          hessianMatrix u x i a *
            ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
  let C := fun x i j =>
    Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  let E := fun x i j =>
    -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x * (Matrix.of fun a b => T x j a b)).trace
  have hQall :
    ∀ i j : Fin n,
      HasWeakDerivAlong
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
          (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => Q x i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro i j
    obtain ⟨hweak, hlocal⟩ := hasWeakDerivAlong_mongeAmpere_first_rhs hu hL hG hW T hT i j
    have htrace :
      (fun x =>
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            ∑ a : Fin n,
              hessianMatrix u x i a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace) := by
      filter_upwards [hFirst i] with x hx
      exact hx.symm
    refine ⟨?_, ?_⟩
    · simpa only [Q] using hweak.congr_ae htrace (Filter.Eventually.of_forall fun _ => rfl)
    · simpa only [Q] using hlocal
  have hcf1 := integral_weak_hessian_flux_eq_trace_derivative hu hG T hT hInv Q hQall
  have hJmem :
    ∀ a : Fin n,
      ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact S →
          MemLp (fun x => J x i j a) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    simpa only [J, R] using (hcf1 i j).1
  have hClocal :
    LocallyIntegrable (fun x => C x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [C, D, Q, R] using (hcf1 i j).2.1
  have hJlocal (a : Fin n) :
    LocallyIntegrable (fun x => J x i j a) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hfinite : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt hK.measure_lt_top
    exact @MemLp.integrable _ _ _ _ _ _ 2 (by norm_num) _ hfinite (hJmem a K hK)
  have hdu (a : Fin n) :
    Continuous (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJdu :
    LocallyIntegrable
      (fun x => ∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => (hJlocal a).mul_continuous (hdu a))
  have hae := ae_hessian_flux_forcing_minus_drift hu hG hW hF hdet T hT hInv
  have hAE :
    (fun x =>
        C x i j -
          ∑ a : Fin n,
            J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
      (fun x => E x i j) := by
    filter_upwards [hae] with x hx
    simpa only [C, D, J, Q, E, R] using hx i j
  have hElocal :
    LocallyIntegrable (fun x => E x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hClocal.sub hJdu).congr hAE
  have hweighted :=
    integral_exp_neg_flux_of_unweighted hu hJlocal hClocal
      (fun φ hφ hφc => by simpa only [C, D, Q, R] using (hcf1 i j).2.2 φ hφ hφc)
  have hEweighted :
    LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hweightedAE :
      (fun x =>
          Real.exp (-u x) *
            (C x i j -
              ∑ a : Fin n,
                J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))) =ᵐ[volume]
        (fun x => Real.exp (-u x) * E x i j) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    exact hweighted.1.congr hweightedAE
  have hfinal :
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ →
        HasCompactSupport ψ →
          (∫ x,
              Real.exp (-u x) *
                (∑ a : Fin n,
                  J x i j a *
                    fderiv ℝ ψ x
                      (EuclideanSpace.basisFun (Fin n) ℝ
                        a)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            -(∫ x,
                Real.exp (-u x) * E x i j *
                  ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    have hid := hweighted.2 ψ hψ hψc
    have hright :
      (fun x =>
          Real.exp (-u x) *
              (C x i j -
                ∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) *
            ψ x) =ᵐ[volume]
        (fun x => Real.exp (-u x) * E x i j * ψ x) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    rw [integral_congr_ae hright] at hid
    exact hid
  exact ⟨hJmem, hElocal, hEweighted, hfinal⟩

end FunctionalInequalities.Analysis
end WeightedWeakHessianEvolution
