/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra
public import LeanPool.KLS.FunctionalInequalities.Probability.Moments
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Hessian trace estimates for log-concave potentials

Letwin arXiv:2607.24164v1 Theorem 2.5 in weak form: for a normalized log-concave law with a C1
globally Lipschitz potential
with Lipschitz gradient, the weak Brascamp–Lieb inequality applied to the entries of `√B ∇²U √B`,
the matrix variance
identity and the half energy bound give `∫ tr(B ∇²U B ∇²U) ≤ 2 tr(B B)` for PSD `B`. Regularity is
explicit in each
statement. The entry Brascamp–Lieb client and the finite component-integrability step are private
one-use supports.
-/

@[expose] public section

section

section ComponentIntegrability

open MeasureTheory

namespace FunctionalInequalities.Probability

private theorem integrable_components_and_sum_integral {alpha I : Type*}
    [MeasurableSpace alpha] [Fintype I] (mu : Measure alpha)
    (F : I → alpha → ℝ) (D : alpha → ℝ)
    (hF : ∀ i, AEStronglyMeasurable (F i) mu)
    (hnonneg : ∀ᵐ x ∂mu, ∀ i, 0 ≤ F i x)
    (hD : Integrable D mu) (heq : (fun x => ∑ i, F i x) =ᵐ[mu] D) :
    (∀ i, Integrable (F i) mu) ∧
      (∑ i, ∫ x, F i x ∂mu) = ∫ x, D x ∂mu := by
  classical
  have hsum : Integrable (fun x => ∑ i, F i x) mu := hD.congr heq.symm
  have hint (i : I) : Integrable (F i) mu := by
    refine hsum.mono' (hF i) (hnonneg.mono fun x hx => ?_)
    rw [Real.norm_of_nonneg (hx i)]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  refine ⟨hint, ?_⟩
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  exact integral_congr_ae heq

end FunctionalInequalities.Probability

end ComponentIntegrability

section HessianEntryBrascampLieb

open MeasureTheory Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff

namespace FunctionalInequalities.KLS.LogConcave

private theorem variance_matrix_product_hessian_entry_le {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hconv : ConvexOn ℝ Set.univ U) (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix U x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
        MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (henergy : Integrable (fun x =>
      (fun k => (S * T x k * S) i j) ⬝ᵥ
        ((hessianMatrix U x)⁻¹ *ᵥ (fun k => (S * T x k * S) i j)))
      (nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    ProbabilityTheory.variance (fun x => (S * hessianMatrix U x * S) i j)
      (nu : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∫ x, (fun k => (S * T x k * S) i j) ⬝ᵥ
        ((hessianMatrix U x)⁻¹ *ᵥ (fun k => (S * T x k * S) i j))
          ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hc (k : Fin n) := bounded_weak_matrix_product_entry S (G : ℝ)
    (fun a b => (hT k a b).1)
    (fun x a b => norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x a b)
    (fun a b => (hT k a b).2) i j
  exact scalar_brascamp_lieb_weak_finite_energy
    (logConcave_of_eq_tilted hnuU hU.continuous hconv) hnuU hU hG hL hnorm hPD
    (fun k x => (S * T x k * S) i j)
    (∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max (G : ℝ) 0)
    (hc i).2.1.1 (hc i).1 (fun k => (hc k).2.1) (fun k => (hc k).2.2) henergy

end FunctionalInequalities.KLS.LogConcave

end HessianEntryBrascampLieb

section HessianTraceBound

open MeasureTheory Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff MatrixOrder

namespace FunctionalInequalities.KLS.LogConcave

/--
Weak Hessian trace bound (Letwin arXiv:2607.24164v1 Theorem 2.5, weak C1,1 form): for a normalized
convex C1 globally
Lipschitz potential with Lipschitz gradient and a.e. positive definite Hessian, weak Hessian tensor
`T`, mean Hessian identity,
and the half energy bound, `tr(B ∇²U B ∇²U)` is integrable and `∫ tr(B ∇²U B ∇²U) ≤ 2 tr(B B)` for
every PSD `B`. -/
theorem integral_trace_quadratic_le_two_mul_trace_sq {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU :
      (nu : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hconv : ConvexOn ℝ Set.univ U) (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix U x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ K : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact K →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hR :
      ∀ i j : Fin n,
        ∀ K : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact K →
            MemLp (fun x => (hessianMatrix U x)⁻¹ i j) (⊤ : ENNReal)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hmean :
      ∀ i j : Fin n,
        Integrable (fun x => hessianMatrix U x i j) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x, hessianMatrix U x i j ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) =
            (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (hD :
      Integrable
        (fun x =>
          ∑ k : Fin n, ∑ l : Fin n, (hessianMatrix U x)⁻¹ k l * (B * T x k * B * T x l).trace)
        (nu : Measure (EuclideanSpace ℝ (Fin n))))
    (hhalf :
      (∫ x,
          (∑ k : Fin n,
            ∑ l : Fin n,
              (hessianMatrix U x)⁻¹ k l *
                (B * T x k * B * T x l).trace) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        (1 / 2 : ℝ) *
          ∫ x,
            (B * hessianMatrix U x * B *
                hessianMatrix U x).trace ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun x => (B * hessianMatrix U x * B * hessianMatrix U x).trace)
        (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x,
          (B * hessianMatrix U x * B *
              hessianMatrix U x).trace ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        2 * (B * B).trace := by
  classical
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := (nu : Measure (EuclideanSpace ℝ (Fin n)))
  let H := fun x => hessianMatrix U x
  let R := fun x => (H x)⁻¹
  let D := fun x => ∑ k : Fin n, ∑ l : Fin n, R x k l * (B * T x k * B * T x l).trace
  let f := fun x => (B * H x * B * H x).trace
  have hDI : Integrable D mu := hD
  have hHalf : (∫ x, D x ∂mu) ≤ (1 / 2 : ℝ) * ∫ x, f x ∂mu := hhalf
  have hac : mu ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    change (nu : Measure (EuclideanSpace ℝ (Fin n))) ≪ _
    rw [hnuU]
    exact tilted_absolutelyContinuous _ _
  have hB0 : 0 ≤ B := by
    change (B - 0).PosSemidef
    simpa only [sub_zero] using hB
  let S := CFC.sqrt B
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg B
  have hSpsd : S.PosSemidef := by
    change (S - 0).PosSemidef at hS0
    simpa only [sub_zero] using hS0
  have hSsym : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hSpsd.isHermitian
  have hSt : S.transpose = S := hSsym
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB0
  let P := Fin n × Fin n
  let A := fun x => S * H x * S
  let F : P → EuclideanSpace ℝ (Fin n) → ℝ := fun p x => A x p.1 p.2
  let a : P → EuclideanSpace ℝ (Fin n) → Fin n → ℝ := fun p x k => (S * T x k * S) p.1 p.2
  let e : P → EuclideanSpace ℝ (Fin n) → ℝ := fun p x => a p x ⬝ᵥ (R x *ᵥ a p x)
  have hExp (Z : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (S * Z * S) i j = ∑ q : P, (S i q.1 * S q.2 j) * Z q.1 q.2 := by
    dsimp only [P]
    simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hData (p : P) (k : Fin n) :=
    bounded_weak_matrix_product_entry S (G : ℝ) (fun i j => (hT k i j).1)
      (fun x i j => norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
      (fun i j => (hT k i j).2) p.1 p.2
  have hF2 (p : P) : MemLp (F p) 2 mu :=
    MemLp.of_bound ((hData p p.1).2.1.1.aestronglyMeasurable.mono_ac hac)
      (∑ q : P, ‖S p.1 q.1 * S q.2 p.2‖ * max (G : ℝ) 0)
      (Filter.Eventually.of_forall (hData p p.1).1)
  have hRm (i j : Fin n) :
    AEMeasurable (fun x => R x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hloc :
      LocallyIntegrable (fun x => R x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro K hK
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
        isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
      exact (hR i j K hK).integrable (by simp)
    exact hloc.aestronglyMeasurable.aemeasurable
  have hTm (k i j : Fin n) :
    AEMeasurable (fun x => T x k i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hT k i j).1.2.1.aestronglyMeasurable.aemeasurable
  have ham (p : P) (k : Fin n) :
    AEMeasurable (fun x => a p x k) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have heq :
      (fun x => a p x k) = (fun x => ∑ q : P, (S p.1 q.1 * S q.2 p.2) * T x k q.1 q.2) := by
      funext x
      exact hExp (T x k) p.1 p.2
    rw [heq]
    apply Finset.aemeasurable_fun_sum
    intro q _
    exact aemeasurable_const.mul (hTm k q.1 q.2)
  have hem (p : P) : AEMeasurable (e p) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    dsimp only [e]
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.aemeasurable_fun_sum
    intro k _
    apply (ham p k).mul
    apply Finset.aemeasurable_fun_sum
    intro l _
    exact (hRm k l).mul (ham p l)
  have henonneg : ∀ᵐ x ∂mu, ∀ p : P, 0 ≤ e p x := by
    filter_upwards [hac.ae_le hPD] with x hx p
    simpa only [e, R, H, star_trivial] using hx.inv.posSemidef.dotProduct_mulVec_nonneg (a p x)
  have hTsym := ae_weak_third_derivative_symm hU hG (fun k i j => (hT k i j).1)
  have hesum : (fun x => ∑ p : P, e p x) =ᵐ[mu] D := by
    filter_upwards [hac.ae_le hTsym] with x hx
    have ht (k : Fin n) : (T x k).IsSymm := by
      change (T x k).transpose = T x k
      ext i j
      exact (hx k j i).2
    simpa only [e, a, D, hSS] using
      sum_matrix_product_entry_quadratic_eq_trace S hSsym (R x) (T x) ht
  obtain ⟨heI, heInt⟩ :=
    FunctionalInequalities.Probability.integrable_components_and_sum_integral mu e D
      (fun p => (hem p).aestronglyMeasurable.mono_ac hac) henonneg hDI hesum
  have hBL (p : P) : ProbabilityTheory.variance (F p) mu ≤ ∫ x, e p x ∂mu :=
    variance_matrix_product_hessian_entry_le hnuU hconv hU hG hL hnorm hPD T hT S p.1 p.2
      (heI p)
  have hVarBound : (∑ p : P, ProbabilityTheory.variance (F p) mu) ≤ ∫ x, D x ∂mu := by
    calc
      _ ≤ ∑ p : P, ∫ x, e p x ∂mu := Finset.sum_le_sum fun p _ => hBL p
      _ = _ := heInt
  have hMeanA (p : P) : (∫ x, F p x ∂mu) = B p.1 p.2 := by
    calc
      _ = ∫ x, ∑ q : P, (S p.1 q.1 * S q.2 p.2) * H x q.1 q.2 ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hExp (H x) p.1 p.2)
      _ = ∑ q : P, (S p.1 q.1 * S q.2 p.2) * ∫ x, H x q.1 q.2 ∂mu := by
        rw [integral_finsetSum _ (fun q _ => (hmean q.1 q.2).1.const_mul _)]
        simp only [integral_const_mul]
      _ = ∑ q : P, (S p.1 q.1 * S q.2 p.2) * (1 : Matrix (Fin n) (Fin n) ℝ) q.1 q.2 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [(hmean q.1 q.2).2]
      _ = (S * (1 : Matrix (Fin n) (Fin n) ℝ) * S) p.1 p.2 := (hExp 1 p.1 p.2).symm
      _ = _ := by rw [Matrix.mul_one, hSS]
  have hASym : ∀ᵐ x ∂mu, (A x).IsSymm := by
    filter_upwards [hac.ae_le hPD] with x hx
    have hHt : (H x).transpose = H x := Matrix.isHermitian_iff_isSymm.mp hx.isHermitian
    change (S * H x * S).transpose = S * H x * S
    simp only [Matrix.transpose_mul, hSt, hHt, Matrix.mul_assoc]
  have hAtrace (x) : (A x * A x).trace = f x := by
    calc
      _ = ((S * S) * H x * (S * S) * H x).trace := by
        simpa only [A, Matrix.mul_assoc] using Matrix.trace_mul_comm (S * H x * S * S * H x) S
      _ = _ := by rw [hSS]
  have hsumf : (fun x => ∑ p : P, F p x ^ 2) =ᵐ[mu] f := by
    filter_upwards [hac.ae_le hPD] with x hx
    have hHsym : (H x).IsSymm := Matrix.isHermitian_iff_isSymm.mp hx.isHermitian
    simpa only [F, A, f, hSS, pow_two] using
      sum_matrix_product_entry_mul_eq_trace S (H x) (H x) hSsym hHsym
  have hf : Integrable f mu :=
    (integrable_finsetSum _ (fun p _ => (hF2 p).integrable_sq)).congr hsumf
  have hBsym : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB.isHermitian
  have hVarEq :=
    FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean mu
      A B hBsym hASym (fun i j => hF2 (i, j)) (fun i j => hMeanA (i, j))
  rw [integral_congr_ae (Filter.Eventually.of_forall hAtrace)] at hVarEq
  have hfinal : (∫ x, f x ∂mu) - (B * B).trace ≤ (1 / 2 : ℝ) * ∫ x, f x ∂mu := by
    calc
      _ = ∑ p : P, ProbabilityTheory.variance (F p) mu := hVarEq.symm
      _ ≤ ∫ x, D x ∂mu := hVarBound
      _ ≤ _ := hHalf
  exact ⟨hf, by linarith only [hfinal]⟩

end FunctionalInequalities.KLS.LogConcave

end HessianTraceBound
