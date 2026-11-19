/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Integral
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import Mathlib.Probability.Moments.Variance
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Sign
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra

/-!
# Quadratic forms, noise shifts and energies of the matrix action

Identities for the Euclidean action `Stein.action` of a real matrix, used for spectral
quadratic-form estimates:
- the coordinate form `Σᵢⱼ Aᵢⱼ xᵢ xⱼ = ⟪A x, x⟫`, the sandwich `⟪Q (S x), S x⟫ = ⟪(S Q S) x, x⟫` for
  symmetric `S`, the conjugated latent
  field `e (H (e† v)) + t v = (S H S + t) v`, and invariance of the variance of a quadratic form
  under the pushforward by `S`;
- `Analysis.sum_norm_action_spectral_sign_noise`: for symmetric invertible `M` with `B = √(M²)`, `S
  = √B` and `Q = sign M`, and any
  symmetric `H`, `Σᵢ ‖(S H S + t) Q eᵢ‖² = tr (B H B H) + 2 t tr (B H) + n t²`;
- `KLS.LogConcave.sum_integral_spectral_noise_energy_le`: for an arbitrary measurable, a.e.
  symmetric random matrix with integrable
  entries and mean `Id` whose `tr (B H B H)` satisfies the trace bound `∫ ≤ 2 tr (B²)` for every
  symmetric `B` (an input), the integrated
  energy of the shifted action is at most `2 tr (M²) + 2 t tr B + n t²`. No log-concavity or Hessian
  hypothesis is used.

All finite dimensions; nothing here asserts a Stein kernel.
-/

@[expose] public section

section
open scoped RealInnerProductSpace MatrixOrder
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

theorem sum_norm_action_spectral_sign_noise {n : ℕ} (M H : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hH : H.IsSymm) (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∑ i : Fin n,
        ‖action (S * H * S + t • (1 : Matrix (Fin n) (Fin n) ℝ))
              (action Q (EuclideanSpace.single i 1))‖ ^
          2) =
      Matrix.trace (B * H * B * H) + 2 * t * Matrix.trace (B * H) + (n : ℝ) * t ^ 2 := by
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  change
    (∑ i : Fin n,
        ‖action (S * H * S + t • (1 : Matrix (Fin n) (Fin n) ℝ))
              (action Q (EuclideanSpace.single i 1))‖ ^
          2) =
      Matrix.trace (B * H * B * H) + 2 * t * Matrix.trace (B * H) + (n : ℝ) * t ^ 2
  obtain ⟨_, hSp, hQ, _, hSS, _, hQQ, _, _, _, _, _⟩ :=
    symmetric_matrix_spectral_geometry M hM hunit
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hSp.isHermitian
  have hb (i : Fin n) : EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin n) ℝ i := by
    rw [EuclideanSpace.basisFun_apply]
  simp_rw [hb, ← action_mul]
  rw [sum_norm_action_basis_sq_eq_trace_transpose_mul,
    trace_transpose_mul_right_involution _ Q hQ hQQ, trace_transpose_mul_shift_one,
    trace_transpose_conjugation_sq S H hS hH, trace_symmetric_conjugation S H, hSS]
  simp only [Fintype.card_fin, B]

end FunctionalInequalities.Analysis

end

section
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace MatrixOrder

namespace FunctionalInequalities.KLS.LogConcave

theorem sum_integral_spectral_noise_energy_le {n : ℕ} {Ω Δ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Δ] (ρ : Measure Ω) [IsProbabilityMeasure ρ] (γ : Measure Δ)
    [IsProbabilityMeasure γ] (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hHmeas : ∀ i j, Measurable (fun y => H y i j)) (hHsym : ∀ᵐ y ∂ρ, (H y).IsSymm)
    (hHint : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hT25 :
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
        B.IsSymm →
          Integrable (fun y => Matrix.trace (B * H y * B * H y)) ρ ∧
            (∫ y, Matrix.trace (B * H y * B * H y) ∂ρ) ≤ 2 * Matrix.trace (B * B))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∀ i : Fin n,
        Integrable
          (fun y => ‖action (S * H y * S + t • 1) (action Q (EuclideanSpace.single i 1))‖ ^ 2)
          ρ) ∧
      (∑ i : Fin n,
          ∫ p : Ω × Δ,
            ‖action (S * H p.1 * S + t • 1) (action Q (EuclideanSpace.single i 1))‖ ^
              2 ∂ρ.prod γ) ≤
        2 * Matrix.trace (M * M) + 2 * t * Matrix.trace B + (n : ℝ) * t ^ 2 := by
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  let F : Fin n → Ω → ℝ := fun i y =>
    ‖action (S * H y * S + t • 1) (action Q (EuclideanSpace.single i 1))‖ ^ 2
  let D : Ω → ℝ := fun y =>
    Matrix.trace (B * H y * B * H y) + 2 * t * Matrix.trace (B * H y) + (n : ℝ) * t ^ 2
  obtain ⟨hBp, _, _, hBB, _, _, _, _, _, _, _, _⟩ :=
    Analysis.symmetric_matrix_spectral_geometry M hM hunit
  have hB : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hBp.isHermitian
  obtain ⟨hEint, hEb⟩ := hT25 B hB
  obtain ⟨hTrint, hTr⟩ := Analysis.integral_trace_mul_of_mean_one ρ H hHint hmean B
  have hlin : Integrable (fun y => 2 * t * Matrix.trace (B * H y)) ρ := hTrint.const_mul (2 * t)
  have hcon : Integrable (fun _ : Ω => (n : ℝ) * t ^ 2) ρ := integrable_const _
  have hD : Integrable D ρ := (hEint.add hlin).add hcon
  have hFmeas (i : Fin n) : Measurable (F i) := by
    have hv := action_measurable hHmeas (action S (action Q (EuclideanSpace.single i 1)))
    have hs := (Matrix.toEuclideanLin S).toContinuousLinearMap.continuous.measurable.comp hv
    have hvec := hs.add (measurable_const (a := t • action Q (EuclideanSpace.single i 1)))
    dsimp only [F]
    simp_rw [action_add, action_smul, action_one, action_mul]
    exact hvec.norm.pow_const 2
  have heq : (fun y => ∑ i, F i y) =ᵐ[ρ] D := by
    filter_upwards [hHsym] with y hy
    exact Analysis.sum_norm_action_spectral_sign_noise M (H y) hM hy hunit t
  have hsumInt : Integrable (fun y => ∑ i, F i y) ρ := hD.congr heq.symm
  have hFi (i : Fin n) : Integrable (F i) ρ := by
    apply hsumInt.mono' (hFmeas i).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change F i y ≤ ∑ j, F j y
    exact Finset.single_le_sum (fun j _ => show 0 ≤ F j y from sq_nonneg _) (Finset.mem_univ i)
  have hsum : (∑ i, ∫ y, F i y ∂ρ) = ∫ y, D y ∂ρ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hFi i)]
    exact integral_congr_ae heq
  have hDint :
    (∫ y, D y ∂ρ) =
      (∫ y, Matrix.trace (B * H y * B * H y) ∂ρ) + 2 * t * Matrix.trace B + (n : ℝ) * t ^ 2 := by
    calc
      _ =
          (∫ y, Matrix.trace (B * H y * B * H y) + 2 * t * Matrix.trace (B * H y) ∂ρ) +
            ∫ _ : Ω, (n : ℝ) * t ^ 2 ∂ρ :=
        integral_add (hEint.add hlin) hcon
      _ =
          ((∫ y, Matrix.trace (B * H y * B * H y) ∂ρ) +
              ∫ y, 2 * t * Matrix.trace (B * H y) ∂ρ) +
            ∫ _ : Ω, (n : ℝ) * t ^ 2 ∂ρ :=
        congrArg (fun z => z + ∫ _ : Ω, (n : ℝ) * t ^ 2 ∂ρ) (integral_add hEint hlin)
      _ = _ := by
        rw [integral_const_mul, hTr]
        simp only [integral_const, probReal_univ, one_smul]
  have hproj : MeasurePreserving (Prod.fst : Ω × Δ → Ω) (ρ.prod γ) ρ := measurePreserving_fst
  have hprod (i : Fin n) : (∫ p : Ω × Δ, F i p.1 ∂ρ.prod γ) = ∫ y, F i y ∂ρ := by
    calc
      _ = ∫ y, F i y ∂(Measure.map Prod.fst (ρ.prod γ)) :=
        (integral_map hproj.measurable.aemeasurable
            ((hFi i).aestronglyMeasurable.mono_measure hproj.map_eq.le)).symm
      _ = _ := by rw [hproj.map_eq]
  change (∀ i, Integrable (F i) ρ) ∧ (∑ i, ∫ p : Ω × Δ, F i p.1 ∂ρ.prod γ) ≤ _
  refine ⟨hFi, ?_⟩
  simp_rw [hprod]
  rw [hsum, hDint]
  have hBB' : B * B = M * M := hBB
  rw [hBB'] at hEb
  dsimp only [B] at hEb ⊢
  linarith only [hEb]

end FunctionalInequalities.KLS.LogConcave

end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

theorem quadratic_matrix_sum_eq_inner_action {n : ℕ} (A : KernelMatrix n)
    (x : EuclideanSpace ℝ (Fin n)) : (∑ i, ∑ j, A i j * x i * x j) = ⟪action A x, x⟫ := by
  simp only [action, PiLp.inner_apply, Real.inner_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem inner_action_sandwich {n : ℕ} (S Q : KernelMatrix n) (hS : S.IsSymm)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪action Q (action S x), action S x⟫ = ⟪action (S * Q * S) x, x⟫ := by
  simp only [action_mul]
  exact inner_action_swap S (fun i j => congrFun (congrFun hS j) i) (action Q (action S x)) x

theorem latent_field_eq_action_conjugation {n : ℕ} (S H : KernelMatrix n)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap)
    (hself : IsSelfAdjoint e.toContinuousLinearMap) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    e (action H (e.toContinuousLinearMap.adjoint v)) + t • v =
      action (S * H * S + t • (1 : KernelMatrix n)) v := by
  rw [hself.adjoint_eq]
  change e.toContinuousLinearMap (action H (e.toContinuousLinearMap v)) + t • v = _
  rw [he]
  simp only [action_add, action_smul, action_one, action_mul]
  rfl

theorem variance_quadratic_map_sandwich {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (S Q : KernelMatrix n) (hS : S.IsSymm) :
    variance (fun x => ⟪action Q x, x⟫)
        (μ.map (Matrix.toEuclideanLin S).toContinuousLinearMap) =
      variance (fun x => ⟪action (S * Q * S) x, x⟫) μ := by
  have hq : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪action Q x, x⟫) :=
    (Matrix.toEuclideanLin Q).toContinuousLinearMap.continuous.inner continuous_id
  rw [variance_map hq.measurable.aemeasurable
      (Matrix.toEuclideanLin S).toContinuousLinearMap.continuous.measurable.aemeasurable]
  exact variance_congr (ae_of_all _ fun x => inner_action_sandwich S Q hS x)

end FunctionalInequalities.Probability.Stein

end
