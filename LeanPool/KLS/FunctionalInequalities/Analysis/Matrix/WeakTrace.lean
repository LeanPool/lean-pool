/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra

/-!
# Weak trace contraction of rough matrix fields

Generic finite trace/integral algebra behind the weak trace identity of Letwin arXiv:2607.24164v1
(2.8)/(2.10):
a fixed-test finite integral contraction from given L1 coordinate pairings, local integrability of
the contracted
coefficients from compact-local Lp entry data, and the full contracted identity
`integral_trace_quadratic_flux_eq_neg_density` for arbitrary rough fields `H`, `R`, `E`, `T`, `ρ`.
No Hessian,
potential or source premise; all finite dimensions. Actual Hessian-evolution specializations live in
`KLS/CEK/MomentRegularity/TraceStein.lean`. One-use supports are private.
-/

@[expose] public section

section

section FixedTestFiniteContraction

open MeasureTheory Matrix

namespace FunctionalInequalities.Analysis

private theorem trace_quadratic_test_pair_contraction {n : ℕ}
    (B H J T : Matrix (Fin n) (Fin n) ℝ) (ψ dψ : ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)) *
        (J q.2.2.2 q.1 * (ψ * T q.2.1 q.2.2.1 + dψ * H q.2.1 q.2.2.1))) =
    ψ * (2 * (B * T * B * J).trace) + dψ * (2 * (B * H * B * J).trace) := by
  rw [trace_mul_mul_mul_eq_sum, trace_mul_mul_mul_eq_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem trace_quadratic_forcing_contraction {n : ℕ}
    (B H E : Matrix (Fin n) (Fin n) ℝ) (ψ : ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)) *
        (E q.2.2.2 q.1 * (ψ * H q.2.1 q.2.2.1))) =
    ψ * (2 * (B * H * B * E).trace) := by
  rw [trace_mul_mul_mul_eq_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem integral_trace_contraction_of_coordinate_pairings {d n m : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d)))
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin d) → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (rho psi : EuclideanSpace ℝ (Fin d) → ℝ)
    (dpsi : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
    (hPair : ∀ l k i j : Fin n, Integrable (fun x => rho x *
      (∑ a : Fin m, J x a i j * (psi x * T x a l k + dpsi a x * H x l k))) mu)
    (hForce : ∀ l k i j : Fin n, Integrable
      (fun x => rho x * E x i j * (psi x * H x l k)) mu)
    (hTensor : ∀ a : Fin m, Integrable
      (fun x => rho x * psi x * (2 * (B * T x a * B * J x a).trace)) mu)
    (hFlux : ∀ a : Fin m, Integrable
      (fun x => rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)) mu)
    (hTraceForce : Integrable
      (fun x => rho x * psi x * (2 * (B * H x * B * E x).trace)) mu)
    (hTest : ∀ l k i j : Fin n,
      (∫ x, rho x * (∑ a : Fin m, J x a i j *
        (psi x * T x a l k + dpsi a x * H x l k)) ∂mu) =
      -(∫ x, rho x * E x i j * (psi x * H x l k) ∂mu)) :
    (∫ x, rho x * (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x) ∂mu) =
      -(∫ x, rho x *
        (2 * (B * H x * B * E x).trace +
          ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x ∂mu) := by
  classical
  let Q := Fin n × Fin n × Fin n × Fin n
  let c : Q → ℝ := fun q => 2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
  let P : Q → EuclideanSpace ℝ (Fin d) → ℝ := fun q x =>
    rho x * ∑ a : Fin m, J x a q.2.2.2 q.1 *
      (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1)
  let F : Q → EuclideanSpace ℝ (Fin d) → ℝ := fun q x =>
    rho x * E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1)
  let A : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    ∑ a : Fin m, rho x * psi x * (2 * (B * T x a * B * J x a).trace)
  let C : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    ∑ a : Fin m, rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)
  let K : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    rho x * psi x * (2 * (B * H x * B * E x).trace)
  have hP (q : Q) : Integrable (P q) mu :=
    hPair q.2.1 q.2.2.1 q.2.2.2 q.1
  have hF (q : Q) : Integrable (F q) mu :=
    hForce q.2.1 q.2.2.1 q.2.2.2 q.1
  have hPC (x) : (∑ q : Q, c q * P q x) = A x + C x := by
    calc
      _ = ∑ q : Q, ∑ a : Fin m, rho x * (c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1))) := by
        apply Finset.sum_congr rfl
        intro q _
        dsimp only [P]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = ∑ a : Fin m, rho x * ∑ q : Q, c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ a : Fin m, rho x *
          (psi x * (2 * (B * T x a * B * J x a).trace) +
           dpsi a x * (2 * (B * H x * B * J x a).trace)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show (∑ q : Q, c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1))) =
          psi x * (2 * (B * T x a * B * J x a).trace) +
           dpsi a x * (2 * (B * H x * B * J x a).trace) from
          trace_quadratic_test_pair_contraction B (H x) (J x a) (T x a) (psi x) (dpsi a x)]
      _ = A x + C x := by
        simp only [A, C, mul_add, mul_assoc, Finset.sum_add_distrib]
  have hFK (x) : (∑ q : Q, c q * F q x) = K x := by
    calc
      _ = rho x * ∑ q : Q, c q *
          (E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1)) := by
        simp only [F, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = K x := by
        rw [show (∑ q : Q, c q *
          (E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1))) =
          psi x * (2 * (B * H x * B * E x).trace) from
          trace_quadratic_forcing_contraction B (H x) (E x) (psi x)]
        simp only [K, mul_assoc]
  have hA : Integrable A mu := integrable_finsetSum _ fun a _ => hTensor a
  have hC : Integrable C mu := integrable_finsetSum _ fun a _ => hFlux a
  have hK : Integrable K mu := hTraceForce
  have hI : (∫ x, A x + C x ∂mu) = -(∫ x, K x ∂mu) := by
    calc
      _ = ∫ x, ∑ q : Q, c q * P q x ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hPC x).symm)
      _ = ∑ q : Q, c q * ∫ x, P q x ∂mu := by
        rw [integral_finsetSum _ (fun q _ => (hP q).const_mul (c q))]
        simp only [integral_const_mul]
      _ = ∑ q : Q, -(c q * ∫ x, F q x ∂mu) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [show (∫ x, P q x ∂mu) = -(∫ x, F q x ∂mu) from
          hTest q.2.1 q.2.2.1 q.2.2.2 q.1]
        ring
      _ = -(∫ x, ∑ q : Q, c q * F q x ∂mu) := by
        rw [integral_finsetSum _ (fun q _ => (hF q).const_mul (c q))]
        simp only [integral_const_mul, Finset.sum_neg_distrib]
      _ = -(∫ x, K x ∂mu) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hFK)
  rw [integral_add hA hC] at hI
  have hLeft : (fun x => rho x *
      (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x)) = C := by
    funext x
    dsimp only [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hRight : (fun x => rho x *
      (2 * (B * H x * B * E x).trace +
        ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x) =
      (fun x => K x + A x) := by
    funext x
    dsimp only [K, A]
    simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
  rw [hLeft, hRight, integral_add hK hA]
  linarith

end FunctionalInequalities.Analysis

end FixedTestFiniteContraction

section WeakTraceLocalCoefficients

open MeasureTheory Filter Set Matrix
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

private theorem trace_mul_sum_smul_slices {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    (A * (∑ i : Fin n, w i • T i)).trace =
      ∑ i : Fin n, w i * (A * T i).trace := by
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

private theorem trace_quadratic_flux_contraction {n : ℕ}
    (B H R : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) :
    (∑ i : Fin n, R i j * (2 * (B * H * B * T i).trace)) =
      2 * (B * H * B * (∑ i : Fin n, R i j • T i)).trace := by
  rw [trace_mul_sum_smul_slices]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem trace_quadratic_tensor_flux_contraction {n : ℕ}
    (B R : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ j : Fin n, 2 * (B * T j * B * (∑ i : Fin n, R i j • T i)).trace) =
      2 * ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace := by
  classical
  calc
    _ = ∑ j : Fin n, ∑ i : Fin n, 2 * R i j * (B * T j * B * T i).trace := by
      apply Finset.sum_congr rfl
      intro j _
      rw [trace_mul_sum_smul_slices, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have ht : (B * T j * B * T i).trace = (B * T i * B * T j).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T j) (B * T i)
      rw [ht]
      ring

private theorem locallyIntegrable_mul_of_memLp_top {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hg1 : MemLp g 1 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_one_iff_integrable.mpr (locallyIntegrable_iff.mp hg S hS)
  exact memLp_one_iff_integrable.mp ((hf.restrict S).fun_mul hg1)

private theorem locallyIntegrable_trace_four_of_entry_products {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (F G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (hFG : ∀ i j k l : Fin n,
      LocallyIntegrable (fun x => F x i j * G x k l)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => (A * F x * B * G x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let c := fun q : Fin n × Fin n × Fin n × Fin n => A q.1 q.2.1 * B q.2.2.1 q.2.2.2
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hsum : IntegrableOn (fun x => ∑ q : Fin n × Fin n × Fin n × Fin n,
      c q * (F x q.2.1 q.2.2.1 * G x q.2.2.2 q.1)) S
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum
    intro q _
    exact ((hFG q.2.1 q.2.2.1 q.2.2.2 q.1).integrableOn_isCompact hS).const_mul (c q)
  convert hsum using 1
  funext x
  exact trace_mul_mul_mul_eq_sum A (F x) B (G x)

private theorem trace_quadratic_contraction_local_coefficients {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j : Fin n, MemLp (fun x => H x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => J x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE : ∀ i j : Fin n, LocallyIntegrable (fun x => E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    LocallyIntegrable (fun x => (B * H x * B * E x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∀ a : Fin n,
      LocallyIntegrable (fun x => (B * T x a * B * J x a).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => (B * H x * B * J x a).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ a l k i j : Fin n,
      LocallyIntegrable (fun x => T x a l k * J x a i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ a l k i j : Fin n,
      LocallyIntegrable (fun x => H x l k * J x a i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    (∀ l k i j : Fin n,
      LocallyIntegrable (fun x => H x l k * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hJT (a l k i j : Fin n) := locallyIntegrable_mul_of_compact_L2
    (hT a l k) (hJ a i j)
  have hHJ (a l k i j : Fin n) := locallyIntegrable_mul_of_memLp_top
    (hH l k) (locallyIntegrable_of_compact_local_memLp_two (hJ a i j))
  have hHE (l k i j : Fin n) := locallyIntegrable_mul_of_memLp_top (hH l k) (hE i j)
  refine ⟨locallyIntegrable_trace_four_of_entry_products B B H E hHE, ?_, hJT, hHJ, hHE⟩
  intro a
  exact ⟨locallyIntegrable_trace_four_of_entry_products B B (fun x => T x a)
      (fun x => J x a) (hJT a),
    locallyIntegrable_trace_four_of_entry_products B B H (fun x => J x a) (hHJ a)⟩

end FunctionalInequalities.Analysis

end WeakTraceLocalCoefficients

section WeakTraceIdentity

open MeasureTheory Filter Set Matrix
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/--
Weak trace contraction of a tested Hessian-type flux identity (Letwin arXiv:2607.24164v1, weak
counterpart of
Lemma 2.4 (2.8)/(2.10)): for rough matrix fields `H`, `R`, `E`, a tensor field `T` and a weight `ρ`
with the stated
compact-local integrability, weak derivatives and tested identities, the contracted trace flux
against every compact
C1 test equals minus the contracted density. All finite dimensions, every constant matrix `B`. -/
theorem integral_trace_quadratic_flux_eq_neg_density {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (H R E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Continuous ρ)
    (hH :
      ∀ i j : Fin n,
        MemLp (fun x => H x i j) (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT :
      ∀ a i j : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => T x a i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ :
      ∀ i j a : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (fun x => ∑ b : Fin n, R x b a * T x b i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE :
      ∀ i j : Fin n,
        LocallyIntegrable (fun x => E x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTest :
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ →
          HasCompactSupport ψ →
            ∀ l k i j : Fin n,
              (∫ x,
                  ρ x *
                    (∑ a : Fin n,
                      (∑ b : Fin n, R x b a * T x b i j) *
                        (ψ x * T x a l k +
                          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) *
                            H x l k)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
                -(∫ x,
                    ρ x * E x i j *
                      (ψ x * H x l k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    let a := fun x i => 2 * (B * H x * B * T x i).trace
    let g := fun x =>
      2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
    LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ →
          HasCompactSupport ψ →
            Integrable (fun x => ρ x * g x * ψ x)
                (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
              (∀ j : Fin n,
                  Integrable
                    (fun x =>
                      ρ x * (∑ i : Fin n, R x i j * a x i) *
                        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
                    (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                (∫ x,
                    ρ x *
                      (∑ j : Fin n,
                        (∑ i : Fin n, R x i j * a x i) *
                          fderiv ℝ ψ x
                            (EuclideanSpace.basisFun (Fin n) ℝ
                              j)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
                  -(∫ x, ρ x * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let Jn := fun x a => ∑ b : Fin n, R x b a • T x b
  have hJn (a i j : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => Jn x a i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    simpa only [Jn, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hJ i j a S hS
  obtain ⟨hFE, hQF, hJT, hHJ, hHE⟩ :=
    trace_quadratic_contraction_local_coefficients B H E T Jn hH hT hJn hE
  let g := fun x =>
    2 * (B * H x * B * E x).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
  let gJ := fun x =>
    2 * (B * H x * B * E x).trace + ∑ a : Fin n, 2 * (B * T x a * B * Jn x a).trace
  have hgJ : LocallyIntegrable gJ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    exact
      ((hFE.integrableOn_isCompact hS).const_mul 2).add
        (integrable_finsetSum Finset.univ fun a _ =>
          ((hQF a).1.integrableOn_isCompact hS).const_mul 2)
  have hgEq : g = gJ := by
    funext x
    dsimp only [g, gJ, Jn]
    rw [trace_quadratic_tensor_flux_contraction]
  have hgApply (x) : g x = gJ x := congrFun hgEq x
  have hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hgEq]
    exact hgJ
  refine ⟨hg, ?_⟩
  intro psi hpsi hcpsi
  let dpsi := fun a x => fderiv ℝ psi x (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hdpsi (a : Fin n) : Continuous (dpsi a) :=
    (hpsi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcdpsi (a : Fin n) : HasCompactSupport (dpsi a) :=
    hcpsi.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hwpsi : Continuous (fun x => ρ x * psi x) := hρ.mul hpsi.continuous
  have hcwpsi : HasCompactSupport (fun x => ρ x * psi x) := hcpsi.mul_left
  have hwdpsi (a : Fin n) : Continuous (fun x => ρ x * dpsi a x) := hρ.mul (hdpsi a)
  have hcwdpsi (a : Fin n) : HasCompactSupport (fun x => ρ x * dpsi a x) := (hcdpsi a).mul_left
  have hweight {f w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hw : Continuous w)
    (hcw : HasCompactSupport w) :
    Integrable (fun x => w x * f x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hw hcw
  have hTensor (a : Fin n) :
    Integrable (fun x => ρ x * psi x * (2 * (B * T x a * B * Jn x a).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight (hQF a).1 hwpsi hcwpsi).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hFlux (a : Fin n) :
    Integrable (fun x => ρ x * dpsi a x * (2 * (B * H x * B * Jn x a).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight (hQF a).2 (hwdpsi a) (hcwdpsi a)).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hTraceForce :
    Integrable (fun x => ρ x * psi x * (2 * (B * H x * B * E x).trace))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := (hweight hFE hwpsi hcwpsi).const_mul 2
    apply hh.congr
    filter_upwards [] with x
    ring
  have hPair (l k i j : Fin n) :
    Integrable
      (fun x => ρ x * (∑ a : Fin n, Jn x a i j * (psi x * T x a l k + dpsi a x * H x l k)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh :=
      integrable_finsetSum Finset.univ fun a _ =>
        (hweight (hJT a l k i j) hwpsi hcwpsi).add
          (hweight (hHJ a l k i j) (hwdpsi a) (hcwdpsi a))
    apply hh.congr
    filter_upwards [] with x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.add_apply]
    ring
  have hForce (l k i j : Fin n) :
    Integrable (fun x => ρ x * E x i j * (psi x * H x l k))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hweight (hHE l k i j) hwpsi hcwpsi).congr
    filter_upwards [] with x
    ring
  have hTestJn (l k i j : Fin n) :
    (∫ x,
        ρ x *
          (∑ a : Fin n,
            Jn x a i j *
              (psi x * T x a l k +
                dpsi a x * H x l k)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x,
          ρ x * E x i j * (psi x * H x l k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    simpa only [Jn, dpsi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      hTest psi hpsi hcpsi l k i j
  have hID :=
    integral_trace_contraction_of_coordinate_pairings
      (volume : Measure (EuclideanSpace ℝ (Fin n))) B H E T Jn ρ psi dpsi hPair hForce hTensor
      hFlux hTraceForce hTestJn
  have hfluxEq (a : Fin n) (x) :
    (∑ i : Fin n, R x i a * (2 * (B * H x * B * T x i).trace)) =
      2 * (B * H x * B * Jn x a).trace :=
    trace_quadratic_flux_contraction B (H x) (R x) (T x) a
  refine ⟨?_, ?_, ?_⟩
  · have hh := hweight hgJ hwpsi hcwpsi
    apply hh.congr
    filter_upwards [] with x
    rw [← hgApply x]
    ring
  · intro a
    apply (hFlux a).congr
    filter_upwards [] with x
    rw [hfluxEq a x]
    ring
  · change
      (∫ x,
          ρ x *
            (∑ a : Fin n,
              (∑ i : Fin n, R x i a * (2 * (B * H x * B * T x i).trace)) *
                dpsi a x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, ρ x * g x * psi x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    simpa only [hfluxEq, hgApply] using hID

end FunctionalInequalities.Analysis

end WeakTraceIdentity
