/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Trace.Algebra

/-!
# Weak derivatives of finite matrix polynomials

Bounded weak matrix fields with compact-local L2 entry derivatives have exact
first directional derivatives of their determinants and trace quadratics.
Ambient and matrix dimensions may differ; zero dimensions and arbitrary real
constant matrices are retained. No C1/C2 regularity, symmetry, positivity or
invertibility of the rough field is assumed for these polynomial rules. The inverse-density
identification additionally takes a locally essentially bounded inverse pair, its given local-L2
weak derivatives and the a.e. inverse identity; it proves the explicit inverse formula without
classical differentiability. Supporting interfaces for Letwin
arXiv:2607.24164v1 Theorem 2.5 and compact Theorem 1.2, constant 8; these do not
establish Hessian evolution, an integrated trace estimate or the main bound.
The four-fold trace
product identity `trace_mul_mul_mul_eq_sum` lives in `Matrix/Trace/Algebra.lean`.
`bounded_trace_quadratic_weak_derivative_data`
packages bounded trace data of `tr(B A B A)` for globally bounded rough fields.
-/

@[expose] public section

section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators

namespace FunctionalInequalities.Analysis

private theorem trace_product_derivative_eq {n : ℕ} (B H T : Matrix (Fin n) (Fin n) ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (B q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
        (T q.2.1 q.2.2.1 * H q.2.2.2 q.1 +
          H q.2.1 q.2.2.1 * T q.2.2.2 q.1)) =
      2 * (B * H * B * T).trace := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← trace_mul_mul_mul_eq_sum B T B H, ← trace_mul_mul_mul_eq_sum B H B T]
  have hcycle : (B * T * B * H).trace = (B * H * B * T).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T) (B * H)
  rw [hcycle]
  ring



/-- The determinant of a bounded weak matrix field has its exact signed
permutation-polynomial directional derivative, locally in L2. -/
theorem hasWeakDerivAlong_det_of_locally_memLp_two {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  have hp (σ : Equiv.Perm ι) :=
    hasWeakDerivAlong_finsetProd_of_locally_memLp_two
      (Finset.univ : Finset ι)
      (f := fun i x => A x (σ i) i)
      (df := fun i x => DA x (σ i) i)
      (v := v)
      (fun i _ => hA (σ i) i)
      (fun i _ => hbound (σ i) i)
      (fun i _ => hDA2 (σ i) i)
  have hs :=
    hasWeakDerivAlong_finsetSum_mul
      (Finset.univ : Finset (Equiv.Perm ι))
      (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ))
      (f := fun σ x => ∏ i : ι, A x (σ i) i)
      (df := fun σ x => ∑ i : ι, DA x (σ i) i *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j)
      (v := v)
      (fun σ _ => (hp σ).1)
      (fun σ _ => (hp σ).2)
  simpa only [Matrix.det_apply'] using hs

/-- A bounded weak matrix field has the exact first directional derivative
of trace(B A B A), with locally L2 density, for arbitrary constant real B. -/
theorem hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
      (fun x => 2 * (B * A x * B * DA x).trace) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  have hprod := fun q : Fin n × Fin n × Fin n × Fin n =>
    (hA q.2.1 q.2.2.1).mul_of_locally_memLp_two
      (hA q.2.2.2 q.1)
      (hbound q.2.1 q.2.2.1) (hbound q.2.2.2 q.1)
      (hDA2 q.2.1 q.2.2.1) (hDA2 q.2.2.2 q.1)
  have hsum := hasWeakDerivAlong_finsetSum_mul
    (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
    (fun q => B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
    (f := fun q x => A x q.2.1 q.2.2.1 * A x q.2.2.2 q.1)
    (df := fun q x =>
      DA x q.2.1 q.2.2.1 * A x q.2.2.2 q.1 +
        A x q.2.1 q.2.2.1 * DA x q.2.2.2 q.1)
    (v := v)
    (fun q _ => (hprod q).1)
    (fun q _ => (hprod q).2)
  simpa only [← trace_mul_mul_mul_eq_sum, trace_product_derivative_eq] using hsum


end FunctionalInequalities.Analysis


section WeakMatrixInverse
open MeasureTheory Set Matrix
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-- The given weak derivatives of a locally bounded inverse pair satisfy the
inverse formula almost everywhere; no classical differentiability is assumed. -/
theorem ae_weak_matrix_inverse_derivative {d m : ℕ}
    {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hR : ∀ i j, HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
    (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => A x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DR x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DR x = -(R x * DA x * R x) := by
  classical
  have hentry (i j : Fin m) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        (DR x * A x + R x * DA x) i j = 0 := by
    have hp (a : Fin m) :=
      (hR i a).mul_of_locally_bounded (hA a j)
        (hR_top i a) (hA_top a j) (hDR2 i a) (hDA2 a j)
    have hs :=
      hasWeakDerivAlong_finsetSum_mul
        (Finset.univ : Finset (Fin m)) (fun _ => (1 : ℝ))
        (fun a _ => (hp a).1)
        (fun a _ => (hp a).2)
    have hw :
        HasWeakDerivAlong
          (fun x => (R x * A x) i j)
          (fun x => (DR x * A x + R x * DA x) i j) v := by
      simpa only [one_mul, Matrix.mul_apply, Matrix.add_apply,
        Finset.sum_add_distrib] using hs.1
    have hc :
        HasWeakDerivAlong
          (fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          (fun _ => (0 : ℝ)) v := by
      simpa using
        (hasWeakDerivAlong_of_contDiff
          (f := fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          contDiff_const v)
    have he :
        (fun x => (R x * A x) i j) =ᵐ[
          (volume : Measure (EuclideanSpace ℝ (Fin d)))]
        (fun _ => (1 : Matrix (Fin m) (Fin m) ℝ) i j) :=
      hRA.mono (fun _ hx => congrArg (fun B => B i j) hx)
    exact (hw.congr_ae he Filter.EventuallyEq.rfl).ae_eq hc
  have hall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        ∀ i j, (DR x * A x + R x * DA x) i j = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hentry i j))
  filter_upwards [hRA, hall] with x hx hentries
  have hzero : DR x * A x + R x * DA x = 0 := by
    ext i j
    exact hentries i j
  have hAR : A x * R x = 1 := mul_eq_one_comm.mp hx
  apply eq_neg_of_add_eq_zero_left
  calc
    DR x + R x * DA x * R x =
        (DR x * A x + R x * DA x) * R x := by
      rw [add_mul, mul_assoc (DR x) (A x) (R x), hAR, mul_one]
    _ = 0 := by rw [hzero, zero_mul]
end FunctionalInequalities.Analysis
end WeakMatrixInverse

section BoundedTraceQuadratic

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/--
For a globally bounded measurable matrix field `A` with compact-local L2 weak entry derivatives
`DA`, the
trace quadratic `tr(B A B A)` is globally bounded, locally integrable, and has the weak coordinate
derivatives
`2 tr(B A B DAₖ)`, which are L2 on every compact set. All finite dimensions are allowed. -/
theorem bounded_trace_quadratic_weak_derivative_data {d n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ) {M : NNReal}
    (hmeas : ∀ i j, Measurable (fun x => A x i j)) (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
    (hweak :
      ∀ k i j,
        HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
          (EuclideanSpace.basisFun (Fin d) ℝ k))
    (hDA2 :
      ∀ k i j,
        ∀ S : Set (EuclideanSpace ℝ (Fin d)),
          IsCompact S →
            MemLp (fun x => DA k x i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
          LocallyIntegrable (fun x => (B * A x * B * A x).trace)
              (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
            ∀ k : Fin d,
              HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
                  (fun x => 2 * (B * A x * B * DA k x).trace)
                  (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
                ∀ S : Set (EuclideanSpace ℝ (Fin d)),
                  IsCompact S →
                    MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
                      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  let C : ℝ :=
    ∑ q : Fin n × Fin n × Fin n × Fin n, ‖B q.1 q.2.1 * B q.2.2.1 q.2.2.2‖ * (M : ℝ) ^ 2
  have hb (x : EuclideanSpace ℝ (Fin d)) : ‖(B * A x * B * A x).trace‖ ≤ C := by
    rw [trace_mul_mul_mul_eq_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_mul]
    have h1 := hbound x q.2.1 q.2.2.1
    have h2 := hbound x q.2.2.2 q.1
    simpa only [pow_two] using
      mul_le_mul h1 h2 (norm_nonneg (A x q.2.2.2 q.1)) (NNReal.coe_nonneg M)
  have hmeasf : Measurable (fun x => (B * A x * B * A x).trace) := by
    simp_rw [trace_mul_mul_mul_eq_sum]
    fun_prop
  have htop :
    MemLp (fun x => (B * A x * B * A x).trace) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound hmeasf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  have htopA (i j : Fin n) :
    MemLp (fun x => A x i j) (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound (hmeas i j).aestronglyMeasurable (M : ℝ)
      (Filter.Eventually.of_forall fun x => hbound x i j)
  refine
    ⟨C, Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)), hb,
      htop.locallyIntegrable le_top, ?_⟩
  intro k
  exact
    hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two B (fun i j => hweak k i j) htopA
      (fun i j => hDA2 k i j)

end FunctionalInequalities.Analysis

end BoundedTraceQuadratic

section BoundedWeakMatrixProduct

open MeasureTheory Matrix

namespace FunctionalInequalities.Analysis

private theorem matrix_product_entry_eq_sum {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : (S * A * S) i j =
    ∑ q : Fin n × Fin n, (S i q.1 * S q.2 j) * A q.1 q.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/--
For a constant real matrix `S` and a matrix field `H` with globally bounded entries and
compact-local L2 weak entry
derivatives `DHₖ`, every entry of the two-sided product `S H S` is globally bounded with weak
derivatives the entries of
`S DHₖ S`, L2 on compact sets. Arbitrary finite ambient and matrix dimensions, including zero. -/
theorem bounded_weak_matrix_product_entry {d n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    {H DH : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (M : ℝ) (hH : ∀ a b, HasWeakDerivAlong (fun x => H x a b) (fun x => DH x a b) v)
    (hbound : ∀ x a b, ‖H x a b‖ ≤ M)
    (hD :
      ∀ a b,
        ∀ K : Set (EuclideanSpace ℝ (Fin d)),
          IsCompact K →
            MemLp (fun x => DH x a b) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K))
    (i j : Fin n) :
    (∀ x, ‖(S * H x * S) i j‖ ≤ ∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max M 0) ∧
      HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin d)),
          IsCompact K →
            MemLp (fun x => (S * DH x * S) i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
  classical
  have hsum :=
    hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
      (fun q => S i q.1 * S q.2 j) (f := fun q x => H x q.1 q.2) (df := fun q x => DH x q.1 q.2)
      (v := v) (fun q _ => hH q.1 q.2) (fun q _ => hD q.1 q.2)
  have hweak :
    HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin d)),
        IsCompact K →
          MemLp (fun x => (S * DH x * S) i j) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
    simpa only [← matrix_product_entry_eq_sum] using hsum
  refine ⟨?_, hweak.1, hweak.2⟩
  intro x
  rw [matrix_product_entry_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hbound x q.1 q.2).trans (le_max_left M 0)) (norm_nonneg _)

end FunctionalInequalities.Analysis

end BoundedWeakMatrixProduct
