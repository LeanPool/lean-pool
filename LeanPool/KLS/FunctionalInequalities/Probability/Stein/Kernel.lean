/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates

/-!
# Stein kernel object and compact-test identities
-/

@[expose] public section

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace FunctionalInequalities.Probability.Stein


/--
The Hilbert–Schmidt (Frobenius) norm of a kernel matrix: `|T|_HS² = ∑_{ij} T_{ij}²` (Letwin (2.19)).
-/
def hsNorm {n : ℕ} (T : KernelMatrix n) : ℝ :=
  ‖T‖

/-- The action `T v` of a kernel matrix on a Euclidean vector. -/
def action {n : ℕ} (T : KernelMatrix n) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (T.mulVec v.ofLp)

/--
**Stein kernel** (Letwin Definition 2.6): `μ` is centered with finite first moment, the entries of
`τ` are measurable and locally integrable, and `∫ x_i f dμ = ∫ (τ(x) ∇f(x))_i dμ` for every `C_c^∞`
test `f`.
Only compactly supported smooth tests enter the definition. -/
structure IsSteinKernel {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) : Prop where
  integrable_id :
    Integrable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (μ : Measure _)
  mean_zero : ∫ x, x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = 0
  measurable_entries : ∀ i j, Measurable (fun x => τ x i j)
  local_entries : ∀ i j, LocallyIntegrable (fun x => τ x i j) (μ : Measure _)
  compact_identity :
    ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ f →
        HasCompactSupport f →
          ∀ i : Fin n,
            (∫ x, x i * f x ∂(μ : Measure _)) =
              ∫ x, action (τ x) (gradient f x) i ∂(μ : Measure _)

/-- `τ(x)` is symmetric for `μ`-a.e. `x` (the symmetry clause of Definition 2.6). -/
def SymmetricAE {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) : Prop :=
  ∀ᵐ x ∂(μ : Measure _), ∀ i j, τ x i j = τ x j i

/-- `‖T v‖ ≤ |T|_HS ‖v‖`. -/
theorem norm_action_le_hsNorm {n : ℕ} (T : KernelMatrix n) (v : EuclideanSpace ℝ (Fin n)) :
    ‖action T v‖ ≤ hsNorm T * ‖v‖ := by
  have h := Matrix.frobenius_norm_mul T (Matrix.replicateCol Unit v.ofLp)
  rw [← Matrix.replicateCol_mulVec] at h
  simpa only [Matrix.frobenius_norm_replicateCol, WithLp.toLp_ofLp, action, hsNorm] using h

/-- `|T|_HS = √(∑_{ij} T_{ij}²)`. -/
theorem hsNorm_eq_sqrt {n : ℕ} (T : KernelMatrix n) :
    hsNorm T = Real.sqrt (∑ i, ∑ j, T i j ^ 2) := by
  rw [hsNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]

theorem hsNorm_nonneg {n : ℕ} (T : KernelMatrix n) : 0 ≤ hsNorm T := norm_nonneg _

/-- Measurability of `x ↦ |τ(x)|_HS` from entrywise measurability. -/
theorem hsNorm_measurable {X : Type*} [MeasurableSpace X] {n : ℕ}
    {τ : X → KernelMatrix n} (hτ : ∀ i j, Measurable (fun x => τ x i j)) :
    Measurable (fun x => hsNorm (τ x)) := by
  have h : Measurable (fun x => ∑ i, ∑ j, τ x i j ^ 2) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => (hτ i j).pow_const 2))
  simpa only [hsNorm_eq_sqrt] using h.sqrt

/-- `|τ|_HS ∈ L²(ν) ↔ ∫ |τ|_HS² dν < ∞`. -/
theorem memLp_hsNorm_iff_integrable_sq {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}
    {τ : X → KernelMatrix n} (hτ : ∀ i j, Measurable (fun x => τ x i j)) :
    MemLp (fun x => hsNorm (τ x)) 2 ν ↔ Integrable (fun x => hsNorm (τ x) ^ 2) ν := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    memLp_two_iff_integrable_sq_norm (hsNorm_measurable hτ).aestronglyMeasurable

/-- Measurability of `x ↦ τ(x) v`. -/
theorem action_measurable {X : Type*} [MeasurableSpace X] {n : ℕ} {τ : X → KernelMatrix n}
    (hτ : ∀ i j, Measurable (fun x => τ x i j)) (v : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => action (τ x) v) := by
  apply (WithLp.measurable_toLp 2 _).comp
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun x => ∑ j, τ x i j * v j)
  exact Finset.measurable_sum _ (fun j _ => (hτ i j).mul measurable_const)

/-- `x ↦ τ(x) v` is in `L²(ν)` when `|τ|_HS ∈ L²(ν)`. -/
theorem action_memLp {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}
    {τ : X → KernelMatrix n} (hτ : ∀ i j, Measurable (fun x => τ x i j))
    (hHS : MemLp (fun x => hsNorm (τ x)) 2 ν) (v : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => action (τ x) v) 2 ν := by
  apply hHS.of_le_mul (c := ‖v‖) (action_measurable hτ v).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_of_nonneg (hsNorm_nonneg (τ x)), mul_comm] using
    norm_action_le_hsNorm (τ x) v

/-- `⟪v, T w⟫ = ⟪T v, w⟫` for symmetric `T`. -/
theorem inner_action_swap {n : ℕ} (T : KernelMatrix n) (hT : ∀ i j, T i j = T j i)
    (v w : EuclideanSpace ℝ (Fin n)) : ⟪v, action T w⟫ = ⟪action T v, w⟫ := by
  simp only [action, PiLp.inner_apply, Real.inner_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT i j]
  ring

/--
**Directional Stein identity on compact tests**: `∫ ⟪x, v⟫ f dμ = ∫ ⟪τ(x) v, ∇f(x)⟫ dμ` for `f ∈
C_c^∞`
(from the coordinate identities of Definition 2.6 and a.e. symmetry). -/
theorem compact_directional_identity {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) (hK : IsSteinKernel μ τ)
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (μ : Measure _))
    (hSym : SymmetricAE μ τ) (hHS : MemLp (fun x => hsNorm (τ x)) 2 (μ : Measure _))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure _)) =
      ∫ x, ⟪action (τ x) v, gradient f x⟫ ∂(μ : Measure _) := by
  classical
  have hf2 : MemLp f 2 (μ : Measure _) := hf.continuous.memLp_of_hasCompactSupport hc
  have hg2 : MemLp (gradient f) 2 (μ : Measure _) :=
    (continuous_gradient (hf.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient hc)
  let L : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x => x i * f x
  let R : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x => action (τ x) (gradient f x) i
  have hLi (i : Fin n) : Integrable (L i) (μ : Measure _) := by
    have hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (μ : Measure _) := by
      simpa only [id_eq, EuclideanSpace.basisFun_inner] using
        hμ2.const_inner (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
    exact hxi.integrable_mul hf2
  have hRi (i : Fin n) : Integrable (R i) (μ : Measure _) := by
    have ha := action_memLp hK.measurable_entries hHS (EuclideanSpace.basisFun (Fin n) ℝ i)
    have hpair := L2.integrable_inner_of_memLp ha hg2
    apply hpair.congr
    filter_upwards [hSym] with x hx
    have hswap :=
      inner_action_swap (τ x) hx (EuclideanSpace.basisFun (Fin n) ℝ i) (gradient f x)
    simpa only [R, EuclideanSpace.basisFun_inner] using hswap.symm
  have hLfun : (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, v⟫ * f x) = fun x => ∑ i, v i * L i x := by
    funext x
    rw [PiLp.inner_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.inner_apply, L]
    ring
  have hRfun :
    (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, v i * R i x) =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin n)))]
      fun x => ⟪action (τ x) v, gradient f x⟫ := by
    filter_upwards [hSym] with x hx
    calc
      (∑ i, v i * R i x) = ⟪v, action (τ x) (gradient f x)⟫ := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Real.inner_apply, R]
      _ = _ := inner_action_swap (τ x) hx v (gradient f x)
  calc
    (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure _)) = ∑ i, v i * ∫ x, L i x ∂(μ : Measure _) := by
      rw [hLfun]
      simpa only [integral_const_mul] using
        (integral_finsetSum (s := (Finset.univ : Finset (Fin n))) (f := fun i x => v i * L i x)
          (fun i _ => (hLi i).const_mul (v i)))
    _ = ∑ i, v i * ∫ x, R i x ∂(μ : Measure _) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hK.compact_identity f hf hc i]
    _ = ∫ x, ∑ i, v i * R i x ∂(μ : Measure _) := by
      symm
      simpa only [integral_const_mul] using
        (integral_finsetSum (s := (Finset.univ : Finset (Fin n))) (f := fun i x => v i * R i x)
          (fun i _ => (hRi i).const_mul (v i)))
    _ = _ := integral_congr_ae hRfun


end FunctionalInequalities.Probability.Stein
end
/-! ### Algebra of the matrix action

`action` is multiplicative, additive, homogeneous and unital; its basis columns and the trace
formula `Σᵢ ‖A eᵢ‖² = tr (Aᵀ A)`. -/

section
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

theorem action_eq_toEuclideanLin {n : ℕ} (A : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action A x = Matrix.toEuclideanLin A x := rfl

theorem action_mul {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A * B) x = action A (action B x) := by
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec x.ofLp A B).symm

theorem action_add {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A + B) x = action A x + action B x := by
  apply WithLp.ofLp_injective
  exact Matrix.add_mulVec A B x.ofLp

theorem action_smul {n : ℕ} (t : ℝ) (A : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (t • A) x = t • action A x := by
  apply WithLp.ofLp_injective
  exact Matrix.smul_mulVec t A x.ofLp

theorem action_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    action (1 : KernelMatrix n) x = x := by
  apply WithLp.ofLp_injective
  exact Matrix.one_mulVec x.ofLp

theorem action_basis_apply {n : ℕ} (A : KernelMatrix n) (i j : Fin n) :
    action A (EuclideanSpace.basisFun (Fin n) ℝ i) j = A j i := by
  rw [EuclideanSpace.basisFun_apply]
  change (A.mulVec (Pi.single i 1)) j = A j i
  rw [Matrix.mulVec_single_one]
  rfl

theorem sum_norm_action_basis_sq_eq_trace_transpose_mul {n : ℕ} (A : KernelMatrix n) :
    (∑ i, ‖action A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) =
      Matrix.trace (A.transpose * A) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [action_basis_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

end FunctionalInequalities.Probability.Stein

end

/-! ### Hilbert–Schmidt norm and trace -/

section
open scoped Matrix.Norms.Frobenius

namespace FunctionalInequalities.Probability.Stein

/-- The Frobenius norm square of a real symmetric matrix is the trace of its square. -/
theorem hsNorm_sq_eq_trace_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    hsNorm A ^ 2 = (A * A).trace := by
  classical
  rw [hsNorm_eq_sqrt]
  have hnonneg : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sq_sqrt hnonneg]
  change (∑ i, ∑ j, A i j ^ 2) = ∑ i, ∑ j, A i j * A j i
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : A j i = A i j := congrArg (fun M => M i j) hA
  rw [hij, pow_two]

end FunctionalInequalities.Probability.Stein

end
