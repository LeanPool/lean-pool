/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.CoeffWkInfty
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM


/-!
# Classical `Cᵏ` coefficients satisfy Guo's `W^{k,∞}` hypothesis

`EllipticPdes.Regularity.IsCkCoeff` states the coefficient hypothesis of Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Theorem 2: every entry is `Cᵏ` with a uniform bound
on each `iteratedFDeriv`. `EllipticPdes.Regularity.IsWkInftyCoeff` states the weaker hypothesis
of Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem VIII.3.2
(p. 65): weak derivatives up to order `k`, essentially bounded. This file connects them, so
that a theorem proved under Guo's hypothesis applies to smooth coefficients with no further
work.

The bridge needs two facts and nothing else. A classical partial derivative of a `C¹` function
is a weak partial derivative, which is integration by parts against a compactly supported test
function. A classical iterated partial derivative is a value of `iteratedFDeriv` on unit
vectors, so the operator-norm bound of `IsCkCoeff` transfers to it pointwise, and a pointwise
bound is in particular an essential bound.

## Iterated classical partial derivative

`iterPartial f α` applies `partialD` once per entry of `α`, outermost first, so that
`iterPartial f (l :: α) = ∂_l (iterPartial f α)`. This is the `cons` convention of
`IsWkInftyCoeff.D`, which is what makes `iterPartial` a legal choice of `D`.

## Main declarations

* `iterPartial`: the iterated classical partial derivative along a list of directions.
* `iterPartial_eq_iteratedFDeriv`: it is `iteratedFDeriv` evaluated on the unit vectors of the
  list.
* `hasWeakPartial_partialD`: a classical partial derivative of a `C¹` function is a weak one.
* `IsCkCoeff.toIsWkInftyCoeff`: the bridge.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Unit vectors along a list of directions -/

/-- The tuple of coordinate unit vectors named by a list of directions, in the order the list
gives them. This is the argument `iteratedFDeriv` is evaluated at to produce an iterated
partial derivative. -/
def dirVec : (α : List (Fin d)) → Fin α.length → EuclideanSpace ℝ (Fin d)
  | [] => Fin.elim0
  | l :: α => Fin.cons (EuclideanSpace.single l 1) (dirVec α)

@[simp]
theorem dirVec_cons_zero (l : Fin d) (α : List (Fin d)) :
    dirVec (l :: α) 0 = EuclideanSpace.single l 1 := rfl

@[simp]
theorem dirVec_cons_tail (l : Fin d) (α : List (Fin d)) :
    Fin.tail (dirVec (l :: α)) = dirVec α := rfl

/-- Every entry of `dirVec` is a unit vector, so a multilinear bound evaluated on it loses
nothing. -/
theorem norm_dirVec (α : List (Fin d)) (i : Fin α.length) : ‖dirVec α i‖ = 1 := by
  induction α with
  | nil => exact i.elim0
  | cons l α ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa [dirVec] using ih j

/-! ### Iterated classical partial derivative -/

/-- The iterated classical partial derivative along a list of directions, outermost first:
`iterPartial f (l :: α) = ∂_l (iterPartial f α)`. The `cons` convention matches
`IsWkInftyCoeff.D`, whose `D_step` differentiates the head. -/
def iterPartial (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    List (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ
  | [] => f
  | l :: α => partialD l (iterPartial f α)

@[simp]
theorem iterPartial_nil (f : EuclideanSpace ℝ (Fin d) → ℝ) : iterPartial f [] = f := rfl

@[simp]
theorem iterPartial_cons (f : EuclideanSpace ℝ (Fin d) → ℝ) (l : Fin d) (α : List (Fin d)) :
    iterPartial f (l :: α) = partialD l (iterPartial f α) := rfl

/-- Each differentiation spends one order of smoothness: `f ∈ C^{n + |α|}` gives
`iterPartial f α ∈ Cⁿ`. -/
theorem contDiff_iterPartial {f : EuclideanSpace ℝ (Fin d) → ℝ} :
    ∀ (α : List (Fin d)) {n : ℕ}, ContDiff ℝ ((n + α.length : ℕ) : ℕ∞) f →
      ContDiff ℝ ((n : ℕ) : ℕ∞) (iterPartial f α) := by
  intro α
  induction α with
  | nil => intro n hf; simpa using hf
  | cons l α ih =>
    intro n hf
    have h1 : ContDiff ℝ (((n + 1) + α.length : ℕ) : ℕ∞) f := by
      have : (n + 1) + α.length = n + (l :: α).length := by simp [List.length_cons]; omega
      rw [this]; exact hf
    have h2 : ContDiff ℝ (((n + 1 : ℕ)) : ℕ∞) (iterPartial f α) := ih h1
    have h3 : ContDiff ℝ ((n : ℕ) : ℕ∞) (fderiv ℝ (iterPartial f α)) := by
      refine h2.fderiv_right ?_
      norm_cast
    have h4 : ContDiff ℝ ((n : ℕ) : ℕ∞)
        (fun x => (fderiv ℝ (iterPartial f α) x) (EuclideanSpace.single l 1)) :=
      h3.clm_apply contDiff_const
    exact h4

/-- **Iterated partial derivative as a value of `iteratedFDeriv`.** Applying `partialD`
once per entry of `α` produces `iteratedFDeriv ℝ |α| f x` evaluated on the unit vectors `α`
names. The proof peels the head with `iteratedFDeriv_succ_apply_left`, which differentiates
the `|α|`-th derivative once more, and commutes that derivative past the evaluation at a
fixed tuple, which is a continuous linear map. -/
theorem iterPartial_eq_iteratedFDeriv {f : EuclideanSpace ℝ (Fin d) → ℝ} :
    ∀ (α : List (Fin d)) {n : ℕ}, α.length ≤ n → ContDiff ℝ ((n : ℕ) : ℕ∞) f →
      ∀ x, iterPartial f α x = iteratedFDeriv ℝ α.length f x (dirVec α) := by
  intro α
  induction α with
  | nil => intro n _ _ x; simp
  | cons l α ih =>
    intro n hα hf x
    have hαn : α.length < n := by simpa [List.length_cons] using hα
    have hIH : iterPartial f α = fun y => iteratedFDeriv ℝ α.length f y (dirVec α) := by
      funext y; exact ih (le_of_lt hαn) hf y
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ α.length f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hαn)
    have hFD : HasFDerivAt (fun y => iteratedFDeriv ℝ α.length f y (dirVec α))
        ((fderiv ℝ (iteratedFDeriv ℝ α.length f) x).flipMultilinear (dirVec α)) x :=
      (hdiff x).hasFDerivAt.continuousMultilinear_apply_const (dirVec α)
    calc iterPartial f (l :: α) x
        = fderiv ℝ (fun y => iteratedFDeriv ℝ α.length f y (dirVec α)) x
            (EuclideanSpace.single l 1) := by rw [iterPartial_cons, hIH]; rfl
      _ = fderiv ℝ (iteratedFDeriv ℝ α.length f) x (EuclideanSpace.single l 1) (dirVec α) := by
            rw [hFD.fderiv]; rfl
      _ = iteratedFDeriv ℝ (l :: α).length f x (dirVec (l :: α)) := rfl

/-- The iterated partial derivative is bounded by the operator norm of the corresponding
`iteratedFDeriv`, because it is that multilinear map evaluated on unit vectors. -/
theorem abs_iterPartial_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (α : List (Fin d)) {n : ℕ}
    (hα : α.length ≤ n) (hf : ContDiff ℝ ((n : ℕ) : ℕ∞) f) (x : EuclideanSpace ℝ (Fin d)) :
    |iterPartial f α x| ≤ ‖iteratedFDeriv ℝ α.length f x‖ := by
  rw [iterPartial_eq_iteratedFDeriv α hα hf x, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  rw [Finset.prod_congr rfl (fun i _ => norm_dirVec α i)]
  simp

/-! ### Classical derivative as a weak derivative -/

/-- **Integration by parts for a `C¹` function against a test function.** The classical
partial derivative of a continuously differentiable function is its weak partial derivative.
No decay is asked of `f`, because the test function has compact support and puts every
integrand into `L¹`. -/
theorem hasWeakPartial_partialD {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ ((1 : ℕ) : ℕ∞) f) (l : Fin d) :
    HasWeakPartial l f (partialD l f) := by
  intro φ hφ hφc
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcf : Continuous f := hfd.continuous
  have hcφ : Continuous φ := hφd.continuous
  have hcdf : Continuous (partialD l f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : Continuous (partialD l φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  -- Every integrand is continuous and inherits the compact support of `φ`.
  have hsuppDφ : HasCompactSupport (partialD l φ) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
  have h1 : Integrable (fun x => partialD l f x * φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (hcdf.mul hcφ).integrable_of_hasCompactSupport hφc.mul_left
  have h2 : Integrable (fun x => f x * partialD l φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (hcf.mul hcdφ).integrable_of_hasCompactSupport hsuppDφ.mul_left
  have h3 : Integrable (fun x => f x * φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (hcf.mul hcφ).integrable_of_hasCompactSupport hφc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (f := f) (g := φ)
    (v := EuclideanSpace.single l 1) h1 h2 h3
    (fun x _ => hfd.differentiableAt) (fun x _ => hφd.differentiableAt)

/-! ### Bridge -/

/-- **`Cᵏ` coefficient bundle as a `W^{k,∞}` bundle.** The classical iterated
partial derivatives serve as the weak derivative family, each step is integration by parts,
and the pointwise `iteratedFDeriv` bound of `IsCkCoeff` is in particular an essential bound.

Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem VIII.3.2
(p. 65) is therefore no weaker than Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2 as far as the coefficients go, and a result proved under `IsWkInftyCoeff` applies
to smooth coefficients through this map. -/
def IsCkCoeff.toIsWkInftyCoeff {A : EllipticCoeff d} {k : ℕ} (hA : IsCkCoeff A k) :
    IsWkInftyCoeff A k where
  D α i j := iterPartial (fun x => A.a x i j) α
  D_nil _ _ := rfl
  D_meas i j α hα := by
    have hk : (((0 + α.length : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : 0 + α.length ≤ k := by omega
      exact_mod_cast this
    have h := contDiff_iterPartial (f := fun x => A.a x i j) (n := 0) α
      ((hA.contDiff i j).of_le hk)
    exact h.continuous.measurable
  D_step i j l α hα := by
    have hk : (((1 + α.length : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : 1 + α.length ≤ k := by omega
      exact_mod_cast this
    have h1 : ContDiff ℝ ((1 + α.length : ℕ) : ℕ∞) (fun x => A.a x i j) :=
      (hA.contDiff i j).of_le hk
    exact hasWeakPartial_partialD (contDiff_iterPartial (n := 1) α h1) l
  -- Order zero is the entry itself, which `EllipticCoeff` bounds by `Λ`. `IsCkCoeff.bound`
  -- constrains orders `1` through `k` only, so `bound 0` is free and `Λ` is what fills it.
  bound m := if m = 0 then A.Λ else hA.bound m
  bound_nonneg m := by
    by_cases h : m = 0
    · simp [h, A.Λ_nonneg]
    · simp [h, hA.bound_nonneg m]
  ess_bdd i j α hα := by
    rcases Nat.eq_zero_or_pos α.length with h0 | hpos
    · have hnil : α = [] := List.length_eq_zero_iff.mp h0
      subst hnil
      filter_upwards [A.bdd i j] with x hx
      simpa using hx
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hle : |iterPartial (fun x => A.a x i j) α x|
          ≤ ‖iteratedFDeriv ℝ α.length (fun y => A.a y i j) x‖ :=
        abs_iterPartial_le α hα (hA.contDiff i j) x
      have hbd := hA.iteratedFDeriv_bdd i j α.length hpos hα x
      simpa [Nat.ne_of_gt hpos] using hle.trans hbd

end EllipticPdes.Regularity
