/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.Optimization.Gradient
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.MetricSpace.Contracting
public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
/-!
# Certified roots of differentiable systems

This module implements a strong, norm-form Krawczyk test for square systems in
LeanCert's `ADSupported` expression fragment. The center and rational
preconditioner are untrusted certificate data;
`krawczykCheck` verifies AD support, center containment, invertibility,
a strict infinity-norm contraction bound, and a strict self-map enclosure.

The golden theorem `krawczykCheck_sound` turns a successful Boolean check into
existence and uniqueness of a real root in the supplied box.
-/

@[expose] public section

namespace LeanCert.Engine
open LeanCert.Core

/-- Use the singleton zero interval as the additive identity. -/
local instance intervalRatZero : Zero IntervalRat := ⟨IntervalRat.singleton 0⟩
/-- Use endpoint-wise interval addition for finite interval sums. -/
local instance intervalRatAdd : Add IntervalRat := ⟨IntervalRat.add⟩

private theorem intervalRat_ext {a b : IntervalRat} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Natural scalar multiplication by repeated interval addition. -/
local instance : SMul Nat IntervalRat where
  smul n a :=
    { lo := (n : ℚ) * a.lo
      hi := (n : ℚ) * a.hi
      le := mul_le_mul_of_nonneg_left a.le (by positivity) }

/-- The additive commutative monoid of rational intervals. -/
local instance : AddCommMonoid IntervalRat :=
  Function.Injective.addCommMonoid
    (fun I : IntervalRat => (I.lo, I.hi))
    (by intro a b h; exact intervalRat_ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- Extend a finite real coordinate vector to an expression environment with zero defaults. -/
noncomputable def finEnv {n : Nat} (x : Fin n → ℝ) : Nat → ℝ :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- Evaluate an expression in the environment of a finite real coordinate vector. -/
noncomputable def evalFin {n : Nat} (e : Expr) (x : Fin n → ℝ) : ℝ :=
  Expr.eval (finEnv x) e

theorem evalFin_differentiable {n : Nat} (e : Expr) (h : ADSupported e) :
    Differentiable ℝ (evalFin (n := n) e) := by
  induction h with
  | const q =>
      rw [show evalFin (n := n) (.const q) = (fun _ : Fin n → ℝ => (q : ℝ)) from rfl]
      exact differentiable_const _
  | var i =>
      by_cases hi : i < n
      · rw [show evalFin (n := n) (.var i) = (fun x : Fin n → ℝ => x ⟨i, hi⟩) by
          funext x; simp [evalFin, finEnv, hi]]
        exact differentiable_apply _
      · rw [show evalFin (n := n) (.var i) = (fun _ : Fin n → ℝ => 0) by
          funext x; simp [evalFin, finEnv, hi]]
        exact differentiable_const _
  | add h₁ h₂ ih₁ ih₂ =>
      rw [show evalFin (n := n) (.add _ _) = evalFin (n := n) _ + evalFin (n := n) _ from rfl]
      exact ih₁.add ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
      rw [show evalFin (n := n) (.mul _ _) = evalFin (n := n) _ * evalFin (n := n) _ from rfl]
      exact ih₁.mul ih₂
  | neg h ih =>
      rw [show evalFin (n := n) (.neg _) = -evalFin (n := n) _ from rfl]
      exact ih.neg
  | sin h ih =>
      rw [show evalFin (n := n) (.sin _) = Real.sin ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_sin.comp ih
  | cos h ih =>
      rw [show evalFin (n := n) (.cos _) = Real.cos ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_cos.comp ih
  | exp h ih =>
      rw [show evalFin (n := n) (.exp _) = Real.exp ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_exp.comp ih

theorem finEnv_update {n : Nat} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    finEnv (Function.update x j t) = Expr.updateVar (finEnv x) j.val t := by
  funext i
  by_cases hi : i < n
  · by_cases hij : i = j.val
    · subst i
      simp [finEnv, Expr.updateVar]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ j := by
        intro h
        exact hij (Fin.ext_iff.mp h)
      simp [finEnv, Expr.updateVar, hi, hij, hfin]
  · have hij : i ≠ j.val := by omega
    simp [finEnv, Expr.updateVar, hi, hij]

theorem fderiv_single_eq_deriv_evalAlong {n : Nat} (e : Expr) (h : ADSupported e)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (evalFin (n := n) e) x (Pi.single j 1) =
      deriv (Expr.evalAlong e (finEnv x) j.val) (x j) := by
  have hout : HasFDerivAt (evalFin (n := n) e)
      (fderiv ℝ (evalFin (n := n) e) (Function.update x j (x j)))
      (Function.update x j (x j)) :=
    (evalFin_differentiable (n := n) e h).differentiableAt.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  rw [Function.update_eq_self] at hcomp
  have heq : (evalFin (n := n) e ∘ Function.update x j) =
      Expr.evalAlong e (finEnv x) j.val := by
    funext t
    simp only [Function.comp_apply, evalFin, Expr.evalAlong_eq]
    rw [finEnv_update]
  rw [heq] at hcomp
  exact hcomp.deriv.symm

/-- Evaluate all coordinate expressions of a finite system. -/
noncomputable def systemEval {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => evalFin (F i) x

theorem systemEval_differentiable {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) : Differentiable ℝ (systemEval F) := by
  rw [differentiable_pi]
  intro i
  exact evalFin_differentiable (F i) (h i)

/-- The matrix of coordinate partial derivatives of an expression system. -/
noncomputable def jacobianAt {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (systemEval F) x).toLinearMap

theorem jacobianAt_apply {n : Nat} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (x : Fin n → ℝ) (i j : Fin n) :
    jacobianAt F x i j = deriv (Expr.evalAlong (F i) (finEnv x) j.val) (x j) := by
  rw [jacobianAt, LinearMap.toMatrix'_apply]
  change fderiv ℝ (systemEval F) x (Pi.single j 1) i = _
  rw [show systemEval F = (fun x i => evalFin (F i) x) from rfl]
  have hpi := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun i => evalFin (F i)) (fun i => (evalFin_differentiable (F i) (h i)).differentiableAt)
  rw [hpi]
  simp only [ContinuousLinearMap.coe_pi']
  exact fderiv_single_eq_deriv_evalAlong (F i) (h i) x j

/-- Extend a finite interval box to the evaluator’s indexed environment. -/
def finBoxEnv {n : Nat} (X : Fin n → IntervalRat) : IntervalEnv :=
  fun i => if h : i < n then X ⟨i, h⟩ else IntervalRat.singleton 0

/-- Coordinatewise membership of a real vector in a rational interval box. -/
def FinBoxMem {n : Nat} (x : Fin n → ℝ) (X : Fin n → IntervalRat) : Prop :=
  ∀ i, x i ∈ X i

/-- Enclose the Jacobian entries by interval automatic differentiation. -/
def intervalJacobian {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cfg : EvalConfig := {}) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => Optimization.derivIntervalCoreN (F i) (finBoxEnv X) j.val cfg

theorem finEnv_mem_finBoxEnv {n : Nat} {x : Fin n → ℝ} {X : Fin n → IntervalRat}
    (hx : FinBoxMem x X) : ∀ i, finEnv x i ∈ finBoxEnv X i := by
  intro i
  by_cases hi : i < n
  · simpa [finEnv, finBoxEnv, hi] using hx ⟨i, hi⟩
  · simpa [finEnv, finBoxEnv, hi] using IntervalRat.mem_singleton 0

theorem jacobianAt_mem_intervalJacobian {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat)
    (x : Fin n → ℝ) (hx : FinBoxMem x X) (cfg : EvalConfig) (i j : Fin n) :
    jacobianAt F x i j ∈ intervalJacobian F X cfg i j := by
  rw [jacobianAt_apply F h x i j]
  exact Optimization.evalDualTotalCore_der_correct_idx (F i) (h i) (finEnv x) (finBoxEnv X)
    j.val (finEnv_mem_finBoxEnv hx) (x j) (by
      simpa only [finBoxEnv, j.isLt, dite_true] using hx j) cfg

/-- Interpret a real matrix as a continuous linear map on finite coordinate vectors. -/
noncomputable def matrixCLM {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

/-- The preconditioned Newton map `x ↦ x - Y (F x)`. -/
noncomputable def newtonMap {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (x : Fin n → ℝ) : Fin n → ℝ :=
  x - Matrix.mulVec Y (systemEval F x)

theorem newtonMap_differentiable {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) :
    Differentiable ℝ (newtonMap Y F) := by
  have hY : Differentiable ℝ (fun x => matrixCLM Y (systemEval F x)) :=
    (matrixCLM Y).differentiable.comp (systemEval_differentiable F h)
  rw [show newtonMap Y F = id - (fun x => matrixCLM Y (systemEval F x)) by
    funext x
    rfl]
  exact differentiable_id.sub hY

theorem newtonMap_fderiv_matrix {n : Nat} (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (x : Fin n → ℝ) :
    LinearMap.toMatrix' (fderiv ℝ (newtonMap Y F) x).toLinearMap =
      1 - Y * jacobianAt F x := by
  have hF : HasFDerivAt (systemEval F) (fderiv ℝ (systemEval F) x) x :=
    (systemEval_differentiable F h).differentiableAt.hasFDerivAt
  have hY := (matrixCLM Y).hasFDerivAt.comp x hF
  have hg : HasFDerivAt (newtonMap Y F)
      (ContinuousLinearMap.id ℝ _ - (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)) x := by
    change HasFDerivAt (fun z => z - matrixCLM Y (systemEval F z)) _ x
    exact (hasFDerivAt_id x).sub hY
  rw [hg.fderiv]
  change LinearMap.toMatrix' ((ContinuousLinearMap.id ℝ _ -
    (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)).toLinearMap) = _
  rw [ContinuousLinearMap.toLinearMap_sub]
  change LinearMap.toMatrix' (1 -
    (matrixCLM Y).toLinearMap.comp (fderiv ℝ (systemEval F) x).toLinearMap) = _
  rw [map_sub, LinearMap.toMatrix'_one, LinearMap.toMatrix'_comp]
  have hmatY : LinearMap.toMatrix' (matrixCLM Y).toLinearMap = Y := by
    change LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y
    exact LinearMap.toMatrix'_toLin' Y
  rw [hmatY]
  rfl

/-- The set of real vectors lying coordinatewise in the interval box. -/
def finBoxSet {n : Nat} (X : Fin n → IntervalRat) : Set (Fin n → ℝ) :=
  {x | FinBoxMem x X}

theorem finBoxSet_closed {n : Nat} (X : Fin n → IntervalRat) : IsClosed (finBoxSet X) := by
  have hi : ∀ i : Fin n, IsClosed {x : Fin n → ℝ | x i ∈ X i} := by
    intro i
    exact isClosed_Icc.preimage (continuous_apply i)
  have hinter := isClosed_iInter hi
  have heq : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ X i}) = finBoxSet X := by
    ext x
    simp [finBoxSet, FinBoxMem]
  rw [← heq]
  exact hinter

theorem finBoxSet_convex {n : Nat} (X : Fin n → IntervalRat) : Convex ℝ (finBoxSet X) := by
  intro x hx y hy a b ha hb hab i
  simp only [finBoxSet, Set.mem_ofPred_eq, FinBoxMem, IntervalRat.mem_def] at hx hy ⊢
  specialize hx i
  specialize hy i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · calc
      (X i).lo = a * (X i).lo + b * (X i).lo := by
        calc
          ((X i).lo : ℝ) = 1 * (X i).lo := by ring
          _ = (a + b) * (X i).lo := by rw [hab]
          _ = _ := by ring
      _ ≤ a * x i + b * y i := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc
      a * x i + b * y i ≤ a * (X i).hi + b * (X i).hi := add_le_add
        (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = (X i).hi := by
        calc
          a * (X i).hi + b * (X i).hi = (a + b) * (X i).hi := by ring
          _ = 1 * (X i).hi := by rw [hab]
          _ = _ := by ring

theorem contraction_unique_fixedPoint_in_finBox {n : Nat}
    (X : Fin n → IntervalRat) (m : Fin n → ℝ) (hm : FinBoxMem m X)
    (g : (Fin n → ℝ) → (Fin n → ℝ)) (hmap : Set.MapsTo g (finBoxSet X) (finBoxSet X))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdiff : ∀ x ∈ finBoxSet X, DifferentiableAt ℝ g x)
    (hderiv : ∀ x ∈ finBoxSet X, ‖fderiv ℝ g x‖ ≤ q) :
    ∃! x, FinBoxMem x X ∧ g x = x := by
  let K : NNReal := ⟨q, hq0⟩
  have hlipOn : LipschitzOnWith K g (finBoxSet X) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    change ‖g x - g y‖ ≤ q * ‖x - y‖
    simpa [norm_sub_rev] using
      (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le hdiff hderiv hy hx
  have hlipRestr : LipschitzWith K (hmap.restrict g (finBoxSet X) (finBoxSet X)) :=
    lipschitzOnWith_iff_restrict.mp hlipOn
  have hcontract : ContractingWith K (hmap.restrict g (finBoxSet X) (finBoxSet X)) := by
    refine ⟨?_, hlipRestr⟩
    exact hq1
  obtain ⟨x, hx, hfix, _⟩ := hcontract.exists_fixedPoint'
    (finBoxSet_closed X).isComplete hmap hm (edist_ne_top m (g m))
  refine ⟨x, ⟨hx, hfix⟩, ?_⟩
  intro y hy
  have hl := (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le
    hdiff hderiv hx hy.1
  rw [hy.2, hfix] at hl
  have hzero : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

open scoped Matrix.Norms.Operator

/-- The identity matrix represented by singleton rational intervals. -/
def intervalIdentity {n : Nat} : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => IntervalRat.singleton (if i = j then 1 else 0)

/-- Multiply a rational matrix by an interval matrix using interval sums. -/
def ratMulInterval {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => ∑ k, IntervalRat.scale (Y i k) (J k j)

/-- The interval matrix `I - Y J` enclosing the Newton-map derivative. -/
def preconditionedJacobian {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) : Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => IntervalRat.sub (intervalIdentity i j) (ratMulInterval Y J i j)

theorem mem_interval_sum {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (I : ι → IntervalRat) (h : ∀ i ∈ s, x i ∈ I i) :
    (∑ i ∈ s, x i) ∈ ∑ i ∈ s, I i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have hz : (0 : IntervalRat) = IntervalRat.singleton 0 :=
        intervalRat_ext rfl rfl
      rw [hz]
      norm_num [IntervalRat.mem_def, IntervalRat.singleton]
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at h
      simp only [Finset.sum_insert ha]
      exact IntervalRat.mem_add (h a (Or.inl rfl))
        (ih fun i hi => h i (Or.inr hi))

theorem mem_ratMulInterval {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (Jreal : Matrix (Fin n) (Fin n) ℝ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (hJ : ∀ i j, Jreal i j ∈ J i j) (i j : Fin n) :
    (Y.map (fun q => (q : ℝ)) * Jreal) i j ∈ ratMulInterval Y J i j := by
  simp only [Matrix.mul_apply, ratMulInterval]
  exact mem_interval_sum Finset.univ (fun k => (Y i k : ℝ) * Jreal k j)
    (fun k => IntervalRat.scale (Y i k) (J k j)) fun k _ =>
      IntervalRat.mem_scale (Y i k) (hJ k j)

theorem mem_preconditionedJacobian {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (Jreal : Matrix (Fin n) (Fin n) ℝ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (hJ : ∀ i j, Jreal i j ∈ J i j) (i j : Fin n) :
    (1 - Y.map (fun q => (q : ℝ)) * Jreal) i j ∈ preconditionedJacobian Y J i j := by
  apply IntervalRat.mem_sub
  · rw [Matrix.one_apply]
    unfold intervalIdentity
    split
    · norm_num [IntervalRat.mem_def, IntervalRat.singleton]
    · norm_num [IntervalRat.mem_def, IntervalRat.singleton]
  · exact mem_ratMulInterval Y Jreal J hJ i j

/-- The larger absolute endpoint, bounding absolute values in the interval. -/
def intervalAbsBound (I : IntervalRat) : ℚ := max |I.lo| |I.hi|

/-- The sum of absolute interval bounds in a selected matrix row. -/
def intervalMatrixRowBound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat)
    (i : Fin n) : ℚ := ∑ j, intervalAbsBound (A i j)

/-- The maximum interval row sum, bounding the matrix’s sup-norm operator norm. -/
def intervalMatrixBound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat) : ℚ :=
  (List.ofFn fun i => intervalMatrixRowBound A i).foldl max 0

theorem abs_le_intervalAbsBound {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x| ≤ intervalAbsBound I := by
  rw [abs_le]
  constructor
  · have hlo : ((I.lo : ℚ) : ℝ) ≤ x := hx.1
    have habs : -|(I.lo : ℝ)| ≤ (I.lo : ℝ) := neg_abs_le _
    have hmax : |(I.lo : ℝ)| ≤ (intervalAbsBound I : ℝ) := by
      exact_mod_cast le_max_left |I.lo| |I.hi|
    linarith [neg_le_neg hmax]
  · have hhi : x ≤ ((I.hi : ℚ) : ℝ) := hx.2
    have habs : (I.hi : ℝ) ≤ |(I.hi : ℝ)| := le_abs_self _
    have hmax : |(I.hi : ℝ)| ≤ (intervalAbsBound I : ℝ) := by
      exact_mod_cast le_max_right |I.lo| |I.hi|
    linarith

private theorem le_foldl_max (xs : List ℚ) (a : ℚ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left _ _) (ih _)

private theorem foldl_max_mono {xs : List ℚ} {a b : ℚ} (hab : a ≤ b) :
    xs.foldl max a ≤ xs.foldl max b := by
  induction xs generalizing a b with
  | nil => simpa using hab
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (max_le_max_right x hab)

private theorem le_foldl_max_of_mem {x : ℚ} {xs : List ℚ} (hx : x ∈ xs) :
    x ≤ xs.foldl max 0 := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · exact le_trans (le_max_right _ _) (le_foldl_max as _)
      · exact le_trans (ih hx) (foldl_max_mono (le_max_left 0 a))

theorem intervalMatrixRowBound_le_bound {n : Nat} (A : Matrix (Fin n) (Fin n) IntervalRat)
    (i : Fin n) : intervalMatrixRowBound A i ≤ intervalMatrixBound A := by
  apply le_foldl_max_of_mem
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem matrix_norm_le_intervalMatrixBound {n : Nat}
    (R : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) IntervalRat)
    (hmem : ∀ i j, R i j ∈ A i j) :
    ‖R‖ ≤ (intervalMatrixBound A : ℝ) := by
  rw [Matrix.linfty_opNorm_def]
  have hbound0 : 0 ≤ intervalMatrixBound A := le_foldl_max _ 0
  let Q : NNReal := ⟨intervalMatrixBound A, by exact_mod_cast hbound0⟩
  change (↑((Finset.univ : Finset (Fin n)).sup fun i => ∑ j, ‖R i j‖₊) : ℝ) ≤ ↑Q
  apply NNReal.coe_le_coe.mpr
  refine Finset.sup_le fun i _ => ?_
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum, coe_nnnorm]
  change (∑ j, |R i j|) ≤ (intervalMatrixBound A : ℝ)
  calc
    (∑ j, |R i j|) ≤ ∑ j, (intervalAbsBound (A i j) : ℝ) :=
      Finset.sum_le_sum fun j _ => abs_le_intervalAbsBound (hmem i j)
    _ = (intervalMatrixRowBound A i : ℝ) := by
      simp [intervalMatrixRowBound]
    _ ≤ (intervalMatrixBound A : ℝ) := by
      exact_mod_cast intervalMatrixRowBound_le_bound A i

theorem newtonMap_fderiv_norm_le {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat)
    (x : Fin n → ℝ) (hx : FinBoxMem x X) (cfg : EvalConfig) :
    ‖fderiv ℝ (newtonMap (Y.map fun q => (q : ℝ)) F) x‖ ≤
      (intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix]
  rw [newtonMap_fderiv_matrix (Y.map fun q => (q : ℝ)) F h x]
  apply matrix_norm_le_intervalMatrixBound
  exact mem_preconditionedJacobian Y (jacobianAt F x) (intervalJacobian F X cfg)
    (jacobianAt_mem_intervalJacobian F h X x hx cfg)

/-- Represent a rational center by singleton intervals in the evaluation environment. -/
def pointIntervalEnv {n : Nat} (m : Fin n → ℚ) : IntervalEnv :=
  fun i => if h : i < n then IntervalRat.singleton (m ⟨i, h⟩) else IntervalRat.singleton 0

/-- Enclose the expression system at a rational center by interval evaluation. -/
def pointEvalIntervals {n : Nat} (F : Fin n → Expr) (m : Fin n → ℚ)
    (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => LeanCert.Internal.Rational.evalTotalCore (F i) (pointIntervalEnv m) cfg

/-- Multiply a rational matrix by an interval vector. -/
def intervalRatMatVec {n : Nat} (Y : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i => ∑ j, IntervalRat.scale (Y i j) (v j)

/-- An interval enclosure of the preconditioned Newton map at the chosen center. -/
def newtonCenterInterval {n : Nat} (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => IntervalRat.sub (IntervalRat.singleton (m i))
    (intervalRatMatVec Y (pointEvalIntervals F m cfg) i)

theorem finEnv_ratCast_mem_pointIntervalEnv {n : Nat} (m : Fin n → ℚ) :
    ∀ i, finEnv (fun j => (m j : ℝ)) i ∈ pointIntervalEnv m i := by
  intro i
  by_cases hi : i < n
  · simpa [finEnv, pointIntervalEnv, hi] using IntervalRat.mem_singleton (m ⟨i, hi⟩)
  · simpa [finEnv, pointIntervalEnv, hi] using IntervalRat.mem_singleton 0

theorem systemEval_mem_pointEvalIntervals {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (m : Fin n → ℚ) (cfg : EvalConfig) (i : Fin n) :
    systemEval F (fun j => (m j : ℝ)) i ∈ pointEvalIntervals F m cfg i := by
  exact evalIntervalCore_correct (F i) (h i).toCore _ _
    (finEnv_ratCast_mem_pointIntervalEnv m) cfg
    (LeanCert.Engine.ADSupported.domainValid (h i) _ cfg)

theorem newtonMap_center_mem {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig) (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F (fun j => (m j : ℝ)) i ∈
      newtonCenterInterval F m Y cfg i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, intervalRatMatVec]
    exact mem_interval_sum Finset.univ
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (pointEvalIntervals F m cfg j))
      (fun j _ => IntervalRat.mem_scale (Y i j)
        (systemEval_mem_pointEvalIntervals F h m cfg j))

/-- The greater endpoint distance from the center in a selected coordinate. -/
def coordinateRadius {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (i : Fin n) : ℚ := max (m i - (X i).lo) ((X i).hi - m i)

/-- The maximum coordinate radius of the box around the chosen center. -/
def boxRadius {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) : ℚ :=
  (List.ofFn fun i => coordinateRadius X m i).foldl max 0

theorem coordinateRadius_le_boxRadius {n : Nat} (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (i : Fin n) : coordinateRadius X m i ≤ boxRadius X m := by
  apply le_foldl_max_of_mem
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem abs_sub_center_le_coordinateRadius {n : Nat} {X : Fin n → IntervalRat}
    {m : Fin n → ℚ} {x : Fin n → ℝ} (hx : FinBoxMem x X) (i : Fin n) :
    |x i - (m i : ℝ)| ≤ coordinateRadius X m i := by
  rw [abs_le]
  constructor
  · have hlo := (hx i).1
    have hmax : m i - (X i).lo ≤ coordinateRadius X m i := le_max_left _ _
    have hmaxR : ((m i - (X i).lo : ℚ) : ℝ) ≤ (coordinateRadius X m i : ℝ) :=
      by exact_mod_cast hmax
    push_cast at hmaxR
    linarith
  · have hhi := (hx i).2
    have hmax : (X i).hi - m i ≤ coordinateRadius X m i := le_max_right _ _
    have hmaxR : (((X i).hi - m i : ℚ) : ℝ) ≤ (coordinateRadius X m i : ℝ) :=
      by exact_mod_cast hmax
    push_cast at hmaxR
    linarith

theorem boxRadius_nonneg {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) :
    0 ≤ boxRadius X m := le_foldl_max _ 0

theorem norm_sub_center_le_boxRadius {n : Nat} {X : Fin n → IntervalRat}
    {m : Fin n → ℚ} {x : Fin n → ℝ} (hx : FinBoxMem x X) :
    ‖x - (fun i => (m i : ℝ))‖ ≤ (boxRadius X m : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro i
    rw [Real.norm_eq_abs]
    exact (abs_sub_center_le_coordinateRadius hx i).trans
      (by exact_mod_cast coordinateRadius_le_boxRadius X m i)
  · exact_mod_cast boxRadius_nonneg X m

/-- The rational interval with endpoints `-d` and `d`. -/
def symmetricInterval (d : ℚ) : IntervalRat :=
  { lo := -|d|
    hi := |d|
    le := neg_nonpos.mpr (abs_nonneg d) |>.trans (abs_nonneg d) }

/-- Enclose the Newton image using its center value and a uniform derivative bound. -/
def newtonImageEnclosure {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig := {}) :
    Fin n → IntervalRat :=
  let q := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg))
  let r := boxRadius X m
  fun i => IntervalRat.add (newtonCenterInterval F m Y cfg i) (symmetricInterval (q * r))

/-- Test whether both endpoints lie strictly inside another interval. -/
def intervalStrictInside (I X : IntervalRat) : Bool := X.lo < I.lo && I.hi < X.hi

theorem intervalStrictInside_sound {I X : IntervalRat} (h : intervalStrictInside I X = true) :
    ∀ x : ℝ, x ∈ I → x ∈ X := by
  intro x hx
  simp only [intervalStrictInside, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨le_trans (by exact_mod_cast h.1.le) hx.1, le_trans hx.2 (by exact_mod_cast h.2.le)⟩

theorem newtonMap_mapsTo_of_imageEnclosure {n : Nat} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig)
    (hencl : ∀ i, intervalStrictInside (newtonImageEnclosure F X m Y cfg i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun q => (q : ℝ)) F) (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let q : ℚ := intervalMatrixBound (preconditionedJacobian Y (intervalJacobian F X cfg))
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff : ‖newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr‖ ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable (Y.map fun q => (q : ℝ)) F h).differentiableAt
    · intro z hz
      exact newtonMap_fderiv_norm_le Y F h X z hz cfg
    · exact hm
    · exact hx
  have hq0 : 0 ≤ q := le_foldl_max _ 0
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm : ‖newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr‖ ≤
      ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx) (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord : |(newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr) i| ≤
      ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr : (newtonMap (Y.map fun q => (q : ℝ)) F x -
      newtonMap (Y.map fun q => (q : ℝ)) F mr) i ∈
      symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def, abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem F h m Y cfg i
  have himage : newtonMap (Y.map fun q => (q : ℝ)) F x i ∈
      newtonImageEnclosure F X m Y cfg i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [newtonImageEnclosure, q, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

/-- Rational center and preconditioner data for a checkable Krawczyk certificate. -/
structure KrawczykCert (n : Nat) where
  /-- The rational center used by the Newton-image enclosure. -/
  center : Fin n → ℚ
  /-- The rational matrix used to precondition the equation system. -/
  preconditioner : Matrix (Fin n) (Fin n) ℚ

/-- Coordinatewise containment of the rational center in the interval box. -/
def centerInside {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) : Prop :=
  ∀ i, (X i).lo ≤ m i ∧ m i ≤ (X i).hi

instance {n : Nat} (X : Fin n → IntervalRat) (m : Fin n → ℚ) :
    Decidable (centerInside X m) := by
  unfold centerInside
  infer_instance

/-- Check supported derivatives, center containment, invertibility, contraction and self-map
bounds. -/
def krawczykCheck {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cert : KrawczykCert n) (cfg : EvalConfig := {}) : Bool :=
  decide (∀ i, (F i).checkADSupported = true) &&
  decide (centerInside X cert.center) &&
  decide (cert.preconditioner.det ≠ 0) &&
  decide (intervalMatrixBound
    (preconditionedJacobian cert.preconditioner (intervalJacobian F X cfg)) < 1) &&
  decide (∀ i, intervalStrictInside
    (newtonImageEnclosure F X cert.center cert.preconditioner cfg i) (X i) = true)

/-- Every expression in the finite system evaluates to zero at the given point. -/
def SystemZero {n : Nat} (F : Fin n → Expr) (x : Fin n → ℝ) : Prop :=
  ∀ i, evalFin (F i) x = 0

theorem centerInside_sound {n : Nat} {X : Fin n → IntervalRat} {m : Fin n → ℚ}
    (h : centerInside X m) : FinBoxMem (fun i => (m i : ℝ)) X := by
  intro i
  constructor
  · change ((X i).lo : ℝ) ≤ (m i : ℝ)
    exact_mod_cast (h i).1
  · change (m i : ℝ) ≤ ((X i).hi : ℝ)
    exact_mod_cast (h i).2

theorem fixedPoint_iff_systemZero {n : Nat} (F : Fin n → Expr)
    (Y : Matrix (Fin n) (Fin n) ℚ) (hdet : Y.det ≠ 0) (x : Fin n → ℝ) :
    newtonMap (Y.map fun q => (q : ℝ)) F x = x ↔ SystemZero F x := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun q => (q : ℝ)
  have hdetR : Yr.det ≠ 0 := by
    simp only [Yr]
    exact_mod_cast hdet
  have hinj : Function.Injective Yr.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Yr.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdetR))
  constructor
  · intro hfix
    have hmul : Yr.mulVec (systemEval F x) = 0 := by
      funext i
      have hi := congrFun hfix i
      change x i - Yr.mulVec (systemEval F x) i = x i at hi
      exact sub_eq_self.mp hi
    have hz : systemEval F x = 0 := hinj (by simpa using hmul)
    intro i
    exact congrFun hz i
  · intro hz
    have hs : systemEval F x = 0 := by
      funext i
      exact hz i
    funext i
    simp [newtonMap, hs]

theorem krawczykCheck_sound {n : Nat} (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cert : KrawczykCert n) (cfg : EvalConfig)
    (hcheck : krawczykCheck F X cert cfg = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  simp only [krawczykCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hsupported, hcenter⟩, hdet⟩, hq⟩, hencl⟩
  have hsupp : ∀ i, ADSupported (F i) := fun i =>
    ((F i).checkADSupported_eq_true_iff).mp (hsupported i)
  let q : ℚ := intervalMatrixBound
    (preconditionedJacobian cert.preconditioner (intervalJacobian F X cfg))
  have hq0 : 0 ≤ q := le_foldl_max _ 0
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (cert.center i : ℝ)) (centerInside_sound hcenter)
    (newtonMap (cert.preconditioner.map fun q => (q : ℝ)) F)
    (newtonMap_mapsTo_of_imageEnclosure F hsupp X cert.center
      (centerInside_sound hcenter) cert.preconditioner cfg hencl)
    (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq)
    (fun x _ => (newtonMap_differentiable
      (cert.preconditioner.map fun q => (q : ℝ)) F hsupp).differentiableAt)
    (fun x hx => newtonMap_fderiv_norm_le cert.preconditioner F hsupp X x hx cfg)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero F cert.preconditioner hdet hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero F cert.preconditioner hdet y).mpr hy.2⟩
    hfixed.choose_spec.1

end LeanCert.Engine
