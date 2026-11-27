/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Data.Matrix.Basis
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The gradient of a Lipschitz map

For a `K`-Lipschitz `φ : ℝ^m → ℝ^d` (sup norms): the entries of `grad φ` are bounded by `K`,
`grad φ` is measurable, it depends only on the germ of `φ`, it is additive at points of
differentiability, and `x ↦ f (A + ∇φ (x))` is bounded and integrable on sets of finite measure
for a Borel, locally bounded `f`.

Two families of lemmas cover the same ground (prefixes `rd_` and `cv_`); they are kept apart for
now.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- `|∂_k φ_i| ≤ K` for a `K`-Lipschitz `φ`. -/
lemma rd_grad_abs_le {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |grad φ x i k| ≤ K := by
  have hi : LipschitzWith K (fun y => φ y i) := by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at h
    exact h
  simp only [grad, Matrix.of_apply]
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ (fun y => φ y i) x (Pi.single k 1)‖
      ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hi
        · rw [Pi.norm_single, norm_one]
    _ = K := mul_one _

lemma rd_measurable_add_grad (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable fun x => A + grad φ x :=
  Measurable.of_eval_matrix _ fun i k => by
    simp only [Matrix.add_apply, grad, Matrix.of_apply]
    exact measurable_const.add (measurable_fderiv_apply_const ℝ (fun y => φ y i) _)

/-- A locally bounded function is bounded on compact sets. -/
private lemma rd_bdd_of_compact {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hbdd : IsLocallyBounded f)
    {K : Set (Matrix (Fin d) (Fin m) ℝ)} (hK : IsCompact K) : ∃ C, ∀ M ∈ K, |f M| ≤ C := by
  choose U hU C hC using hbdd
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |C x|, fun M hM => ?_⟩
  obtain ⟨x, hx, hMx⟩ := Set.mem_iUnion₂.1 (hcover hM)
  exact (hC x M hMx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))

private lemma rd_isCompact_box (B : Matrix (Fin d) (Fin m) ℝ) (K : ℝ) :
    IsCompact {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} := by
  have : {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} =
      Set.pi univ fun i => Set.pi univ fun k => Icc (B i k - K) (B i k + K) := by
    ext M
    constructor
    · intro h i _ k _
      exact ⟨by linarith [(abs_le.1 (h i k)).1], by linarith [(abs_le.1 (h i k)).2]⟩
    · intro h i k
      have := h i (Set.mem_univ _) k (Set.mem_univ _)
      exact abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun k => isCompact_Icc

/-- A bound for `f` on all matrices `A + G` with entries `|G_{ik}| ≤ L`. -/
lemma rd_bound_near {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hbdd : IsLocallyBounded f)
    (A : Matrix (Fin d) (Fin m) ℝ) (L : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ G : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |G i k| ≤ L) → |f (A + G)| ≤ C := by
  obtain ⟨C, hC⟩ := rd_bdd_of_compact hbdd (rd_isCompact_box A L)
  refine ⟨max C 0, le_max_right _ _, fun G hG => (hC _ fun i k => ?_).trans (le_max_left _ _)⟩
  simpa using hG i k

/-- A continuous function is locally bounded. -/
lemma isLocallyBounded_of_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    IsLocallyBounded f := fun A => by
  refine ⟨f ⁻¹' Metric.ball (f A) 1, hf.continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds _ one_pos), |f A| + 1, fun B hB => ?_⟩
  rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hB
  linarith [abs_sub_abs_le_abs_sub (f B) (f A)]

/-- For a Borel, locally bounded `f` and a Lipschitz `φ`, `x ↦ f (A + ∇φ (x))` is integrable on
sets of finite measure (it is measurable and bounded). -/
lemma rd_integrableOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Measurable f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hφ : LipschitzWith K φ) {s : Set (Fin m → ℝ)} (hs : volume s < ⊤) :
    IntegrableOn (fun x => f (A + grad φ x)) s := by
  obtain ⟨C, -, hC⟩ := rd_bound_near hbdd A K
  refine IntegrableOn.of_bound hs
    (hf.comp (rd_measurable_add_grad A φ)).aestronglyMeasurable C
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hC _ (rd_grad_abs_le hφ x)

lemma rd_volume_unitCube (m : ℕ) : volume (unitCube m) = 1 := by
  simp [unitCube, Real.volume_pi_Ioo]

/-- The entries of the gradient of a `K`-Lipschitz map are bounded by `K`. -/
theorem cv_grad_abs_le {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |grad φ x i k| ≤ K := by
  have hφi : LipschitzWith K (fun y => φ y i) := by
    have := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at this
    exact this
  change |fderiv ℝ (fun y => φ y i) x (Pi.single k 1)| ≤ K
  calc |fderiv ℝ (fun y => φ y i) x (Pi.single k 1)|
      ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        (fderiv ℝ (fun y => φ y i) x).le_opNorm _
    _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hφi
        · simp [Pi.norm_single]
    _ = K := mul_one _

/-- The gradient, as a map to `Fin d → Fin m → ℝ`, is measurable. -/
theorem cv_measurable_grad (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable (fun x i k => grad φ x i k : (Fin m → ℝ) → Fin d → Fin m → ℝ) :=
  Measurable.of_eval fun i => Measurable.of_eval fun k =>
    measurable_fderiv_apply_const ℝ (fun y => φ y i) (Pi.single k 1)

/-- `x ↦ F (A + ∇φ x)` is measurable for a measurable `F` on `Fin d → Fin m → ℝ`. -/
theorem cv_measurable_comp_grad {F : (Fin d → Fin m → ℝ) → ℝ} (hF : Measurable F)
    (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable fun x => F (fun i k => A i k + grad φ x i k) :=
  hF.comp (Measurable.of_eval fun i => Measurable.of_eval fun k =>
    measurable_const.add ((measurable_pi_iff.1 ((measurable_pi_iff.1 (cv_measurable_grad φ)) i)) k))

/-- A continuous function of a matrix is continuous on `Fin d → Fin m → ℝ`. -/
theorem cv_continuous_of {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    Continuous fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := hf

/-- The gradient at `x` only depends on the map near `x`. -/
theorem cv_grad_congr {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (h : φ =ᶠ[𝓝 x] ψ) :
    grad φ x = grad ψ x := by
  ext i k
  change fderiv ℝ (fun y => φ y i) x (Pi.single k 1) = fderiv ℝ (fun y => ψ y i) x (Pi.single k 1)
  have := (h.fun_comp (fun v : Fin d → ℝ => v i)).fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L => L (Pi.single k 1)) this

/-- The gradient of a map vanishing near `x` vanishes at `x`. -/
theorem cv_grad_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ}
    (h : φ =ᶠ[𝓝 x] fun _ => 0) : grad φ x = 0 := by
  rw [cv_grad_congr h]
  ext i k
  change fderiv ℝ (fun _ => (0 : Fin d → ℝ) i) x (Pi.single k 1) = 0
  simp

/-- The gradient of the sum of two maps, at a point where both are differentiable. -/
theorem cv_grad_add {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    grad (φ + ψ) x = grad φ x + grad ψ x := by
  ext i k
  change fderiv ℝ (fun y => φ y i + ψ y i) x (Pi.single k 1) =
    fderiv ℝ (fun y => φ y i) x (Pi.single k 1) + fderiv ℝ (fun y => ψ y i) x (Pi.single k 1)
  have h1 : DifferentiableAt ℝ (fun y => φ y i) x :=
    (differentiableAt_pi.1 hφ) i
  have h2 : DifferentiableAt ℝ (fun y => ψ y i) x :=
    (differentiableAt_pi.1 hψ) i
  rw [fderiv_fun_add h1 h2]
  rfl

end CalculusOfVariations
