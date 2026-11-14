/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum

/-!
# Iterated derivatives along a line

Let `f : E → ℂ` be analytic (`ContDiff ℂ ω f`), `w : Fin t → E` and `ζ ∈ E`. For
`g z = D^t f (z • ζ) (w)` we show

  `iteratedDeriv k g z = D^{t+k} f (z • ζ) (w, ζ, …, ζ)`        (`iteratedDeriv_line`).

The proof peels one direction off an iterated derivative, using symmetry of iterated
derivatives of analytic functions (`peel`).
-/

@[expose] public section

namespace LeanPool

open Function
open scoped ContDiff

namespace StrongSix.Thm1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Moving the last argument to the front. -/
theorem comp_finRotate_symm {α : Type*} {k : ℕ} (m : Fin (k + 1) → α) :
    m ∘ (finRotate (k + 1)).symm = Fin.cons (m (Fin.last k)) (Fin.init m) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have : (finRotate (k + 1)).symm 0 = Fin.last k := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    simp [this]
  · have : (finRotate (k + 1)).symm j.succ = j.castSucc := by
      rw [Equiv.symm_apply_eq]
      ext
      rw [show j.castSucc = (⟨(j : ℕ), by omega⟩ : Fin (k + 1)) from rfl, finRotate_of_lt j.isLt]
      simp
    simp [this, Fin.init]

/-- **Peeling the last direction.** -/
theorem peel {f : E → ℂ} (hf : ContDiff ℂ ω f) (k : ℕ) (x : E) (m : Fin (k + 1) → E) :
    iteratedFDeriv ℂ (k + 1) f x m =
      fderiv ℂ (fun y => iteratedFDeriv ℂ k f y (Fin.init m)) x (m (Fin.last k)) := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k f) x :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
  rw [← hf.contDiffAt.iteratedFDeriv_comp_perm m (finRotate (k + 1)).symm, comp_finRotate_symm,
    hd.iteratedFDeriv_succ_apply_left']
  simp

/-- `w` followed by `k` copies of `ζ`. -/
def ext {t : ℕ} (w : Fin t → E) (ζ : E) : (k : ℕ) → Fin (t + k) → E
  | 0 => w
  | k + 1 => Fin.snoc (α := fun _ => E) (ext w ζ k) ζ

theorem differentiable_iteratedFDeriv_apply {f : E → ℂ} (hf : ContDiff ℂ ω f) (k : ℕ)
    (v : Fin k → E) : Differentiable ℂ (fun y => iteratedFDeriv ℂ k f y v) := fun x =>
  ((hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _))
    x).continuousMultilinear_apply_const v

theorem hasDerivAt_line {f : E → ℂ} (hf : ContDiff ℂ ω f) {t : ℕ} (w : Fin t → E) (ζ : E)
    (k : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => iteratedFDeriv ℂ (t + k) f (z • ζ) (ext w ζ k))
      (iteratedFDeriv ℂ (t + k + 1) f (z • ζ) (ext w ζ (k + 1))) z := by
  have hH := differentiable_iteratedFDeriv_apply hf (t + k) (ext w ζ k)
  have hline : HasDerivAt (fun z : ℂ => z • ζ) ζ z := by
    simpa using (hasDerivAt_id z).smul_const ζ
  have := (hH (z • ζ)).hasFDerivAt.comp_hasDerivAt z hline
  refine this.congr_deriv ?_
  rw [peel hf]
  simp [ext, Fin.init_snoc, Fin.snoc_last]

/-- **Iterated derivatives along a line.** -/
theorem iteratedDeriv_line {f : E → ℂ} (hf : ContDiff ℂ ω f) {t : ℕ} (w : Fin t → E) (ζ : E)
    (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => iteratedFDeriv ℂ t f (z • ζ) w) =
      fun z => iteratedFDeriv ℂ (t + k) f (z • ζ) (ext w ζ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hasDerivAt_line hf w ζ k z).deriv

theorem differentiable_line {f : E → ℂ} (hf : ContDiff ℂ ω f) {t : ℕ} (w : Fin t → E) (ζ : E) :
    Differentiable ℂ (fun z : ℂ => iteratedFDeriv ℂ t f (z • ζ) w) := fun z => by
  exact (hasDerivAt_line hf w ζ 0 z).differentiableAt

end StrongSix.Thm1

end LeanPool
