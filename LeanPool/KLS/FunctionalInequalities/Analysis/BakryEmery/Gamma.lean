/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Laplacian

/-!
# The carre du champ and its iteration

Gamma, Gamma_2 and the product identity. Generic differential tools live in
Calculus.lean. These pointwise statements provide no semigroup gradient estimate.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The carré du champ and the carré-du-champ product identity -/

section Gamma

variable [CompleteSpace E]

/-- The **carré du champ** `Γ(f, g)(x) = ⟪∇f(x), ∇g(x)⟫`, defined geometrically. -/
def gamma (f g : E → ℝ) (x : E) : ℝ := ⟪gradient f x, gradient g x⟫

theorem gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl

theorem gamma_comm (f g : E → ℝ) (x : E) : gamma f g x = gamma g f x := real_inner_comm _ _

/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem gamma_self_fun (f : E → ℝ) : gamma f f = fun y => ‖gradient f y‖ ^ 2 :=
  funext (gamma_self f)

/-- Regularity of the carré du champ: `C^{n+1}` data give a `C^n` carré du champ. -/
theorem contDiff_gamma {n p q : WithTop ℕ∞} {f g : E → ℝ} (hf : ContDiff ℝ p f)
    (hg : ContDiff ℝ q g) (hp : n + 1 ≤ p) (hq : n + 1 ≤ q) : ContDiff ℝ n (gamma f g) :=
  ContDiff.inner ℝ (contDiff_gradient hf hp) (contDiff_gradient hg hq)

/-- The carré du champ inherits the compact support of its first argument. -/
theorem hasCompactSupport_gamma_left {f : E → ℝ} (g : E → ℝ) (hfc : HasCompactSupport f) :
    HasCompactSupport (gamma f g) := by
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [gamma_apply, h0]

/-- The carré du champ of two `C¹` functions is continuous. -/
theorem continuous_gamma {f g : E → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Continuous (gamma f g) :=
  (continuous_gradient hf).inner (continuous_gradient hg)

variable [FiniteDimensional ℝ E]

/-- Product rule for the weighted Laplacian: `ℒ(fg) = f ℒg + g ℒf + 2 Γ(f, g)`, for `C²` `f`, `g`
and an arbitrary potential `U`. -/
theorem weightedLaplacian_mul (U : E → ℝ) {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    weightedLaplacian U (fun y => f y * g y) x =
      f x * weightedLaplacian U g x + g x * weightedLaplacian U f x + 2 * gamma f g x := by
  simp only [weightedLaplacian_apply, gamma_apply]
  rw [laplacian_mul hf hg x, gradient_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x), inner_add_right, inner_smul_right, inner_smul_right]
  ring

/-- **Chain rule for the weighted Laplacian.** Under the hypotheses of `laplacian_comp`,
`ℒ(h ∘ G) = h'(G) ℒG + h''(G) Γ(G, G)`. -/
theorem weightedLaplacian_comp (U : E → ℝ) {h h' h'' : ℝ → ℝ} {G : E → ℝ} (hG : ContDiff ℝ 2 G)
    (hh : ∀ y, HasDerivAt h (h' (G y)) (G y)) {x : E} (hh' : HasDerivAt h' (h'' (G x)) (G x)) :
    weightedLaplacian U (fun y => h (G y)) x =
      h' (G x) * weightedLaplacian U G x + h'' (G x) * gamma G G x := by
  simp only [weightedLaplacian_apply, gamma_self]
  rw [laplacian_comp hG hh hh', gradient_comp (hh x).differentiableAt
    ((hG.differentiable (by norm_num)) x), (hh x).deriv, inner_smul_right]
  ring

/--
**the carré-du-champ product identity, the carré-du-champ product identity**: for `C²` functions
`f`, `g` and any
potential `U`, `(ℒ(fg) - f ℒg - g ℒf) / 2 = Γ(f, g) = ⟪∇f, ∇g⟫`. -/
theorem gamma_eq_weightedLaplacian (U : E → ℝ) {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    (weightedLaplacian U (fun y => f y * g y) x - f x * weightedLaplacian U g x -
          g x * weightedLaplacian U f x) /
        2 =
      gamma f g x := by
  rw [weightedLaplacian_mul U hf hg x]
  ring

/-- The **iterated carré du champ** in the diffusion convention,
`Γ₂(f) = ℒ(Γ(f, f)) / 2 - Γ(f, ℒf)`, with `Γ(f, ℒf) = ⟪∇f, ∇(ℒf)⟫` read geometrically. -/
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x

theorem gammaTwo_apply (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x := rfl

/--
`Γ₂` written out in gradients and Laplacians, exactly the left-hand side of the Bochner identity. -/
theorem gammaTwo_eq_expanded (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
            ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫) /
          2 -
        ⟪gradient f x,
          gradient (fun y => Laplacian.laplacian f y - ⟪gradient U y, gradient f y⟫) x⟫ := by
  simp only [gammaTwo_apply, gamma_self, weightedLaplacian_apply, gamma_apply]
  rfl

end Gamma

end FunctionalInequalities.Analysis.BakryEmery
