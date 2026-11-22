/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerDefs
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedPointwise

/-! # The drift term in the iterated carré du champ -/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

namespace CutCur.WBoch

section Quad

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Metric compatibility for the Levi-Civita connection, in directional form. -/
theorem mvfderiv_inner_lc {σ τ : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, σ y⟩ : TangentBundle 𝓘(ℝ, F) M)) x)
    (hτ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, τ y⟩ : TangentBundle 𝓘(ℝ, F) M)) x)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (σ y) (τ y)) x v =
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M σ x v) (τ x)
        + inner ℝ (σ x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M τ x v) := by
  have hh := (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, F)
    (M := M)).mvfderiv_inner_eq (FiberBundle.extend F v) hσ hτ
  have hv : FiberBundle.extend F v x = v := FiberBundle.extend_apply_self F v
  simp only [hv] at hh
  exact hh

theorem smAt_mgrad {f : M → ℝ} (hf : MSmooth F f) (x : M) : SmAt F (mgrad F f) x :=
  (CutCur.WReg.contMDiff_mgrad hf) x

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mdiffAt_of_smAt {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (h : SmAt F X x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, F) M)) x :=
  h.mdifferentiableAt (by simp)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- `⟨∇ φ, Y⟩ = dφ(Y)`. -/
theorem inner_mgrad_eq (φ : M → ℝ) (y : M) (w : TangentSpace 𝓘(ℝ, F) y) :
    inner ℝ (mgrad F φ y) w = mvfderiv 𝓘(ℝ, F) φ y w :=
  CutoffRigidity.inner_manifoldGradient (I := 𝓘(ℝ, F)) φ y w

/-- `dΓ(f)(w) = 2 ⟨∇_w u, u⟩`. -/
theorem mvfderiv_carre_apply {f : M → ℝ} (hf : MSmooth F f) (y : M)
    (w : TangentSpace 𝓘(ℝ, F) y) :
    mvfderiv 𝓘(ℝ, F) (carre F f f) y w =
      2 * inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) y w)
        (mgrad F f y) :=
  mvfderiv_carre_self F hf y w

theorem carre2_eq {V f : M → ℝ} (hV : MSmooth F V) (hf : MSmooth F f)
    (hsymm : ∀ φ : M → ℝ, MSmooth F φ → ∀ (y : M) (v w : TangentSpace 𝓘(ℝ, F) y),
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) y v) w =
        inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) y w) v)
    (hΔ : MSmooth F (mlaplacian F f)) (x : M) :
    carre2 F V f x = mlaplacian F (carre F f f) x / 2
      - mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x (mgrad F f x)
      + inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x))
          (mgrad F f x) := by
  have hu := mdiffAt_of_smAt F (smAt_mgrad F hf x)
  have hv := mdiffAt_of_smAt F (smAt_mgrad F hV x)
  have hin : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => inner ℝ (mgrad F V y) (mgrad F f y)) x :=
    MDifferentiableAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) hv hu
  have hΔd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (mlaplacian F f) x :=
    (hΔ x).mdifferentiableAt (by simp)
  have hg : mgenerator F V f = fun y => mlaplacian F f y - inner ℝ (mgrad F V y) (mgrad F f y) :=
    rfl
  have h1 : carre F f (mgenerator F V f) x =
      mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x (mgrad F f x)
        - (inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x))
            (mgrad F f x)
          + inner ℝ (mgrad F V x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
              (mgrad F f) x (mgrad F f x))) := by
    rw [carre_eq_mvfderiv, hg, mvfderiv_fun_sub hΔd hin, sub_apply,
      mvfderiv_inner_lc F hv hu]
  have h2 : inner ℝ (mgrad F V x) (mgrad F (carre F f f) x) =
      2 * inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
        (mgrad F V x)) (mgrad F f x) := by
    rw [real_inner_comm, inner_mgrad_eq, mvfderiv_carre_apply F hf]
  have h3 := hsymm f hf x (mgrad F V x) (mgrad F f x)
  have h4 := real_inner_comm (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
    (mgrad F f) x (mgrad F f x)) (mgrad F V x)
  unfold carre2
  rw [h1]
  simp only [mgenerator]
  rw [h2]
  linarith

end Quad

end CutCur.WBoch
