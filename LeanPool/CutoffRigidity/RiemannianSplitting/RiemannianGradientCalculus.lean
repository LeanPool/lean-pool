/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateGradient

/-! # Genuine gradient/Hessian calculus in the source smooth domain

Gradient differentiability is derived from C² functions and the actual metric.
The finite squared tensor norm is the sum of squares of all Hessian entries.
Product rules are proved using the actual Levi-Civita Leibniz law.
-/
@[expose] public section
open Bundle
open scoped Manifold ContDiff
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

/-- The first Bochner derivative identity with all gradient-regularity
obligations derived from the source scalar C² assumption. -/
theorem mvfderiv_manifoldGradient_norm_sq_of_C2 {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => ‖manifoldGradient I f y‖^2) x v =
      2*manifoldHessian I f x v (manifoldGradient I f x) :=
  mvfderiv_manifoldGradient_norm_sq I
    ((contMDiff_manifoldGradient hf x).mdifferentiableAt one_ne_zero) v

omit [BoundarylessManifold I M] in
/-- The actual squared Hilbert--Schmidt Hessian norm is the finite sum of
squares of every tensor coefficient, with no curvature premise. -/
theorem manifoldHessianNormSq_eq_sum_sq (f : M → ℝ) (x : M) :
    manifoldHessianNormSq I f x =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
      ∑ j : Fin (Module.finrank ℝ (TangentSpace I x)),
        (manifoldHessian I f x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) j))^2 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact ((stdOrthonormalBasis ℝ (TangentSpace I x)).sum_sq_inner_left _).symm

/-- Product Hessian rule for the true covariant Hessian, with all field
regularity supplied by the actual C² scalar functions. -/
theorem manifoldHessian_mul {f g : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ, ℝ) 2 g)
    (x : M) (v w : TangentSpace I x) :
    manifoldHessian I (f*g) x v w =
      f x*manifoldHessian I g x v w + g x*manifoldHessian I f x v w +
      mvfderiv I f x v*mvfderiv I g x w + mvfderiv I g x v*mvfderiv I f x w := by
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hdf := (hf x).mdifferentiableAt (by norm_num : (2:ℕ∞ω) ≠ 0)
  have hdg := (hg x).mdifferentiableAt (by norm_num : (2:ℕ∞ω) ≠ 0)
  have hgf := (contMDiff_manifoldGradient hf x).mdifferentiableAt one_ne_zero
  have hgg := (contMDiff_manifoldGradient hg x).mdifferentiableAt one_ne_zero
  have hgrad : manifoldGradient I (f*g) = f • manifoldGradient I g + g • manifoldGradient I f := by
    funext y
    exact manifoldGradient_mul I ((hf y).mdifferentiableAt (by norm_num))
      ((hg y).mdifferentiableAt (by norm_num))
  have ha : cov (f • manifoldGradient I g + g • manifoldGradient I f) x =
      cov (f • manifoldGradient I g) x + cov (g • manifoldGradient I f) x := by
    exact cov.isCovariantDerivativeOn.add (s := Set.univ)
      (hdf.fun_smul_section hgg) (hdg.fun_smul_section hgf)
  have hb : cov (f • manifoldGradient I g) x =
      f x • cov (manifoldGradient I g) x + (mvfderiv I f x).smulRight (manifoldGradient I g x) := by
    exact cov.isCovariantDerivativeOn.leibniz (s := Set.univ) hgg hdf
  have hc : cov (g • manifoldGradient I f) x =
      g x • cov (manifoldGradient I f) x + (mvfderiv I g x).smulRight (manifoldGradient I f x) := by
    exact cov.isCovariantDerivativeOn.leibniz (s := Set.univ) hgf hdg
  have hd := (congrArg (fun Y => cov Y x) hgrad).trans
    (ha.trans (congrArg₂ (fun A B => A+B) hb hc))
  have he := congrArg (fun L => inner ℝ (L v) w) hd
  change manifoldHessian I (f*g) x v w = _ at he
  rw [he]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,inner_add_left,
    inner_smul_left,starRingEnd_apply,star_trivial,inner_manifoldGradient]
  dsimp only [manifoldHessian,cov]
  ring

end CutoffRigidity
