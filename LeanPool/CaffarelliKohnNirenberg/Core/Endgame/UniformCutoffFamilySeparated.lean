/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

/-!
# Derivatives of a separated space-time product

For a function on space-time written as the separated product
`v ↦ g v.1 * h v.2` of a spatial factor `g` and a time factor `h`, this file
records the smoothness of the product and expresses its factor-wise spatial and
time derivatives through the derivatives of the two factors.  It also places
the support and the topological support of the product inside the product of
the corresponding one-factor sets.
-/

public section

open Set
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Endgame

/-- A product `v ↦ g v.1 * h v.2` of a smooth spatial factor and a smooth time
factor is smooth on space-time. -/
theorem contDiff_separatedProduct {g : Vec3 → ℝ} {h : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : Vec3 × ℝ => g v.1 * h v.2) :=
  (hg.comp contDiff_fst).mul (hh.comp contDiff_snd)

/-- The support of a separated product is contained in the product of the two
factor supports. -/
theorem support_separatedProduct_subset (g : Vec3 → ℝ) (h : ℝ → ℝ) :
    Function.support (fun v : Vec3 × ℝ => g v.1 * h v.2) ⊆
      Function.support g ×ˢ Function.support h := by
  intro v hv
  rw [Function.mem_support] at hv
  exact Set.mem_prod.mpr
    ⟨fun hz => hv (by rw [hz, zero_mul]), fun hz => hv (by rw [hz, mul_zero])⟩

/-- The topological support of a separated product is contained in the product
of the two factor topological supports. -/
theorem tsupport_separatedProduct_subset (g : Vec3 → ℝ) (h : ℝ → ℝ) :
    tsupport (fun v : Vec3 × ℝ => g v.1 * h v.2) ⊆ tsupport g ×ˢ tsupport h := by
  intro v hv
  have hv' : v ∈ closure (Function.support (fun v : Vec3 × ℝ => g v.1 * h v.2)) := hv
  have hmem : v ∈ closure (Function.support g ×ˢ Function.support h) :=
    closure_mono (support_separatedProduct_subset g h) hv'
  rw [closure_prod_eq] at hmem
  exact hmem

/-- The spatial partial derivative of a separated product is the product of the
spatial derivative of the spatial factor with the time factor. -/
theorem spatialPartial_separatedProduct {g : Vec3 → ℝ} (h : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (w : Vec3 × ℝ) :
    spatialPartial (fun v : Vec3 × ℝ => g v.1 * h v.2) i w = spatialDeriv g i w.1 * h w.2 := by
  have hfd : HasFDerivAt (fun x : Vec3 => g x * h w.2)
      ((h w.2) • (fderiv ℝ g w.1)) w.1 :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt.mul_const (h w.2)
  unfold spatialPartial
  change (fderiv ℝ (fun x : Vec3 => g x * h w.2) w.1) (basisVec i)
      = spatialDeriv g i w.1 * h w.2
  rw [hfd.fderiv, smul_apply, smul_eq_mul]
  unfold spatialDeriv
  ring

/-- The time partial derivative of a separated product is the product of the
spatial factor with the ordinary derivative of the time factor. -/
theorem timePartial_separatedProduct (g : Vec3 → ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (w : Vec3 × ℝ) :
    timePartial (fun v : Vec3 × ℝ => g v.1 * h v.2) w = g w.1 * deriv h w.2 := by
  have hfd : HasFDerivAt (fun s : ℝ => g w.1 * h s)
      ((g w.1) • (fderiv ℝ h w.2)) w.2 :=
    (hh.differentiable (by simp)).differentiableAt.hasFDerivAt.const_mul (g w.1)
  unfold timePartial
  change (fderiv ℝ (fun s : ℝ => g w.1 * h s) w.2) 1 = g w.1 * deriv h w.2
  rw [hfd.fderiv, smul_apply, smul_eq_mul, fderiv_apply_one_eq_deriv]

/-- The second spatial partial derivative of a separated product is the product
of the corresponding mixed second derivative of the spatial factor with the time
factor. -/
theorem spatialSecondPartial_separatedProduct {g : Vec3 → ℝ} (h : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin 3) (w : Vec3 × ℝ) :
    spatialSecondPartial (fun v : Vec3 × ℝ => g v.1 * h v.2) i j w =
      mixedSecond g j i w.1 * h w.2 := by
  unfold spatialSecondPartial
  have hfun : (fun w : ParabolicPoint =>
        spatialPartial (fun v : Vec3 × ℝ => g v.1 * h v.2) i w)
      = fun v : ParabolicPoint => spatialDeriv g i v.1 * h v.2 := by
    funext v
    exact spatialPartial_separatedProduct h hg i v
  rw [hfun]
  exact spatialPartial_separatedProduct h (contDiff_spatialDeriv_smooth hg i) j w

end CKN.Core.Endgame
