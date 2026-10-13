/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderPolar
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# OneStepSchauderWeakId

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weak Laplacian identity, the radial Laplacian, and cutoff localization

Three further ingredients of the flux-vanishing crux:

* the **weak identity** `∫ u · Δψ = ∫ Δu · ψ` for globally `C²` data with one
  factor compactly supported, obtained from Mathlib's line-derivative
  integration by parts;
* the **radial Laplacian**, i.e. the second-derivative calculus of `r ↦ f(x+r•ω)`
  used to convert the sphere-average derivative into a flux;
* **cutoff localization**, which upgrades the globally-`C²` weak identity to a
  function harmonic only on a neighbourhood of a closed ball, by multiplying by
  a smooth bump.
-/

-- ==== the weak identity ====
open scoped Real Laplacian
open MeasureTheory InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- The second directional derivative of `f` in direction `v`: `∂ᵥᵥ f (x) = D(y ↦
Df(y)·v)(x)·v`.  For `C²` functions this agrees with the iterated Fréchet
derivative `iterated ℝ 2 f x ![v, v]` (see `iteratedFDeriv_two_eq_dirDeriv2`). -/
def dirDeriv2 (v : EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y v) x v

/-! ### Smoothness / support bookkeeping for `dirDeriv2` -/

/-- The second directional derivative of a `C²` function is continuous. -/
theorem continuous_dirDeriv2 {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 2 f)
    (v : EuclideanSpace ℝ (Fin d)) : Continuous (dirDeriv2 v f) := by
  have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have h2 : ContDiff ℝ 0 (dirDeriv2 v f) :=
    (h1.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact h2.continuous

/-- The second directional derivative of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_dirDeriv2 {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (dirDeriv2 v f) :=
  (hf.fderiv_apply ℝ v).fderiv_apply ℝ v

/-- Continuity × compact support ⇒ integrability of a product. -/
private theorem integrable_mul_ccs {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport (by
    simpa [Pi.mul_def] using hgc.mul_left (f := f))

/-! ### The iterated-derivative ↔ second-directional-derivative bridge -/

/-- For `C²` `f`, the diagonal value of the iterated Fréchet derivative equals the second
directional derivative in direction `v`. -/
theorem iteratedFDeriv_two_eq_dirDeriv2 {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 2 f)
    (x v : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ 2 f x ![v, v] = dirDeriv2 v f x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (by norm_num)).differentiable_one) x
  have hcalc : fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    have h := fderiv_clm_apply (𝕜 := ℝ) (c := fun y => fderiv ℝ f y) (u := fun _ : _ => v)
      hfd (differentiableAt_const v)
    simpa using h
  rw [iteratedFDeriv_two_apply, dirDeriv2, hcalc]
  simp [ContinuousLinearMap.flip_apply]

/-! ### Green's second identity, one direction at a time -/

/-- **Green's identity in a single direction.**  For `u ∈ C²` and a compactly supported `ψ ∈ C²`,
`∫ u · ∂ᵥᵥψ = ∫ ∂ᵥᵥu · ψ`.  Proved by integrating by parts twice in direction `v`
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`); the boundary terms vanish because `ψ` has
compact support. -/
theorem green_dirDeriv2 {u ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 2 u) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ x, u x * dirDeriv2 v ψ x = ∫ x, dirDeriv2 v u x * ψ x := by
  -- differentiability / continuity of the first directional derivatives
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu_cont : Continuous u := hu.continuous
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψ_cont : Continuous ψ := hψ.continuous
  have hcd_d1u : ContDiff ℝ 1 (fun x => fderiv ℝ u x v) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hcd_d1ψ : ContDiff ℝ 1 (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hd1u_diff : Differentiable ℝ (fun x => fderiv ℝ u x v) := hcd_d1u.differentiable_one
  have hd1u_cont : Continuous (fun x => fderiv ℝ u x v) := hcd_d1u.continuous
  have hd1ψ_diff : Differentiable ℝ (fun x => fderiv ℝ ψ x v) := hcd_d1ψ.differentiable_one
  have hd1ψ_cont : Continuous (fun x => fderiv ℝ ψ x v) := hcd_d1ψ.continuous
  have hd1ψ_supp : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hψc.fderiv_apply ℝ v
  have hd2ψ_cont : Continuous (dirDeriv2 v ψ) := continuous_dirDeriv2 hψ v
  have hd2ψ_supp : HasCompactSupport (dirDeriv2 v ψ) := hasCompactSupport_dirDeriv2 hψc v
  have hd2u_cont : Continuous (dirDeriv2 v u) := continuous_dirDeriv2 hu v
  -- first integration by parts: ∫ u · ∂ᵥᵥψ = -∫ ∂ᵥu · ∂ᵥψ
  have hIBP1 : (∫ x, u x * dirDeriv2 v ψ x)
      = -∫ x, (fderiv ℝ u x v) * (fderiv ℝ ψ x v) := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := u) (g := fun x => fderiv ℝ ψ x v) (v := v)
      (integrable_mul_ccs hd1u_cont hd1ψ_cont hd1ψ_supp)
      (integrable_mul_ccs hu_cont hd2ψ_cont hd2ψ_supp)
      (integrable_mul_ccs hu_cont hd1ψ_cont hd1ψ_supp)
      (fun x _ => hu_diff.differentiableAt) (fun x _ => hd1ψ_diff.differentiableAt)
    simpa [dirDeriv2] using h
  -- second integration by parts: ∫ ∂ᵥu · ∂ᵥψ = -∫ ∂ᵥᵥu · ψ
  have hIBP2 : (∫ x, (fderiv ℝ u x v) * (fderiv ℝ ψ x v))
      = -∫ x, dirDeriv2 v u x * ψ x := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun x => fderiv ℝ u x v) (g := ψ) (v := v)
      (integrable_mul_ccs hd2u_cont hψ_cont hψc)
      (integrable_mul_ccs hd1u_cont hd1ψ_cont hd1ψ_supp)
      (integrable_mul_ccs hd1u_cont hψ_cont hψc)
      (fun x _ => hd1u_diff.differentiableAt) (fun x _ => hψ_diff.differentiableAt)
    simpa [dirDeriv2] using h
  rw [hIBP1, hIBP2, neg_neg]

/-! ### Green's second identity and the weak harmonic identity -/

/-- **Green's second identity.**  For `u ∈ C²` and a compactly supported `ψ ∈ C²`,
`∫ u · Δψ = ∫ Δu · ψ`.  Obtained by summing the single-direction Green identity
(`green_dirDeriv2`) over the standard orthonormal coordinate directions and identifying
`∑ᵢ ∂ᵢᵢ` with the Laplacian. -/
theorem integral_mul_laplacian_eq_integral_laplacian_mul {u ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 2 u) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, u x * Δ ψ x = ∫ x, Δ u x * ψ x := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  -- rewrite `∫ u · Δψ` as `∑ᵢ ∫ u · ∂ᵢᵢψ`
  have hΨ : ∫ x, u x * Δ ψ x = ∑ i, ∫ x, u x * dirDeriv2 (b i) ψ x := by
    have hpt : (fun x => u x * Δ ψ x) = fun x => ∑ i, u x * dirDeriv2 (b i) ψ x := by
      funext x
      have hlap : Δ ψ x = ∑ i, iteratedFDeriv ℝ 2 ψ x ![b i, b i] := by
        rw [laplacian_eq_iteratedFDeriv_orthonormalBasis ψ b]
      rw [hlap, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [iteratedFDeriv_two_eq_dirDeriv2 hψ x (b i)]
    rw [hpt, MeasureTheory.integral_finsetSum]
    intro i _
    exact integrable_mul_ccs hu.continuous (continuous_dirDeriv2 hψ (b i))
      (hasCompactSupport_dirDeriv2 hψc (b i))
  -- rewrite `∫ Δu · ψ` as `∑ᵢ ∫ ∂ᵢᵢu · ψ`
  have hU : ∫ x, Δ u x * ψ x = ∑ i, ∫ x, dirDeriv2 (b i) u x * ψ x := by
    have hpt : (fun x => Δ u x * ψ x) = fun x => ∑ i, dirDeriv2 (b i) u x * ψ x := by
      funext x
      have hlap : Δ u x = ∑ i, iteratedFDeriv ℝ 2 u x ![b i, b i] := by
        rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
      rw [hlap, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [iteratedFDeriv_two_eq_dirDeriv2 hu x (b i)]
    rw [hpt, MeasureTheory.integral_finsetSum]
    intro i _
    exact integrable_mul_ccs (continuous_dirDeriv2 hu (b i)) hψ.continuous hψc
  rw [hΨ, hU]
  exact Finset.sum_congr rfl fun i _ => green_dirDeriv2 hu hψ hψc (b i)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the radial Laplacian ====
open scoped Real RealInnerProductSpace ContDiff Laplacian
open MeasureTheory InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Second directional derivative of a radial function.**  For `φ ∈ C^∞` and the radial test
`ψ(z) = φ(‖z − x₀‖²)`, the second directional derivative in direction `v` is
`dirDeriv2 v ψ y = 4 ⟪y − x₀, v⟫² φ''(‖y−x₀‖²) + 2 ‖v‖² φ'(‖y−x₀‖²)`.

Computed by restricting to the line `t ↦ y + t v`, along which `‖(y+t v)−x₀‖²` is a quadratic, and
applying two 1-D chain rules. -/
theorem dirDeriv2_radial {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x₀ y v : 𝔼) :
    dirDeriv2 v (fun z => φ (‖z - x₀‖ ^ 2)) y
      = 4 * ⟪y - x₀, v⟫ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2)
        + 2 * ‖v‖ ^ 2 * deriv φ (‖y - x₀‖ ^ 2) := by
  set ψ : 𝔼 → ℝ := fun z => φ (‖z - x₀‖ ^ 2) with hψdef
  -- smoothness facts
  have hφdiff : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
  have hφ'C : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'diff : Differentiable ℝ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ'C).1
  have hqsmooth : ContDiff ℝ ∞ (fun z : 𝔼 => ‖z - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hψC : ContDiff ℝ ∞ ψ := hφ.comp hqsmooth
  have hψdiff : Differentiable ℝ ψ := hψC.differentiable (by norm_cast)
  -- the quadratic along the line
  set q : ℝ → ℝ := fun t => ‖y - x₀‖ ^ 2 + 2 * ⟪y - x₀, v⟫ * t + ‖v‖ ^ 2 * t ^ 2 with hqdef
  have hL : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y + s • v) v t := by
    intro t
    simpa using (((hasDerivAt_id t).smul_const v).const_add y)
  have hq_eq : ∀ t : ℝ, ‖(y + t • v) - x₀‖ ^ 2 = q t := by
    intro t
    have hsplit : (y + t • v) - x₀ = (y - x₀) + t • v := by abel
    rw [hsplit, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    simp only [hqdef]
    ring
  have hq_deriv : ∀ t : ℝ,
      HasDerivAt q (2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 2 * ⟪y - x₀, v⟫ * s) (2 * ⟪y - x₀, v⟫) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * ⟪y - x₀, v⟫)
    have h2 : HasDerivAt (fun s : ℝ => ‖v‖ ^ 2 * s ^ 2) (‖v‖ ^ 2 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (‖v‖ ^ 2))
    have h : HasDerivAt (fun s : ℝ => ‖y - x₀‖ ^ 2 + 2 * ⟪y - x₀, v⟫ * s + ‖v‖ ^ 2 * s ^ 2)
        (0 + 2 * ⟪y - x₀, v⟫ + ‖v‖ ^ 2 * (2 * t)) t :=
      ((hasDerivAt_const t (‖y - x₀‖ ^ 2)).add h1).add h2
    simp only [hqdef]
    refine h.congr_deriv ?_
    ring
  -- along-the-line function `γ` and its two derivatives
  have hγ_eq : (fun s : ℝ => ψ (y + s • v)) = fun s : ℝ => φ (q s) := by
    funext s
    simp only [hψdef]
    rw [hq_eq s]
  -- via the outer function ψ
  have hval : ∀ t : ℝ,
      fderiv ℝ ψ (y + t • v) v = deriv φ (q t) * (2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t) := by
    intro t
    have e1 : HasDerivAt (fun s : ℝ => ψ (y + s • v)) (fderiv ℝ ψ (y + t • v) v) t :=
      HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => y + s • v) (x := t)
        (hψdiff (y + t • v)).hasFDerivAt (hL t)
    have e2 : HasDerivAt (fun s : ℝ => φ (q s))
        (deriv φ (q t) * (2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t)) t :=
      (hφdiff (q t)).hasDerivAt.comp t (hq_deriv t)
    rw [hγ_eq] at e1
    exact e1.unique e2
  -- `g z = fderiv ℝ ψ z v` is differentiable at `y`
  have hg_cd : ContDiff ℝ 1 (fun z : 𝔼 => fderiv ℝ ψ z v) :=
    (hψC.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ ∞ by norm_cast)).clm_apply contDiff_const
  have hg_diff : DifferentiableAt ℝ (fun z : 𝔼 => fderiv ℝ ψ z v) y :=
    (hg_cd.differentiable_one) y
  -- `dirDeriv2 = deriv along v of g`
  have hdir : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (y + t • v) v) (dirDeriv2 v ψ y) 0 := by
    have hpt : y = (fun s : ℝ => y + s • v) 0 := by simp
    have h := HasFDerivAt.comp_hasDerivAt_of_eq (f := fun s : ℝ => y + s • v) (x := 0)
      (hg_diff.hasFDerivAt) (hL 0) hpt
    simpa only [dirDeriv2, Function.comp_def] using h
  -- rewrite that function through `hval`
  have hdir' : HasDerivAt
      (fun t : ℝ => deriv φ (q t) * (2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t))
      (dirDeriv2 v ψ y) 0 := by
    have hfun : (fun t : ℝ => fderiv ℝ ψ (y + t • v) v)
        = fun t : ℝ => deriv φ (q t) * (2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t) := by
      funext t; exact hval t
    rwa [hfun] at hdir
  -- compute that derivative directly
  have hq0 : q 0 = ‖y - x₀‖ ^ 2 := by simp only [hqdef]; ring
  have hcomp : HasDerivAt (fun t : ℝ => deriv φ (q t))
      (deriv (deriv φ) (‖y - x₀‖ ^ 2) * (2 * ⟪y - x₀, v⟫)) 0 := by
    have hchain := (hφ'diff (q 0)).hasDerivAt.comp 0 (hq_deriv 0)
    rw [hq0] at hchain
    simpa [Function.comp_def] using hchain
  have hlin : HasDerivAt (fun t : ℝ => 2 * ⟪y - x₀, v⟫ + 2 * ‖v‖ ^ 2 * t) (2 * ‖v‖ ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * ‖v‖ ^ 2)).const_add
      (2 * ⟪y - x₀, v⟫)
  have hprod := hcomp.mul hlin
  -- identify the two computations
  have := hdir'.unique hprod
  rw [this]
  simp only [hq0]
  ring

/-- **The radial Laplacian profile.**  For `φ ∈ C^∞` and the radial test `ψ(y) = φ(‖y − x₀‖²)`,
  `Δψ(y) = 4 ‖y − x₀‖² · φ''(‖y−x₀‖²) + 2 d · φ'(‖y−x₀‖²)`.

Obtained by summing `dirDeriv2_radial` over the standard orthonormal basis and using Parseval
`∑ᵢ ⟪y−x₀, eᵢ⟫² = ‖y−x₀‖²` together with `∑ᵢ ‖eᵢ‖² = d`. -/
theorem laplacian_radial {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x₀ y : 𝔼) :
    Δ (fun z => φ (‖z - x₀‖ ^ 2)) y
      = 4 * ‖y - x₀‖ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2)
        + 2 * (d : ℝ) * deriv φ (‖y - x₀‖ ^ 2) := by
  set ψ : 𝔼 → ℝ := fun z => φ (‖z - x₀‖ ^ 2) with hψdef
  have hqsmooth : ContDiff ℝ ∞ (fun z : 𝔼 => ‖z - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hψC2 : ContDiff ℝ 2 ψ := (hφ.comp hqsmooth).of_le (by norm_cast)
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis ψ b]
  have hterm : ∀ i : Fin d, iteratedFDeriv ℝ 2 ψ y ![b i, b i]
      = 4 * ⟪y - x₀, b i⟫ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2)
        + 2 * ‖b i‖ ^ 2 * deriv φ (‖y - x₀‖ ^ 2) := by
    intro i
    rw [iteratedFDeriv_two_eq_dirDeriv2 hψC2 y (b i)]
    exact dirDeriv2_radial hφ x₀ y (b i)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hsum1 : ∑ i : Fin d, 4 * ⟪y - x₀, b i⟫ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2)
      = 4 * ‖y - x₀‖ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2) := by
    have : ∑ i : Fin d, 4 * ⟪y - x₀, b i⟫ ^ 2 * deriv (deriv φ) (‖y - x₀‖ ^ 2)
        = (4 * deriv (deriv φ) (‖y - x₀‖ ^ 2)) * ∑ i : Fin d, ⟪y - x₀, b i⟫ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, b.sum_sq_inner_left (y - x₀)]; ring
  have hsum2 : ∑ i : Fin d, 2 * ‖b i‖ ^ 2 * deriv φ (‖y - x₀‖ ^ 2)
      = 2 * (d : ℝ) * deriv φ (‖y - x₀‖ ^ 2) := by
    have hnorm : ∀ i : Fin d, ‖b i‖ ^ 2 = 1 := by
      intro i; rw [hb]; rw [(EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i]; norm_num
    simp_rw [hnorm, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum1, hsum2]

/-! ### The one-dimensional radial profiles -/

/-- The radial profile `p(r) = φ(r²)` of `ψ(y) = φ(‖y − x₀‖²)` has derivative
`p'(r) = 2 r · φ'(r²)`. -/
theorem deriv_radialProfile {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    deriv (fun s : ℝ => φ (s ^ 2)) r = 2 * r * deriv φ (r ^ 2) := by
  have hφdiff : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h : HasDerivAt (fun s : ℝ => φ (s ^ 2)) (deriv φ (r ^ 2) * (2 * r)) r := by
    simpa [Function.comp_def] using (hφdiff (r ^ 2)).hasDerivAt.comp r hsq
  rw [h.deriv]; ring

/-- **The load-bearing 1-D radial identity** `(r^{d−1} p'(r))' = r^{d−1} m(r)`, in IBP-ready
`HasDerivAt` form.  Here `p(r) = φ(r²)` is the radial profile of `ψ(y) = φ(‖y − x₀‖²)` (so
`p'(r) = 2 r φ'(r²)`, cf. `deriv_radialProfile`) and
  `m(r) = 4 r² φ''(r²) + 2 d φ'(r²)`

is the radial profile of `Δψ` (cf. `laplacian_radial`, evaluated at `‖y − x₀‖ = r`).  This is the
total-derivative structure the flux-vanishing assembly integrates by parts against in the radial
variable.  Pure one-dimensional calculus (no inner-product geometry). -/
theorem hasDerivAt_weighted_radialProfile {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (d - 1) * (2 * s * deriv φ (s ^ 2)))
      (r ^ (d - 1) *
        (4 * r ^ 2 * deriv (deriv φ) (r ^ 2) + 2 * (d : ℝ) * deriv φ (r ^ 2))) r := by
  have hφ'diff : Differentiable ℝ (deriv φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).1
  have hpow : HasDerivAt (fun s : ℝ => s ^ (d - 1)) (↑(d - 1) * r ^ (d - 1 - 1)) r :=
    hasDerivAt_pow (d - 1) r
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h_dphi_sq : HasDerivAt (fun s : ℝ => deriv φ (s ^ 2))
      (deriv (deriv φ) (r ^ 2) * (2 * r)) r := by
    simpa [Function.comp_def] using (hφ'diff (r ^ 2)).hasDerivAt.comp r hsq
  have h_2s : HasDerivAt (fun s : ℝ => 2 * s) 2 r := by simpa using (hasDerivAt_id r).const_mul 2
  have hmul : HasDerivAt (fun s : ℝ => s ^ (d - 1) * (2 * s * deriv φ (s ^ 2)))
      (↑(d - 1) * r ^ (d - 1 - 1) * (2 * r * deriv φ (r ^ 2)) +
        r ^ (d - 1) * (2 * deriv φ (r ^ 2) + 2 * r * (deriv (deriv φ) (r ^ 2) * (2 * r)))) r :=
    hpow.mul (h_2s.mul h_dphi_sq)
  refine hmul.congr_deriv ?_
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos hd).symm⟩
  simp only [Nat.add_sub_cancel]
  rcases k with _ | k' <;> push_cast <;> ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== cutoff localization ====
open scoped Real Topology Laplacian
open MeasureTheory InnerProductSpace Metric Filter

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- The Laplacian of the zero function is zero. -/
private theorem laplacian_zero_fun :
    Δ (0 : EuclideanSpace ℝ (Fin d) → ℝ) = 0 := by
  rw [show (0 : EuclideanSpace ℝ (Fin d) → ℝ) = fun _ => (0 : ℝ) from rfl]
  funext z
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_fun_zero]
  simp

/-- The support of `Δψ` is contained in the topological support of `ψ`: if `ψ` vanishes near `y`,
so does its Laplacian. -/
private theorem support_laplacian_subset {ψ : EuclideanSpace ℝ (Fin d) → ℝ} :
    Function.support (Δ ψ) ⊆ tsupport ψ := by
  intro y hy
  by_contra hy'
  rw [Function.mem_support] at hy
  refine hy ?_
  have hev : ψ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
  have := (laplacian_congr_nhds hev).eq_of_nhds
  rw [this, laplacian_zero_fun]; rfl

/-- **Cutoff localization of the weak harmonic identity.**  If `u` is harmonic on the open ball
`Metric.ball x R` and `ψ ∈ C²` has compact support inside a strictly smaller ball
`tsupport ψ ⊆ Metric.ball x r` (`0 < r < R`), then `∫ u · Δψ = 0`.

This is the local version of `integral_mul_laplacian_eq_zero_of_harmonic`: `u` need only be harmonic
near the closed ball, not on all of space. -/
theorem integral_mul_laplacian_eq_zero_of_harmonicOn
    {u ψ : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOnNhd u (Metric.ball x R))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Metric.ball x r) :
    ∫ y, u y * Δ ψ y = 0 := by
  classical
  -- The cutoff bump: `= 1` on `closedBall x r`, `tsupport = closedBall x ((r+R)/2) ⊆ ball x R`.
  set χ : ContDiffBump x := ⟨r, (r + R) / 2, hr, by linarith⟩ with hχ
  -- `tsupport χ ⊆ ball x R`.
  have htsχ : tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ Metric.ball x R := by
    rw [χ.tsupport_eq]
    intro z hz
    rw [mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc dist z x ≤ (r + R) / 2 := hz
      _ < R := by linarith
  -- The cutoffed function `w = χ·u`.
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun y => χ y * u y with hw
  -- `w` is globally `C²`.
  have hw_cd : ContDiff ℝ 2 w := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    · -- inside `tsupport χ ⊆ ball x R`: both factors are `C²` at `y`.
      have hyR : y ∈ Metric.ball x R := htsχ hy
      have hχcd : ContDiffAt ℝ 2 (χ : EuclideanSpace ℝ (Fin d) → ℝ) y :=
        χ.contDiff.contDiffAt
      have hucd : ContDiffAt ℝ 2 u y := (hu y hyR).1
      exact hχcd.mul hucd
    · -- off `tsupport χ`: `w` vanishes on a neighbourhood, hence `C²`.
      have hev : w =ᶠ[𝓝 y] 0 := by
        have hχ0 : (χ : EuclideanSpace ℝ (Fin d) → ℝ) =ᶠ[𝓝 y] 0 :=
          notMem_tsupport_iff_eventuallyEq.mp hy
        filter_upwards [hχ0] with z hz
        simp [hw, hz]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  -- Step: replace `u` by `w` under the integral (they agree wherever `Δψ ≠ 0`).
  have hstep_a : (fun y => u y * Δ ψ y) = fun y => w y * Δ ψ y := by
    funext y
    by_cases hy : Δ ψ y = 0
    · simp [hy]
    · -- `Δψ y ≠ 0 ⟹ y ∈ tsupport ψ ⊆ ball x r ⊆ closedBall x r ⟹ χ y = 1`.
      have hyts : y ∈ tsupport ψ := support_laplacian_subset (Function.mem_support.mpr hy)
      have hyr : y ∈ Metric.ball x r := hsupp hyts
      have hycb : y ∈ closedBall x r := ball_subset_closedBall hyr
      have hχ1 : (χ : EuclideanSpace ℝ (Fin d) → ℝ) y = 1 := χ.one_of_mem_closedBall hycb
      simp only [hw, hχ1, one_mul]
  -- Step (b): global Green identity applied to `w`.
  have hstep_b : (∫ y, w y * Δ ψ y) = ∫ y, Δ w y * ψ y :=
    integral_mul_laplacian_eq_integral_laplacian_mul hw_cd hψ hψc
  -- Step (c): `Δw·ψ ≡ 0` because `Δw = Δu = 0` on `ball x r ⊇ tsupport ψ`.
  have hstep_c : (∫ y, Δ w y * ψ y) = 0 := by
    have hzero : (fun y => Δ w y * ψ y) = 0 := by
      funext y
      by_cases hy : ψ y = 0
      · simp [hy]
      · -- `ψ y ≠ 0 ⟹ y ∈ tsupport ψ ⊆ ball x r`; there `χ ≡ 1`, so `Δw = Δu = 0`.
        have hyts : y ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hy)
        have hyr : y ∈ Metric.ball x r := hsupp hyts
        have hyR : y ∈ Metric.ball x R := (ball_subset_ball hrR.le) hyr
        -- `w =ᶠ[𝓝 y] u` since `χ =ᶠ[𝓝 y] 1` on the open ball `ball x r`.
        have hχ1 : (χ : EuclideanSpace ℝ (Fin d) → ℝ) =ᶠ[𝓝 y] 1 :=
          χ.eventuallyEq_one_of_mem_ball hyr
        have hwu : w =ᶠ[𝓝 y] u := by
          filter_upwards [hχ1] with z hz
          simp [hw, hz]
        have hΔeq : Δ w y = Δ u y := (laplacian_congr_nhds hwu).eq_of_nhds
        have hΔu : Δ u y = 0 := by
          have := (hu y hyR).2.eq_of_nhds
          simpa using this
        simp only [Pi.zero_apply, hΔeq, hΔu, zero_mul]
    rw [hzero]; simp
  rw [hstep_a, hstep_b, hstep_c]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

