/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# HomCGFinalExtend

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The McShane extension of a Hölder field, with the sup bound preserved

## What this file supplies

The measurement named a second "absent analytic input": a smooth-test
approximation of a merely Hölder field on `□_m`, preserving both the sup bound
and the Hölder bound.  This file is its **first half**: the extension of a
`C^{0,α}` field from an arbitrary nonempty set `A` to all of `Vec d`, at the
SAME two constants.

The construction is McShane's, applied coordinatewise and then clamped:

```text
  φ(x)_i  =  clamp_{K_sup} ( inf_{y ∈ A} ( φ(y)_i + K_Höl ‖x - y‖^α ) ).
```

Three facts, in the ambient supremum metric of `Vec d`:

* `holderExtend_eq_of_mem` — `φ = φ` on `A` (the clamp is inert there because
  `|φ(x)_i| ≤ ‖φ(x)‖ ≤ K_sup`, and the infimum is attained at `y = x`);
* `norm_holderExtend_le` — `‖φ(x)‖ ≤ K_sup` **everywhere**, by construction;
* `holderSeminormBoundOn_univ_holderExtend` — `φ` is `α`-Hölder on all of
  `Vec d` at the same constant `K_Höl`.

The Hölder half needs `α ≤ 1` exactly once, for the subadditivity
`(a+b)^α ≤ a^α + b^α` (`Real.rpow_add_le_add_rpow`); the sup half needs nothing
beyond `0 ≤ K_sup`, because clamping is a `1`-Lipschitz retraction of `ℝ` onto
`[-K_sup, K_sup]`.

Nothing here is specific to a cube, to a fractional Sobolev carrier, or to the
homogenization lane: it is the pure extension statement.
-/

open HCPolySupport
open Algsuperdiff.Section4.Support

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Clamping to a symmetric interval -/

/-- The `1`-Lipschitz retraction of `ℝ` onto `[-B, B]`. -/
def clampAbs (B t : ℝ) : ℝ := max (-B) (min B t)

/-- The clamp lands in `[-B, B]`. -/
theorem abs_clampAbs_le {B : ℝ} (hB : 0 ≤ B) (t : ℝ) : |clampAbs B t| ≤ B := by
  rw [abs_le]
  refine ⟨le_max_left _ _, max_le (by linarith only [hB]) (min_le_left _ _)⟩

/-- The clamp is inert on `[-B, B]`. -/
theorem clampAbs_eq_self {B t : ℝ} (h : |t| ≤ B) : clampAbs B t = t := by
  rw [abs_le] at h
  rw [clampAbs, min_eq_right h.2, max_eq_right h.1]

/-- The clamp is `1`-Lipschitz. -/
theorem abs_clampAbs_sub_clampAbs_le (B t u : ℝ) :
    |clampAbs B t - clampAbs B u| ≤ |t - u| := by
  have h1 : |clampAbs B t - clampAbs B u| ≤ max |(-B) - (-B)| |min B t - min B u| :=
    abs_max_sub_max_le_max _ _ _ _
  have h2 : |min B t - min B u| ≤ max |B - B| |t - u| :=
    abs_min_sub_min_le_max _ _ _ _
  have h3 : |(-B) - (-B)| = 0 := by simp
  have h4 : |B - B| = 0 := by simp
  rw [h3, max_eq_right (abs_nonneg _)] at h1
  rw [h4, max_eq_right (abs_nonneg _)] at h2
  exact h1.trans h2

/-! ## 2. The McShane infimum of a scalar Hölder datum -/

/-- **McShane's infimum**, in the ambient supremum metric:
`m(x) = inf_{y ∈ A} (f(y) + K‖x - y‖^α)`. -/
def mcShaneInf (A : Set (Vec d)) (K alpha : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ⨅ y : A, (f (y : Vec d) + K * ‖x - (y : Vec d)‖ ^ alpha)

/-- The McShane family is bounded below by `-B` whenever `|f| ≤ B` on `A`. -/
private theorem bddBelow_mcShane {A : Set (Vec d)} {K alpha B : ℝ} {f : Vec d → ℝ}
    (hK : 0 ≤ K) (hf : ∀ y ∈ A, |f y| ≤ B) (x : Vec d) :
    BddBelow (Set.range fun y : A => f (y : Vec d) + K * ‖x - (y : Vec d)‖ ^ alpha) := by
  refine ⟨-B, ?_⟩
  rintro z ⟨y, rfl⟩
  have h1 : -B ≤ f (y : Vec d) := neg_le_of_abs_le (hf (y : Vec d) y.2)
  have h2 : 0 ≤ K * ‖x - (y : Vec d)‖ ^ alpha :=
    mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) alpha)
  linarith only [h1, h2]

/-- The infimum is below every member of the family. -/
theorem mcShaneInf_le {A : Set (Vec d)} {K alpha B : ℝ} {f : Vec d → ℝ}
    (hK : 0 ≤ K) (hf : ∀ y ∈ A, |f y| ≤ B) (x : Vec d) {y : Vec d} (hy : y ∈ A) :
    mcShaneInf A K alpha f x ≤ f y + K * ‖x - y‖ ^ alpha :=
  ciInf_le (bddBelow_mcShane hK hf x) (⟨y, hy⟩ : A)

/-- A uniform lower bound on the family bounds the infimum. -/
theorem le_mcShaneInf {A : Set (Vec d)} {K alpha c : ℝ} {f : Vec d → ℝ}
    (hA : A.Nonempty) (x : Vec d)
    (h : ∀ y ∈ A, c ≤ f y + K * ‖x - y‖ ^ alpha) :
    c ≤ mcShaneInf A K alpha f x := by
  have : Nonempty (A : Type _) := hA.to_subtype
  exact le_ciInf fun y => h (y : Vec d) y.2

/-- **The extension is an extension**: on `A` the McShane infimum returns `f`. -/
theorem mcShaneInf_eq_of_mem {A : Set (Vec d)} {K alpha B : ℝ} {f : Vec d → ℝ}
    (hK : 0 ≤ K) (halpha : alpha ≠ 0) (hf : ∀ y ∈ A, |f y| ≤ B)
    (hhol : ∀ y ∈ A, ∀ z ∈ A, |f y - f z| ≤ K * ‖y - z‖ ^ alpha)
    {x : Vec d} (hx : x ∈ A) : mcShaneInf A K alpha f x = f x := by
  refine le_antisymm ?_ ?_
  · have h := mcShaneInf_le (alpha := alpha) hK hf x hx
    rwa [sub_self, norm_zero, Real.zero_rpow halpha, mul_zero, add_zero] at h
  · refine le_mcShaneInf ⟨x, hx⟩ x ?_
    intro y hy
    have h : f x - f y ≤ K * ‖x - y‖ ^ alpha := (abs_le.mp (hhol x hx y hy)).2
    linarith only [h]

/-- One direction of the Hölder estimate for the McShane infimum. -/
private theorem mcShaneInf_sub_le {A : Set (Vec d)} {K alpha B : ℝ} {f : Vec d → ℝ}
    (hK : 0 ≤ K) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hA : A.Nonempty)
    (hf : ∀ y ∈ A, |f y| ≤ B) (x x' : Vec d) :
    mcShaneInf A K alpha f x - mcShaneInf A K alpha f x' ≤ K * ‖x - x'‖ ^ alpha := by
  have key : ∀ y ∈ A, mcShaneInf A K alpha f x - K * ‖x - x'‖ ^ alpha ≤
      f y + K * ‖x' - y‖ ^ alpha := by
    intro y hy
    have h1 := mcShaneInf_le (alpha := alpha) hK hf x hy
    have htri : ‖x - y‖ ≤ ‖x - x'‖ + ‖x' - y‖ := by
      calc ‖x - y‖ = ‖(x - x') + (x' - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖x - x'‖ + ‖x' - y‖ := norm_add_le _ _
    have h2 : ‖x - y‖ ^ alpha ≤ (‖x - x'‖ + ‖x' - y‖) ^ alpha :=
      Real.rpow_le_rpow (norm_nonneg _) htri ha0
    have h3 : (‖x - x'‖ + ‖x' - y‖) ^ alpha ≤ ‖x - x'‖ ^ alpha + ‖x' - y‖ ^ alpha :=
      Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) ha0 ha1
    have h4 : K * ‖x - y‖ ^ alpha ≤ K * (‖x - x'‖ ^ alpha + ‖x' - y‖ ^ alpha) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) hK
    have h5 : K * (‖x - x'‖ ^ alpha + ‖x' - y‖ ^ alpha) =
        K * ‖x - x'‖ ^ alpha + K * ‖x' - y‖ ^ alpha := by ring
    rw [h5] at h4
    linarith only [h1, h4]
  have hle : mcShaneInf A K alpha f x - K * ‖x - x'‖ ^ alpha ≤
      mcShaneInf A K alpha f x' := le_mcShaneInf hA x' key
  linarith only [hle]

/-- **The McShane infimum is `α`-Hölder at the same constant, on all of `Vec d`.** -/
theorem abs_mcShaneInf_sub_le {A : Set (Vec d)} {K alpha B : ℝ} {f : Vec d → ℝ}
    (hK : 0 ≤ K) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hA : A.Nonempty)
    (hf : ∀ y ∈ A, |f y| ≤ B) (x x' : Vec d) :
    |mcShaneInf A K alpha f x - mcShaneInf A K alpha f x'| ≤ K * ‖x - x'‖ ^ alpha := by
  have h1 := mcShaneInf_sub_le hK ha0 ha1 hA hf x x'
  have h2 := mcShaneInf_sub_le hK ha0 ha1 hA hf x' x
  rw [norm_sub_rev x' x] at h2
  rw [abs_sub_le_iff]
  exact ⟨h1, h2⟩

/-! ## 3. The coordinatewise extension of a vector field -/

/-- **The McShane extension of a Hölder vector field**, coordinatewise, clamped
to the sup bound. -/
def holderExtend (A : Set (Vec d)) (Ksup KHol alpha : ℝ) (phi : Vec d → Vec d) :
    Vec d → Vec d :=
  fun x i => clampAbs Ksup (mcShaneInf A KHol alpha (fun y => phi y i) x)

theorem holderExtend_apply (A : Set (Vec d)) (Ksup KHol alpha : ℝ)
    (phi : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    holderExtend A Ksup KHol alpha phi x i =
      clampAbs Ksup (mcShaneInf A KHol alpha (fun y => phi y i) x) := rfl

/-- The coordinate sup bound implied by the ambient supremum-norm bound. -/
private theorem abs_coord_le_of_sup {A : Set (Vec d)} {Ksup : ℝ} {phi : Vec d → Vec d}
    (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup) (i : Fin d) : ∀ y ∈ A, |phi y i| ≤ Ksup := by
  intro y hy
  have h : ‖phi y i‖ ≤ ‖phi y‖ := norm_le_pi_norm (phi y) i
  rw [Real.norm_eq_abs] at h
  exact h.trans (hsup y hy)

/-- The coordinate Hölder bound implied by the ambient supremum-norm bound. -/
private theorem abs_coord_sub_le_of_holder {A : Set (Vec d)} {alpha KHol : ℝ}
    {phi : Vec d → Vec d} (hhol : HolderSeminormBoundOn A alpha KHol phi) (i : Fin d) :
    ∀ y ∈ A, ∀ z ∈ A, |phi y i - phi z i| ≤ KHol * ‖y - z‖ ^ alpha := by
  intro y hy z hz
  have h : ‖(phi y - phi z) i‖ ≤ ‖phi y - phi z‖ := norm_le_pi_norm (phi y - phi z) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h
  exact h.trans (hhol y hy z hz)

/-- **`φ = φ` on `A`.** -/
theorem holderExtend_eq_of_mem {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (halpha : alpha ≠ 0)
    (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup)
    (hhol : HolderSeminormBoundOn A alpha KHol phi)
    {x : Vec d} (hx : x ∈ A) : holderExtend A Ksup KHol alpha phi x = phi x := by
  funext i
  show clampAbs Ksup (mcShaneInf A KHol alpha (fun y => phi y i) x) = phi x i
  rw [mcShaneInf_eq_of_mem hKHol halpha (abs_coord_le_of_sup hsup i)
    (abs_coord_sub_le_of_holder hhol i) hx]
  exact clampAbs_eq_self (abs_coord_le_of_sup hsup i x hx)

/-- **`‖φ‖ ≤ K_sup` everywhere.** -/
theorem norm_holderExtend_le {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKsup : 0 ≤ Ksup) (x : Vec d) :
    ‖holderExtend A Ksup KHol alpha phi x‖ ≤ Ksup := by
  refine (pi_norm_le_iff_of_nonneg hKsup).2 fun i => ?_
  rw [holderExtend_apply, Real.norm_eq_abs]
  exact abs_clampAbs_le hKsup _

/-- **`φ` is `α`-Hölder on all of `Vec d` at the constant `K_Höl`.** -/
theorem holderSeminormBoundOn_univ_holderExtend {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup) :
    HolderSeminormBoundOn Set.univ alpha KHol (holderExtend A Ksup KHol alpha phi) := by
  intro x _ y _
  have hrhs : (0 : ℝ) ≤ KHol * ‖x - y‖ ^ alpha :=
    mul_nonneg hKHol (Real.rpow_nonneg (norm_nonneg _) alpha)
  refine (pi_norm_le_iff_of_nonneg hrhs).2 fun i => ?_
  rw [Pi.sub_apply, holderExtend_apply, holderExtend_apply, Real.norm_eq_abs]
  refine (abs_clampAbs_sub_clampAbs_le _ _ _).trans ?_
  exact abs_mcShaneInf_sub_le hKHol ha0 ha1 hA (abs_coord_le_of_sup hsup i) x y

end

end Algsuperdiff.Section4.Provider.Homogenization
