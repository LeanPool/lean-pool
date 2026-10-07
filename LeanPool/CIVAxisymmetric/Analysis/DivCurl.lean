/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The elliptic identity `‖∇v‖² = ‖curl v‖² + ‖div v‖²`

This file proves the elliptic identity `eq:aniso:closure:elliptic` of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803: for a smooth, compactly supported vector field
`v : Vec3 → Vec3`, the gradient energy `∫ ∑ᵢⱼ (∂ⱼvᵢ)²` splits as `∫ ‖curl v‖²` plus
`∫ (div v)²`.

The proof expands both sides pointwise: `∑ᵢ (curl v)ᵢ²` equals `∑ᵢⱼ (∂ⱼvᵢ)² - ∑ᵢⱼ ∂ⱼvᵢ ∂ᵢvⱼ`,
so the identity reduces to showing `∫ ∑ᵢⱼ ∂ⱼvᵢ ∂ᵢvⱼ = ∫ (∑ⱼ ∂ⱼvⱼ)²`. This cross-term identity
is proved by two integrations by parts (moving `∂ⱼ` off `vᵢ` and `∂ᵢ` back onto `vⱼ`), with the
symmetry of the second derivative used in between to commute the mixed partial `∂ⱼ∂ᵢvⱼ` to
`∂ᵢ∂ⱼvⱼ`.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- The curl of a time-independent vector field `v : Vec3 → Vec3`, with components
`(∂₂v₃ - ∂₃v₂, ∂₃v₁ - ∂₁v₃, ∂₁v₂ - ∂₂v₁)`. -/
@[expose] def curlVec (v : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  ![fderiv ℝ (fun y : Vec3 => v y 2) x (basisVec 1)
      - fderiv ℝ (fun y : Vec3 => v y 1) x (basisVec 2),
    fderiv ℝ (fun y : Vec3 => v y 0) x (basisVec 2)
      - fderiv ℝ (fun y : Vec3 => v y 2) x (basisVec 0),
    fderiv ℝ (fun y : Vec3 => v y 1) x (basisVec 0)
      - fderiv ℝ (fun y : Vec3 => v y 0) x (basisVec 1)]

/-- On a time slice, `curlVec` agrees with the spatial part of the `curlComp`. -/
theorem curlVec_apply_eq_curlComp (v : Vec3 → Vec3) (x : Vec3) (t : ℝ) :
    curlVec v x = ![curlComp (fun z : ParabolicPoint => v z.1) 0 (x, t),
      curlComp (fun z : ParabolicPoint => v z.1) 1 (x, t),
      curlComp (fun z : ParabolicPoint => v z.1) 2 (x, t)] := by
  ext i
  fin_cases i <;>
    simp [curlVec, curlComp, spatialPartial, basisVec]

/-! ## Regularity helpers -/

/-- The `i`-th component of a smooth vector field is smooth. -/
lemma contDiff_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => v x i) :=
  (contDiff_pi.mp hv) i

/-- The derivative of the `i`-th component of a smooth vector field in a fixed direction
is again smooth. -/
lemma contDiff_fderiv_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun x : Vec3 => v x i)) :=
    (contDiff_comp v hv i).fderiv_right (by simp)
  exact h_fderiv.clm_apply contDiff_const

/-- `v · i` is continuous. -/
lemma continuous_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin 3) :
    Continuous (fun x : Vec3 => v x i) :=
  (contDiff_comp v hv i).continuous

/-- `fderiv ℝ (v · i) · (basisVec j)` is continuous for a smooth vector field. -/
lemma continuous_fderiv_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) :
    Continuous (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) := by
  have h_cont : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ (fun y : Vec3 => v y i) p.1) p.2) :=
    (contDiff_comp v hv i).continuous_fderiv_apply (by simp)
  exact h_cont.comp (continuous_id.prodMk continuous_const)

/-- The second derivative `∂ₖ∂ⱼvᵢ` is continuous for a smooth vector field. -/
lemma continuous_fderiv_fderiv_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (i j k : Fin 3) :
    Continuous (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x
        (basisVec k)) := by
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec
    j)) :=
    contDiff_fderiv_comp v hv i j
  have h_cont : Continuous (fun p : Vec3 × Vec3 =>
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) p.1) p.2) :=
    hCD.continuous_fderiv_apply (by simp)
  exact h_cont.comp (continuous_id.prodMk continuous_const)

/-- `v · i` has compact support. -/
lemma hasCompactSupport_comp (v : Vec3 → Vec3) (hsupp : HasCompactSupport v) (i : Fin 3) :
    HasCompactSupport (fun x : Vec3 => v x i) :=
  hsupp.comp_left (g := fun w : Vec3 => w i) (by simp)

/-- `fderiv ℝ (v · i) · (basisVec j)` has compact support. -/
lemma hasCompactSupport_fderiv_comp (v : Vec3 → Vec3) (hsupp : HasCompactSupport v)
    (i j : Fin 3) :
    HasCompactSupport (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) :=
  (hasCompactSupport_comp v hsupp i).fderiv_apply (𝕜 := ℝ) (basisVec j)

/-- The second derivative `∂ₖ∂ⱼvᵢ` has compact support. -/
lemma hasCompactSupport_fderiv_fderiv_comp (v : Vec3 → Vec3) (hsupp : HasCompactSupport v)
    (i j k : Fin 3) :
    HasCompactSupport (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x
        (basisVec k)) :=
  (hasCompactSupport_fderiv_comp v hsupp i j).fderiv_apply (𝕜 := ℝ) (basisVec k)

/-- `v · i` is differentiable everywhere. -/
lemma differentiableAt_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin 3)
    (x : Vec3) : DifferentiableAt ℝ (fun y : Vec3 => v y i) x :=
  (contDiff_comp v hv i).differentiable (by simp) x

/-- `fderiv ℝ (v · i) · (basisVec j)` is differentiable everywhere. -/
lemma differentiableAt_fderiv_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (i j : Fin 3) (x : Vec3) :
    DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x :=
  (contDiff_fderiv_comp v hv i j).differentiable (by simp) x

/-- A product of two continuous functions, one of them compactly supported, is integrable. -/
lemma integrable_mul_of_continuous_of_hasCompactSupport {f g : Vec3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hsupp : HasCompactSupport f) :
    Integrable (fun x : Vec3 => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport hsupp.mul_right

/-- `(∂ⱼvᵢ)²` is integrable. -/
lemma integrable_sq_fderiv_comp (v : Vec3 → Vec3) (hsupp : HasCompactSupport v)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) :
    Integrable (fun x : Vec3 => (fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) ^ 2) := by
  have h := integrable_mul_of_continuous_of_hasCompactSupport
    (continuous_fderiv_comp v hv i j) (continuous_fderiv_comp v hv i j)
    (hasCompactSupport_fderiv_comp v hsupp i j)
  simpa [sq] using h

/-- Pushing a finite double integral of a sum inside, or pulling it back out. -/
lemma integral_sum_sum_eq (f : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hf : ∀ i j : Fin 3, Integrable (f i j)) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, f i j x
      = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, f i j x := by
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hf
    i j))]
  exact Finset.sum_congr rfl (fun i _ => integral_finsetSum Finset.univ (fun j _ => hf i j))

/-! ## Symmetry of the second derivative -/

/-- Mixed partial derivatives of a smooth scalar function on `Vec3` commute. -/
lemma fderiv_fderiv_comp_symm (G : Vec3 → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (a b : Fin 3)
    (x : Vec3) :
    fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec a)) x (basisVec b)
      = fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec b)) x (basisVec a) := by
  have hf : ∀ y : Vec3, HasFDerivAt G (fderiv ℝ G y) y :=
    fun y => (hG.differentiable (by simp) y).hasFDerivAt
  have h_fderiv_cont : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hx' : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    (h_fderiv_cont.differentiable (by simp) x).hasFDerivAt
  have h_symm := second_derivative_symmetric hf hx' (basisVec a) (basisVec b)
  have h_diff : DifferentiableAt ℝ (fderiv ℝ G) x := hx'.differentiableAt
  have eq_a : fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec a)) x
      = (fderiv ℝ (fderiv ℝ G) x).flip (basisVec a) := by
    have := fderiv_clm_apply h_diff (differentiableAt_const (basisVec a))
    simpa [fderiv_const] using this
  have eq_b : fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec b)) x
      = (fderiv ℝ (fderiv ℝ G) x).flip (basisVec b) := by
    have := fderiv_clm_apply h_diff (differentiableAt_const (basisVec b))
    simpa [fderiv_const] using this
  rw [eq_a, eq_b]
  exact h_symm.symm

/-! ## The cross-term identity -/

/-- For a compactly supported smooth vector field, `∫ ∂ⱼvᵢ ∂ᵢvⱼ = ∫ ∂ᵢvᵢ ∂ⱼvⱼ`. This is the
key cancellation lemma for the elliptic identity: two integrations by parts, moving `∂ⱼ` off
`vᵢ` and `∂ᵢ` back onto `vⱼ`, with the symmetry of the second derivative used in between to
commute `∂ⱼ∂ᵢvⱼ` to `∂ᵢ∂ⱼvⱼ`. -/
lemma integral_fderiv_mul_fderiv_symm (v : Vec3 → Vec3) (hsupp : HasCompactSupport v)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) :
    ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)
      = ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
          fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) := by
  -- Step 1: integrate by parts in direction `basisVec j`, moving `∂ⱼ` off `v · i`.
  have step1 : ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i) *
        fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)
      = - ∫ x : Vec3, fderiv ℝ
              (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec i)) x (basisVec j)
            * v x i := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_fderiv_comp v hv j i j) (continuous_comp v hv i)
        (hasCompactSupport_fderiv_fderiv_comp v hsupp j i j)
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_comp v hv j i) (continuous_fderiv_comp v hv i j)
        (hasCompactSupport_fderiv_comp v hsupp j i)
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_comp v hv j i) (continuous_comp v hv i)
        (hasCompactSupport_fderiv_comp v hsupp j i)
    · exact fun x _ => differentiableAt_fderiv_comp v hv j i x
    · exact fun x _ => differentiableAt_comp v hv i x
  -- Step 2: integrate by parts in direction `basisVec i`, moving `∂ᵢ` back onto `v · j`.
  have step2 : ∫ x : Vec3, v x i *
        fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec i)
      = - ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
          fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_comp v hv i i) (continuous_fderiv_comp v hv j j)
        (hasCompactSupport_fderiv_comp v hsupp i i)
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_comp v hv i) (continuous_fderiv_fderiv_comp v hv j j i)
        (hasCompactSupport_comp v hsupp i)
    · exact integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_comp v hv i) (continuous_fderiv_comp v hv j j)
        (hasCompactSupport_comp v hsupp i)
    · exact fun x _ => differentiableAt_comp v hv i x
    · exact fun x _ => differentiableAt_fderiv_comp v hv j j x
  have h_symm_int : ∫ x : Vec3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec i)) x (basisVec j) * v x i
      = ∫ x : Vec3, fderiv ℝ
          (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec i)
          * v x i := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [fderiv_fderiv_comp_symm (fun y : Vec3 => v y j) (contDiff_comp v hv j) i j x]
  calc
    ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)
        = ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i) *
            fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_)); ring
    _ = - ∫ x : Vec3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec i)) x (basisVec j)
          * v x i := step1
    _ = - ∫ x : Vec3, fderiv ℝ
            (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec i)
          * v x i := by rw [h_symm_int]
    _ = - ∫ x : Vec3, v x i *
            fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
              (basisVec i) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_)); ring
    _ = - - ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
            fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) := by rw [step2]
    _ = ∫ x : Vec3, fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
          fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) := by rw [neg_neg]

/-- The double-sum cross-term identity: `∫ ∑ᵢⱼ ∂ⱼvᵢ ∂ᵢvⱼ = ∫ (∑ⱼ ∂ⱼvⱼ)²`. -/
lemma integral_cross_term_eq_sq_div (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
          fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)
      = ∫ x : Vec3, (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)) ^ 2 := by
  have hint : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)) := fun i j =>
    integrable_mul_of_continuous_of_hasCompactSupport
      (continuous_fderiv_comp v hv i j) (continuous_fderiv_comp v hv j i)
      (hasCompactSupport_fderiv_comp v hsupp i j)
  have hint2 : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
      fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)) := fun i j =>
    integrable_mul_of_continuous_of_hasCompactSupport
      (continuous_fderiv_comp v hv i i) (continuous_fderiv_comp v hv j j)
      (hasCompactSupport_fderiv_comp v hsupp i i)
  calc
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
          fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)
        = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
            fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
              fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i) :=
      integral_sum_sum_eq (fun i j x => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)) hint
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
          fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
            fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) :=
      Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => integral_fderiv_mul_fderiv_symm v hsupp hv i j))
    _ = ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
            fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) :=
      (integral_sum_sum_eq (fun i j x => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec i) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)) hint2).symm
    _ = ∫ x : Vec3, (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Fin.sum_univ_three]
      ring

/-! ## The elliptic identity -/

/-- The elliptic identity `‖∇v‖² = ‖curl v‖² + ‖div v‖²` for a smooth compactly supported
vector field on `ℝ³`. -/
theorem integral_sq_fderiv_eq_curl_add_div (v : Vec3 → Vec3)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hsupp : HasCompactSupport v) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + ∫ x : Vec3, (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j)) ^ 2 := by
  have hpt : ∀ x : Vec3, ∑ i : Fin 3, (curlVec v x i) ^ 2
      = (∑ i : Fin 3, ∑ j : Fin 3, (fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) ^ 2)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
              fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i) := by
    intro x
    simp only [curlVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hgrad_integrable : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) ^ 2) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_sq_fderiv_comp v hsupp hv i j))
  have hcross_integrable : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
        fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i)) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_comp v hv i j) (continuous_fderiv_comp v hv j i)
        (hasCompactSupport_fderiv_comp v hsupp i j)))
  have hcurl_int : ∫ x : Vec3, ∑ i : Fin 3, (curlVec v x i) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) ^ 2)
        - ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j) *
              fderiv ℝ (fun y : Vec3 => v y j) x (basisVec i) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_sub hgrad_integrable hcross_integrable
  rw [hcurl_int, integral_cross_term_eq_sq_div v hv hsupp]
  ring

end CIV
