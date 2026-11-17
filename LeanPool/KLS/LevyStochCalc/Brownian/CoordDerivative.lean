/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.TaylorTwoVector
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives on `Fin n → ℝ`

A continuous linear functional on `Fin n → ℝ` is determined by its values on the standard basis
vectors `Pi.single p 1`, so the first- and second-order terms of a Taylor expansion split into
partial derivatives. The bounds and Lipschitz constants of those scalar functions come from the
operator norms of the Fréchet derivatives.

## Main statements

* `LevyStochCalc.clm_apply_pi` — expansion of a continuous linear map on `Fin n → ℝ`.
* `LevyStochCalc.coordDeriv`, `LevyStochCalc.coordDeriv₂` — the partial derivatives.
* `LevyStochCalc.apply_eq_sum_coordDeriv`, `LevyStochCalc.apply₂_eq_sum_coordDeriv₂` — the
  first- and second-order terms in coordinates.
* `LevyStochCalc.abs_coordDeriv_sub_le` — the Lipschitz bound of a partial derivative, from
  the bound on the second derivative.
-/

@[expose] public section

namespace LevyStochCalc

open ContinuousLinearMap

variable {n : ℕ}

section Expansion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map on `Fin n → ℝ` is the sum of its values on the standard basis,
weighted by the coordinates. -/
theorem clm_apply_pi (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ p, v p • L (Pi.single p 1) := by
  have hsingle : ∀ p : Fin n, (Pi.single p (v p) : Fin n → ℝ) = v p • Pi.single p (1 : ℝ) := by
    intro p
    rw [← Pi.single_smul']
    simp
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [hsingle p, map_smul]

/-- The scalar form of `clm_apply_pi`. -/
theorem clm_apply_pi_real (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ p, v p * L (Pi.single p 1) := by
  simpa [smul_eq_mul] using clm_apply_pi L v

end Expansion

section Coord

variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}

/-- The `p`-th partial derivative carried by a Fréchet derivative on `Fin n → ℝ`. -/
noncomputable def coordDeriv (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (p : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  f' x (Pi.single p 1)

/-- The `(p, q)` second partial derivative carried by a second Fréchet derivative on
`Fin n → ℝ`. -/
noncomputable def coordDeriv₂ (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (p q : Fin n) (x : Fin n → ℝ) : ℝ :=
  f'' x (Pi.single p 1) (Pi.single q 1)

/-- The first-order term of a Taylor expansion in coordinates. -/
theorem apply_eq_sum_coordDeriv (x v : Fin n → ℝ) :
    f' x v = ∑ p, v p * coordDeriv f' p x :=
  clm_apply_pi_real (f' x) v

/-- The second-order term of a Taylor expansion in coordinates. -/
theorem apply₂_eq_sum_coordDeriv₂ (x v : Fin n → ℝ) :
    f'' x v v = ∑ p, ∑ q, v p * v q * coordDeriv₂ f'' p q x := by
  have houter : f'' x v = ∑ p, v p • f'' x (Pi.single p 1) := clm_apply_pi (f'' x) v
  rw [houter, _root_.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, clm_apply_pi_real (f'' x (Pi.single p 1)) v,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [coordDeriv₂]; ring

/-- A partial derivative is bounded by the operator norm of the Fréchet derivative. -/
theorem abs_coordDeriv_le {K₁ : ℝ} (h : ∀ x, ‖f' x‖ ≤ K₁) (p : Fin n) (x : Fin n → ℝ) :
    |coordDeriv f' p x| ≤ K₁ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  calc |coordDeriv f' p x| = ‖f' x (Pi.single p 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x).le_opNorm _
    _ = ‖f' x‖ := by rw [hnorm, mul_one]
    _ ≤ K₁ := h x

/-- A second partial derivative is bounded by the operator norm of the second Fréchet
derivative. -/
theorem abs_coordDeriv₂_le {K₂ : ℝ} (h : ∀ x, ‖f'' x‖ ≤ K₂) (p q : Fin n) (x : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x| ≤ K₂ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  calc |coordDeriv₂ f'' p q x| = ‖f'' x (Pi.single p 1) (Pi.single q 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖f'' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x).le_opNorm₂ _ _
    _ = ‖f'' x‖ := by rw [hnorm, hnormq, mul_one, mul_one]
    _ ≤ K₂ := h x

/-- **The mean value theorem for the first derivative.** A bound on the second Fréchet derivative
is a Lipschitz constant for the first. -/
theorem norm_fderiv_sub_le (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (h : ∀ z, ‖f'' z‖ ≤ K₂) (x y : Fin n → ℝ) : ‖f' x - f' y‖ ≤ K₂ * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f') (f' := f'') (s := Set.univ)
    (C := K₂) (fun z _ => (hf' z).hasFDerivWithinAt) (fun z _ => h z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)

/-- A partial derivative is Lipschitz with the second derivative's bound. -/
theorem abs_coordDeriv_sub_le (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (h : ∀ z, ‖f'' z‖ ≤ K₂) (p : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv f' p x - coordDeriv f' p y| ≤ K₂ * ‖x - y‖ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hsub : coordDeriv f' p x - coordDeriv f' p y = (f' x - f' y) (Pi.single p 1) := by
    simp [coordDeriv]
  calc |coordDeriv f' p x - coordDeriv f' p y| = ‖(f' x - f' y) (Pi.single p 1)‖ := by
        rw [hsub]; exact (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x - f' y‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x - f' y).le_opNorm _
    _ = ‖f' x - f' y‖ := by rw [hnorm, mul_one]
    _ ≤ K₂ * ‖x - y‖ := norm_fderiv_sub_le hf' h x y

/-- A vector of `Fin n → ℝ` is the sum of its coordinate multiples of the standard basis. -/
theorem sum_single_eq (x : Fin n → ℝ) : ∑ p, (x p) • (Pi.single p 1 : Fin n → ℝ) = x := by
  have h : ∀ p : Fin n, (x p) • (Pi.single p 1 : Fin n → ℝ) = Pi.single p (x p) := by
    intro p
    funext i
    by_cases hi : i = p
    · subst hi; simp
    · simp [hi]
  simp only [h]
  exact Finset.univ_sum_single x

/-- The operator norm of a functional on `Fin n → ℝ` is at most the sum of the absolute values of
its coordinates. -/
theorem norm_le_sum_abs_apply (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun p _ => abs_nonneg _) fun x => ?_
  have hx : A x = ∑ p, x p * A (Pi.single p 1) := by
    conv_lhs => rw [← sum_single_eq x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]; simp
  rw [Real.norm_eq_abs, hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul]
  have h1 : |x p| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x p
  calc |x p| * |A (Pi.single p 1)|
      ≤ ‖x‖ * |A (Pi.single p 1)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |A (Pi.single p 1)| * ‖x‖ := by ring

/-- The operator norm of a bilinear form on `Fin n → ℝ` is at most the sum of the absolute values
of its coordinates. -/
theorem norm_le_sum_abs_apply₂ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
  refine A.opNorm_le_bound₂ (Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => abs_nonneg _) fun x y => ?_
  have hx : A x y = ∑ p, x p * (A (Pi.single p 1) y) := by
    conv_lhs => rw [← sum_single_eq x]
    rw [map_sum]
    simp only [_root_.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]; simp
  have hy : ∀ p : Fin n, A (Pi.single p 1) y
      = ∑ q, y q * (A (Pi.single p 1) (Pi.single q 1)) := by
    intro p
    conv_lhs => rw [← sum_single_eq y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_smul]; simp
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hynn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  rw [Real.norm_eq_abs, hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      |x p * (A (Pi.single p 1) y)|
        ≤ ‖x‖ * ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
    intro p _
    rw [abs_mul, hy p]
    have h1 : |x p| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x p
    have h2 : |∑ q, y q * (A (Pi.single p 1) (Pi.single q 1))|
        ≤ ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      simpa [Real.norm_eq_abs] using norm_le_pi_norm y q
    calc |x p| * |∑ q, y q * (A (Pi.single p 1) (Pi.single q 1))|
        ≤ ‖x‖ * (‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)|) :=
          mul_le_mul h1 h2 (abs_nonneg _) hxnn
      _ = ‖x‖ * ‖y‖ * ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring

/-- A second partial derivative inherits an affine oscillation bound on the second derivative. -/
theorem abs_coordDeriv₂_sub_le_affine {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hsub : coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y
      = (f'' x - f'' y) (Pi.single p 1) (Pi.single q 1) := by simp [coordDeriv₂]
  calc |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y|
      = ‖(f'' x - f'' y) (Pi.single p 1) (Pi.single q 1)‖ := by
        rw [hsub]; exact (Real.norm_eq_abs _).symm
    _ ≤ ‖f'' x - f'' y‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x - f'' y).le_opNorm₂ _ _
    _ = ‖f'' x - f'' y‖ := by rw [hnorm, hnormq, mul_one, mul_one]
    _ ≤ A + K * ‖x - y‖ := h x y

/-- Continuity of a partial derivative. -/
theorem continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const

/-- Continuity of a second partial derivative. -/
theorem continuous_coordDeriv₂ (hf''c : Continuous f'') (p q : Fin n) :
    Continuous (coordDeriv₂ f'' p q) :=
  (hf''c.clm_apply continuous_const).clm_apply continuous_const

end Coord

end LevyStochCalc
