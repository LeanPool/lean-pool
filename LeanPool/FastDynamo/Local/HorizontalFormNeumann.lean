/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalFormDelta
public import LeanPool.FastDynamo.Operator.AnalyticFredholm

/-!
# The Neumann series for a perturbed complex form

The proof of `prop:local-seed` in the paper reads

> The inverses `𝔸_{0,1}(z)^{-1} : V^* → V` are uniformly bounded on `Γ`.  Applying a Neumann
> series, we obtain, for `h^{1/4} + |δ-1|` sufficiently small,
> `sup_{z∈Γ} ‖𝔸_{h,δ}(z)^{-1} - 𝔸_{0,1}(z)^{-1}‖_{V^*→V} ≤ C(h^{1/4} + |δ-1|)`.

This module is the quantitative Neumann series behind that sentence, stated for an abstract
complex Hilbert space `V` and an abstract complex form.

Given a form `A₀ : V → V^*` with a two-sided inverse `T : V^* → V` of norm at most `B`, and a
perturbation `D : V → V^*` of norm at most `η` with `Bη < 1`, the composite `T D : V → V` has
norm `< 1`, so the *Neumann factor*

`S = 1 + T D : V → V`

is invertible in the Banach algebra `V →L[ℂ] V` by the geometric series.  Since `A₀ T = 1`,

`A₀ S = A₀ + A₀ T D = A₀ + D`,

so `A₀ + D` is invertible with inverse `S⁻¹ T`, and the two estimates of the paper are

`‖(A₀+D)^{-1}‖ ≤ B/(1-Bη)`,   `‖(A₀+D)^{-1} - T‖ ≤ B²η/(1-Bη)`.

Everything is phrased through the two definitions `complexFormOpNorm` (of
`FastDynamo/Local/HorizontalFormDelta.lean`) and `complexFormInvNorm` (introduced here) rather
than through `‖·‖`: instance search does not find `Norm (ComplexForm V)` or
`Norm (V^* →L[ℂ] V)` at the concrete horizontal form domain, a submodule of a `PiLp` of `Lp`
quotients, whereas it succeeds for a generic `V`.  The `V → V` operator norms that the Neumann
series itself uses *do* synthesise at the concrete domain, which is why the series is run in
`V →L[ℂ] V` and never in the antidual-valued operator space.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace HorizontalWeakForm

/-! ## The `V* → V` operator norm -/

section InvNorm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The `V* → V` operator norm of an inverse of a complex form, i.e. `‖T‖` for
`T : V^* →L[ℂ] V`.

As with `complexFormOpNorm`, it is introduced as a definition because instance search does
not find `Norm (ComplexAntiDual V →L[ℂ] V)` at the concrete form domain `H¹(ℝ²;ℂ²)`; stated
generically in `V` it elaborates once and instantiates without search.  This is the norm
appearing in the Neumann-series bound of the proof of `prop:local-seed`. -/
noncomputable def complexFormInvNorm (T : ComplexAntiDual V →L[ℂ] V) : ℝ :=
  ‖T‖

/-- The `V* → V` operator norm is nonnegative. -/
theorem complexFormInvNorm_nonneg (T : ComplexAntiDual V →L[ℂ] V) :
    0 ≤ complexFormInvNorm T :=
  norm_nonneg T

/-- Post-composing an inverse with an endomorphism of `V` multiplies the norms. -/
theorem complexFormInvNorm_comp_le (X : V →L[ℂ] V) (T : ComplexAntiDual V →L[ℂ] V) :
    complexFormInvNorm (X.comp T) ≤ ‖X‖ * complexFormInvNorm T :=
  ContinuousLinearMap.opNorm_comp_le X T

/-- Pre-composing an inverse with a complex form gives an endomorphism of `V` whose norm is
controlled by the two form norms.  This is the composite `T D` on which the Neumann series
runs. -/
theorem norm_comp_complexForm_le (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V) :
    ‖T.comp D‖ ≤ complexFormInvNorm T * complexFormOpNorm D :=
  ContinuousLinearMap.opNorm_comp_le T D

end InvNorm

/-! ## The Neumann factor -/

section Neumann

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The Neumann factor `S = 1 + A₀^{-1}(A - A₀) : V → V` of the Neumann series in the proof
of `prop:local-seed`. -/
def formNeumannFactor (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V) : V →L[ℂ] V :=
  1 + T.comp D

omit [CompleteSpace V] in
/-- Value of the Neumann factor. -/
@[simp] theorem formNeumannFactor_apply (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V)
    (b : V) : formNeumannFactor T D b = b + T (D b) :=
  rfl

/-- **The Neumann factor is invertible** once `‖A₀^{-1}(A-A₀)‖ < 1`; this is Mathlib's
geometric series in the Banach algebra `V →L[ℂ] V`. -/
theorem isInvertible_formNeumannFactor {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) : (formNeumannFactor T D).IsInvertible := by
  have hneg : ‖-(T.comp D)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(T.comp D)) := isUnit_one_sub_of_norm_lt_one hneg
  rw [sub_neg_eq_add] at hunit
  exact AnalyticFredholm.isUnit_iff_isInvertible.mp hunit

/-- The inverse of the Neumann factor, as a total function of the data. -/
def formNeumannFactorInv (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V) : V →L[ℂ] V :=
  (formNeumannFactor T D).inverse

/-- The Neumann factor undoes its inverse. -/
theorem formNeumannFactor_factorInv_apply {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) (b : V) :
    formNeumannFactor T D (formNeumannFactorInv T D b) = b :=
  (isInvertible_formNeumannFactor hlt).self_apply_inverse b

/-- The inverse undoes the Neumann factor. -/
theorem formNeumannFactorInv_factor_apply {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) (b : V) :
    formNeumannFactorInv T D (formNeumannFactor T D b) = b :=
  (isInvertible_formNeumannFactor hlt).inverse_apply_self b

/-- The algebraic Neumann identity `S⁻¹ = 1 - (T D) S⁻¹`. -/
theorem formNeumannFactorInv_eq {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) :
    formNeumannFactorInv T D = 1 - (T.comp D).comp (formNeumannFactorInv T D) := by
  refine ContinuousLinearMap.ext fun b => ?_
  have h := formNeumannFactor_factorInv_apply hlt b
  rw [formNeumannFactor_apply] at h
  have hb : formNeumannFactorInv T D b =
      b - T (D (formNeumannFactorInv T D b)) := by
    linear_combination (norm := module) h
  simpa using hb

/-- **The Neumann bound `‖S⁻¹‖ ≤ (1 - c)⁻¹`** for any bound `c < 1` on `‖T D‖`. -/
theorem norm_formNeumannFactorInv_le {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V}
    {c : ℝ} (hc : ‖T.comp D‖ ≤ c) (hc1 : c < 1) :
    ‖formNeumannFactorInv T D‖ ≤ (1 - c)⁻¹ := by
  have hlt : ‖T.comp D‖ < 1 := lt_of_le_of_lt hc hc1
  have hpos : 0 < 1 - c := by linarith
  have hone : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hu0 : 0 ≤ ‖formNeumannFactorInv T D‖ := norm_nonneg _
  have hcomp : ‖(T.comp D).comp (formNeumannFactorInv T D)‖ ≤
      ‖T.comp D‖ * ‖formNeumannFactorInv T D‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have htri : ‖formNeumannFactorInv T D‖ ≤
      ‖(1 : V →L[ℂ] V)‖ + ‖(T.comp D).comp (formNeumannFactorInv T D)‖ := by
    conv_lhs => rw [formNeumannFactorInv_eq hlt]
    exact norm_sub_le _ _
  have hkey : (1 - c) * ‖formNeumannFactorInv T D‖ ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hpos))
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul, mul_one] at hmul

/-- **The Neumann bound `‖S⁻¹ - 1‖ ≤ c(1 - c)⁻¹`** for any bound `c < 1` on `‖T D‖`. -/
theorem norm_formNeumannFactorInv_sub_one_le {T : ComplexAntiDual V →L[ℂ] V}
    {D : ComplexForm V} {c : ℝ} (hc : ‖T.comp D‖ ≤ c) (hc1 : c < 1) :
    ‖formNeumannFactorInv T D - 1‖ ≤ c * (1 - c)⁻¹ := by
  have hlt : ‖T.comp D‖ < 1 := lt_of_le_of_lt hc hc1
  have hc0 : 0 ≤ c := le_trans (norm_nonneg (T.comp D)) hc
  have heq : formNeumannFactorInv T D - 1 = -((T.comp D).comp (formNeumannFactorInv T D)) := by
    conv_lhs => rw [formNeumannFactorInv_eq hlt]
    abel
  rw [heq, norm_neg]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul hc (norm_formNeumannFactorInv_le hc hc1) (norm_nonneg _) hc0

/-! ## The Neumann inverse of the perturbed form -/

/-- The Neumann inverse `(A₀ + D)^{-1} = S^{-1}A₀^{-1} : V^* → V` of the proof of
`prop:local-seed`. -/
def formNeumannInverse (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V) :
    ComplexAntiDual V →L[ℂ] V :=
  (formNeumannFactorInv T D).comp T

omit [CompleteSpace V] in
/-- Value of the Neumann inverse. -/
@[simp] theorem formNeumannInverse_apply (T : ComplexAntiDual V →L[ℂ] V) (D : ComplexForm V)
    (g : ComplexAntiDual V) :
    formNeumannInverse T D g = formNeumannFactorInv T D (T g) :=
  rfl

omit [CompleteSpace V] in
/-- **The factorisation `A₀S = A₀ + D`** of the perturbed form, evaluated at a vector.  It uses
only that `A₀^{-1}` is a right inverse of `A₀`. -/
theorem formNeumannFactorisation_apply (A₀ : ComplexForm V) {T : ComplexAntiDual V →L[ℂ] V}
    (hAT : ∀ g : ComplexAntiDual V, A₀ (T g) = g) (D : ComplexForm V) (b : V) :
    A₀ (formNeumannFactor T D b) = (A₀ + D) b := by
  rw [formNeumannFactor_apply, map_add, hAT (D b), add_apply]

/-- **The Neumann inverse is a right inverse of `A₀ + D`.** -/
theorem formNeumannInverse_right_apply (A₀ : ComplexForm V) {T : ComplexAntiDual V →L[ℂ] V}
    (hAT : ∀ g : ComplexAntiDual V, A₀ (T g) = g) {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) (g : ComplexAntiDual V) :
    (A₀ + D) (formNeumannInverse T D g) = g := by
  have hfac := formNeumannFactorisation_apply A₀ hAT D (formNeumannFactorInv T D (T g))
  rw [formNeumannFactor_factorInv_apply hlt (T g)] at hfac
  rw [formNeumannInverse_apply, ← hfac, hAT]

/-- **The Neumann inverse is a left inverse of `A₀ + D`.** -/
theorem formNeumannInverse_left_apply (A₀ : ComplexForm V) {T : ComplexAntiDual V →L[ℂ] V}
    (hAT : ∀ g : ComplexAntiDual V, A₀ (T g) = g)
    (hTA : ∀ b : V, T (A₀ b) = b) {D : ComplexForm V}
    (hlt : ‖T.comp D‖ < 1) (b : V) :
    formNeumannInverse T D ((A₀ + D) b) = b := by
  have hfac := formNeumannFactorisation_apply A₀ hAT D b
  rw [formNeumannInverse_apply, ← hfac, hTA, formNeumannFactorInv_factor_apply hlt]

/-- The perturbed form is injective; this is the hypothesis the resolvent construction of
`FastDynamo/Local/HorizontalFormResolvent.lean` asks for. -/
theorem eq_zero_of_formNeumann_apply_eq_zero (A₀ : ComplexForm V)
    {T : ComplexAntiDual V →L[ℂ] V} (hAT : ∀ g : ComplexAntiDual V, A₀ (T g) = g)
    (hTA : ∀ b : V, T (A₀ b) = b) {D : ComplexForm V} (hlt : ‖T.comp D‖ < 1) {e : V}
    (he : (A₀ + D) e = 0) : e = 0 := by
  have h := formNeumannInverse_left_apply A₀ hAT hTA hlt e
  rw [he, map_zero] at h
  exact h.symm

/-! ## The quantitative form of the series -/

omit [CompleteSpace V] in
/-- `‖A₀^{-1}(A - A₀)‖ ≤ Bη` from the two form bounds. -/
theorem norm_comp_le_of_bounds {T : ComplexAntiDual V →L[ℂ] V} {D : ComplexForm V} {B eta : ℝ}
    (hB : complexFormInvNorm T ≤ B) (heta : complexFormOpNorm D ≤ eta) :
    ‖T.comp D‖ ≤ B * eta := by
  refine le_trans (norm_comp_complexForm_le T D) ?_
  exact mul_le_mul hB heta (complexFormOpNorm_nonneg D)
    (le_trans (complexFormInvNorm_nonneg T) hB)

end Neumann

end HorizontalWeakForm

end

end FastDynamo
