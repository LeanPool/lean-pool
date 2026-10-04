/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.InteriorCompactSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set


/-!
# Interior difference quotient on `L2D Ω` / `H1amb Ω`

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) needs a difference
quotient that stays on the restricted-domain space `L2D Ω`. Rather than build a
self-contained restricted translation calculus (translation by `h eₖ` is not an
endomorphism of `L2D Ω`, since it maps into `Lp ℝ 2 (volume.restrict (Ω - h eₖ))`), this
file *conjugates the whole-space difference-quotient engine*
(`EllipticPdes.Regularity.diffQuot`) through the extension-by-zero bridge
`extendL2 : L2D Ω →ₗᵢ[ℝ] EucL2 d` and its retraction `restrictL2 : EucL2 d →L[ℝ] L2D Ω`:
extend by zero, translate on the whole space where `diffQuot` already lives, restrict back.

## Main definitions

* `restrictL2`: the retraction `EucL2 d →L[ℝ] L2D Ω`, adjoint to `extendL2`.
* `diffQuotD`: the interior difference quotient `Dₖʰ` on `L2D Ω`.
* `diffQuotG`: the graph-level interior difference quotient on `H1amb Ω`.

## Main results

* `extendL2_inner_restrictL2`: `restrictL2` is the adjoint of `extendL2`.
* `extendL2_diffQuotD_eq`: on classes whose translated support stays in `Ω`, the restricted
  difference quotient's extension equals the whole-space difference quotient.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Restriction as the retraction and adjoint of `extendL2` -/

/-- **Restriction** `EucL2 d →L[ℝ] L2D Ω`, `g ↦ g|_Ω`: the retraction and adjoint of
`extendL2`. Built from the Mathlib restriction of `Lp` classes to a restricted measure
(`MeasureTheory.LpToLpRestrictCLM`), non-expansive since `volume.restrict Ω ≤ volume`
(Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
def restrictL2 : EucL2 d →L[ℝ] L2D Ω :=
  LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℝ ℝ volume 2 Ω

/-- The a.e. representative of the restriction: `restrictL2 g =ᵐ g` on `volume.restrict Ω`. -/
theorem coeFn_restrictL2 (g : EucL2 d) :
    (restrictL2 (Ω := Ω) g : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] (g : EuclideanSpace ℝ (Fin d) → ℝ) :=
  LpToLpRestrictCLM_coeFn ℝ Ω g

/-- **Restriction is a left inverse of extension by zero.** Extending a class by zero to
the whole space and restricting back to `Ω` recovers the original class.

The companion of `extendL2_inner_restrictL2`, which states the adjoint law and is the form
the difference-quotient argument takes. -/
theorem restrictL2_extendL2 (hΩm : MeasurableSet Ω) (g : L2D Ω) :
    restrictL2 (extendL2 hΩm g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictL2 (extendL2 hΩm g),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm] with x hx1 hx2 hx3
  rw [hx1, hx2, Set.indicator_of_mem hx3]

/-- **`restrictL2` is the adjoint of `extendL2`.** Every restricted inner product against
`restrictL2 w` equals the whole-space inner product of `extendL2 hΩm g` against `w`,
turning restricted-domain inner products into whole-space ones so that
`diffQuot_inner_adjoint` can be applied directly. -/
theorem extendL2_inner_restrictL2 (hΩm : MeasurableSet Ω) (g : L2D Ω) (w : EucL2 d) :
    ⟪extendL2 hΩm g, w⟫ = ⟪g, restrictL2 w⟫ := by
  have hLHS : ⟪extendL2 hΩm g, w⟫ = ∫ x in Ω, (g x : ℝ) * (w x : ℝ) ∂volume := by
    rw [L2.inner_def, ← integral_indicator hΩm]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_extendL2 hΩm g] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx]
    by_cases hxΩ : x ∈ Ω
    · simp [Set.indicator_of_mem hxΩ, mul_comm]
    · simp [Set.indicator_of_notMem hxΩ]
  have hRHS : ⟪g, restrictL2 w⟫ = ∫ x in Ω, (g x : ℝ) * (w x : ℝ) ∂volume := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_restrictL2 w] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  exact hLHS.trans hRHS.symm

/-! ### Interior difference quotient on `L2D Ω` -/

/-- **Interior difference quotient** `Dₖʰ` on `L2D Ω`: extend by zero, translate on the
whole space, restrict back. A bounded operator for every `h` (no support hypothesis needed
for boundedness; the identity with the whole-space difference quotient needs a
support condition, see `extendL2_diffQuotD_eq`). Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1. -/
def diffQuotD (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) : L2D Ω →L[ℝ] L2D Ω :=
  h⁻¹ • ((restrictL2).comp
      ((transL2 (hshift k h)).toContinuousLinearMap.comp (extendL2 hΩm).toContinuousLinearMap)
    - ContinuousLinearMap.id ℝ (L2D Ω))

/-- The pointwise a.e. formula for the interior difference quotient:
`Dₖʰ g(x) = ((extendL2 g)(x + h eₖ) - g(x)) / h`, valid on `Ω` (`volume.restrict Ω`-a.e.). -/
theorem coeFn_diffQuotD (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) (g : L2D Ω) :
    (diffQuotD k h hΩm g : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => ((extendL2 hΩm g) (x + hshift k h) - g x) / h := by
  have htrans : (restrictL2 (Ω := Ω) (transL2 (hshift k h) (extendL2 hΩm g))
        : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => (extendL2 hΩm g) (x + hshift k h) := by
    filter_upwards [coeFn_restrictL2 (transL2 (hshift k h) (extendL2 hΩm g)),
        ae_restrict_of_ae (coeFn_transL2 (hshift k h) (extendL2 hΩm g))] with x hx1 hx2
    rw [hx1, hx2]
  have hval : diffQuotD k h hΩm g
      = h⁻¹ • (restrictL2 (transL2 (hshift k h) (extendL2 hΩm g)) - g) := by
    simp [diffQuotD, _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [hval]
  filter_upwards [Lp.coeFn_smul h⁻¹ (restrictL2 (transL2 (hshift k h) (extendL2 hΩm g)) - g),
      Lp.coeFn_sub (restrictL2 (transL2 (hshift k h) (extendL2 hΩm g))) g, htrans]
    with x hx1 hx2 hx3
  simp only [hx1, Pi.smul_apply, hx2, Pi.sub_apply, hx3, smul_eq_mul, div_eq_inv_mul]

/-! ### Graph-level interior difference quotient -/

/-- **Graph-level interior difference quotient** `diffQuotG k h : H1amb Ω →L[ℝ] H1amb Ω`,
applying `diffQuotD k h` in every ambient coordinate. Assembled exactly as `cutoffMul`
(`EllipticPdes.Regularity.cutoffMul`), by conjugating the coordinatewise pi-map with
`PiLp.continuousLinearEquiv`. Since `Dₖʰ` commutes with weak differentiation coordinatewise,
this is `(Dₖʰ u₀, Dₖʰ ∂₁u, …, Dₖʰ ∂ₙu)` on graphs (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1). -/
def diffQuotG (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) : H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi
        (fun j : Fin (d + 1) => (diffQuotD k h hΩm).comp (ContinuousLinearMap.proj j))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).toContinuousLinearMap)

/-- Every ambient coordinate of `diffQuotG` is `diffQuotD` applied coordinatewise:
`diffQuotG k h U j = diffQuotD k h (U j)`. -/
@[simp] theorem diffQuotG_apply (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) (U : H1amb Ω)
    (j : Fin (d + 1)) : diffQuotG k h hΩm U j = diffQuotD k h hΩm (U j) := by
  simp only [diffQuotG, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]

/-! ### Whole-space compatibility as the integration-by-parts bridge -/

/-- **Whole-space compatibility.** On classes whose whole-space translate stays supported
in `Ω`, the interior difference quotient's extension by zero equals the whole-space
difference quotient of the extension: `extendL2 (Dₖʰ g) = Dₖʰ (extendL2 g)`. This lets the
whole-space adjoint relation `diffQuot_inner_adjoint` act on restricted-domain difference
quotients (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, proof of Theorem 1). -/
theorem extendL2_diffQuotD_eq (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) (g : L2D Ω)
    (hsupp : ∀ᵐ x ∂volume, (extendL2 hΩm g) (x + hshift k h) ≠ 0 → x ∈ Ω) :
    extendL2 hΩm (diffQuotD k h hΩm g) = diffQuot k h (extendL2 hΩm g) := by
  have hDQ : ∀ᵐ x ∂volume, x ∈ Ω →
      (diffQuotD k h hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x
        = ((extendL2 hΩm g) (x + hshift k h) - g x) / h :=
    ae_imp_of_ae_restrict (coeFn_diffQuotD k h hΩm g)
  apply Lp.ext
  filter_upwards [coeFn_extendL2 hΩm (diffQuotD k h hΩm g), coeFn_diffQuot k h (extendL2 hΩm g),
      extendL2_ae_eq_zero hΩm (diffQuotD k h hΩm g), extendL2_ae_eq_zero hΩm g,
      coeFn_extendL2 hΩm g, hsupp, hDQ]
    with x hx1 hx2 hx3 hx4 hx7 hx5 hx6
  rw [hx1, hx2]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, hx6 hxΩ, hx7, Set.indicator_of_mem hxΩ]
  · rw [Set.indicator_of_notMem hxΩ, hx4 hxΩ]
    have h0 : (extendL2 hΩm g) (x + hshift k h) = 0 := by
      by_contra hne
      exact hxΩ (hx5 hne)
    rw [h0]
    ring

end EllipticPdes.Regularity
