/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Caccioppoli
public import LeanPool.EllipticPDE.Analysis.LpExtendByZero


/-!
# Whole-space extension bridge for the interior `H²` estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) runs the
difference-quotient method of the whole-space engine
(`EllipticPdes.Regularity.DifferenceQuotient`,
`EllipticPdes.Regularity.DiffQuotientBound`) against the restricted-domain weak
solution and its Caccioppoli energy bound
(`EllipticPdes.Regularity.Caccioppoli`).

The two layers live on different measures: the difference-quotient engine is built on the
whole-space space `EucL2 d = Lp ℝ 2 volume`, while the weak solution, the cutoff multiplication
keystone, and the Caccioppoli estimate live on the restricted-domain space `L2D Ω = Lp ℝ 2
(volume.restrict Ω)`. This file provides the bridge between them: extension by zero `L2D Ω
→ₗᵢ[ℝ] EucL2 d`, packaged from the Mathlib linear isometry `MeasureTheory.lpExtendByZero`,
together with the compatibility that moves the cutoff-weighted gradient energy of the
Caccioppoli estimate onto whole-space `EucL2 d` classes with the `L²` norm preserved.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Extension by zero as the restricted-to-whole-space bridge -/

/-- **Extension by zero**, `L2D Ω →ₗᵢ[ℝ] EucL2 d`. A class on the restricted measure
`volume.restrict Ω` is sent to the whole-space `L²(ℝ^d)` class of its extension by zero,
with the `L²` norm preserved. This is the substrate bridge that lets the whole-space
difference-quotient engine act on restricted-domain gradient data (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
def extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω) :
    L2D Ω →ₗᵢ[ℝ] EucL2 d :=
  lpExtendByZero volume 2 Ω hΩm

/-- The a.e. representative of the extension by zero: `extendL2 hΩm g =ᵐ Ω.indicator g`. -/
theorem coeFn_extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) :
    (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] Ω.indicator (g : EuclideanSpace ℝ (Fin d) → ℝ) :=
  coeFn_lpExtendByZero hΩm g

/-- The extension by zero preserves the `L²` norm: `‖extendL2 hΩm g‖ = ‖g‖`. -/
theorem norm_extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) : ‖extendL2 hΩm g‖ = ‖g‖ :=
  (extendL2 hΩm).norm_map g

/-- The extension by zero vanishes almost everywhere off `Ω`. -/
theorem extendL2_ae_eq_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) :
    ∀ᵐ x ∂volume, x ∉ Ω → (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x = 0 :=
  lpExtendByZero_ae_eq_zero hΩm g

/-! ### Caccioppoli energy on whole-space classes -/

/-- **Caccioppoli energy on whole-space classes.** Feeding the interior energy estimate
`EllipticPdes.Regularity.caccioppoli` through the norm-preserving extension bridge, the
cutoff-weighted gradient energy of a weak solution `u ∈ H₀¹(Ω)` of `L u = f`, measured on the
whole-space `EucL2 d` classes `extendL2 hΩm (ζ · ∂ᵢu)`, is bounded by the data:
`(λ/2) ∑ᵢ ‖extendL2 hΩm (ζ · ∂ᵢu)‖² ≤ C (‖f‖² + ‖u₀‖²)`. These whole-space classes are the
gradient data on which the difference-quotient method of the interior second-derivative
estimate operates (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8).

One of the two deliverables the module docstring names. The interior chain reaches the same
energy through `Caccioppoli` on the restricted-domain classes. -/
theorem extendL2_cutoffGrad_energy_le (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      Op.lam / 2 * ∑ i : Fin d, ‖extendL2 hΩm (mulTest hζ ((u : H1amb Ω) i.succ))‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := caccioppoli Op hζ
  refine ⟨C, hC0, fun u f hu => ?_⟩
  have hnorm : ∀ i : Fin d,
      ‖extendL2 hΩm (mulTest hζ ((u : H1amb Ω) i.succ))‖
        = ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ :=
    fun i => norm_extendL2 hΩm _
  simp_rw [hnorm]
  exact hC u f hu

/-! ### Leibniz for extension against a coefficient, and translated coefficients

The interior second-derivative estimate runs the whole-space difference-quotient method
against the coefficient-weighted energy form. These three lemmas supply the pointwise
algebra: extension by zero commutes with coefficient multiplication (`extendL2_actL`), the
discrete Leibniz rule splits the difference quotient of a coefficient-multiplied field into
an elliptic leading term and a commutator term (`coeFn_diffQuot_mul_coeff`), and a
translated coefficient bundle stays uniformly elliptic (`EllipticCoeff.translate`), which
lets the leading term reuse the energy lower bound directly (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1; Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Theorem 8.8).
-/

/-- **Extension commutes with coefficient multiplication.** Extending `A.actL i j g` by zero
to the whole space agrees, `volume`-a.e., with multiplying the whole-space extension of `g`
by the coefficient `A.a · i j` (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
theorem extendL2_actL {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (A : EllipticCoeff d) (i j : Fin d) (g : L2D Ω) :
    (extendL2 hΩm (A.actL i j g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => A.a x i j * (extendL2 hΩm g x) := by
  have hact : ∀ᵐ x ∂volume, x ∈ Ω →
      (A.actL i j g : EuclideanSpace ℝ (Fin d) → ℝ) x = A.a x i j * (g x : ℝ) :=
    (ae_restrict_iff' hΩm).mp (A.actL_coeFn i j g)
  filter_upwards [coeFn_extendL2 hΩm (A.actL i j g), coeFn_extendL2 hΩm g, hact]
    with x hx1 hx2 hact_x
  rw [hx1, hx2]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ]
    exact hact_x hxΩ
  · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ, mul_zero]

/-- **Discrete Leibniz for coefficient × field on the whole space.** Splits the difference
quotient of a coefficient-multiplied extension into the elliptic leading term (the
coefficient translated to the shifted point, times the difference quotient of the field)
and the commutator term (the coefficient's own difference quotient, times the field),
`volume`-a.e.: `Dₖʰ(a · w) = (τ_{h eₖ} a) · Dₖʰw + (Dₖʰa) · w` for `w = extendL2 g` (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
theorem coeFn_diffQuot_mul_coeff {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (A : EllipticCoeff d) (i j k : Fin d) {h : ℝ} (g : L2D Ω) :
    (diffQuot k h (extendL2 hΩm (A.actL i j g)) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x =>
        A.a (x + hshift k h) i j * (diffQuot k h (extendL2 hΩm g) x)
          + ((A.a (x + hshift k h) i j - A.a x i j) / h) * (extendL2 hΩm g x) := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hact_shift :
      (fun x => (extendL2 hΩm (A.actL i j g) : EuclideanSpace ℝ (Fin d) → ℝ)
          (x + hshift k h))
        =ᵐ[volume]
      (fun x => A.a (x + hshift k h) i j *
          (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h)) :=
    hqmp.ae_eq_comp (extendL2_actL hΩm A i j g)
  filter_upwards [coeFn_diffQuot k h (extendL2 hΩm (A.actL i j g)),
      coeFn_diffQuot k h (extendL2 hΩm g), extendL2_actL hΩm A i j g, hact_shift]
    with x hLHS hDQ hAct0 hActShift
  rw [hLHS, hAct0, hActShift, hDQ]
  ring

/-- **Translated coefficients stay elliptic.** `A.translate v` is the coefficient bundle
`(A.translate v).a x i j = A.a (x + v) i j`, with the same ellipticity constant `lam` and
sup bound `Λ`; measurability, boundedness, and ellipticity transfer from `A` by
translation-invariance of `volume` (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1). -/
def _root_.EllipticPdes.Sobolev.EllipticCoeff.translate (A : EllipticCoeff d)
    (v : EuclideanSpace ℝ (Fin d)) : EllipticCoeff d where
  a := fun x i j => A.a (x + v) i j
  lam := A.lam
  Λ := A.Λ
  lam_pos := A.lam_pos
  Λ_nonneg := A.Λ_nonneg
  measurable i j := (A.measurable i j).comp (measurable_add_const v)
  bdd i j := (measurePreserving_add_right volume v).quasiMeasurePreserving.ae (A.bdd i j)
  elliptic := (measurePreserving_add_right volume v).quasiMeasurePreserving.ae A.elliptic

/-- Simp/access lemma: the translated bundle's coefficient entry is the original coefficient
evaluated at the shifted point, `(A.translate v).a x i j = A.a (x + v) i j`. -/
@[simp] theorem _root_.EllipticPdes.Sobolev.EllipticCoeff.translate_a
    (A : EllipticCoeff d) (v x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    (A.translate v).a x i j = A.a (x + v) i j := rfl

end EllipticPdes.Regularity
