/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Martingale.Basic

/-!
# The Bayes change-of-measure martingale engine

The abstract heart of Girsanov's theorem, isolated from any stochastic-calculus
machinery. Fix a finite measure `P`, a filtration `𝓕`, and a **density process**
`Z` that is a `P`-martingale with `Z_T ≥ 0`. Let `Q := P.withDensity Z_T` be the
tilted measure. Then a process `D` is a **`Q`-martingale on `[0, T]`** when
the product `Z · D` is a `P`-martingale (one direction; the set-integral form is proved):

  `∫_A D_t dQ = ∫_A Z_t D_t dP = ∫_A Z_s D_s dP = ∫_A D_s dQ`  for `A ∈ 𝓕_s`.

The two outer equalities are the **Bayes/pull-out step** — for a set `A ∈ 𝓕_s ⊆ 𝓕_u`
and `D_u` `𝓕_u`-measurable,
`∫_A D_u Z_T dP = ∫_A D_u · P[Z_T | 𝓕_u] dP = ∫_A D_u Z_u dP` since `Z` is a
`P`-martingale (`condExp_mul_of_stronglyMeasurable_left` + `setIntegral_condExp`).
The middle equality is the `Z · D` martingale property (`Martingale.setIntegral_eq`).

This is the reusable engine: any concrete change of measure (the Black–Scholes
Girsanov tilt in `MathFin/Pricing/Girsanov.lean`; and, once the tower gains an
adapted-integrand Itô formula, the general Doléans–Dade exponential) is one
instance — supply `Z`, `D`, and the two martingale facts.

## Main results

* `MathFin.changeOfMeasure_setIntegral_eq`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 9
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Ch 5.2

## Tags

Bayes rule, change of measure, density process, Radon–Nikodym, Girsanov tilt, martingale under Q,
MSC 60G44, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Bayes change-of-measure engine (`[0,T]` form).** Let `Z` be a `P`-martingale with `Z_T ≥ 0`
(the density process), `D` an `𝓕`-adapted process, `M` a `P`-martingale, and suppose the product
`Z · D` agrees with `M` a.e. on `[0, T]` (`Z_u · D_u =ᵐ M_u` for `u ≤ T`). Then `D` is a martingale
under `Q := P.withDensity (Z_T)` on `[0, T]`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the `Q`-integrals of
`D_t` and `D_s` over `A` agree.

The generality over the full-martingale form `changeOfMeasure_setIntegral_eq` is that `Z · D` itself
need **not** be a martingale — only its `[0,T]`-restriction need agree with an honest martingale
`M`. This is exactly the simple-θ Girsanov situation, where the tilted-density identity
`Z · D =ᵐ E^{a−c}` (`simple_spine_ae`) holds only on `[0,T]` (beyond the last partition point
`Z · D` diverges from the Doléans martingale `E^{a−c}` by a forward Wald factor). The mechanism is
unchanged: `∫_A D_u dQ = ∫_A Z_u D_u dP` (withDensity conversion + Bayes pull-out, using `hmix`,
`hZ`, `hDsm`, none of which touch `M`), then `Z_u D_u =ᵐ M_u` and `M`'s martingale property close
the loop. No stochastic calculus, only conditional expectations. -/
theorem changeOfMeasure_setIntegral_eq_of_ae_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {Z D M : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hZmeasT : Measurable (Z T)) (hZpos : ∀ ω, 0 ≤ Z T ω)
    (hDsm : ∀ u, StronglyMeasurable[𝓕 u] (D u))
    (hZ : Martingale Z 𝓕 P) (hM : Martingale M 𝓕 P)
    (hZDM : ∀ u, u ≤ T → (fun ω ↦ Z u ω * D u ω) =ᵐ[P] M u)
    (hmix : ∀ u, u ≤ T → Integrable (fun ω ↦ D u ω * Z T ω) P)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, D t ω ∂(P.withDensity (fun ω ↦ ENNReal.ofReal (Z T ω)))
      = ∫ ω in A, D s ω ∂(P.withDensity (fun ω ↦ ENNReal.ofReal (Z T ω))) := by
  have hAmΩ : MeasurableSet A := 𝓕.le s A hA
  -- `∫_A D_u dQ = ∫_A Z_u D_u dP` for `s ≤ u ≤ T` (withDensity conversion + Bayes pull-out).
  have helper : ∀ u, s ≤ u → u ≤ T →
      ∫ ω in A, D u ω ∂(P.withDensity (fun ω ↦ ENNReal.ofReal (Z T ω)))
        = ∫ ω in A, Z u ω * D u ω ∂P := by
    intro u hsu huT
    have hAu : MeasurableSet[𝓕 u] A := 𝓕.mono hsu A hA
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hZmeasT.ennreal_ofReal
          (ae_of_all (P.restrict A) fun _ ↦ ENNReal.ofReal_lt_top) _ hAmΩ]
    have hconv : ∀ ω, (ENNReal.ofReal (Z T ω)).toReal • D u ω = D u ω * Z T ω := by
      intro ω; rw [ENNReal.toReal_ofReal (hZpos ω), smul_eq_mul, mul_comm]
    simp_rw [hconv]
    rw [← setIntegral_condExp (𝓕.le u) (hmix u huT) hAu]
    have hae : P[fun ω ↦ D u ω * Z T ω | 𝓕 u] =ᵐ[P] fun ω ↦ Z u ω * D u ω := by
      have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 u)
        (hDsm u) (hmix u huT) (hZ.integrable T)
      refine h1.trans ?_
      filter_upwards [hZ.condExp_ae_eq huT] with ω hh2
      simp only [Pi.mul_apply, hh2]; ring
    exact setIntegral_congr_ae hAmΩ (hae.mono fun ω h _ ↦ h)
  rw [helper t hst htT, helper s le_rfl (hst.trans htT),
    setIntegral_congr_ae hAmΩ ((hZDM t htT).mono fun ω h _ ↦ h),
    setIntegral_congr_ae hAmΩ ((hZDM s (hst.trans htT)).mono fun ω h _ ↦ h)]
  exact (hM.setIntegral_eq hst hA).symm

/-- **Bayes change-of-measure engine (full-martingale form).** The special case of
`changeOfMeasure_setIntegral_eq_of_ae_martingale` where the product `Z · D` is itself a
`P`-martingale (take `M := Z · D`, so the `=ᵐ` hypothesis is reflexivity): then `D` is a martingale
under `Q := P.withDensity (Z_T)` on `[0,T]`. This is the constant-θ Girsanov situation, where
`Z · D = Wald(a−θ)` is a genuine martingale everywhere. -/
theorem changeOfMeasure_setIntegral_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {Z D : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hZmeasT : Measurable (Z T)) (hZpos : ∀ ω, 0 ≤ Z T ω)
    (hDsm : ∀ u, StronglyMeasurable[𝓕 u] (D u))
    (hZ : Martingale Z 𝓕 P)
    (hZD : Martingale (fun t ω ↦ Z t ω * D t ω) 𝓕 P)
    (hmix : ∀ u, u ≤ T → Integrable (fun ω ↦ D u ω * Z T ω) P)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, D t ω ∂(P.withDensity (fun ω ↦ ENNReal.ofReal (Z T ω)))
      = ∫ ω in A, D s ω ∂(P.withDensity (fun ω ↦ ENNReal.ofReal (Z T ω))) :=
  changeOfMeasure_setIntegral_eq_of_ae_martingale T hZmeasT hZpos hDsm hZ hZD
    (fun _ _ ↦ Filter.EventuallyEq.rfl) hmix hst htT hA

end MathFin
