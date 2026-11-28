/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stochastic Fubini for an `L²`-continuous linear map

A stochastic integral on a finite measure space `(S, m)` is a continuous linear map
`I : Lp ℝ 2 m →L[ℝ] F` (the Wiener, Itô and Lévy integrals all are, in `F = Lp ℝ 2 P`; the Wiener
and Itô cases are instantiated in `StochasticFubiniIto`). A parameter integral `∫ φ u dν(u)` of
`L²`-valued integrands commutes with `I`, because `I` is
continuous linear (`ContinuousLinearMap.integral_comp_comm`). What makes this the *stochastic
Fubini theorem* is the representative of the left side: the Bochner integral
`∫ φ u dν(u)` in `Lp ℝ 2 m` is the class of the pointwise parameter integral
`x ↦ ∫ ψ u x dν(u)` of any jointly integrable representatives `ψ u = φ u` (`m`-a.e.).
`coeFn_integral_ae_eq` proves that representative fact (by testing against indicators of
measurable sets and the scalar Fubini theorem), and `stochFubini_ofCLM` combines it with the
commutation.

No `StochasticIntegralTower` class is introduced: `I` as an explicit continuous linear map is
already maximal generality; the isometry of the towers is never used.

## Main definitions

* `JointIntegrable`: joint integrability of a family of representatives on `ν ⊗ m`.

## Main results

* `coeFn_integral_ae_eq`: the `Lp ℝ 2 m`-valued Bochner integral `∫ u, φ u ∂ν` is
  `m`-a.e. the pointwise integral `x ↦ ∫ u, ψ u x ∂ν`, for `ψ` jointly integrable.
* `stochFubini_ofCLM`: for every continuous linear `I : Lp ℝ 2 m →L[ℝ] F`,
  `∫ u, I (φ u) ∂ν = I g` for any `g ∈ Lp ℝ 2 m` representing `x ↦ ∫ u, ψ u x ∂ν`.

## References

* [M. Veraar, *The stochastic Fubini theorem revisited*][Veraar2012], Thm 2.2

## Tags

stochastic Fubini theorem, stochastic integral, Bochner integral, continuous linear map,
L2 space, MSC 60H05
-/

@[expose] public section

open MeasureTheory

namespace MathFin
namespace StochasticFubini

variable {A S : Type*} {mA : MeasurableSpace A} {mS : MeasurableSpace S}
  {ν : Measure A} {m : Measure S}

/-- **Joint integrability** of a family of representatives `ψ : A → S → ℝ` on the product
`ν ⊗ m`. An abbreviation so that the product `σ`-algebra is the one of the implicit `mS`
(not the instance on a type such as `ℝ≥0 × Ω` that already carries the predictable one). -/
abbrev JointIntegrable (ψ : A → S → ℝ) (ν : Measure A) (m : Measure S) : Prop :=
  Integrable (Function.uncurry ψ) (ν.prod m)

/-- On a finite measure space the set integral over a measurable `s` commutes with the `Lp`-valued
parameter integral: the set integral is the continuous linear functional `⟪1_s, ·⟫`. -/
lemma setIntegral_integral_lp [IsFiniteMeasure m] (φ : A → Lp ℝ 2 m) (hφ : Integrable φ ν)
    {s : Set S} (hs : MeasurableSet s) :
    ∫ x in s, (∫ u, φ u ∂ν) x ∂m = ∫ u, ∫ x in s, φ u x ∂m ∂ν := by
  have key (f : Lp ℝ 2 m) : innerSL ℝ (indicatorConstLp 2 hs (measure_ne_top m s) (1 : ℝ)) f
      = ∫ x in s, f x ∂m := by
    simpa using L2.inner_indicatorConstLp_one hs (measure_ne_top m s) f
  calc ∫ x in s, (∫ u, φ u ∂ν) x ∂m
      = innerSL ℝ (indicatorConstLp 2 hs (measure_ne_top m s) (1 : ℝ)) (∫ u, φ u ∂ν) :=
        (key _).symm
    _ = ∫ u, innerSL ℝ (indicatorConstLp 2 hs (measure_ne_top m s) (1 : ℝ)) (φ u) ∂ν :=
        ((innerSL ℝ (indicatorConstLp 2 hs (measure_ne_top m s) (1 : ℝ))).integral_comp_comm
          hφ).symm
    _ = ∫ u, ∫ x in s, φ u x ∂m ∂ν := integral_congr_ae (ae_of_all _ fun u ↦ key (φ u))

/-- **The `L²`-representative fact.** The Bochner integral `∫ u, φ u ∂ν` in `Lp ℝ 2 m` is
`m`-a.e. the pointwise parameter integral `x ↦ ∫ u, ψ u x ∂ν`, where each `ψ u` represents
`φ u` and `(u, x) ↦ ψ u x` is jointly integrable (on a finite `m` this follows from joint
square-integrability). -/
theorem coeFn_integral_ae_eq [IsFiniteMeasure m] [SFinite ν] (φ : A → Lp ℝ 2 m)
    (hφ : Integrable φ ν) (ψ : A → S → ℝ) (hψ : JointIntegrable ψ ν m)
    (hφψ : ∀ u, ⇑(φ u) =ᵐ[m] ψ u) :
    ⇑(∫ u, φ u ∂ν) =ᵐ[m] fun x ↦ ∫ u, ψ u x ∂ν := by
  replace hψ : Integrable (Function.uncurry ψ) (ν.prod m) := hψ
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ ↦ ?_) (fun s _ _ ↦ ?_)
    fun s hs _ ↦ ?_
  · exact ((Lp.memLp _).integrable one_le_two).integrableOn
  · exact hψ.integral_prod_right.integrableOn
  · have hs' : Integrable (Function.uncurry ψ) (ν.prod (m.restrict s)) :=
      hψ.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    rw [setIntegral_integral_lp φ hφ hs]
    calc ∫ u, ∫ x in s, φ u x ∂m ∂ν = ∫ u, ∫ x in s, ψ u x ∂m ∂ν :=
          integral_congr_ae (ae_of_all _ fun u ↦
            integral_congr_ae ((hφψ u).filter_mono (ae_mono Measure.restrict_le_self)))
      _ = ∫ x in s, ∫ u, ψ u x ∂ν ∂m := integral_integral_swap hs'

/-- **Stochastic Fubini for a continuous linear integral** (tower-agnostic). If `I` is a
continuous linear map out of `Lp ℝ 2 m` (a Wiener, Itô or Lévy integral), `φ : A → Lp ℝ 2 m`
is Bochner integrable (`∫ ‖φ u‖₂ dν < ∞`, Veraar's sharp condition), `ψ` is a jointly integrable
family of representatives of `φ`, and `g ∈ Lp ℝ 2 m` represents the integrated integrand
`x ↦ ∫ u, ψ u x ∂ν`, then
`∫ u, I (φ u) ∂ν = I g`: the parameter integral of the stochastic integrals is the stochastic
integral of the parameter integral. -/
theorem stochFubini_ofCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [IsFiniteMeasure m] [SFinite ν] (I : Lp ℝ 2 m →L[ℝ] F) (φ : A → Lp ℝ 2 m)
    (hφ : Integrable φ ν) (ψ : A → S → ℝ) (hψ : JointIntegrable ψ ν m)
    (hφψ : ∀ u, ⇑(φ u) =ᵐ[m] ψ u) (g : Lp ℝ 2 m) (hg : ⇑g =ᵐ[m] fun x ↦ ∫ u, ψ u x ∂ν) :
    ∫ u, I (φ u) ∂ν = I g := by
  rw [I.integral_comp_comm hφ]
  exact congrArg I (Lp.ext ((coeFn_integral_ae_eq φ hφ ψ hψ hφψ).trans hg.symm))

end StochasticFubini
end MathFin
