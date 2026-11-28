/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Integration

/-!
# Freezing an independent variable

If `X` and `Y` are independent, the expectation of `g(X, Y)` can be computed by freezing `X` at
a value `x`, averaging `g(x, Y)` over `Y` alone, and then averaging the result over the law of
`X`:

  `𝔼[g(X, Y)] = ∫ x, 𝔼[g(x, Y)] d(law X)`.

This is the *freezing lemma*. When `X = N` is a count it is the law of total expectation over the
number of jumps, the step every Poisson-mixture computation takes: the jump-diffusion price,
Merton's among them, and the compound-Poisson moment generating function
(`Probability/Jumps/CompoundPoissonMGF.lean`) both go through it. With `X` a jump part of any law it
is the mixing formula of `Models/Jumps/JumpDiffusionMixing.lean`: a jump-diffusion call is the
Black–Scholes price averaged over the jumps.

The proof composes two Mathlib facts: independence makes the joint law the product of the
marginal laws (`IndepFun.map_prod_eq_prod_map_map`), and an integral against a product measure
is an iterated integral (`integral_prod`).

Its conditional form is Shreve's *independence lemma* (*Stochastic Calculus for Finance II*,
Lemma 2.3.4): if `X` is measurable for a σ-algebra `𝓜` and `Y` is independent of `𝓜`, then

  `𝔼[g(X, Y) | 𝓜] = G(X)`, with `G(x) = 𝔼[g(x, Y)]`.

Given `𝓜`, `X` is known and `Y` keeps its law. On an event `s ∈ 𝓜` the joint law of `(X, Y)`
is the law of `X` on `s` times the law of `Y` (`map_restrict_prodMk_of_indep`), so the
unconditional computation runs on every such event, which characterizes the conditional
expectation. This is the step that prices an option at an intermediate date: the state at `t` is
known, and the increment to maturity is independent of the past (the American put's Brownian
transitions, `Models/BlackScholes/American/Stopping/BrownianTransition.lean`, and the jump-diffusion
prices of `Models/Jumps/JumpDiffusionOptionPrices.lean`).

## Main results

* `integrable_comp_prodMk_iff_of_indepFun`: `g(X, Y)` is integrable exactly when `g` is
  integrable against the product of the laws.
* `integral_comp_prodMk_of_indepFun`: the freezing lemma.
* `integrable_prod_map_of_countable`: for a countable-valued `X`, integrability against the
  product of the laws is checked one value of `X` at a time.
* `integral_comp_prodMk_of_indepFun_of_countable`: the freezing lemma for a countable-valued `X`
  and a nonnegative `g`, with integrability checked one value of `X` at a time.
* `integral_comp_of_hasLaw_of_countable`: integrating out a countable variable. For `X` with
  a countable law `ν`, independent of `Y`, and a nonnegative `F` whose expectations
  `c a = 𝔼[F(a, Y)]` are finite and integrable against `ν`, `𝔼[F(X, Y)] = ∫ a, c a ∂ν`. With
  `ν = Poisson(Λ)` this is the Poisson-mixture step.
* `condExp_comp_prodMk_of_indep`: the conditional freezing lemma (Shreve's independence lemma),
  `𝔼[g(X, Y) | 𝓜] = G(X)` for `X` measurable for `𝓜` and `Y` independent of `𝓜`.
* `condExp_mul_of_indep`: `𝔼[X·Y | m] = X·𝔼[Y]` for `X` measurable for `m` and `Y` for a σ-algebra
  independent of `m`.
* `indepFun_prodMk_of_indepFun_prodMk`: if `X` is independent of `(Y, W)` and `Y` of `W`, then
  `Y` is independent of `(X, W)`. Mutual independence of three variables can be stated with any
  of them split off first.

## References

* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Lemma
  2.3.4

## Tags

freezing lemma, independence lemma, Shreve, law of total expectation, Poisson mixture,
conditional expectation, independent random variables, MSC 60E05, MSC 28A25, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

-- `m` (a sub-σ-algebra, used by the conditional lemmas) precedes `mΩ`, so that `mΩ` is the
-- measurable-space instance in force
variable {Ω α β E : Type*} {m mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β}

/-- For independent `X` and `Y`, `g(X, Y)` is integrable exactly when `g` is integrable against
the product of the laws of `X` and `Y`. -/
theorem integrable_comp_prodMk_iff_of_indepFun (hXY : X ⟂ᵢ[P] Y) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {g : α × β → E}
    (hg : AEStronglyMeasurable g ((P.map X).prod (P.map Y))) :
    Integrable (fun ω ↦ g (X ω, Y ω)) P ↔ Integrable g ((P.map X).prod (P.map Y)) := by
  rw [← hXY.map_prod_eq_prod_map_map hX hY] at hg ⊢
  exact (integrable_map_measure hg (hX.prodMk hY)).symm

/-- **The freezing lemma.** For independent `X` and `Y`, and `g` integrable against the product
of their laws, `𝔼[g(X, Y)] = ∫ x, 𝔼[g(x, Y)] d(law X)`. -/
theorem integral_comp_prodMk_of_indepFun [NormedSpace ℝ E] (hXY : X ⟂ᵢ[P] Y)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) {g : α × β → E}
    (hg : Integrable g ((P.map X).prod (P.map Y))) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ x, ∫ ω, g (x, Y ω) ∂P ∂(P.map X) := by
  have hmap := hXY.map_prod_eq_prod_map_map hX hY
  have hgm : AEStronglyMeasurable g (P.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  calc ∫ ω, g (X ω, Y ω) ∂P = ∫ p, g p ∂(P.map fun ω ↦ (X ω, Y ω)) :=
        (integral_map (hX.prodMk hY) hgm).symm
    _ = ∫ x, ∫ y, g (x, y) ∂(P.map Y) ∂(P.map X) := by rw [hmap, integral_prod g hg]
    _ = ∫ x, ∫ ω, g (x, Y ω) ∂P ∂(P.map X) := integral_congr_ae <| by
        filter_upwards [hg.prod_right_ae] with x hx
        exact integral_map hY hx.aestronglyMeasurable

/-- For a countable-valued `X`, integrability of `g` against the product of the laws is checked
one value of `X` at a time: each `g(a, Y)` integrable, and `a ↦ 𝔼‖g(a, Y)‖` integrable against
the law of `X`. Measurability of the sections suffices, since `X` takes countably many values. -/
theorem integrable_prod_map_of_countable [Countable α] [MeasurableSingletonClass α]
    (hY : AEMeasurable Y P) {g : α × β → ℝ} (hgm : ∀ a, Measurable fun b ↦ g (a, b))
    (hint : ∀ a, Integrable (fun ω ↦ g (a, Y ω)) P)
    (hint' : Integrable (fun a ↦ ∫ ω, ‖g (a, Y ω)‖ ∂P) (P.map X)) :
    Integrable g ((P.map X).prod (P.map Y)) := by
  refine (integrable_prod_iff
    (measurable_from_prod_countable_right (f := g) hgm).aestronglyMeasurable).mpr
    ⟨ae_of_all _ fun a ↦ (integrable_map_measure (hgm a).aestronglyMeasurable hY).mpr (hint a),
      hint'.congr (ae_of_all _ fun a ↦ ?_)⟩
  exact (integral_map hY (hgm a).norm.aestronglyMeasurable).symm

/-- **The freezing lemma for a countable variable.** For a countable-valued `X` independent of `Y`
and a nonnegative `g`, if each `g(a, Y)` is integrable and `a ↦ 𝔼[g(a, Y)]` is integrable against
the law of `X`, then `𝔼[g(X, Y)] = ∫ a, 𝔼[g(a, Y)] d(law X)`. -/
theorem integral_comp_prodMk_of_indepFun_of_countable [Countable α]
    [MeasurableSingletonClass α] (hXY : X ⟂ᵢ[P] Y) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {g : α × β → ℝ} (hgm : ∀ a, Measurable fun b ↦ g (a, b))
    (hg0 : ∀ p, 0 ≤ g p) (hint : ∀ a, Integrable (fun ω ↦ g (a, Y ω)) P)
    (hint' : Integrable (fun a ↦ ∫ ω, g (a, Y ω) ∂P) (P.map X)) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ a, ∫ ω, g (a, Y ω) ∂P ∂(P.map X) :=
  integral_comp_prodMk_of_indepFun hXY hX hY <| integrable_prod_map_of_countable hY hgm hint <|
    hint'.congr <| ae_of_all _ fun a ↦ integral_congr_ae <| ae_of_all _ fun ω ↦
      (Real.norm_of_nonneg (hg0 (a, Y ω))).symm

/-- **Integrating out a countable variable.** For `X` with a countable law `ν`, independent of
`Y`, and a nonnegative `F`, if each `F(a, Y)` is integrable with expectation `c a` and `c` is
integrable against `ν`, then `𝔼[F(X, Y)] = ∫ a, c a ∂ν`. For a Poisson count this is the
Poisson-mixture step of a compound-Poisson computation. -/
theorem integral_comp_of_hasLaw_of_countable [Countable α] [MeasurableSingletonClass α]
    {ν : Measure α} (hX : HasLaw X ν P) (hY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y)
    {F : α → β → ℝ} (hFm : ∀ a, Measurable fun y ↦ F a y) (hF0 : ∀ a y, 0 ≤ F a y)
    {c : α → ℝ} (hint : ∀ a, Integrable (fun ω ↦ F a (Y ω)) P)
    (hc : ∀ a, ∫ ω, F a (Y ω) ∂P = c a) (hcint : Integrable c ν) :
    ∫ ω, F (X ω) (Y ω) ∂P = ∫ a, c a ∂ν := by
  have hint' : Integrable (fun a ↦ ∫ ω, F a (Y ω) ∂P) (P.map X) := by
    rw [hX.map_eq]
    exact hcint.congr (ae_of_all _ fun a ↦ (hc a).symm)
  calc ∫ ω, F (X ω) (Y ω) ∂P = ∫ a, ∫ ω, F a (Y ω) ∂P ∂(P.map X) :=
        integral_comp_prodMk_of_indepFun_of_countable (g := fun p ↦ F p.1 p.2) hXY
          hX.aemeasurable hY hFm (fun p ↦ hF0 p.1 p.2) hint hint'
    _ = ∫ a, c a ∂ν := by
        rw [hX.map_eq]
        exact integral_congr_ae (ae_of_all _ hc)

/-! ### The conditional freezing lemma -/

/-- On an event `s` of a σ-algebra `m` for which `X` is measurable and of which `Y` is independent,
the joint law of `(X, Y)` under `P` restricted to `s` is the law of `X` on `s` times the law of `Y`
under `P`. Normalized by `P(s)`, it says that given `s`, `Y` keeps its law and stays independent of
`X`. -/
theorem map_restrict_prodMk_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X) (hY : AEMeasurable Y P)
    (hi : Indep (MeasurableSpace.comap Y mβ) m P) {s : Set Ω} (hs : MeasurableSet[m] s) :
    (P.restrict s).map (fun ω ↦ (X ω, Y ω)) = ((P.restrict s).map X).prod (P.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  refine (Measure.prod_eq fun A B hA hB ↦ ?_).symm
  rw [Measure.map_apply_of_aemeasurable (hX'.aemeasurable.prodMk hY).restrict (hA.prod hB),
    Measure.map_apply hX' hA, Measure.map_apply_of_aemeasurable hY hB,
    Measure.restrict_apply' (hm s hs), Measure.restrict_apply' (hm s hs), Set.mk_preimage_prod,
    Set.inter_right_comm, Set.inter_comm _ (Y ⁻¹' B), mul_comm]
  exact (Indep_iff _ _ _).1 hi _ _ ⟨B, hB, rfl⟩ ((hX hA).inter hs)

/-- **The conditional freezing lemma** (Shreve's independence lemma). If `X` is measurable for a
σ-algebra `m` and `Y` is independent of `m`, then `𝔼[g(X, Y) | m] = G(X)` almost surely, with
`G(x) = ∫ g(x, y) d(law Y)(y)`, for `g` strongly measurable and `g(X, Y)` integrable: given `m`,
`X` is known and `Y` keeps its law. On each event of `m` the joint law of `(X, Y)` is a product
(`map_restrict_prodMk_of_indep`), so both sides have the same integral over it. -/
theorem condExp_comp_prodMk_of_indep [NormedSpace ℝ E] [CompleteSpace E] (hm : m ≤ mΩ)
    (hX : Measurable[m] X) (hY : AEMeasurable Y P)
    (hi : Indep (MeasurableSpace.comap Y mβ) m P) {g : α × β → E} (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    P[fun ω ↦ g (X ω, Y ω) | m] =ᵐ[P] fun ω ↦ ∫ y, g (X ω, y) ∂(P.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  have hG : StronglyMeasurable fun x ↦ ∫ y, g (x, y) ∂(P.map Y) := hg.integral_prod_right'
  -- on each event of `m`, `g` is integrable against the product law
  have hgs (s : Set Ω) (hs : MeasurableSet[m] s) :
      Integrable g (((P.restrict s).map X).prod (P.map Y)) := by
    rw [← map_restrict_prodMk_of_indep hm hX hY hi hs]
    exact (integrable_map_measure hg.aestronglyMeasurable
      (hX'.aemeasurable.prodMk hY).restrict).2 hgi.restrict
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hgi (fun _ _ _ ↦ ?_) (fun s hs _ ↦ ?_)
    (hG.comp_measurable hX).aestronglyMeasurable).symm
  · have hGi := (hgs Set.univ MeasurableSet.univ).integral_prod_left
    rw [Measure.restrict_univ] at hGi
    exact (hGi.comp_measurable hX').integrableOn
  · calc ∫ ω in s, ∫ y, g (X ω, y) ∂(P.map Y) ∂P
        = ∫ x, ∫ y, g (x, y) ∂(P.map Y) ∂((P.restrict s).map X) :=
          (integral_map hX'.aemeasurable hG.aestronglyMeasurable).symm
      _ = ∫ p, g p ∂((P.restrict s).map fun ω ↦ (X ω, Y ω)) := by
          rw [map_restrict_prodMk_of_indep hm hX hY hi hs, integral_prod g (hgs s hs)]
      _ = ∫ ω in s, g (X ω, Y ω) ∂P :=
          integral_map (hX'.aemeasurable.prodMk hY).restrict hg.aestronglyMeasurable

/-- **Pulling out a known factor against an independent one.** If `X` is `m`-measurable and `Y`
is measurable for a σ-algebra `m'` independent of `m` (both integrable), then
`𝔼[X·Y | m] = X·𝔼[Y]` almost surely: given `m`, `X` is known and `Y` keeps its mean. With
`X = e^{a+Z}` and `Y = e^{W}`, for `Z` known and `W` independent of the past, this is the
conditional exponential moment of a sum. -/
theorem condExp_mul_of_indep {m' : MeasurableSpace Ω} {X Y : Ω → ℝ} (hm : m ≤ mΩ)
    (hm' : m' ≤ mΩ) (hi : Indep m' m P) (hX : StronglyMeasurable[m] X)
    (hY : StronglyMeasurable[m'] Y) (hXi : Integrable X P) (hYi : Integrable Y P) :
    P[X * Y | m] =ᵐ[P] fun ω ↦ X ω * ∫ ω, Y ω ∂P := by
  have hind : IndepFun X Y P :=
    (IndepFun_iff_Indep _ _ _).2
      (indep_of_indep_of_le_right (indep_of_indep_of_le_left hi.symm hX.measurable.comap_le)
        hY.measurable.comap_le)
  refine (condExp_mul_of_stronglyMeasurable_left hX (hind.integrable_mul hXi hYi) hYi).trans ?_
  filter_upwards [condExp_indep_eq hm' hm hY hi] with ω h
  rw [Pi.mul_apply, h]

/-! ### Re-associating independence -/

/-- Moving the middle factor of a triple product measure to the front:
`(μ ⊗ (ν ⊗ ρ)).map ((a, b, c) ↦ (b, a, c)) = ν ⊗ (μ ⊗ ρ)`. -/
theorem map_prod_prod_rotate {γ : Type*} {mγ : MeasurableSpace γ} (μ : Measure α)
    (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (μ.prod (ν.prod ρ)).map (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2)) = ν.prod (μ.prod ρ) := by
  have hrot : (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2))
      = MeasurableEquiv.prodAssoc ∘ Prod.map Prod.swap id ∘ MeasurableEquiv.prodAssoc.symm :=
    rfl
  rw [hrot, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
      ((measurable_swap.prodMap measurable_id).comp MeasurableEquiv.prodAssoc.symm.measurable),
    ← Measure.map_map (measurable_swap.prodMap measurable_id)
      MeasurableEquiv.prodAssoc.symm.measurable,
    ← Measure.prodAssoc_prod (μ := μ), MeasurableEquiv.map_symm_map,
    ← Measure.map_prod_map (μ.prod ν) ρ measurable_swap measurable_id, Measure.prod_swap,
    Measure.map_id, Measure.prodAssoc_prod]

/-- **Re-associating independence.** If `X` is independent of `(Y, W)` and `Y` of `W`, then `Y`
is independent of `(X, W)`. Either pair of hypotheses says that `X`, `Y` and `W` are mutually
independent: the joint law is the product of the three marginal laws. -/
theorem indepFun_prodMk_of_indepFun_prodMk {γ : Type*} {mγ : MeasurableSpace γ} {W : Ω → γ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hW : AEMeasurable W P)
    (hXYW : X ⟂ᵢ[P] fun ω ↦ (Y ω, W ω)) (hYW : Y ⟂ᵢ[P] W) :
    Y ⟂ᵢ[P] fun ω ↦ (X ω, W ω) := by
  have hXW : X ⟂ᵢ[P] W := hXYW.comp measurable_id measurable_snd
  have hrot : Measurable fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2) := by fun_prop
  rw [indepFun_iff_map_prod_eq_prod_map_map hY (hX.prodMk hW),
    hXW.map_prod_eq_prod_map_map hX hW,
    show (fun ω ↦ (Y ω, X ω, W ω))
      = (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2)) ∘ fun ω ↦ (X ω, Y ω, W ω) from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hrot.aemeasurable (hX.prodMk (hY.prodMk hW)),
    hXYW.map_prod_eq_prod_map_map hX (hY.prodMk hW), hYW.map_prod_eq_prod_map_map hY hW]
  exact map_prod_prod_rotate _ _ _

end MathFin
