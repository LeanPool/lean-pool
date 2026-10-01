/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAt
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.UnboundedTruncations

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Injectivity of translated truncation on `P_α` for successor `α`

For every `α`, `∂` is injective on `P_{α+1}` (Berarducci's Lem. 6.8 in the present language).
Let `α = β + 1` be a successor ordinal and `u` a series with `v_J(u) = ω^α = ω^β · ω`. A
sufficiently short support tail `B` of `u` is order isomorphic to `ω` copies of `ω^β`. Let `S`
be its first block, the set of points of `B` of index below `ω^β`, and let `γ = sup S`. Then
`v_J(u^{|γ}) = ω^β`:

* if `β = 0`, then `S` is a single support point `γ`, so `u^{|γ}` has nonzero constant term and
  support otherwise bounded away from zero;
* if `β ≥ 1`, then `ω^β` is a limit, `S` has no largest element, the exponents of `u^{|γ}`
  immediately below zero are the translates of final segments of `S`, and every nonempty final
  segment of `S` has order type `ω^β` because `ω^β` is additively indecomposable.

Applying this to the tail above any `θ < 0` produces cutoffs `γ ∈ (θ, 0)` at which
`∂(u)(γ) = u^{|γ} + J_{ω^β}` is nonzero, so `∂(B) ≠ 0` for every nonzero `B ∈ P_α`.
-/

open Filter Topology Ordinal
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open Berarducci HahnSeries

variable {K : Type v} [Field K]

/-- If `v_J(u) = ω^(β+1)` and `θ < 0`, there is a cutoff `θ < γ < 0` with
`v_J(u^{|γ}) = ω^β`. -/
@[blueprint "lem:successor-truncation-value"
  (phase := "Translated truncations")
  (title := "Translated truncations of successor ordinal value")
  (statement := /--
    Let $\beta<\omega_1$ and $b\in K((\mathbb R^{\le0}))$. If
    $v_J(b)=\omega^{\beta+1}$, then for every $\theta<0$ there is
    $\gamma\in(\theta,0)$ such that $v_J(b^{|\gamma})=\omega^\beta$.
  -/)
  (proof := /--
  By \ref{fact:ordinal-value-support-tail}, choose above $\theta$ a support
  tail $B$ of order type
  $\omega^{\beta+1}=\omega^\beta\cdot\omega$. Let $S$ be its initial block
  of order type $\omega^\beta$, and put $\gamma=\sup S$.

  If $\beta=0$, then $S=\{\gamma\}$. The translated truncation has a non-zero
  constant coefficient and a gap immediately below zero, so its ordinal value
  is $1$.

  If $\beta>0$, then $\omega^\beta$ is an additively principal limit ordinal.
  The set $S$ is a final segment of the support below $\gamma$, giving
  $v_J(b^{|\gamma})\le\omega^\beta$. Every interval immediately below
  $\gamma$ contains a final segment of $S$, still of order type
  $\omega^\beta$, giving the reverse inequality. Thus
  $v_J(b^{|\gamma})=\omega^\beta$, and the choice of $B$ gives
  $\theta<\gamma<0$.
  -/)]
theorem exists_ordinalValue_translatedTruncation_eq_wpow_of_ordinalValue_eq_wpow_add_one
    (beta : NatOrdinal) (u : Series K) (hu : ordinalValue u = ω^ (beta + 1))
    {θ : ℝ} (hθ : θ < 0) :
    ∃ γ : ℝ, θ < γ ∧ γ < 0 ∧ ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) = ω^ beta := by
  exact exists_ordinalValue_translatedTruncation_eq_wpow_of_lt (lt_add_one beta) u hu hθ

/-- A nonzero class in `P_α`, for successor `α`, has a representative of ordinal value exactly
`ω^α`. -/
theorem ordinalValue_eq_wpow_of_principalComponentMk_ne_zero (alpha : NatOrdinal)
    (u : Series K) (hu : ordinalValue u < ω^ (alpha + 1))
    (hne : principalComponentMk alpha u hu ≠ 0) :
    ordinalValue u = ω^ alpha := by
  have hnot : ¬ ordinalValue u < ω^ alpha := fun h ↦
    hne ((principalComponentMk_eq_zero_iff alpha u hu).mpr h)
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal u with hzero | hprincipal
  · exact absurd (hzero ▸ NatOrdinal.wpow_pos alpha) hnot
  · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprincipal
    rw [NatOrdinal.of_val] at hxi
    rw [hxi] at hu hnot ⊢
    rw [NatOrdinal.wpow_inj]
    exact le_antisymm (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hu))
      (not_lt.mp fun h ↦ hnot (NatOrdinal.wpow_lt_wpow.mpr h))

/-- If `α` is a successor, translated truncation sends every nonzero class in `P_α` to a nonzero
function at `0⁻`. -/
theorem principalComponentDerivAt_ne_zero
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    {x : PrincipalComponent K alpha} (hx : x ≠ 0) :
    principalComponentDerivAt K alpha halpha x ≠ 0 := by
  obtain ⟨u, hu, rfl⟩ := exists_principalComponentMk alpha x
  have hvalue := ordinalValue_eq_wpow_of_principalComponentMk_ne_zero alpha u hu hx
  have halpha' : alpha.removeNat 1 + 1 = alpha := by
    simpa using NatOrdinal.removeNat_add_natCast halpha
  rw [principalComponentDerivAt_principalComponentMk]
  intro hzero
  obtain ⟨θ, hθ, hθzero⟩ := (FunAtZeroMinus.coe_eq_zero_iff_exists _).mp hzero
  obtain ⟨γ, hθγ, hγ0, hγvalue⟩ :=
    exists_ordinalValue_translatedTruncation_eq_wpow_of_ordinalValue_eq_wpow_add_one
        (alpha.removeNat 1) u
      (by rw [hvalue, halpha']) hθ
  have hbound : ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) < ω^ (alpha.removeNat 1 + 1) := by
    rw [hγvalue]
    exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)
  have hcut := hθzero γ hθγ hγ0
  rw [derivAt_eq alpha u γ hbound, principalComponentMk_eq_zero_iff, hγvalue] at hcut
  exact lt_irrefl _ hcut

variable (K) in
/-- Translated truncation is injective on `P_α` for every successor ordinal `α`. -/
@[blueprint "prop:successor-principal-rv-injective"
  (phase := "Translated truncations")
  (title := "Injectivity of the translated-truncation map on $\\mathrm P_\\alpha$")
  (statement := /--
    Let $K$ be a field, let $\alpha<\omega_1$ be a successor ordinal, and write
    $\alpha=\beta+1$. Put
    \[
      \mathrm P_\delta:=J_{\omega^{\delta+1}}/J_{\omega^\delta}.
    \]
    Let $\operatorname{Fun}_{0^-}(V)$ be the space of $V$-valued functions on
    intervals $(\eta,0)$, identified when they agree sufficiently close to $0$.
    Then the $K$-linear map
    \[
      \partial_\alpha:\mathrm P_\alpha\longrightarrow
        \operatorname{Fun}_{0^-}(\mathrm P_\beta),\qquad
      \partial_\alpha([b])=[\gamma\mapsto[b^{|\gamma}]],
    \]
    is injective. The inner class is taken modulo $J_{\omega^\beta}$.
  -/)
  (proof := /--
  By \ref{lem:truncation-drop}, every series of ordinal value below
  $\omega^\alpha$ has translated truncations of ordinal value below $\omega^\beta$
  sufficiently close to $0$. Thus translated truncation induces the displayed map on the
  quotient.

  A nonzero class $[b]\in\mathrm P_\alpha$ has a representative with
  $v_J(b)=\omega^\alpha$. By
  \ref{lem:successor-truncation-value}, every interval $(\theta,0)$ contains
  a cutoff $\gamma$ with $v_J(b^{|\gamma})=\omega^\beta$. Hence
  $[b^{|\gamma}]\ne0$ in $\mathrm P_\beta$, so
  $\partial_\alpha([b])\ne0$. The kernel of the linear map
  $\partial_\alpha$ is therefore zero, and the map is injective.
  -/)]
theorem principalComponentDerivAt_injective
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    Function.Injective (principalComponentDerivAt K alpha halpha) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  exact principalComponentDerivAt_ne_zero alpha halpha hne hx

end Berarducci
