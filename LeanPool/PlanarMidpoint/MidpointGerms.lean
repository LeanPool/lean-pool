/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.GeodesicDefinitions
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Tactic.NormNum

/-! Restricting canonical midpoint germs to arbitrarily small geodesic neighborhoods. -/

@[expose] public section

open Set Metric

namespace PlanarMidpoint

theorem IsShortGeodesic.mono_radius {C : E → Coeff} {σ r s : ℝ}
    {p P Q : E} {γ v : ℝ → E}
    (h : IsShortGeodesic C σ p r P Q γ v) (hrs : r ≤ s) :
    IsShortGeodesic C σ p s P Q γ v := by
  obtain ⟨hg, h0, h1, hb⟩ := h
  refine ⟨hg, h0, h1, fun t ht => ?_⟩
  exact ⟨(hb t ht).1.trans_le hrs, (hb t ht).2.trans_le hrs⟩

/-- Canonical uniqueness identifies all sufficiently small representatives.
The small-solution existence premise is supplied by the local BVP theorem. -/
theorem arbitrarilyShortPairs_of_canonical
    {Ω : Set E} {C : E → Coeff} {p : E}
    (hlocal : LocalMidpointInvariance Ω C) (hp : p ∈ Ω)
    (hexists : ∀ σ ∈ ({1, -1} : Set ℝ), ∀ r > (0 : ℝ),
      ∃ δ > (0 : ℝ), ∀ P Q, P ∈ ball p δ → Q ∈ ball p δ →
        ∃ γ v, IsShortGeodesic C σ p r P Q γ v) :
    ArbitrarilyShortComplementaryPairs C p := by
  obtain ⟨rp, rm, W, Ap, Am, hAp, hAm, hcomp⟩ := hlocal p hp
  obtain ⟨hrp, _, hW, hpp, hplus⟩ := hAp
  obtain ⟨hrm, _, _, _, hminus⟩ := hAm
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hW (p, p) hpp
  intro r hr
  let s := min r (min rp rm)
  have hs : 0 < s := lt_min hr (lt_min hrp hrm)
  obtain ⟨dp, hdp, hpSol⟩ := hexists 1 (by simp) s hs
  obtain ⟨dm, hdm, hmSol⟩ := hexists (-1) (by simp) s hs
  refine ⟨min e (min dp dm), lt_min he (lt_min hdp hdm), ?_⟩
  intro P Q hP hQ
  have hPe : P ∈ ball p e := mem_ball.mpr ((mem_ball.mp hP).trans_le (min_le_left _ _))
  have hQe : Q ∈ ball p e := mem_ball.mpr ((mem_ball.mp hQ).trans_le (min_le_left _ _))
  have hPQ : (P, Q) ∈ W := hball (by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (mem_ball.mp hPe) (mem_ball.mp hQe))
  have hPp : P ∈ ball p dp := mem_ball.mpr
    ((mem_ball.mp hP).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hQp : Q ∈ ball p dp := mem_ball.mpr
    ((mem_ball.mp hQ).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hPm : P ∈ ball p dm := mem_ball.mpr
    ((mem_ball.mp hP).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hQm : Q ∈ ball p dm := mem_ball.mpr
    ((mem_ball.mp hQ).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨γp, vp, hgp⟩ := hpSol P Q hPp hQp
  obtain ⟨γm, vm, hgm⟩ := hmSol P Q hPm hQm
  obtain ⟨γp', vp', _, hmp, hup⟩ := hplus P Q hPQ
  obtain ⟨γm', vm', _, hmm, hum⟩ := hminus P Q hPQ
  have heqp := (hup γp vp (hgp.mono_radius ((min_le_right _ _).trans (min_le_left _ _)))
    (1 / 2) (by norm_num)).1
  have heqm := (hum γm vm (hgm.mono_radius ((min_le_right _ _).trans (min_le_right _ _)))
    (1 / 2) (by norm_num)).1
  refine ⟨γp, vp, γm, vm, hgp.mono_radius (min_le_left _ _),
    hgm.mono_radius (min_le_left _ _), ?_⟩
  rw [heqp, heqm, ← hmp, ← hmm]
  exact hcomp P Q hPQ

end PlanarMidpoint
