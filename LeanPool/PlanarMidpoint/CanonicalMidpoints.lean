/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.GeodesicBVP
public import LeanPool.PlanarMidpoint.MidpointGerms
public import Mathlib.Tactic.NormNum

/-!
# Existence and restriction of canonical local midpoint maps

The small geodesic branch is constructed by the boundary-value contraction.
Consequently canonical complementarity supplies complementary curves of
arbitrarily small position and velocity size, without endpoint regularity
as an additional hypothesis.
-/

@[expose] public section

open Set Metric
open scoped ContDiff

noncomputable section

namespace PlanarMidpoint

theorem exists_arbitrarily_short_geodesic {C : E → Coeff} {p : E}
    (hC : ContDiffAt ℝ 1 C p) (σ : ℝ) (r : ℝ) (hr : 0 < r) :
    ∃ δ > (0 : ℝ), ∀ P Q, P ∈ ball p δ → Q ∈ ball p δ →
      ∃ γ v, IsShortGeodesic C σ p r P Q γ v := by
  obtain ⟨s, hs, hsr, δ, hδ, hsol⟩ := exists_unique_short_geodesic hC σ r hr
  refine ⟨δ, hδ, fun P Q hP hQ => ?_⟩
  obtain ⟨γ, v, hg, _⟩ := hsol P Q hP hQ
  exact ⟨γ, v, hg.mono_radius hsr⟩

theorem localMidpointInvariance_arbitrarilyShort
    {Ω : Set E} {C : E → Coeff} {p : E}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hC : ContDiffOn ℝ 2 C Ω)
    (hlocal : LocalMidpointInvariance Ω C) : ArbitrarilyShortComplementaryPairs C p := by
  apply arbitrarilyShortPairs_of_canonical hlocal hp
  intro σ _ r hr
  apply exists_arbitrarily_short_geodesic _ σ r hr
  exact ((hC p hp).contDiffAt (hΩ.mem_nhds hp)).of_le (by norm_num)

/-- Smooth coefficient fields genuinely have canonical local midpoint maps;
the defining predicate is witnessed by the constructed short BVP branch. -/
theorem exists_canonical_local_midpoint {Ω : Set E} {C : E → Coeff} {p : E}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hC : ContDiffAt ℝ 1 C p) (σ : ℝ) :
    ∃ r W A, IsCanonicalLocalMidpoint Ω C σ p r W A := by
  classical
  obtain ⟨η, hη, hηΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  obtain ⟨r, hr, hrη, δ, hδ, hsol⟩ := exists_unique_short_geodesic hC σ η hη
  let W : Set (E × E) := ball p δ ×ˢ ball p δ
  let A : E → E → E := fun P Q =>
    if h : (P, Q) ∈ W then (Classical.choose (hsol P Q h.1 h.2)) (1 / 2) else 0
  refine ⟨r, W, A, hr, fun x hx => hηΩ (ball_subset_ball hrη hx),
    isOpen_ball.prod isOpen_ball, ⟨mem_ball_self hδ, mem_ball_self hδ⟩, ?_⟩
  intro P Q hPQ
  let sol := hsol P Q hPQ.1 hPQ.2
  refine ⟨Classical.choose sol, Classical.choose (Classical.choose_spec sol),
    (Classical.choose_spec (Classical.choose_spec sol)).1, ?_,
    (Classical.choose_spec (Classical.choose_spec sol)).2⟩
  simp only [A, dite_eq_left hPQ]

/-- Any two canonical midpoint constructions for the same local connection
agree after restriction to a common open neighborhood of the diagonal point.
The comparison uses actual geodesics shorter than both defining radii. -/
theorem canonical_midpoint_germs_agree
    {Ω₁ Ω₂ : Set E} {C : E → Coeff} {σ : ℝ} {p : E}
    {r₁ r₂ : ℝ} {W₁ W₂ : Set (E × E)} {A₁ A₂ : E → E → E}
    (hC : ContDiffAt ℝ 1 C p)
    (hA₁ : IsCanonicalLocalMidpoint Ω₁ C σ p r₁ W₁ A₁)
    (hA₂ : IsCanonicalLocalMidpoint Ω₂ C σ p r₂ W₂ A₂) :
    ∃ W : Set (E × E), IsOpen W ∧ (p, p) ∈ W ∧ W ⊆ W₁ ∩ W₂ ∧
      ∀ P Q, (P, Q) ∈ W → A₁ P Q = A₂ P Q := by
  obtain ⟨hr₁, _, hW₁, hpp₁, hsol₁⟩ := hA₁
  obtain ⟨hr₂, _, hW₂, hpp₂, hsol₂⟩ := hA₂
  obtain ⟨δ, hδ, hsmall⟩ := exists_arbitrarily_short_geodesic hC σ
    (min r₁ r₂) (lt_min hr₁ hr₂)
  refine ⟨(W₁ ∩ W₂) ∩ (ball p δ ×ˢ ball p δ),
    (hW₁.inter hW₂).inter (isOpen_ball.prod isOpen_ball),
    ⟨⟨hpp₁, hpp₂⟩, mem_ball_self hδ, mem_ball_self hδ⟩, inter_subset_left, ?_⟩
  intro P Q hPQ
  obtain ⟨γ, v, hg⟩ := hsmall P Q hPQ.2.1 hPQ.2.2
  obtain ⟨γ₁, v₁, _, hm₁, hu₁⟩ := hsol₁ P Q hPQ.1.1
  obtain ⟨γ₂, v₂, _, hm₂, hu₂⟩ := hsol₂ P Q hPQ.1.2
  have he₁ := (hu₁ γ v (hg.mono_radius (min_le_left _ _)) (1 / 2) (by norm_num)).1
  have he₂ := (hu₂ γ v (hg.mono_radius (min_le_right _ _)) (1 / 2) (by norm_num)).1
  rw [hm₁, hm₂, ← he₁, ← he₂]

end PlanarMidpoint
