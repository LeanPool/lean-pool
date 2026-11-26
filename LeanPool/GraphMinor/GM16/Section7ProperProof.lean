/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section7
public import LeanPool.GraphMinor.GM16.ProperEyeInduction
import LeanPool.GraphMinor.GM16.VortexComparison
import LeanPool.GraphMinor.GM16.Section3
import LeanPool.GraphMinor.GM11.PlaneFacts

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Bridge

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Bridge

import LeanPool.GraphMinor.GM15.Section3Crosscap

import LeanPool.GraphMinor.GM15.Section3Parallel

/-!
# Graph Minors XVI (7.2)

We follow XV (8.4), using XV (8.3) to pass from level spans to flat
spans and XV (8.1) to replace independent eyes by a controlled clique.
The arrangement outcome retains properness from its construction in
XV (7.7), as the proof of XVI (7.2), page 62, requires.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- Graph Minors XVI, (7.2), page 62. The properness omitted from the
statement of XV (8.4) is proved at the construction of its arrangements
in XV (7.7) and retained through the downward eye induction. -/
theorem theorem_7_2_proof
     :
    GM16Theorem72Statement.{u, v, w} := by
  intro S _ _ hClosed hConn p φ μ
  have hSurf : IsSurface S := hClosed.isSurface
  have hBd : bd S = ∅ := by
    ext x
    exact iff_false_intro (fun hx => hx (hClosed.2.2 x))
  let p4 := max p 4
  obtain ⟨κ, φ₁, hClique⟩ := GM15.theorem_8_1_proof S hSurf hConn hBd p4
  let φ₂ := max φ φ₁
  obtain ⟨θ₁, lam, ρ, hMain⟩ :=
    proper_arrangement_or_independent_eyes_or_crosscap
      S hSurf hConn hBd κ φ₂ μ
  let θ := max (max θ₁ p4) (4 * (lam + μ + 2) + 3)
  refine ⟨κ, lam + μ + 2, ρ, θ, ?_, ?_⟩
  · dsimp [θ]; omega
  intro α β G θ_star θ_span T_star H η T d hT hθ hLevel
  have hθ₁ : θ₁ ≤ θ_span := (le_max_left _ _).trans ((le_max_left _ _).trans hθ)
  have hp4 : p4 ≤ θ_star :=
    ((le_max_right θ₁ p4).trans ((le_max_left _ _).trans hθ)).trans
      hLevel.isSpan.isControlling.theta_le
  have hFlat : IsFlatSpan G H η θ_star θ_span lam μ T_star T :=
    GM15.theorem_8_3_proof G H η θ_star θ_span lam μ T_star T d
      (by have := (le_max_right (max θ₁ p4) (4 * (lam + μ + 2) + 3)).trans hθ; omega)
      hLevel
  rcases hMain G θ_star T_star H η θ_span T d hFlat hLevel.hasMetric hθ₁ with
    ⟨H', η', θ', T', d', hSpan', hMetric', hφ₂, hEyes⟩ |
    ⟨S', hTS', hT2S', hCross, H', η', θ', T', hφ₂, hSpan'⟩ |
    ⟨𝒮, disc, pt, hCentral, hType, hProper⟩
  · right; right
    have hMinor : ControlsCliqueMinor G p4 T_star :=
      hClique G θ_star T_star H' η' θ' T' d' hSpan' hMetric' hp4
        ((le_max_right φ φ₁).trans hφ₂) (hEyes.mono (Nat.le_succ κ))
    have hβ : Nonempty β := by
      obtain ⟨X, _, _, hlink, _⟩ := hMinor
      obtain ⟨e, _⟩ := hlink ⟨0, by dsimp [p4]; omega⟩ ⟨1, by dsimp [p4]; omega⟩
        (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
      exact ⟨e⟩
    exact controlsMinor_of_controlsCliqueMinor (Or.inr hβ) (hMinor.mono (le_max_left p 4))
  · left
    have hClosed' : IsClosedSurface S' :=
      ⟨hSpan'.isSurface.1, hSpan'.isSurface.2.1, fun x => by
        by_contra hx
        exact Set.eq_empty_iff_forall_notMem.mp hSpan'.bd_empty x hx⟩
    exact ⟨S', hTS', hT2S', H', η', θ', T', hClosed', hSpan'.isConnected,
      hCross, (le_max_left φ φ₁).trans hφ₂, hSpan'⟩
  · right; left
    exact ⟨𝒮, disc, pt, hCentral, isSegregationOfType_of_gm15 hType, hProper⟩

end GraphMinor.GM16
