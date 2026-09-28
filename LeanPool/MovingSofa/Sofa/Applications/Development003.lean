/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Applications.Development003
public import LeanPool.MovingSofa.Gerver.Applications.Development004
public import LeanPool.MovingSofa.Sofa.Applications.Development002
/-!
# Moving sofa: related mathematical developments

* `Sofa.Maximum`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver's sofa attains the maximum moving-sofa area

The paper's main theorem: Gerver's paper-frame set `paperGerverSofa` is a moving
sofa, and every moving sofa has area at most its area.

The proof splits on the certified lower bound `11 / 5`.  A sofa below that bound
is dominated outright.  A sofa at or above it is dominated by a balanced maximum
sofa of angle `π / 2`, whose cap lies in the special domain and extends to a
triple in the cap-tail space; the area functional is then bounded by `Q`, which
is maximized by Gerver's triple and matches the area functional there.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem paperGerverSofa_maximum :
    IsPaperMovingSofa paperGerverSofa ∧
      ∀ s : Set Point, IsPaperMovingSofa s →
        ClassicalResults.area s ≤ ClassicalResults.area paperGerverSofa := by
  -- `G` is a moving sofa in standard position at angle `π / 2`.
  have hstd : IsStandardPosition paperGerverSofa (Real.pi / 2) := by
    rw [gerver_capSupport_identification.2.1]
    exact gerver_capSupport_identification.2.2.1
  -- `G` is monotone, so the sofa-area identity applies to it.
  have hmono : ∃ s₀ : Set Point, IsStandardPosition s₀ (Real.pi / 2) ∧
      paperGerverSofa = monotonization s₀ (Real.pi / 2) :=
    ⟨paperGerverSofa, hstd, (gerver_paperNiche_identification.2.2.1).symm⟩
  -- The certified lower bound, transported along the path identification.
  have hG : (11 : ℝ) / 5 ≤ ClassicalResults.area paperGerverSofa := by
    rw [← gerver_canonical_paper_literal.1]
    exact gerver_area_lower_bound.2
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm, -⟩ := hstd.2.1
    exact ⟨m, hm⟩
  intro s hs
  by_cases harea : (11 : ℝ) / 5 ≤ ClassicalResults.area s
  · -- `K_G` maximizes `Q`, and `Q (K_G, B, D) = A (K_G) = |G|`.
    obtain ⟨X, hK, hB, hD, hmax⟩ := gerver_upperBoundQ_maximum
    have hGarea : rightAngleAreaFunctional X.cap.val = ClassicalResults.area paperGerverSofa :=
      capAreaFunctional_eq_sofaArea paperGerverSofa (Real.pi / 2) hmono X.cap.val hK
    -- Dominate `S` by a balanced maximum sofa of angle `π / 2`.
    obtain ⟨s', ⟨hmono', L, hL, hbalanced⟩, hdom⟩ :=
      exists_dominating_balancedRightAngleSofa s hs harea
    obtain ⟨M, hM⟩ := specialCap_isConvexDomain.2.2.1 L hbalanced
    obtain ⟨Y, rfl, hYR, hYL⟩ := exists_canonicalCapTail M
    calc
      ClassicalResults.area s ≤ ClassicalResults.area s' := hdom
      _ = rightAngleAreaFunctional L :=
        (capAreaFunctional_eq_sofaArea s' (Real.pi / 2) hmono' L hL).symm
      _ = rightAngleAreaFunctional Y.cap.val := by rw [hM]
      _ ≤ upperBoundQ Y := areaFunctional_le_upperBoundQ Y hYR hYL
      _ ≤ upperBoundQ X := hmax Y
      _ = rightAngleAreaFunctional X.cap.val := (gerver_upperBoundQ_matches X hK hB hD).symm
      _ = ClassicalResults.area paperGerverSofa := hGarea
  · exact (le_of_not_ge harea).trans hG

end MovingSofa

end

end

end
