/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortErrorL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCompact

/-!
# Compact support in the Carleman cylinder

The scalar cutoff support lies strictly inside the half-space and strictly
between the shifted initial and final times.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The parabolic support of the short-time scalar cutoff is compact and
lies inside the half-space Carleman cylinder. -/
theorem bu_short_cutoff_support_geometry
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    IsCompact (buCutSupportSet (buShortFullCutoff scale R hR ε)) ∧
      buCutSupportSet (buShortFullCutoff scale R hR ε) ⊆
        halfSpaceDomain ∧
      buCutSupportSet (buShortFullCutoff scale R hR ε) ⊆
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1) := by
  obtain ⟨hκcompact, hκts⟩ :=
    buShortFullCutoff_compact_support hscale hscale1 hR hε
  have hKcompact : IsCompact
      (buCutSupportSet (buShortFullCutoff scale R hR ε)) := by
    dsimp [buCutSupportSet]
    exact parabolicHomeomorph.isCompact_preimage.mpr hκcompact.isCompact
  constructor
  · exact hKcompact
  constructor
  · intro z hz
    have hq := hκts hz
    rcases z with ⟨y, s⟩
    change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hq
    exact ⟨hq.1, (by linarith only [hq.2.1]), hq.2.2⟩
  · intro z hz
    have hq := hκts hz
    rcases z with ⟨y, s⟩
    change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hq
    exact ⟨lt_trans (by norm_num : (0 : ℝ) < 1) hq.1, hq.2⟩

end ESS
