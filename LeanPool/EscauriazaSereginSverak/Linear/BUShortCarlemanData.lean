/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendWeak
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFieldSupport

/-!
# Weak data on the full half-space cylinder

The short-time cutoff field extends across its artificial lower time face
while retaining compact support and global quadratic derivative data.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The cutoff field has weak derivative data on the full half-space
Carleman cylinder, with compact support and global `L²` bounds. -/
theorem bu_short_cutoff_carleman_data
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
    let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    HasSpaceTimeWeakDerivs {x : Vec3 | 1 < x 2} (Ioo 0 1)
      W DW D2W DtW ∧
    HasCompactSupport W ∧
    tsupport W ⊆ spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1) ∧
    MemLp W 2 volume ∧ MemLp DW 2 volume ∧
      MemLp D2W 2 volume ∧ MemLp DtW 2 volume := by
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  obtain ⟨hκcompact, hκts⟩ :=
    buShortFullCutoff_compact_support hscale hscale1 hR hε
  have hKcompact : IsCompact K := by
    dsimp [K, buCutSupportSet]
    exact parabolicHomeomorph.isCompact_preimage.mpr hκcompact.isCompact
  have hKsource : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) 1) := by
    intro z hz
    have hq := hκts hz
    rcases z with ⟨y, s⟩
    change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hq
    exact ⟨lt_trans (by norm_num : (0 : ℝ) < 1) hq.1, hq.2⟩
  have hKtarget : K ⊆ spaceTimeSet {x : Vec3 | 1 < x 2}
      (Ioo (0 : ℝ) 1) := by
    intro z hz
    have hq := hκts hz
    rcases z with ⟨y, s⟩
    change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hq
    exact ⟨hq.1, (by linarith only [hq.2.1]), hq.2.2⟩
  have hzero (z : ParabolicPoint) (hz : z ∉ K) :
      W z = 0 ∧ DW z = 0 ∧ D2W z = 0 ∧ DtW z = 0 :=
    buCut_data_zero_off_support κ v Dv D2v Dtv z hz
  have hweakCut : HasSpaceTimeWeakDerivs
      {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1)
      W DW D2W DtW :=
    bu_short_cutoff_weak_derivatives scale R ε hscale hscale1 hR
      w Dw D2w Dtw hweak
  have hmem : MemLp W 2 volume ∧ MemLp DW 2 volume ∧
      MemLp D2W 2 volume ∧ MemLp DtW 2 volume :=
    bu_short_cutoff_memLp_data scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  have hweakTarget := bu_weak_extend_compact
    (isOpen_lt continuous_const (continuous_apply 2)) isOpen_Ioo
    hKcompact hKsource hKtarget W DW D2W DtW hzero hweakCut hmem
  obtain ⟨hcompact, htsupport⟩ :=
    bu_short_cutoff_field_support hscale hscale1 hR hε v
  exact ⟨hweakTarget, hcompact, htsupport,
    hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2⟩

end ESS
