/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShellLimit

/-!
# Lower normal height of the compact cutoff support

The compact cutoff support remains above the closed lower edge of its
normal transition.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The high normal strip containing all compact short-time cutoffs. -/
@[expose] def buShortHighStrip (scale : ℝ) : Set ParabolicPoint :=
  {z | buShortYMinus scale ≤ z.1 2 ∧
    (1 / 2 : ℝ) < z.2 ∧ z.2 < 1}

/-- Every point of the compact cutoff support is at or above the lower
normal transition height. -/
theorem buShortCutSupport_height_lower
    (scale R ε : ℝ) (hR : 0 < R)
    {z : ParabolicPoint}
    (hz : z ∈ buCutSupportSet (buShortFullCutoff scale R hR ε)) :
    buShortYMinus scale ≤ z.1 2 := by
  let κ := buShortFullCutoff scale R hR ε
  let H : Set (Vec3 × ℝ) :=
    {q | buShortYMinus scale ≤ q.1 2}
  have hHclosed : IsClosed H := by
    exact isClosed_le continuous_const
      ((continuous_apply 2).comp continuous_fst)
  have hsupport : Function.support κ ⊆ H := by
    intro q hq
    by_contra hnot
    have hlow : q.1 2 ≤ buShortYMinus scale := le_of_not_ge hnot
    have hzero : buShortNormalCutoff scale (q.1 2) = 0 :=
      buShortNormalCutoff_eq_zero hlow
    apply hq
    dsimp [κ, buShortFullCutoff, buShortEtaExt]
    rw [hzero]
    ring
  have hts : tsupport κ ⊆ H :=
    closure_minimal hsupport hHclosed
  exact hts hz

/-- The support of every compact short-time cutoff lies in the high
normal strip. -/
theorem buShortCutSupport_subset_highStrip
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    buCutSupportSet (buShortFullCutoff scale R hR ε) ⊆
      buShortHighStrip scale := by
  intro z hz
  have hheight := buShortCutSupport_height_lower scale R ε hR hz
  have htime :=
    (bu_short_cutoff_support_geometry scale R ε
      hscale hscale1 hR hε).2.2 hz
  exact ⟨hheight, htime.2⟩

/-- The high normal strip is measurable. -/
theorem buShortHighStrip_measurable (scale : ℝ) :
    MeasurableSet (buShortHighStrip scale) := by
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have hheight : Continuous (fun z : ParabolicPoint => z.1 2) :=
    (continuous_apply 2).comp hspace
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  unfold buShortHighStrip
  have h₁ := (isClosed_le (continuous_const : Continuous
    (fun _ : ParabolicPoint => buShortYMinus scale)) hheight).measurableSet
  have h₂ := (isOpen_lt (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 / 2 : ℝ))) htime).measurableSet
  have h₃ := (isOpen_lt htime (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 : ℝ)))).measurableSet
  simpa only [Set.ofPred_and] using h₁.inter (h₂.inter h₃)

/-- The negative phase gap is contained in the high normal strip. -/
theorem buShortWideGapRegion_subset_highStrip (scale : ℝ) :
    buShortWideGapRegion scale ⊆ buShortHighStrip scale := by
  intro z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.1⟩

end ESS
