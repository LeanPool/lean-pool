/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEtaGapSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffBounds

/-!
# Plateau of the short-time cutoff

In the spatial interior, after the lower-time transition, and above the
phase gap, the compact cutoff is locally constant one.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The open plateau of the full compact cutoff. -/
@[expose] def buShortCoreRegion (scale R ε : ℝ) : Set (Vec3 × ℝ) :=
  {q | q.1 ∈ vec3Ball 0 R ∧ q ∈ buShortAboveGap scale ∧
    1 / 2 + 2 * ε < q.2}

/-- The cutoff plateau is open. -/
theorem buShortCoreRegion_isOpen (scale R ε : ℝ) :
    IsOpen (buShortCoreRegion scale R ε) := by
  have hball : IsOpen {q : Vec3 × ℝ | q.1 ∈ vec3Ball 0 R} :=
    (isOpen_vec3Ball 0 R).preimage continuous_fst
  have htime : IsOpen {q : Vec3 × ℝ | 1 / 2 + 2 * ε < q.2} :=
    isOpen_lt continuous_const continuous_snd
  change IsOpen ({q | q.1 ∈ vec3Ball 0 R} ∩
    (buShortAboveGap scale ∩ {q | 1 / 2 + 2 * ε < q.2}))
  exact hball.inter ((buShortAboveGap_isOpen scale).inter htime)

/-- All three cutoff factors equal one on the plateau. -/
theorem buShortFullCutoff_eq_one_on_core
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    EqOn (buShortFullCutoff scale R hR ε) (fun _ => 1)
      (buShortCoreRegion scale R ε) := by
  intro q hq
  rcases hq with ⟨hball, hgap, htime⟩
  have hχ : ucSpatialCutoff (2 * R) (by positivity) q.1 = 1 := by
    apply ucSpatialCutoff_eq_one (show 0 < 2 * R by positivity)
    simpa only [show 2 * R / 2 = R by ring] using hball
  have hη : buShortEtaExt scale q = 1 :=
    buShortEtaExt_eq_one_on_aboveGap hscale hscale1 hgap
  have hθ : buShortTimeCutoff ε q.2 = 1 := by
    apply ucInitialTimeCutoff_eq_one hε
    linarith only [htime]
  unfold buShortFullCutoff
  rw [hχ, hη, hθ]
  norm_num

/-- The first, second, and time derivatives of the full cutoff vanish
throughout its open plateau. -/
theorem buShortFullCutoff_derivatives_zero_on_core
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortCoreRegion scale R ε) :
    (∀ j : Fin 3,
      spatialPartial (buCutScalar (buShortFullCutoff scale R hR ε)) j z = 0) ∧
    (∀ j k : Fin 3,
      spatialSecondPartial (buCutScalar (buShortFullCutoff scale R hR ε)) j k z = 0) ∧
    timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z = 0 := by
  exact buCutScalar_derivatives_eq_zero_of_eqOn
    (buShortCoreRegion_isOpen scale R ε)
    (buShortFullCutoff_eq_one_on_core scale R ε hscale hscale1 hR hε)
    hz

end ESS
