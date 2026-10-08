/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortParameterLimits

/-!
# Uniform cutoff plateau around a compact region

A compact subset above the negative phase gap lies in the plateau of
every sufficiently wide spatial cutoff and every sufficiently short
lower-time cutoff.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A compact region above the phase gap stays in the open cutoff
plateau for all large radii and small lower-time widths. -/
theorem bu_short_compact_subset_core_eventually
    (scale : ℝ) (S : Set ParabolicPoint)
    (hScompact : IsCompact S) (hSne : S.Nonempty)
    (hSgap : ∀ z ∈ S,
      parabolicHomeomorph z ∈ buShortAboveGap scale) :
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧
      ∀ R : ℝ, R₀ ≤ R →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∀ z ∈ S,
          parabolicHomeomorph z ∈ buShortCoreRegion scale R ε := by
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have hnorm : Continuous (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1) :=
    continuous_vec3EuclideanNorm.comp hspace
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  obtain ⟨zR, hzR, hRmax⟩ :=
    hScompact.exists_isMaxOn hSne hnorm.continuousOn
  obtain ⟨zt, hzt, htmin⟩ :=
    hScompact.exists_isMinOn hSne htime.continuousOn
  have htpos : 1 / 2 < zt.2 := (hSgap zt hzt).2.1
  let R₀ := max 1 (vec3EuclideanNorm zR.1) + 1
  let ε₀ := (zt.2 - 1 / 2) / 4
  have hR₀ : 1 ≤ R₀ := by
    dsimp [R₀]
    have h := le_max_left (1 : ℝ) (vec3EuclideanNorm zR.1)
    linarith only [h]
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith only [htpos]
  refine ⟨R₀, ε₀, hR₀, hε₀, ?_⟩
  intro R hR ε hε hεsmall z hz
  have hnormz : vec3EuclideanNorm z.1 ≤ vec3EuclideanNorm zR.1 :=
    hRmax hz
  have hnormR : vec3EuclideanNorm z.1 < R := by
    have hmax : vec3EuclideanNorm zR.1 ≤
        max 1 (vec3EuclideanNorm zR.1) := le_max_right _ _
    dsimp [R₀] at hR
    linarith only [hnormz, hmax, hR]
  have hball : z.1 ∈ vec3Ball 0 R := by
    apply (mem_vec3Ball).2
    simpa only [sub_zero] using hnormR
  have htimez : zt.2 ≤ z.2 := htmin hz
  have hlate : 1 / 2 + 2 * ε < z.2 := by
    dsimp [ε₀] at hεsmall
    linarith only [hεsmall, htimez, htpos]
  exact ⟨hball, hSgap z hz, hlate⟩

end ESS
