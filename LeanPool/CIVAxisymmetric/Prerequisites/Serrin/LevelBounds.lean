/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.LocalSteps
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.WeightedAbsorption

/-!
# The level bounds of the interior estimates

On an annular cylinder `{a < |x| < b} × (t₁, 0)` inside the unit cylinder where the velocity is
bounded, the vorticity and its first two spatial derivatives are bounded on every smaller annular
cylinder, uniformly up to the top time `t = 0`. Each level is the weighted absorption applied to
the corresponding local step. These are the level bounds of the interior estimates in the proof
of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The absorption step shared by the three levels: a nonnegative level function, continuous on
the unit cylinder, that satisfies a local circular estimate on backward windows inside the
annular cylinder is bounded on every smaller annular cylinder. -/
theorem level_bound_of_local {g : ParabolicPoint → ℝ} {a b t₁ c₁ c₂ : ℝ}
    (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgc : ContinuousOn (fun z : Vec3 × ℝ => g z) unitCylinder)
    (hstep : ∀ (x : Vec3) (s ρ Λ : ℝ), 0 < ρ → ρ ≤ 1 →
      (∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' → s' ≤ s →
        a < vec3EuclideanNorm y ∧ vec3EuclideanNorm y < b ∧ t₁ < s' ∧ s' < 0 ∧ g (y, s') ≤ Λ) →
      g (x, s) ≤ c₁ * ρ * Λ + c₂ / ρ)
    {a' b' t₁' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) (ht₁' : t₁ < t₁' ∧ t₁' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁' 0, g (x, s) ≤ K := by
  obtain ⟨ha0, hab0, hb1⟩ := hab
  obtain ⟨hta, htb⟩ := ht₁
  obtain ⟨ha', hab'', hb'⟩ := hab'
  obtain ⟨ht1', ht1'0⟩ := ht₁'
  obtain ⟨K, hK⟩ := exists_bound_of_weighted_absorption (g := g) (a := (a + a') / 2)
    (b := (b' + b) / 2) (a' := a') (b' := b') (t₁ := t₁') (τ := (t₁' - t₁) / 2)
    (c₁ := c₁) (c₂ := c₂)
    ⟨by linarith only [ha0, ha'], by linarith only [ha'], hab'', by linarith only [hb'],
      by linarith only [hb', hb1]⟩ (by linarith only [ht1']) ht1'0 hc₁ hc₂
    (hgc.mono (by
      rintro ⟨y, t⟩ ⟨⟨hy1, hy2⟩, ht1, ht2⟩
      refine ⟨?_, ?_, ?_⟩
      · change vec3EuclideanNorm (y - 0) < 1
        rw [sub_zero]; linarith only [hy2, hb', hb1]
      · change -1 < t; linarith only [ht1, hta, ht1']
      · exact ht2))
    (by
      intro x s ρ Λ hx1 hx2 hs1 hs2 hρ hρ1 hρτ hball hΛ
      refine (abs_of_nonneg (hg0 _)).le.trans ?_
      refine hstep x s ρ Λ hρ hρ1 (fun y s' hy hs'1 hs'2 => ?_)
      obtain ⟨hy1, hy2⟩ := hball y hy
      refine ⟨by linarith only [hy1, ha'], by linarith only [hy2, hb'], ?_,
        by linarith only [hs'2, hs2], (le_abs_self _).trans (hΛ y s' hy hs'1 hs'2)⟩
      linarith only [hs'1, hρτ, hs1, ht1'])
  exact ⟨K, fun x h1 h2 s hs => (le_abs_self _).trans (hK x h1 h2 s hs.1.le hs.2)⟩

/-- A point of the annular cylinder lies in the unit cylinder. -/
theorem mem_unitCylinder_of_annulus {b t₁ : ℝ} (hb1 : b < 1) (ht₁ : -1 < t₁) {y : Vec3}
    {s : ℝ} (hy : vec3EuclideanNorm y < b) (hs : t₁ < s) (hs0 : s < 0) :
    ((y, s) : ParabolicPoint) ∈ unitCylinder := by
  refine ⟨?_, ?_, hs0⟩
  · change vec3EuclideanNorm (y - 0) < 1
    rw [sub_zero]; linarith only [hy, hb1]
  · linarith only [hs, ht₁]

/-- Level zero: the vorticity is bounded on every smaller annular cylinder. -/
theorem LV0_level0 {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) {Mf : ℝ}
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf)
    {a b t₁ Mu : ℝ} (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0)
    (hu : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu)
    {a' b' t₁' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) (ht₁' : t₁ < t₁' ∧ t₁' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁' 0, vortSum0 u (x, s) ≤ K := by
  obtain ⟨C, hC, hLS⟩ := LS0_local_level0
  set Mu' : ℝ := max Mu 0
  set Mf' : ℝ := max Mf 0
  have hMu' : 0 ≤ Mu' := le_max_right _ _
  have hMf' : 0 ≤ Mf' := le_max_right _ _
  have hMfx : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf' := fun z hz i α hα =>
    (hMf z hz i α hα).trans (le_max_left _ _)
  refine level_bound_of_local hab ht₁ (c₁ := C * (1 + Mu')) (c₂ := C * (1 + Mu' + Mf'))
    (by positivity) (by positivity) (fun z => (levelSums_nonneg u z).1)
    (continuousOn_levelSums hcl.1).1 ?_ hab' ht₁'
  intro x s ρ Λ hρ hρ1 hw
  exact hLS u p f hcl Mf' Mu' hMfx x s ρ Λ hρ hρ1 (fun y s' hy hs'1 hs'2 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw y s' hy hs'1 hs'2
    exact ⟨mem_unitCylinder_of_annulus hab.2.2 ht₁.1 h2 h3 h4,
      fun i => (hu y h1 h2 s' ⟨h3, h4⟩ i).trans (le_max_left _ _), h5⟩)

/-- Level one: the first spatial derivatives of the vorticity are bounded on every smaller
annular cylinder. -/
theorem LV1_level1 {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) {Mf : ℝ}
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf)
    {a b t₁ Mu Ω₀ : ℝ} (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0)
    (hu : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu)
    (hω₀ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, vortSum0 u (x, s) ≤ Ω₀)
    {a' b' t₁' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) (ht₁' : t₁ < t₁' ∧ t₁' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁' 0, vortSum1 u (x, s) ≤ K := by
  obtain ⟨C, hC, hLS⟩ := LS1_local_level1
  set Mu' : ℝ := max Mu 0
  set Mf' : ℝ := max Mf 0
  set Ω₀' : ℝ := max Ω₀ 0
  have hMu' : 0 ≤ Mu' := le_max_right _ _
  have hMf' : 0 ≤ Mf' := le_max_right _ _
  have hΩ₀' : 0 ≤ Ω₀' := le_max_right _ _
  have hMfx : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf' := fun z hz i α hα =>
    (hMf z hz i α hα).trans (le_max_left _ _)
  refine level_bound_of_local hab ht₁ (c₁ := C * (1 + Mu' + Ω₀'))
    (c₂ := C * (1 + Mu' + Ω₀' + Mf') ^ 2) (by positivity) (by positivity)
    (fun z => (levelSums_nonneg u z).2.1) (continuousOn_levelSums hcl.1).2.1 ?_ hab' ht₁'
  intro x s ρ Λ hρ hρ1 hw
  have h := hLS u p f hcl Mf' Mu' Ω₀' hMfx x s ρ Λ hρ hρ1 (fun y s' hy hs'1 hs'2 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw y s' hy hs'1 hs'2
    exact ⟨mem_unitCylinder_of_annulus hab.2.2 ht₁.1 h2 h3 h4,
      fun i => (hu y h1 h2 s' ⟨h3, h4⟩ i).trans (le_max_left _ _),
      (hω₀ y h1 h2 s' ⟨h3, h4⟩).trans (le_max_left _ _), h5⟩)
  refine h.trans (le_of_eq ?_)
  ring

/-- Level two: the second spatial derivatives of the vorticity are bounded on every smaller
annular cylinder. -/
theorem LV2_level2 {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder) {Mf : ℝ}
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf)
    {a b t₁ Mu Ω₀ Ω₁ V₁ : ℝ} (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0)
    (hu : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu)
    (hω₀ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, vortSum0 u (x, s) ≤ Ω₀)
    (hω₁ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, vortSum1 u (x, s) ≤ Ω₁)
    (hv₁ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, velSum1 u (x, s) ≤ V₁)
    {a' b' t₁' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) (ht₁' : t₁ < t₁' ∧ t₁' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁' 0, vortSum2 u (x, s) ≤ K := by
  obtain ⟨C, hC, hLS⟩ := LS2_local_level2
  set Mu' : ℝ := max Mu 0
  set Mf' : ℝ := max Mf 0
  set Ω₀' : ℝ := max Ω₀ 0
  set Ω₁' : ℝ := max Ω₁ 0
  set V₁' : ℝ := max V₁ 0
  have hMu' : 0 ≤ Mu' := le_max_right _ _
  have hMf' : 0 ≤ Mf' := le_max_right _ _
  have hΩ₀' : 0 ≤ Ω₀' := le_max_right _ _
  have hΩ₁' : 0 ≤ Ω₁' := le_max_right _ _
  have hV₁' : 0 ≤ V₁' := le_max_right _ _
  have hMfx : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf' := fun z hz i α hα =>
    (hMf z hz i α hα).trans (le_max_left _ _)
  refine level_bound_of_local hab ht₁ (c₁ := C * (1 + Mu' + Ω₀'))
    (c₂ := C * (1 + Mu' + Ω₀' + Ω₁' + V₁' + Mf') ^ 2) (by positivity) (by positivity)
    (fun z => (levelSums_nonneg u z).2.2.1) (continuousOn_levelSums hcl.1).2.2.1 ?_ hab' ht₁'
  intro x s ρ Λ hρ hρ1 hw
  have h := hLS u p f hcl Mf' Mu' Ω₀' Ω₁' V₁' hMfx x s ρ Λ hρ hρ1 (fun y s' hy hs'1 hs'2 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw y s' hy hs'1 hs'2
    exact ⟨mem_unitCylinder_of_annulus hab.2.2 ht₁.1 h2 h3 h4,
      fun i => (hu y h1 h2 s' ⟨h3, h4⟩ i).trans (le_max_left _ _),
      (hω₀ y h1 h2 s' ⟨h3, h4⟩).trans (le_max_left _ _),
      (hω₁ y h1 h2 s' ⟨h3, h4⟩).trans (le_max_left _ _),
      (hv₁ y h1 h2 s' ⟨h3, h4⟩).trans (le_max_left _ _), h5⟩)
  refine h.trans (le_of_eq ?_)
  ring

end CIV
