/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.LevelBounds
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.MultiIndexCases
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Serrin's interior estimates up to the top time

A suitable weak solution on the unit cylinder, smooth there, with a force bounded in `C²` and a
velocity bounded on an annular cylinder `{Rm < |x| < Rp} × (t₀, 0)`, has its velocity and its
spatial derivatives of order at most two bounded on every smaller annular cylinder, uniformly up
to the top time. The proof passes to the classical equations, bounds the vorticity and its first
two derivatives level by level (heat representation and weighted absorption), recovers the
velocity derivatives from the vorticity, and shrinks the annulus six times. This is the interior
regularity used in the proof of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Serrin's interior estimates for a suitable weak solution that is smooth on the unit
cylinder. -/
theorem serrin_interior_estimates_of_suitable (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (Rm Rp t₀ : ℝ) (hR : 0 ≤ Rm ∧ Rm < Rp ∧ Rp ≤ 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (Mu : ℝ) (hbdd : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (Rm' Rp' t₀' : ℝ) (hR' : Rm < Rm' ∧ Rm' < Rp' ∧ Rp' < Rp) (ht₀' : t₀ < t₀' ∧ t₀' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
      ∀ t ∈ Ioo t₀' 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ K := by
  obtain ⟨Mf, hMf'⟩ := hMf
  have hcl : IsClassicalSolutionOn u p f unitCylinder := isClassicalSolutionOn_of_suitable hsol
    hu hp hf
  obtain ⟨hRm, hRmp, hRp⟩ := hR
  obtain ⟨hRm', hRmp', hRp'⟩ := hR'
  obtain ⟨ht₀l, ht₀r⟩ := ht₀
  obtain ⟨ht₀'l, ht₀'r⟩ := ht₀'
  set da : ℝ := (Rm' - Rm) / 6 with hda
  set db : ℝ := (Rp - Rp') / 6 with hdb
  set dt : ℝ := (t₀' - t₀) / 6 with hdt
  have hda0 : 0 < da := by rw [hda]; linarith only [hRm']
  have hdb0 : 0 < db := by rw [hdb]; linarith only [hRp']
  have hdt0 : 0 < dt := by rw [hdt]; linarith only [ht₀'l]
  have hRp'eq : Rp' = Rp - 6 * db := by rw [hdb]; ring
  have hRm'eq : Rm' = Rm + 6 * da := by rw [hda]; ring
  have ht₀'eq : t₀' = t₀ + 6 * dt := by rw [hdt]; ring
  -- component bound on the largest annular cylinder
  have hu0 : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp - db →
      ∀ s ∈ Ioo t₀ 0, ∀ i, |u (x, s) i| ≤ Mu := fun x h1 h2 s hs i =>
    (abs_apply_le_vec3EuclideanNorm _ i).trans (hbdd x h1 (by linarith only [h2, hdb0]) s hs)
  have huk : ∀ (a b t₁ : ℝ), Rm ≤ a → b ≤ Rp - db → t₀ ≤ t₁ →
      ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu := fun a b t₁ ha hb ht x h1 h2 s hs i =>
    hu0 x (by linarith only [ha, h1]) (by linarith only [hb, h2]) s ⟨by linarith only [ht,
      hs.1], hs.2⟩ i
  -- level 0
  obtain ⟨K₀, hK₀⟩ := LV0_level0 hcl hMf' (a := Rm) (b := Rp - db) (t₁ := t₀)
    ⟨hRm, by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0,
      hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp',
      ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩ ⟨ht₀l, ht₀r⟩ hu0 (a'
      := Rm + da) (b' := Rp - 2 * db)
    (t₁' := t₀ + dt) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l,
      ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm',
      hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by
      linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩
  -- level 1
  obtain ⟨K₁, hK₁⟩ := LV1_level1 hcl hMf' (a := Rm + da) (b := Rp - 2 * db) (t₁ := t₀ + dt)
    ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩
    (huk _ _ _ (by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq])) hK₀
    (a' := Rm + 2 * da) (b' := Rp - 3 * db) (t₁' := t₀ + 2 * dt)
    ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩
  -- velocity gradient
  obtain ⟨V₁, hV₁⟩ := EV1_velocity_gradient hcl (a := Rm + 2 * da) (b := Rp - 3 * db)
    (t₁ := t₀ + 2 * dt) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l,
      ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm',
      hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by
      linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩
    (huk _ _ _ (by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq])) hK₁
    (a' := Rm + 3 * da) (b' := Rp - 4 * db) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r,
      ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩
  -- level 2
  obtain ⟨K₂, hK₂⟩ := LV2_level2 hcl hMf' (a := Rm + 3 * da) (b := Rp - 4 * db)
    (t₁ := t₀ + 2 * dt) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l,
      ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm',
      hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by
      linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩
    (huk _ _ _ (by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq]))
    (fun x h1 h2 s hs => hK₀ x (by linarith only [h1, hda0]) (by linarith only [h2, hdb0]) s ⟨by
      linarith only [hs.1, hdt0], hs.2⟩)
    (fun x h1 h2 s hs => hK₁ x (by linarith only [h1, hda0]) (by linarith only [h2, hdb0]) s hs)
    hV₁ (a' := Rm + 4 * da) (b' := Rp - 5 * db) (t₁' := t₀ + 3 * dt)
    ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩
  -- velocity Hessian
  obtain ⟨V₂, hV₂⟩ := EV2_velocity_hessian hcl (a := Rm + 4 * da) (b := Rp - 5 * db)
    (t₁ := t₀ + 3 * dt) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l,
      ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm',
      hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by
      linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0,
      hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩ ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l,
      ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm,
      hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq,
      ht₀'eq]⟩
    (huk _ _ _ (by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r,
      hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]) (by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq])) hK₂
    (a' := Rm + 5 * da) (b' := Rp - 6 * db) ⟨by linarith only [hRm, hRmp, hRp, hRm', hRmp',
      hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq], by linarith
      only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r, ht₀'l, ht₀'r, hda0, hdb0, hdt0,
      hRp'eq, hRm'eq, ht₀'eq], by linarith only [hRm, hRmp, hRp, hRm', hRmp', hRp', ht₀l, ht₀r,
      ht₀'l, ht₀'r, hda0, hdb0, hdt0, hRp'eq, hRm'eq, ht₀'eq]⟩
  refine ⟨max Mu (max V₁ V₂), ?_⟩
  intro x hx1 hx2 t ht i α hα
  have hts : t ∈ Ioo (t₀ + 3 * dt) 0 := ⟨by linarith only [ht.1, ht₀'eq, hdt0], ht.2⟩
  have hts2 : t ∈ Ioo (t₀ + 2 * dt) 0 := ⟨by linarith only [ht.1, ht₀'eq, hdt0], ht.2⟩
  rcases multiPartial_cases_of_order_le_two (fun w => u w i) α hα with h0 | ⟨j, h1⟩ | ⟨j, l, h2⟩
  · rw [h0]
    exact (hu0 x (by linarith only [hx1, hRm'eq, hda0]) (by linarith only [hx2, hRp'eq, hdb0]) t
      ⟨by linarith only [ht.1, ht₀'eq, hdt0], ht.2⟩ i).trans
      (le_max_left _ _)
  · rw [h1]
    have hv := hV₁ x (by linarith only [hx1, hRm'eq, hda0]) (by linarith only [hx2, hRp'eq,
      hdb0]) t hts2
    have hterm : |spatialPartial (fun w => u w i) j (x, t)| ≤ velSum1 u (x, t) := by
      unfold velSum1
      calc |spatialPartial (fun w => u w i) j (x, t)|
          ≤ ∑ j', |spatialPartial (fun w => u w i) j' (x, t)| :=
            Finset.single_le_sum (f := fun j' => |spatialPartial (fun w => u w i) j' (x, t)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', |spatialPartial (fun w => u w i') j' (x, t)| :=
            Finset.single_le_sum
              (f := fun i' => ∑ j', |spatialPartial (fun w => u w i') j' (x, t)|)
              (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
    exact hterm.trans (hv.trans ((le_max_left _ _).trans (le_max_right _ _)))
  · rw [h2]
    have hv := hV₂ x (by linarith only [hx1, hRm'eq, hda0]) (by linarith only [hx2, hRp'eq,
      hdb0]) t hts
    have hterm : |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l (x, t)| ≤
        velSum2 u (x, t) := by
      unfold velSum2
      calc |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l (x, t)|
          ≤ ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l' (x, t)| :=
            Finset.single_le_sum
              (f := fun l' => |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l'
                (x, t)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
        _ ≤ ∑ j', ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j' w) l'
              (x, t)| :=
            Finset.single_le_sum
              (f := fun j' => ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i)
                j' w)
                l' (x, t)|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
              (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i') j' w)
              l' (x, t)| :=
            Finset.single_le_sum
              (f := fun i' => ∑ j', ∑ l', |spatialPartial
                (fun w => spatialPartial (fun w' => u w' i') j' w) l' (x, t)|)
              (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
                (fun _ _ => abs_nonneg _))) (Finset.mem_univ i)
    exact hterm.trans (hv.trans ((le_max_right _ _).trans (le_max_right _ _)))

end CIV
