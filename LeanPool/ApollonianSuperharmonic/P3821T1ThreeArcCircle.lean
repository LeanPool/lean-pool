/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- [TABLET NODE: P3821T1ThreeArcCircle]

/-!
# P3821T1ThreeArcCircle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ThreeArcCircleLemmas

private theorem hq₀ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (h₀ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    Continuous q₀ := by
  classical
  intro ι P a b h₀ clamp q₀
  dsimp [q₀, clamp]
  fun_prop

private theorem hq₁ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    Continuous q₁ := by
  classical
  intro ι P b c h₁ clamp q₁
  dsimp [q₁, clamp]
  fun_prop

private theorem hq₂ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (c : ι), ∀ (h₂ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    Continuous q₂ := by
  classical
  intro ι P a c h₂ clamp q₂
  dsimp [q₂, clamp]
  fun_prop

private theorem hmid :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₁ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ((↑((h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) → (↑(P.edgeArc b c) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position c) → ∀
            (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc
        (0 : ℝ) 1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position
        c) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    (Continuous q₁) → (Continuous q₂) →
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    Continuous mid := by
  classical
  intro ι P a b c h₁ h₁c h₂ h₂c clamp q₁ q₂ hq₁ hq₂ mid
  apply continuous_if_le continuous_id continuous_const hq₁.continuousOn hq₂.continuousOn
  intro x hx
  have hx' : x = 2 := hx
  subst x
  have hleft : clamp (2 - 1) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  have hright : clamp (2 - 2) = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  simp only [q₁, q₂, hleft, hright]
  exact h₁c.trans h₂c.symm

private theorem hf :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ)
        1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position b) → ∀
            (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ((↑((h₁ : (↑(Set.Icc
        (0 : ℝ) 1) : Type) → (↑(P.edgeArc b c) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position
        b) → ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    (Continuous q₀) →
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    (Continuous mid) →
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    Continuous f := by
  classical
  intro ι P a b c h₀ h₀b h₁ h₁b h₂ clamp q₀ q₁ q₂ hq₀ mid hmid f
  apply continuous_if_le continuous_id continuous_const hq₀.continuousOn hmid.continuousOn
  intro x hx
  have hx' : x = 1 := hx
  subst x
  have hleft : clamp 1 = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  have hright : clamp (1 - 1) = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  simp only [mid,
    ite_eq_left (by norm_num : (1 : ℝ) ≤ 2), q₀, q₁, hleft, hright]
  exact h₀b.trans h₁b.symm

private theorem hf0 :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ)
        1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position a) → ∀
            (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0
        : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) →
        (↑(P.edgeArc c a) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position a) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    f 0 = f 3 := by
  classical
  intro ι P a b c h₀ h₀a h₁ h₂ h₂a clamp q₀ q₁ q₂ mid f
  have hleft : clamp 0 = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  have hright : clamp (3 - 2) = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [clamp]
  simp only [f, ite_eq_left (by norm_num : (0 : ℝ) ≤ 1),
    ite_eq_right (by norm_num : ¬ (3 : ℝ) ≤ 1), mid,
    ite_eq_right (by norm_num : ¬ (3 : ℝ) ≤ 2), q₀, q₂, hright, hleft]
  exact h₀a.trans h₂a.symm

private theorem hℓc :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (Continuous f) → (f 0 = f 3) → ∀ [this : Fact (0 < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    Continuous ℓ := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f hf hf0 this ℓ
  apply AddCircle.liftIco_zero_continuous hf0
  exact hf.continuousOn

private theorem clamp_eq_self :
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    ∀ (x : ℝ), ∀ (hx : x ∈ Set.Icc (0 : ℝ) 1), clamp x = ⟨x, hx⟩ := by
  classical
  intro clamp x hx
  apply Subtype.ext
  simp [clamp, hx.1, hx.2]

private theorem fseg₀ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : x ∈ Set.Icc (0 : ℝ) 1), clamp x = ⟨x, hx⟩) → ∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀
        (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b) := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f clamp_eq_self x hx h₁x
  simp [f, q₀, ite_eq_left h₁x, clamp_eq_self x ⟨hx, h₁x⟩]

private theorem fseg₁ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : x ∈ Set.Icc (0 : ℝ) 1), clamp x = ⟨x, hx⟩) → ∀ (x : ℝ), ∀ (h₁x : 1 < x),
        ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by linarith [h₂x]⟩⟩ : P.edgeArc b
        c) := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f clamp_eq_self x h₁x h₂x
  have hc : clamp (x - 1) = ⟨x - 1, ⟨by linarith, by linarith⟩⟩ :=
    clamp_eq_self (x - 1) ⟨by linarith, by linarith⟩
  simp [f, mid, q₁, not_le.mpr h₁x, ite_eq_left h₂x, hc]

private theorem fseg₂ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : x ∈ Set.Icc (0 : ℝ) 1), clamp x = ⟨x, hx⟩) → ∀ (x : ℝ), ∀ (h₂x : 2 < x),
        ∀ (h₃x : x < 3), f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c
        a) := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f clamp_eq_self x h₂x h₃x
  have hc : clamp (x - 2) = ⟨x - 2, ⟨by linarith, by linarith⟩⟩ :=
    clamp_eq_self (x - 2) ⟨by linarith, by linarith⟩
  simp [f, mid, q₂, not_le.mpr (by linarith : 1 < x),
    not_le.mpr h₂x, hc]

private theorem hint₀₁ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), (a ≠ b) → (b ≠
        c) → (c ≠ a) → (P.adjacent a b) → (P.adjacent b c) → ∀ (h₀ : (↑(Set.Icc (0 : ℝ) 1) :
        Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ) 1) : Type) →
        (↑(P.edgeArc a b) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position a) → ((↑((h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) =
        P.position b) → ∀ (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)),
            ((↑((h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc b c) : Type)) ⟨0, (by norm_num)⟩)
        : ℝ × ℝ) = P.position b) → ((↑((h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc b c) :
        Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position c) → ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) :
        Type) ≃ₜ (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    (Continuous q₀) → (Continuous q₁) →
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    (Continuous mid) →
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (Continuous f) → (f 0 = f 3) → ∀ [this : Fact (0 < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    (Continuous ℓ) → (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ :
        P.edgeArc a b)) → (∀ (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by
        linarith [h₁x], by linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀
            (h₃x : x < 3), f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c
        a)) → P.edgeArc a b ∩ P.edgeArc b c = {P.position b} := by
  classical
  intro ι P a b c hab hbc hca eab ebc h₀ h₀a h₀b h₁ h₁b h₁c h₂ clamp q₀ q₁ q₂ hq₀ hq₁ mid hmid f
      hf hf0 this ℓ hℓc fseg₀ fseg₁ fseg₂
  have hne : ({a, b} : Set ι) ≠ {b, c} := by
    intro hh
    have ha : a ∈ ({b, c} : Set ι) := by rw [← hh]; simp
    simp [hab, hca.symm] at ha
  have hcommon : ({a, b} : Set ι) ∩ {b, c} = {b} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, k⟩
      rcases h with h | h
      · subst x
        rcases k with k | k
        · exact (hab k).elim
        · exact (hca k.symm).elim
      · subst x
        rfl
    · rintro rfl
      simp
  rw [P.arc_intersections a b b c eab ebc hne]
  rw [hcommon]
  simp

private theorem hint₁₂ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), (a ≠ b) → (b ≠
        c) → (c ≠ a) → (P.adjacent b c) → (P.adjacent c a) → ∀ (h₀ : (↑(Set.Icc (0 : ℝ) 1) :
        Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc b c) : Type)), ((↑((h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc b c) :
        Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position b) → ((↑((h₁ : (↑(Set.Icc (0 : ℝ) 1) :
        Type) → (↑(P.edgeArc b c) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position c) → ∀ (h₂ :
            (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc (0
            : ℝ)
        1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position c) →
        ((↑((h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨1, (by norm_num)⟩)
        : ℝ × ℝ) = P.position a) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    (Continuous q₁) → (Continuous q₂) →
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    (Continuous mid) →
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (Continuous f) → (f 0 = f 3) → ∀ [this : Fact (0 < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    (Continuous ℓ) → (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ :
        P.edgeArc a b)) → (∀ (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by
        linarith [h₁x], by linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀
            (h₃x : x < 3), f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c
        a)) → (P.edgeArc a b ∩ P.edgeArc b c = {P.position b}) → P.edgeArc b c ∩ P.edgeArc c a =
        {P.position c} := by
  classical
  intro ι P a b c hab hbc hca ebc eca h₀ h₁ h₁b h₁c h₂ h₂c h₂a clamp q₀ q₁ q₂ hq₁ hq₂ mid hmid f
      hf hf0 this ℓ hℓc fseg₀ fseg₁ fseg₂ hint₀₁
  have hne : ({b, c} : Set ι) ≠ {c, a} := by
    intro hh
    have hb : b ∈ ({c, a} : Set ι) := by rw [← hh]; simp
    simp [hbc, hab.symm] at hb
  have hcommon : ({b, c} : Set ι) ∩ {c, a} = {c} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, k⟩
      rcases h with h | h
      · subst x
        rcases k with k | k
        · exact (hbc k).elim
        · exact (hab k.symm).elim
      · subst x
        rfl
    · rintro rfl
      simp
  rw [P.arc_intersections b c c a ebc eca hne]
  rw [hcommon]
  simp

private theorem hint₂₀ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), (a ≠ b) → (b ≠
        c) → (c ≠ a) → (P.adjacent a b) → (P.adjacent c a) → ∀ (h₀ : (↑(Set.Icc (0 : ℝ) 1) :
        Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ) 1) : Type) →
        (↑(P.edgeArc a b) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position a) → ((↑((h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) =
        P.position b) → ∀ (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀
            (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc
        (0 : ℝ) 1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position
        c) → ((↑((h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨1, (by
        norm_num)⟩) : ℝ × ℝ) = P.position a) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    (Continuous q₀) → (Continuous q₂) →
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    (Continuous mid) →
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (Continuous f) → (f 0 = f 3) → ∀ [this : Fact (0 < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    (Continuous ℓ) → (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ :
        P.edgeArc a b)) → (∀ (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by
        linarith [h₁x], by linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀
            (h₃x : x < 3), f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c
        a)) → (P.edgeArc a b ∩ P.edgeArc b c = {P.position b}) → (P.edgeArc b c ∩ P.edgeArc c a =
        {P.position c}) → P.edgeArc c a ∩ P.edgeArc a b = {P.position a} := by
  classical
  intro ι P a b c hab hbc hca eab eca h₀ h₀a h₀b h₁ h₂ h₂c h₂a clamp q₀ q₁ q₂ hq₀ hq₂ mid hmid f
      hf hf0 this ℓ hℓc fseg₀ fseg₁ fseg₂ hint₀₁ hint₁₂
  have hne : ({c, a} : Set ι) ≠ {a, b} := by
    intro hh
    have hc : c ∈ ({a, b} : Set ι) := by rw [← hh]; simp
    simp [hca, hbc.symm] at hc
  have hcommon : ({c, a} : Set ι) ∩ {a, b} = {a} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, k⟩
      rcases h with h | h
      · subst x
        rcases k with k | k
        · exact (hca k).elim
        · exact (hbc k.symm).elim
      · subst x
        rfl
    · rintro rfl
      simp
  rw [P.arc_intersections c a a b eca eab hne]
  rw [hcommon]
  simp

private theorem cross₀₁ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ)
        1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position b) → ∀
            (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ((↑((h₁ : (↑(Set.Icc
        (0 : ℝ) 1) : Type) → (↑(P.edgeArc b c) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position
        b) → ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b)) → (∀
        (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by
        linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (P.edgeArc a b ∩ P.edgeArc b c = {P.position b}) → ∀
            {x : ℝ}, ∀ {y : ℝ}, (0 ≤ x) → (x ≤ 1) → (1 < y) → (y ≤ 2) → (f x = f y) → x = y := by
  classical
  intro ι P a b c h₀ h₀b h₁ h₁b h₂ clamp q₀ q₁ q₂ mid f fseg₀ fseg₁ hint₀₁ x y hx₀ hx₁ hy₁ hy₂ hxy
  rw [fseg₀ x hx₀ hx₁, fseg₁ y hy₁ hy₂] at hxy
  let u : Set.Icc (0 : ℝ) 1 := ⟨x, ⟨hx₀, hx₁⟩⟩
  let v : Set.Icc (0 : ℝ) 1 := ⟨y - 1, ⟨by linarith, by linarith⟩⟩
  have hmem₀ : ((h₀ u : P.edgeArc a b) : Real × Real) ∈ P.edgeArc a b := (h₀ u).property
  have hmem₁ : ((h₁ v : P.edgeArc b c) : Real × Real) ∈ P.edgeArc b c := (h₁ v).property
  have hmem : ((h₀ u : P.edgeArc a b) : Real × Real) ∈
      P.edgeArc a b ∩ P.edgeArc b c := ⟨hmem₀, hxy ▸ hmem₁⟩
  have hpos : ((h₀ u : P.edgeArc a b) : Real × Real) = P.position b := by
    have hm : ((h₀ u : P.edgeArc a b) : Real × Real) ∈
        ({P.position b} : Set (Real × Real)) := by
      rw [← hint₀₁]
      exact hmem
    simpa using hm
  have hu : u = ⟨1, by norm_num⟩ := by
    apply h₀.injective
    apply Subtype.ext
    exact hpos.trans h₀b.symm
  have hv : v = ⟨0, by norm_num⟩ := by
    apply h₁.injective
    apply Subtype.ext
    exact hxy.symm.trans hpos |>.trans h₁b.symm
  have hx : x = 1 := congrArg Subtype.val hu
  have hy : y - 1 = 0 := congrArg Subtype.val hv
  linarith

private theorem cross₁₂ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ((↑((h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) →
        (↑(P.edgeArc b c) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position c) → ∀ (h₂ :
            (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc (0
            : ℝ)
        1) : Type) → (↑(P.edgeArc c a) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position c) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by
        linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀ (h₃x : x < 3), f x =
        (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c a)) → (P.edgeArc b c ∩
        P.edgeArc c a = {P.position c}) → ∀ {x : ℝ}, ∀ {y : ℝ}, (1 < x) → (x ≤ 2) → (2 < y) → (y
        < 3) → (f x = f y) → x = y := by
  classical
  intro ι P a b c h₀ h₁ h₁c h₂ h₂c clamp q₀ q₁ q₂ mid f fseg₁ fseg₂ hint₁₂ x y hx₁ hx₂ hy₂ hy₃ hxy
  rw [fseg₁ x hx₁ hx₂, fseg₂ y hy₂ hy₃] at hxy
  let u : Set.Icc (0 : ℝ) 1 := ⟨x - 1, ⟨by linarith, by linarith⟩⟩
  let v : Set.Icc (0 : ℝ) 1 := ⟨y - 2, ⟨by linarith, by linarith⟩⟩
  have hmem₁ : ((h₁ u : P.edgeArc b c) : Real × Real) ∈ P.edgeArc b c := (h₁ u).property
  have hmem₂ : ((h₂ v : P.edgeArc c a) : Real × Real) ∈ P.edgeArc c a := (h₂ v).property
  have hmem : ((h₁ u : P.edgeArc b c) : Real × Real) ∈
      P.edgeArc b c ∩ P.edgeArc c a := ⟨hmem₁, hxy ▸ hmem₂⟩
  have hpos : ((h₁ u : P.edgeArc b c) : Real × Real) = P.position c := by
    have hm : ((h₁ u : P.edgeArc b c) : Real × Real) ∈
        ({P.position c} : Set (Real × Real)) := by
      rw [← hint₁₂]
      exact hmem
    simpa using hm
  have hu : u = ⟨1, by norm_num⟩ := by
    apply h₁.injective
    apply Subtype.ext
    exact hpos.trans h₁c.symm
  have hv : v = ⟨0, by norm_num⟩ := by
    apply h₂.injective
    apply Subtype.ext
    exact hxy.symm.trans hpos |>.trans h₂c.symm
  have hx : x - 1 = 1 := congrArg Subtype.val hu
  have hy : y - 2 = 0 := congrArg Subtype.val hv
  linarith

private theorem cross₀₂ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc (0 : ℝ)
        1) : Type) → (↑(P.edgeArc a b) : Type)) ⟨0, (by norm_num)⟩) : ℝ × ℝ) = P.position a) → ∀
            (h₁ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0
        : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc c a) : Type)), ((↑((h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) →
        (↑(P.edgeArc c a) : Type)) ⟨1, (by norm_num)⟩) : ℝ × ℝ) = P.position a) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b)) → (∀
        (x : ℝ), ∀ (h₂x : 2 < x), ∀ (h₃x : x < 3), f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by
        linarith [h₃x]⟩⟩ : P.edgeArc c a)) → (P.edgeArc c a ∩ P.edgeArc a b = {P.position a}) → ∀
            {x : ℝ}, ∀ {y : ℝ}, (0 ≤ x) → (x ≤ 1) → (2 < y) → (y < 3) → (f x = f y) → False := by
  classical
  intro ι P a b c h₀ h₀a h₁ h₂ h₂a clamp q₀ q₁ q₂ mid f fseg₀ fseg₂ hint₂₀ x y hx₀ hx₁ hy₂ hy₃ hxy
  rw [fseg₀ x hx₀ hx₁, fseg₂ y hy₂ hy₃] at hxy
  let u : Set.Icc (0 : ℝ) 1 := ⟨x, ⟨hx₀, hx₁⟩⟩
  let v : Set.Icc (0 : ℝ) 1 := ⟨y - 2, ⟨by linarith, by linarith⟩⟩
  have hmem₀ : ((h₀ u : P.edgeArc a b) : Real × Real) ∈ P.edgeArc a b := (h₀ u).property
  have hmem₂ : ((h₂ v : P.edgeArc c a) : Real × Real) ∈ P.edgeArc c a := (h₂ v).property
  have hmem : ((h₀ u : P.edgeArc a b) : Real × Real) ∈
      P.edgeArc a b ∩ P.edgeArc c a := ⟨hmem₀, hxy ▸ hmem₂⟩
  have hpos : ((h₀ u : P.edgeArc a b) : Real × Real) = P.position a := by
    have hm : ((h₀ u : P.edgeArc a b) : Real × Real) ∈
        ({P.position a} : Set (Real × Real)) := by
      rw [← hint₂₀]
      exact ⟨hxy ▸ hmem₂, hmem₀⟩
    simpa using hm
  have hu : u = ⟨0, by norm_num⟩ := by
    apply h₀.injective
    apply Subtype.ext
    exact hpos.trans h₀a.symm
  have hx : x = 0 := congrArg Subtype.val hu
  have hv : v = ⟨1, by norm_num⟩ := by
    apply h₂.injective
    apply Subtype.ext
    exact hxy.symm.trans hpos |>.trans h₂a.symm
  have hy : y - 2 = 1 := congrArg Subtype.val hv
  linarith

private theorem hf_inj :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b)) → (∀
        (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by
        linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀ (h₃x : x < 3), f x =
        (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c a)) → (∀ {x : ℝ}, ∀ {y
            : ℝ}, (0 ≤ x) → (x ≤ 1) → (1 < y) → (y ≤ 2) → (f x = f y) → x = y) → (∀ {x : ℝ}, ∀ {y
            : ℝ}, (1 < x) → (x ≤ 2) → (2 < y) → (y < 3) → (f x = f y) → x = y) → (∀ {x : ℝ}, ∀ {y
            : ℝ}, (0 ≤ x) → (x ≤ 1) → (2 < y) → (y < 3) → (f x = f y) → False) → ∀ x y : ℝ, x ∈
            Set.Ico (0
        : ℝ) 3 → y ∈ Set.Ico 0 3 →
      f x = f y → x = y := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f fseg₀ fseg₁ fseg₂ cross₀₁ cross₁₂ cross₀₂ x y hx
      hy hxy
  rcases hx with ⟨hx₀, hx₃⟩
  rcases hy with ⟨hy₀, hy₃⟩
  by_cases hx₁ : x ≤ 1
  · by_cases hy₁ : y ≤ 1
    · rw [fseg₀ x hx₀ hx₁, fseg₀ y hy₀ hy₁] at hxy
      have heq : (⟨x, ⟨hx₀, hx₁⟩⟩ : Set.Icc (0 : ℝ) 1) = ⟨y, ⟨hy₀, hy₁⟩⟩ := by
        apply h₀.injective
        exact Subtype.ext hxy
      exact congrArg Subtype.val heq
    · by_cases hy₂ : y ≤ 2
      · exact cross₀₁ hx₀ hx₁ (by linarith) hy₂ hxy
      · exact cross₀₂ hx₀ hx₁ (by linarith) hy₃ hxy |>.elim
  · by_cases hx₂ : x ≤ 2
    · by_cases hy₁ : y ≤ 1
      · have h := cross₀₁ hy₀ hy₁ (by linarith) hx₂ hxy.symm
        exact h.symm
      · by_cases hy₂ : y ≤ 2
        · rw [fseg₁ x (by linarith) hx₂, fseg₁ y (by linarith) hy₂] at hxy
          have heq : (⟨x - 1, ⟨by linarith, by linarith⟩⟩ : Set.Icc (0 : ℝ) 1) =
              ⟨y - 1, ⟨by linarith, by linarith⟩⟩ := by
            apply h₁.injective
            exact Subtype.ext hxy
          have hv := congrArg Subtype.val heq
          linarith
        · exact cross₁₂ (by linarith) hx₂ (by linarith) hy₃ hxy
    · by_cases hy₁ : y ≤ 1
      · exact (cross₀₂ hy₀ hy₁ (by linarith) hx₃ hxy.symm).elim
      · by_cases hy₂ : y ≤ 2
        · have h := cross₁₂ (by linarith) hy₂ (by linarith) hx₃ hxy.symm
          exact h.symm
        · rw [fseg₂ x (by linarith) hx₃, fseg₂ y (by linarith) hy₃] at hxy
          have heq : (⟨x - 2, ⟨by linarith, by linarith⟩⟩ : Set.Icc (0 : ℝ) 1) =
              ⟨y - 2, ⟨by linarith, by linarith⟩⟩ := by
            apply h₂.injective
            exact Subtype.ext hxy
          have hv := congrArg Subtype.val heq
          linarith

private theorem lift_eq :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ∀ (h₁ : (↑(Set.Icc (0 : ℝ)
        1) : Type) ≃ₜ (↑(P.edgeArc b c) : Type)), ∀ (h₂ : (↑(Set.Icc (0 : ℝ) 1) : Type) ≃ₜ
        (↑(P.edgeArc c a) : Type)),
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    ∀ [this : Fact (0 < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    ∀ (x : ℝ), (x ∈ Set.Ico (0 : ℝ) 3) → ℓ (x : AddCircle (3 : ℝ)) = f x := by
  classical
  intro ι P a b c h₀ h₁ h₂ clamp q₀ q₁ q₂ mid f this ℓ x hx
  dsimp [ℓ]
  apply AddCircle.liftIco_coe_apply
  simpa using hx

end ThreeArcCircleLemmas

namespace ThreeArcCircleRange

private theorem hrangeℓ :
    ∀ (ι : Type), ∀ (P : PlaneTriangulation ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (h₀ :
        (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) ≃ₜ (↑(P.edgeArc a b) : Type)), ((↑((h₀ : (↑(Set.Icc
        (0 : ℝ) (1 : ℝ)) : Type) → (↑(P.edgeArc a b) : Type)) ⟨(0 : ℝ),
        (by norm_num)⟩) : ℝ × ℝ) = P.position a) → ((↑((h₀ : (↑(Set.Icc (0 : ℝ) (1
        : ℝ)) : Type) → (↑(P.edgeArc a b) : Type)) ⟨(1 : ℝ), (by norm_num)⟩) : ℝ ×
        ℝ) = P.position b) → ∀ (h₁ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) ≃ₜ (↑(P.edgeArc b c) :
        Type)), ((↑((h₁ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → (↑(P.edgeArc b c) : Type)) ⟨(0 :
        ℝ), (by norm_num)⟩) : ℝ × ℝ) = P.position b) → ((↑((h₁ : (↑(Set.Icc (0 : ℝ)
        (1 : ℝ)) : Type) → (↑(P.edgeArc b c) : Type)) ⟨(1 : ℝ), (by norm_num)⟩) : ℝ
        × ℝ) = P.position c) → ∀ (h₂ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) ≃ₜ (↑(P.edgeArc c a) :
        Type)), ((↑((h₂ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type) → (↑(P.edgeArc c a) : Type)) ⟨(0 :
        ℝ), (by norm_num)⟩) : ℝ × ℝ) = P.position c) → ((↑((h₂ : (↑(Set.Icc (0 : ℝ)
        (1 : ℝ)) : Type) → (↑(P.edgeArc c a) : Type)) ⟨(1 : ℝ), (by norm_num)⟩) : ℝ
        × ℝ) = P.position a) →
    let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
      ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
    let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
    let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
    let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
    let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
    let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
    ∀ [this : Fact ((0 : ℝ) < (3 : ℝ))],
    let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
    (∀ (x : ℝ), ∀ (hx : 0 ≤ x), ∀ (h₁x : x ≤ 1), f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b)) → (∀
        (x : ℝ), ∀ (h₁x : 1 < x), ∀ (h₂x : x ≤ 2), f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by
        linarith [h₂x]⟩⟩ : P.edgeArc b c)) → (∀ (x : ℝ), ∀ (h₂x : 2 < x), ∀ (h₃x : x < 3), f x =
        (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c a)) → (∀ (x : ℝ), (x ∈
        Set.Ico (0 : ℝ) 3) → ℓ (x : AddCircle (3 : ℝ)) = f x) → Set.range ℓ =
      P.edgeArc a b ∪ P.edgeArc b c ∪ P.edgeArc c a := by
  classical
  intro ι P a b c h₀ h₀a h₀b h₁ h₁b h₁c h₂ h₂c h₂a clamp q₀ q₁ q₂ mid f this ℓ fseg₀ fseg₁ fseg₂
      lift_eq
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    let u := AddCircle.equivIco (3 : ℝ) 0 y
    have hu : (u : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by simpa using u.property
    have hy : ℓ y = f (u : ℝ) := by
      rw [← AddCircle.coe_equivIco (p := (3 : ℝ)) (a := (0 : ℝ)) (y := y)]
      exact lift_eq (u : ℝ) hu
    rw [hy]
    by_cases hu₁ : (u : ℝ) ≤ 1
    · rw [fseg₀ (u : ℝ) u.property.1 hu₁]
      exact Or.inl (Or.inl (h₀ _).property)
    · by_cases hu₂ : (u : ℝ) ≤ 2
      · rw [fseg₁ (u : ℝ) (by linarith) hu₂]
        exact Or.inl (Or.inr (h₁ _).property)
      · rw [fseg₂ (u : ℝ) (by linarith) hu.2]
        exact Or.inr (h₂ _).property
  · intro hz
    simp only [Set.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · obtain ⟨t, ht⟩ := h₀.surjective ⟨z, hz⟩
      refine ⟨(t : ℝ), ?_⟩
      have htIco : (t : ℝ) ∈ Set.Ico (0 : ℝ) 3 :=
        ⟨t.property.1, by linarith [t.property.2]⟩
      rw [lift_eq (t : ℝ) htIco]
      rw [fseg₀ (t : ℝ) (by linarith [t.property.1]) (by linarith [t.property.2])]
      simpa using congrArg Subtype.val ht
    · obtain ⟨t, ht⟩ := h₁.surjective ⟨z, hz⟩
      by_cases ht0 : (t : ℝ) = 0
      · have hzv : z = P.position b := by
          have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht0
          have ht'' := ht
          rw [ht'] at ht''
          have := congrArg Subtype.val ht''
          rw [h₁b] at this
          exact this.symm
        refine ⟨(1 : ℝ), ?_⟩
        rw [lift_eq 1 (by norm_num)]
        rw [fseg₀ 1 (by norm_num) (by norm_num)]
        change ((h₀ (1 : Set.Icc (0 : ℝ) 1) : P.edgeArc a b) : Real × Real) = z
        exact h₀b.trans hzv.symm
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
        let x := (t : ℝ) + 1
        refine ⟨x, ?_⟩
        have hx₁ : 1 < x := by dsimp [x]; linarith
        have hx₂ : x ≤ 2 := by dsimp [x]; linarith [t.property.2]
        rw [lift_eq x (by constructor <;> dsimp [x] <;> linarith [t.property.1, t.property.2])]
        rw [fseg₁ x hx₁ hx₂]
        have hparam : (⟨x - 1, by constructor <;> linarith⟩ : Set.Icc (0 : ℝ) 1) = t := by
          apply Subtype.ext
          dsimp [x]
          ring
        rw [hparam]
        simpa using congrArg Subtype.val ht
    · obtain ⟨t, ht⟩ := h₂.surjective ⟨z, hz⟩
      by_cases ht0 : (t : ℝ) = 0
      · have hzv : z = P.position c := by
          have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht0
          have ht'' := ht
          rw [ht'] at ht''
          have := congrArg Subtype.val ht''
          rw [h₂c] at this
          exact this.symm
        refine ⟨(2 : ℝ), ?_⟩
        rw [lift_eq 2 (by norm_num)]
        rw [fseg₁ 2 (by norm_num) (by norm_num)]
        have hparam : (⟨(2 : ℝ) - 1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) =
            ⟨1, by norm_num⟩ := by apply Subtype.ext; norm_num
        rw [hparam]
        simpa [hzv] using h₁c
      · by_cases ht1 : (t : ℝ) = 1
        · have hzv : z = P.position a := by
            have ht' : t = ⟨1, by norm_num⟩ := Subtype.ext ht1
            have ht'' := ht
            rw [ht'] at ht''
            have := congrArg Subtype.val ht''
            rw [h₂a] at this
            exact this.symm
          refine ⟨(0 : ℝ), ?_⟩
          rw [lift_eq 0 (by norm_num)]
          rw [fseg₀ 0 (by norm_num) (by norm_num)]
          change ((h₀ (0 : Set.Icc (0 : ℝ) 1) : P.edgeArc a b) : Real × Real) = z
          exact h₀a.trans hzv.symm
        · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
          have htne : (t : ℝ) ≠ 1 := ht1
          have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 htne
          let x := (t : ℝ) + 2
          refine ⟨x, ?_⟩
          have hx₂ : 2 < x := by dsimp [x]; linarith
          have hx₃ : x < 3 := by dsimp [x]; linarith
          rw [lift_eq x (by constructor <;> dsimp [x] <;> linarith [t.property.1,
              t.property.2])]
          rw [fseg₂ x hx₂ hx₃]
          have hparam : (⟨x - 2, by constructor <;> linarith⟩ : Set.Icc (0 : ℝ) 1) = t := by
            apply Subtype.ext
            dsimp [x]
            ring
          rw [hparam]
          simpa using congrArg Subtype.val ht

end ThreeArcCircleRange

theorem P3821T1ThreeArcCircle {ι : Type} (P : PlaneTriangulation ι)
    (a b c : ι) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (eab : P.adjacent a b) (ebc : P.adjacent b c) (eca : P.adjacent c a) :
    ∃ e : C(Circle, Real × Real), Function.Injective e ∧
      Set.range e = P.edgeArc a b ∪ P.edgeArc b c ∪ P.edgeArc c a := by
-- BODY
  obtain ⟨h₀, h₀a, h₀b⟩ := P.arc_homeomorph a b eab
  obtain ⟨h₁, h₁b, h₁c⟩ := P.arc_homeomorph b c ebc
  obtain ⟨h₂, h₂c, h₂a⟩ := P.arc_homeomorph c a eca
  let clamp (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
    ⟨max 0 (min x 1), ⟨le_max_left _ _, max_le_iff.mpr ⟨by norm_num, min_le_right _ _⟩⟩⟩
  let q₀ : ℝ → Real × Real := fun x => (h₀ (clamp x) : Real × Real)
  let q₁ : ℝ → Real × Real := fun x => (h₁ (clamp (x - 1)) : Real × Real)
  let q₂ : ℝ → Real × Real := fun x => (h₂ (clamp (x - 2)) : Real × Real)
  have hq₀ : Continuous q₀ := ThreeArcCircleLemmas.hq₀ ι P a b h₀
  have hq₁ : Continuous q₁ := ThreeArcCircleLemmas.hq₁ ι P b c h₁
  have hq₂ : Continuous q₂ := ThreeArcCircleLemmas.hq₂ ι P a c h₂
  let mid : ℝ → Real × Real := fun x => if x ≤ 2 then q₁ x else q₂ x
  have hmid : Continuous mid := ThreeArcCircleLemmas.hmid ι P a b c h₁ h₁c h₂ h₂c hq₁ hq₂
  let f : ℝ → Real × Real := fun x => if x ≤ 1 then q₀ x else mid x
  have hf : Continuous f := ThreeArcCircleLemmas.hf ι P a b c h₀ h₀b h₁ h₁b h₂ hq₀ hmid
  have hf0 : f 0 = f 3 := ThreeArcCircleLemmas.hf0 ι P a b c h₀ h₀a h₁ h₂ h₂a
  let : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  let ℓ : AddCircle (3 : ℝ) → Real × Real := AddCircle.liftIco 3 0 f
  have hℓc : Continuous ℓ := ThreeArcCircleLemmas.hℓc ι P a b c h₀ h₁ h₂ hf hf0 (this := this)
  have clamp_eq_self (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      clamp x = ⟨x, hx⟩ := ThreeArcCircleLemmas.clamp_eq_self x hx
  have fseg₀ (x : ℝ) (hx : 0 ≤ x) (h₁x : x ≤ 1) :
      f x = (h₀ ⟨x, ⟨hx, h₁x⟩⟩ : P.edgeArc a b) := ThreeArcCircleLemmas.fseg₀ ι P a b c h₀ h₁ h₂
          clamp_eq_self x hx h₁x
  have fseg₁ (x : ℝ) (h₁x : 1 < x) (h₂x : x ≤ 2) :
      f x = (h₁ ⟨x - 1, ⟨by linarith [h₁x], by linarith [h₂x]⟩⟩ : P.edgeArc b c) :=
          ThreeArcCircleLemmas.fseg₁ ι P a b c h₀ h₁ h₂ clamp_eq_self x h₁x h₂x
  have fseg₂ (x : ℝ) (h₂x : 2 < x) (h₃x : x < 3) :
      f x = (h₂ ⟨x - 2, ⟨by linarith [h₂x], by linarith [h₃x]⟩⟩ : P.edgeArc c a) :=
          ThreeArcCircleLemmas.fseg₂ ι P a b c h₀ h₁ h₂ clamp_eq_self x h₂x h₃x
  have hint₀₁ : P.edgeArc a b ∩ P.edgeArc b c = {P.position b} := ThreeArcCircleLemmas.hint₀₁ ι P
      a b c hab hbc hca eab ebc h₀ h₀a h₀b h₁ h₁b h₁c h₂ hq₀ hq₁ hmid hf hf0 (this := this) hℓc
      fseg₀ fseg₁ fseg₂
  have hint₁₂ : P.edgeArc b c ∩ P.edgeArc c a = {P.position c} := ThreeArcCircleLemmas.hint₁₂ ι P
      a b c hab hbc hca ebc eca h₀ h₁ h₁b h₁c h₂ h₂c h₂a hq₁ hq₂ hmid hf hf0 (this := this) hℓc
      fseg₀ fseg₁ fseg₂ hint₀₁
  have hint₂₀ : P.edgeArc c a ∩ P.edgeArc a b = {P.position a} := ThreeArcCircleLemmas.hint₂₀ ι P
      a b c hab hbc hca eab eca h₀ h₀a h₀b h₁ h₂ h₂c h₂a hq₀ hq₂ hmid hf hf0 (this := this) hℓc
      fseg₀ fseg₁ fseg₂ hint₀₁ hint₁₂
  have cross₀₁ {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
      (hy₁ : 1 < y) (hy₂ : y ≤ 2) (hxy : f x = f y) : x = y := ThreeArcCircleLemmas.cross₀₁ ι P a
          b c h₀ h₀b h₁ h₁b h₂ fseg₀ fseg₁ hint₀₁ (x := x) (y := y) hx₀ hx₁ hy₁ hy₂ hxy
  have cross₁₂ {x y : ℝ} (hx₁ : 1 < x) (hx₂ : x ≤ 2)
      (hy₂ : 2 < y) (hy₃ : y < 3) (hxy : f x = f y) : x = y := ThreeArcCircleLemmas.cross₁₂ ι P a
          b c h₀ h₁ h₁c h₂ h₂c fseg₁ fseg₂ hint₁₂ (x := x) (y := y) hx₁ hx₂ hy₂ hy₃ hxy
  have cross₀₂ {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
      (hy₂ : 2 < y) (hy₃ : y < 3) (hxy : f x = f y) : False := ThreeArcCircleLemmas.cross₀₂ ι P a
          b c h₀ h₀a h₁ h₂ h₂a fseg₀ fseg₂ hint₂₀ (x := x) (y := y) hx₀ hx₁ hy₂ hy₃ hxy
  have hf_inj : ∀ x y : ℝ, x ∈ Set.Ico (0 : ℝ) 3 → y ∈ Set.Ico 0 3 →
      f x = f y → x = y := ThreeArcCircleLemmas.hf_inj ι P a b c h₀ h₁ h₂ fseg₀ fseg₁ fseg₂
          cross₀₁ cross₁₂ cross₀₂
  have lift_eq (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 3) :
      ℓ (x : AddCircle (3 : ℝ)) = f x := ThreeArcCircleLemmas.lift_eq ι P a b c h₀ h₁ h₂ (this :=
          this) x hx
  let e : Circle → Real × Real := ℓ ∘ (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm
  refine ⟨⟨e, ?_⟩, ?_, ?_⟩
  · exact hℓc.comp (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm.continuous
  · intro x y hxy
    change ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x) =
      ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm y) at hxy
    let u := AddCircle.equivIco (3 : ℝ) 0
      ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x)
    let v := AddCircle.equivIco (3 : ℝ) 0
      ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm y)
    have hu : (u : AddCircle (3 : ℝ)) =
        (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x := by
      simp [u]
    have hv : (v : AddCircle (3 : ℝ)) =
        (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm y := by
      simp [v]
    have hfu : ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x) = f u := by
      rw [← hu]
      exact AddCircle.liftIco_coe_apply u.property
    have hfv : ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm y) = f v := by
      rw [← hv]
      exact AddCircle.liftIco_coe_apply v.property
    have hu' : (u : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by simpa using u.property
    have hv' : (v : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by simpa using v.property
    have huv : (u : ℝ) = (v : ℝ) :=
      hf_inj (u : ℝ) (v : ℝ) hu' hv' (by rw [← hfu, ← hfv]; exact hxy)
    have huv' : u = v := by
      apply Subtype.ext
      exact huv
    apply (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm.injective
    calc
      (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x = u := hu.symm
      _ = (v : AddCircle (3 : ℝ)) := congrArg
        (fun z : Set.Ico (0 : ℝ) (0 + 3) => (z : AddCircle (3 : ℝ))) huv'
      _ = (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm y := hv
  · have hrangeℓ : Set.range ℓ =
      P.edgeArc a b ∪ P.edgeArc b c ∪ P.edgeArc c a := ThreeArcCircleRange.hrangeℓ ι P a b c h₀
          h₀a h₀b h₁ h₁b h₁c h₂ h₂c h₂a (this := this) fseg₀ fseg₁ fseg₂ lift_eq
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hx : ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm x) ∈
          P.edgeArc a b ∪ P.edgeArc b c ∪ P.edgeArc c a := by
        rw [← hrangeℓ]
        exact ⟨_, rfl⟩
      exact hx
    · intro hz
      have hz' : z ∈ Set.range ℓ := by rw [hrangeℓ]; exact hz
      rcases hz' with ⟨y, hy⟩
      refine ⟨(AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)) y, ?_⟩
      change ℓ ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm
        ((AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)) y)) = z
      simpa using hy

end ApollonianSuperharmonic

end
