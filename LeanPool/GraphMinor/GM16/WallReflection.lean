/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallHorizontalBoundary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reflection across the middle of the wall

Every row interval is symmetric about the same vertical line.
Horizontal reflection therefore preserves the enclosed disc and
its frontier. It carries the left horizontal joins to the right
joins, and will also carry left outside-face boundary lines to
the corresponding right boundary lines.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Reflection across the vertical line through the wall's middle. -/
def wallHorizontalReflection (θ : ℕ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (2*(θ : ℝ)-p.1,p.2)
  invFun p := (2*(θ : ℝ)-p.1,p.2)
  left_inv p := Prod.ext (by dsimp; ring) rfl
  right_inv p := Prod.ext (by dsimp; ring) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Reflecting twice is the identity. -/
theorem wallHorizontalReflection_involutive (θ : ℕ) : Function.Involutive
  (wallHorizontalReflection θ) := by
  intro p
  exact Prod.ext (by dsimp [wallHorizontalReflection]; ring) rfl

/-- The enclosed stack is symmetric under horizontal reflection. -/
theorem wallHorizontalReflection_mem_iff (θ : ℕ) (p : ℝ × ℝ) :
    wallHorizontalReflection θ p ∈ wallEnclosedSet θ ↔ p ∈ wallEnclosedSet θ := by
  constructor
  · intro hp
    obtain ⟨k,hk,hp⟩ := mem_iUnion₂.mp hp
    apply mem_iUnion₂.mpr
    refine ⟨k,hk,?_,hp.2⟩
    have hHor : wallRowLeft k ≤ 2*(θ : ℝ)-p.1 ∧
        2*(θ : ℝ)-p.1 ≤ ((2*θ : ℕ) : ℝ)-wallRowLeft k := hp.1
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hHor
    dsimp only [wallRowRight]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    constructor <;> linarith [hHor.1,hHor.2]
  · intro hp
    obtain ⟨k,hk,hp⟩ := mem_iUnion₂.mp hp
    apply mem_iUnion₂.mpr
    refine ⟨k,hk,?_,hp.2⟩
    have hHor : wallRowLeft k ≤ p.1 ∧ p.1 ≤ ((2*θ : ℕ) : ℝ)-wallRowLeft k := hp.1
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hHor
    change wallRowLeft k ≤ 2*(θ : ℝ)-p.1 ∧
      2*(θ : ℝ)-p.1 ≤ ((2*θ : ℕ) : ℝ)-wallRowLeft k
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    constructor <;> linarith [hHor.1,hHor.2]

/-- Reflection preserves the enclosed set. -/
theorem wallHorizontalReflection_image (θ : ℕ) :
    wallHorizontalReflection θ '' wallEnclosedSet θ = wallEnclosedSet θ := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (wallHorizontalReflection_mem_iff θ q).mpr hq
  · intro hp
    exact ⟨wallHorizontalReflection θ p,(wallHorizontalReflection_mem_iff θ p).mpr hp,
      wallHorizontalReflection_involutive θ p⟩

/-- Reflection preserves the enclosed set's frontier. -/
theorem wallHorizontalReflection_frontier (θ : ℕ) :
    wallHorizontalReflection θ '' frontier (wallEnclosedSet θ) = frontier (wallEnclosedSet θ) := by
  rw [(wallHorizontalReflection θ).image_frontier,wallHorizontalReflection_image]

/-- Reflection carries a closed rectangle to the reflected rectangle. -/
theorem wallHorizontalReflection_image_rectangle (θ : ℕ) (a b c d : ℝ) :
    wallHorizontalReflection θ '' (Icc a b ×ˢ Icc c d) =
      Icc (2*(θ : ℝ)-b) (2*(θ : ℝ)-a) ×ˢ Icc c d := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change (2*(θ : ℝ)-b ≤ 2*(θ : ℝ)-q.1 ∧
      2*(θ : ℝ)-q.1 ≤ 2*(θ : ℝ)-a) ∧ q.2 ∈ Icc c d
    exact ⟨⟨by linarith [hq.1.2],by linarith [hq.1.1]⟩,hq.2⟩
  · intro hp
    refine ⟨wallHorizontalReflection θ p,?_,wallHorizontalReflection_involutive θ p⟩
    change (a ≤ 2*(θ : ℝ)-p.1 ∧ 2*(θ : ℝ)-p.1 ≤ b) ∧ p.2 ∈ Icc c d
    exact ⟨⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩,hp.2⟩

/-- The short horizontal joins on the right are on the outer boundary. -/
theorem wall_right_horizontal_join_subset_frontier {θ j : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ) (hj : j < θ) :
    Icc (2*(θ : ℝ)-1) (2*(θ : ℝ)) ×ˢ {(j : ℝ)} ⊆ frontier (wallEnclosedSet θ) := by
  rintro p ⟨hx,hy⟩
  have hLeft : wallHorizontalReflection θ p ∈ Icc (0 : ℝ) 1 ×ˢ {(j : ℝ)} := by
    change (0 ≤ 2*(θ : ℝ)-p.1 ∧ 2*(θ : ℝ)-p.1 ≤ 1) ∧ p.2 = (j : ℝ)
    exact ⟨⟨by linarith [hx.2],by linarith [hx.1]⟩,hy⟩
  have hFr := wall_left_horizontal_join_subset_frontier hθ hEven hj hLeft
  have hImage : p ∈ wallHorizontalReflection θ '' frontier (wallEnclosedSet θ) :=
    ⟨wallHorizontalReflection θ p,hFr,wallHorizontalReflection_involutive θ p⟩
  exact wallHorizontalReflection_frontier θ ▸ hImage

end GraphMinor.GM16
