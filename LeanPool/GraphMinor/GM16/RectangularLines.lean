/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings

/-!
# Straight sides of rectangles

Parametrising a horizontal or vertical side by its varying
coordinate proves it is a line. Unlike the unit lattice lines,
these sides can have any positive length. They are used when
joining rows of wall bricks into the disc bounded by the wall's
outer boundary in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Surface GM11

/-- A nondegenerate horizontal interval is a line. -/
theorem horizontal_interval_isLine {a b : ℝ} (hab : a < b) (c : ℝ) :
    IsLineWithEnds (Icc a b ×ˢ {c}) (a,c) (b,c) := by
  let f : ℝ → ℝ × ℝ := fun t => (t,c)
  have hc : Continuous f := continuous_id.prodMk continuous_const
  have hi : InjOn f (Icc a b) := fun _ _ _ _ h => congrArg Prod.fst h
  have he : f '' Icc a b = Icc a b ×ˢ {c} := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨ht,rfl⟩
    · rintro ⟨hx,hc⟩
      exact ⟨x.1,hx,Prod.ext rfl hc.symm⟩
  exact he ▸ isLine_of_injOn hc hab hi

/-- A nondegenerate vertical interval is a line. -/
theorem vertical_interval_isLine (c : ℝ) {a b : ℝ} (hab : a < b) :
    IsLineWithEnds ({c} ×ˢ Icc a b) (c,a) (c,b) := by
  let f : ℝ → ℝ × ℝ := fun t => (c,t)
  have hc : Continuous f := continuous_const.prodMk continuous_id
  have hi : InjOn f (Icc a b) := fun _ _ _ _ h => congrArg Prod.snd h
  have he : f '' Icc a b = {c} ×ˢ Icc a b := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨rfl,ht⟩
    · rintro ⟨hc,hx⟩
      exact ⟨x.2,hx,Prod.ext hc.symm rfl⟩
  exact he ▸ isLine_of_injOn hc hab hi

end GraphMinor.GM16
