/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# A stack of horizontal rectangles

Each row is a rectangle of height one. The top of a stack of `n`
rows is at height `n`. A new row meets the stack only in the top
side of the last row. These set calculations support the disc
construction for the outer boundary of the wall in XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set

/-- The union of the first `n` horizontal rectangles with the given
left and right sides. -/
def rectangleStack (left right : ℕ → ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ k < n, Icc (left k) (right k) ×ˢ Icc (k : ℝ) ((k : ℝ)+1)

/-- Appending the next row is set union with its rectangle. -/
theorem rectangleStack_succ (left right : ℕ → ℝ) (n : ℕ) :
    rectangleStack left right (n+1) = rectangleStack left right n ∪
      (Icc (left n) (right n) ×ˢ Icc (n : ℝ) ((n : ℝ)+1)) := by
  exact biUnion_lt_succ _ _

/-- The vertical coordinate of a point in the first `n` rows is at most `n`. -/
theorem rectangleStack_vertical_le {left right : ℕ → ℝ} {n : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ rectangleStack left right n) : p.2 ≤ (n : ℝ) := by
  obtain ⟨k,hk,hp⟩ := mem_iUnion₂.mp hp
  have hk' : (k : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast hk
  exact hp.2.2.trans hk'

/-- A stack and the next row meet in the overlap of their horizontal
sides at the stack's top height. -/
theorem rectangleStack_inter_next {left right : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) :
    rectangleStack left right n ∩
      (Icc (left n) (right n) ×ˢ Icc (n : ℝ) ((n : ℝ)+1)) =
      Icc (max (left (n-1)) (left n)) (min (right (n-1)) (right n)) ×ˢ {(n : ℝ)} := by
  ext p
  constructor
  · rintro ⟨hp,hpNew⟩
    obtain ⟨k,hk,hpOld⟩ := mem_iUnion₂.mp hp
    have hnk : n ≤ k+1 := by exact_mod_cast (hpNew.2.1.trans hpOld.2.2)
    have hkn : k = n-1 := by omega
    have hpTop : p.2 = (n : ℝ) := le_antisymm
      (rectangleStack_vertical_le (mem_iUnion₂.mpr ⟨k,hk,hpOld⟩)) hpNew.2.1
    refine ⟨⟨max_le ?_ hpNew.1.1,le_min ?_ hpNew.1.2⟩,hpTop⟩
    · exact hkn ▸ hpOld.1.1
    · exact hkn ▸ hpOld.1.2
  · rintro ⟨⟨hpLo,hpHi⟩,hpTop⟩
    have hPrev : n-1 < n := by omega
    have hPrevReal : ((n-1 : ℕ) : ℝ)+1 = (n : ℝ) := by
      exact_mod_cast (show n-1+1=n by omega)
    have hPrevLe : ((n-1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show n-1≤n by omega)
    constructor
    · apply mem_iUnion₂.mpr
      refine ⟨n-1,hPrev,⟨⟨(max_le_iff.mp hpLo).1,(le_min_iff.mp hpHi).1⟩,?_⟩⟩
      exact ⟨hpTop.symm ▸ hPrevLe, by rw [hpTop,hPrevReal]⟩
    · exact ⟨⟨(max_le_iff.mp hpLo).2,(le_min_iff.mp hpHi).2⟩,
        ⟨hpTop.ge,by rw [hpTop]; exact le_add_of_nonneg_right zero_le_one⟩⟩

end GraphMinor.GM16
