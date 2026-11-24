/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Unit lattice lines for the wall drawing

The planar wall in XVI (4.2), page 53, uses horizontal and vertical
unit segments between lattice points. Parametrising each interval
proves that it is a line with the intended ends. The coordinate
lemmas below describe which lattice points lie on such a line.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A lattice point in the real coordinate plane. -/
def latticePoint (p : ℕ × ℕ) : ℝ × ℝ := (p.1,p.2)

/-- The horizontal unit line starting at `(i,j)`. -/
def horizontalLatticeLine (i j : ℕ) : Set (ℝ × ℝ) :=
  Icc (i : ℝ) ((i : ℝ) + 1) ×ˢ {(j : ℝ)}

/-- The vertical unit line starting at `(i,j)`. -/
def verticalLatticeLine (i j : ℕ) : Set (ℝ × ℝ) :=
  {(i : ℝ)} ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)

/-- A horizontal lattice segment is a line with its indicated ends. -/
theorem horizontalLatticeLine_isLine (i j : ℕ) :
    IsLineWithEnds (horizontalLatticeLine i j) (latticePoint (i,j)) (latticePoint (i+1,j)) := by
  let p : ℝ → ℝ × ℝ := fun t => ((i : ℝ) + t, j)
  have hp : Continuous p := by fun_prop
  have hi : InjOn p (Icc (0 : ℝ) 1) := by
    intro s _ t _ heq
    have h := congrArg Prod.fst heq
    dsimp only [p] at h
    linarith
  have hImage : p '' Icc (0 : ℝ) 1 = horizontalLatticeLine i j := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨by dsimp only [p]; linarith [ht.1], by dsimp only [p]; linarith [ht.2]⟩, rfl⟩
    · rintro ⟨hx,hj⟩
      refine ⟨x.1 - i,⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
      apply Prod.ext
      · dsimp only [p]
        linarith
      · exact hj.symm
  have h := isLine_of_injOn hp (by norm_num : (0 : ℝ) < 1) hi
  simpa only [hImage,p,latticePoint,Nat.cast_add,Nat.cast_one,add_zero] using h

/-- A vertical lattice segment is a line with its indicated ends. -/
theorem verticalLatticeLine_isLine (i j : ℕ) :
    IsLineWithEnds (verticalLatticeLine i j) (latticePoint (i,j)) (latticePoint (i,j+1)) := by
  let p : ℝ → ℝ × ℝ := fun t => (i, (j : ℝ) + t)
  have hp : Continuous p := by fun_prop
  have hi : InjOn p (Icc (0 : ℝ) 1) := by
    intro s _ t _ heq
    have h := congrArg Prod.snd heq
    dsimp only [p] at h
    linarith
  have hImage : p '' Icc (0 : ℝ) 1 = verticalLatticeLine i j := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨rfl,⟨by dsimp only [p]; linarith [ht.1],by dsimp only [p]; linarith [ht.2]⟩⟩
    · rintro ⟨hi,hx⟩
      refine ⟨x.2 - j,⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
      apply Prod.ext
      · exact hi.symm
      · dsimp only [p]
        linarith
  have h := isLine_of_injOn hp (by norm_num : (0 : ℝ) < 1) hi
  simpa only [hImage,p,latticePoint,Nat.cast_add,Nat.cast_one,add_zero] using h

/-- The only lattice points on a horizontal unit line are its ends. -/
theorem latticePoint_mem_horizontal {i j k l : ℕ}
    (h : latticePoint (k, l) ∈ horizontalLatticeLine i j) :
    (k,l) = (i,j) ∨ (k,l) = (i+1,j) := by
  have hj : l = j := Nat.cast_injective h.2
  have hloR : (i : ℝ) ≤ (k : ℝ) := h.1.1
  have hhiR : (k : ℝ) ≤ (i : ℝ) + 1 := h.1.2
  have hlo : i ≤ k := by exact_mod_cast hloR
  have hhi : k ≤ i + 1 := by exact_mod_cast hhiR
  have hk : k = i ∨ k = i + 1 := by omega
  exact hk.elim (fun heq => Or.inl (Prod.ext heq hj)) (fun heq => Or.inr (Prod.ext heq hj))

/-- The only lattice points on a vertical unit line are its ends. -/
theorem latticePoint_mem_vertical {i j k l : ℕ}
    (h : latticePoint (k, l) ∈ verticalLatticeLine i j) :
    (k,l) = (i,j) ∨ (k,l) = (i,j+1) := by
  have hi : k = i := Nat.cast_injective h.1
  have hloR : (j : ℝ) ≤ (l : ℝ) := h.2.1
  have hhiR : (l : ℝ) ≤ (j : ℝ) + 1 := h.2.2
  have hlo : j ≤ l := by exact_mod_cast hloR
  have hhi : l ≤ j + 1 := by exact_mod_cast hhiR
  have hl : l = j ∨ l = j + 1 := by omega
  exact hl.elim (fun heq => Or.inl (Prod.ext hi heq)) (fun heq => Or.inr (Prod.ext hi heq))

end GraphMinor.GM16
