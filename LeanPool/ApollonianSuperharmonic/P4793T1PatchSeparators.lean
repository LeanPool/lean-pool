/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import LeanPool.ApollonianSuperharmonic.P4783T1PatchCoordinates

-- [TABLET NODE: P4793T1PatchSeparators]

/-!
# P4793T1PatchSeparators

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1PatchSeparators (i j : Fin 12) (hij : i < j) :
    let p := fun j => P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j)
    ∃ a b c : Int,
      let f := fun z : Real × Real => (a : Real)*(12*z.1)+(b : Real)*(12*z.2)+(c : Real)
      (∀ k, 0 ≤ f (p i k)) ∧ (∀ k, f (p j k) ≤ 0) ∧
      ((∀ k, f (p i k) = 0 → ∃ l, p i k = p j l) ∨
       (∀ k, f (p j k) = 0 → ∃ l, p j k = p i l)) := by
-- BODY
  let q : Fin 12 → Fin 3 → Int × Int := ![
    ![(0, 0), (-4, -8), (-6, -6)],
    ![(-12, -12), (-4, -8), (-6, -6)],
    ![(-12, 0), (-16, -8), (-10, -2)],
    ![(-12, 0), (-4, 4), (-10, -2)],
    ![(-12, -12), (-6, -6), (-11, -7)],
    ![(-6, -6), (-10, -2), (-11, -7)],
    ![(-16, -8), (-10, -2), (-11, -7)],
    ![(-12, -12), (-16, -8), (-11, -7)],
    ![(0, 0), (-6, -6), (-5, -1)],
    ![(-6, -6), (-10, -2), (-5, -1)],
    ![(-4, 4), (-10, -2), (-5, -1)],
    ![(0, 0), (-4, 4), (-5, -1)]]
  let sep : Fin 12 → Fin 12 → Int × Int × Int := ![
    ![(0, 0, 0), (1, 1, 12), (1, -1, 0), (1, -1, 0), (1, 0, 6), (1, -1, 0), (1, -1, 0), (1, 0,
        6), (1, -1, 0), (1, -1, 0), (1, -1, 0), (1, -1, 0)],
    ![(0, 0, 0), (0, 0, 0), (1, -1, 0), (0, -1, -6), (1, -1, 0), (1, -1, 0), (1, -1, 0), (1, -1,
        0), (-1, -1, -12), (0, -1, -6), (0, -1, -6), (-1, -1, -12)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (-1, -1, -12), (-1, 1, -8), (-1, 1, -8), (-1, 1, -8), (-1,
        1, -8), (-1, 0, -10), (-1, 0, -10), (-1, -1, -12), (-1, -1, -12)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (-1, 1, -8), (-1, 1, -8), (0, 1, 2), (0, 1, 2),
        (-1, 1, -8), (-1, 1, -8), (-1, 1, -8), (-1, 1, -8)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (1, -5, -24), (1, -1, 4), (5, -1,
        48), (-1, -1, -12), (-1, -1, -12), (0, -1, -6), (-1, -1, -12)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (5, -1, 48), (0, 1, 7),
        (-1, -1, -12), (-1, -1, -12), (-1, -1, -12), (-1, -1, -12)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (-1, 5, 24),
        (-1, 0, -10), (-1, -1, -12), (-1, -1, -12), (-1, -1, -12)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
        (-1, -1, -18), (-1, -1, -18), (-1, -1, -18), (-1, -1, -18)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0,
        0, 0), (5, -1, 24), (1, -1, 4), (1, -5, 0)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0,
        0, 0), (0, 0, 0), (1, -5, 0), (-1, -1, -6)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0,
        0, 0), (0, 0, 0), (0, 0, 0), (-5, 1, -24)],
    ![(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0,
        0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]]
  let ev := fun (t : Int × Int × Int) (z : Int × Int) =>
    t.1*z.1+t.2.1*z.2+t.2.2
  have cert : ∀ i j : Fin 12, i < j →
      (∀ k : Fin 3, 0 ≤ ev (sep i j) (q i k)) ∧
      (∀ k : Fin 3, ev (sep i j) (q j k) ≤ 0) ∧
      ((∀ k : Fin 3, ev (sep i j) (q i k) = 0 → ∃ l, q i k = q j l) ∨
       (∀ k : Fin 3, ev (sep i j) (q j k) = 0 → ∃ l, q j k = q i l)) := by
    decide +kernel
  let p := fun j => P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j)
  have coordinates (j : Fin 12) (k : Fin 3) :
      12*(p j k).1 = ((q j k).1 : Real) ∧
      12*(p j k).2 = ((q j k).2 : Real) := by
    dsimp only [p]
    rw [P4783T1PatchCoordinates]
    fin_cases j <;> fin_cases k <;> norm_num [q]
  let f := fun z : Real × Real =>
    ((sep i j).1 : Real)*(12*z.1)+((sep i j).2.1 : Real)*(12*z.2)+((sep i j).2.2 : Real)
  have values (r : Fin 12) (k : Fin 3) :
      f (p r k) = (ev (sep i j) (q r k) : Real) := by
    dsimp only [f, ev]
    rw [(coordinates r k).1, (coordinates r k).2]
    push_cast
    rfl
  have equal (r s : Fin 12) (k l : Fin 3) (h : q r k = q s l) :
      p r k = p s l := by
    have hx := congrArg (fun z : Int × Int => (z.1 : Real)) h
    have hy := congrArg (fun z : Int × Int => (z.2 : Real)) h
    ext
    · linarith [(coordinates r k).1, (coordinates s l).1]
    · linarith [(coordinates r k).2, (coordinates s l).2]
  refine ⟨(sep i j).1, (sep i j).2.1, (sep i j).2.2, ?_, ?_, ?_⟩
  · intro k
    change 0 ≤ f (p i k)
    rw [values]
    exact_mod_cast (cert i j hij).1 k
  · intro k
    change f (p j k) ≤ 0
    rw [values]
    exact_mod_cast (cert i j hij).2.1 k
  · rcases (cert i j hij).2.2 with h | h
    · left
      intro k hk
      change f (p i k) = 0 at hk
      rw [values] at hk
      have hk' : ev (sep i j) (q i k) = 0 := by exact_mod_cast hk
      obtain ⟨l, hl⟩ := h k hk'
      exact ⟨l, equal i j k l hl⟩
    · right
      intro k hk
      change f (p j k) = 0 at hk
      rw [values] at hk
      have hk' : ev (sep i j) (q j k) = 0 := by exact_mod_cast hk
      obtain ⟨l, hl⟩ := h k hk'
      exact ⟨l, equal j i k l hl⟩

end ApollonianSuperharmonic

end
