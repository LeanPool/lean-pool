/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionGraph
public import LeanPool.GraphMinor.GM12.Section4CrossingPoints

/-!
# Positions of the subdivision vertices

In XII (4.5), page 252, keep the original vertex positions and
put each new vertex at its internal cut. The two endpoint cuts
agree with their original vertices. Internal cuts avoid original
vertices and all meetings of different original edges, so the
resulting global vertex-position map is injective.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The position of an original or internal vertex in the source
subdivision of XII (4.5), page 252. -/
@[expose] def subdivisionPosition {m n : ℕ} (V : Fin m → ℂ) (k : Fin n → ℕ)
    (w : ∀ e, Fin (k e + 1) → ℂ) : SubdivisionVertex m n k → ℂ
  | Sum.inl v => V v
  | Sum.inr ⟨e, j⟩ => w e ⟨j.val + 1, by have := j.isLt; omega⟩

/-- The position map agrees with every cut on every original
edge, including the endpoint cuts. -/
theorem subdivisionPosition_vertexAt {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (e : Fin n) (i : Fin (k e + 1)) :
    subdivisionPosition V k w (subdivisionVertexAt κ k e i) = w e i := by
  by_cases hi0 : i.val = 0
  · have heq : i = 0 := Fin.ext hi0
    subst i
    rw [subdivisionVertexAt_zero]
    exact (hw0 e).symm
  by_cases hilast : i.val = k e
  · have heq : i = Fin.last (k e) := Fin.ext hilast
    subst i
    rw [subdivisionVertexAt_last κ k e (hk e)]
    exact (hwlast e).symm
  · unfold subdivisionVertexAt
    simp only [hi0, hilast, ↓reduceDIte, subdivisionPosition]
    apply congrArg (w e)
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega

/-- Avoiding old vertices and old edge meetings makes the global
subdivision positions distinct. This is the injectivity assertion
for the source subdivision in XII (4.5), page 252. -/
theorem subdivisionPosition_injective {m n : ℕ}
    (V : Fin m → ℂ) (E : Fin n → Set ℂ) (k : Fin n → ℕ)
    (w : ∀ e, Fin (k e + 1) → ℂ) (hV : Function.Injective V)
    (hw : ∀ e, Function.Injective (w e))
    (hmem : ∀ e i, w e i ∈ E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hinterior : ∀ e (j : Fin (k e - 1)),
      w e ⟨j.val + 1, by have := j.isLt; omega⟩ ∉ range V) :
    Function.Injective (subdivisionPosition V k w) := by
  intro x y hxy
  cases x with
  | inl u =>
    cases y with
    | inl v => exact congrArg Sum.inl (hV hxy)
    | inr q =>
      obtain ⟨e, j⟩ := q
      exact False.elim (hinterior e j ⟨u, hxy⟩)
  | inr q =>
    obtain ⟨e, j⟩ := q
    cases y with
    | inl v => exact False.elim (hinterior e j ⟨v, hxy.symm⟩)
    | inr q' =>
      obtain ⟨f, l⟩ := q'
      by_cases hef : e = f
      · subst f
        have hcut := hw e hxy
        have hval := congrArg Fin.val hcut
        change j.val + 1 = l.val + 1 at hval
        have hjl : j = l := Fin.ext (by omega)
        subst l
        rfl
      · let r : Fin (k e + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
        let s : Fin (k f + 1) := ⟨l.val + 1, by have := l.isLt; omega⟩
        have heq : w e r = w f s := hxy
        have hmeeting : w e r ∈ edgeMeetingPoints V E :=
          ⟨e, f, hef, ⟨hmem e r, heq ▸ hmem f s⟩, hinterior e j⟩
        exact False.elim (havoid e r ⟨hmem e r, hmeeting⟩)

/-- No vertex of the global subdivision is an old meeting point.
The original vertices are excluded by definition, and every new
vertex is a cut chosen away from meetings in XII (4.5), page 252. -/
theorem disjoint_subdivisionPositions_meetings {m n : ℕ}
    (V : Fin m → ℂ) (E : Fin n → Set ℂ) (k : Fin n → ℕ)
    (w : ∀ e, Fin (k e + 1) → ℂ)
    (hmem : ∀ e i, w e i ∈ E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E) :
    Disjoint (range (subdivisionPosition V k w)) (edgeMeetingPoints V E) := by
  apply disjoint_left.mpr
  rintro x ⟨v, rfl⟩ hx
  cases v with
  | inl z =>
    obtain ⟨i, j, hij, hmeet, hnot⟩ := hx
    exact hnot ⟨z, rfl⟩
  | inr q =>
    obtain ⟨e, j⟩ := q
    exact havoid e _ ⟨hmem e _, hx⟩

end GraphMinor.GM12
