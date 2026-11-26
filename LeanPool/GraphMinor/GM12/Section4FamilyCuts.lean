/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4FamilySubdivision
public import LeanPool.GraphMinor.GM12.Section4SubdivisionPositions
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The cuts of different source edges

In XII (4.5), page 252, the new vertices lie on their original
edges and avoid all crossings. An internal cut cannot be an old
vertex: an old edge contains only its own two old endpoints, and
the cut map is injective. These facts justify the injective global
vertex map of the subdivision.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- All cuts lie on the original edge, since consecutive pieces
cover that edge and have the cuts as ends. -/
theorem family_cut_mem_original_edge {n : ℕ} (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e) (e : Fin n) (r : Fin (k e + 1)) :
    w e r ∈ E e := by
  have hsub : ∀ i, P e i ⊆ E e := by
    intro i x hx
    rw [← hcover e]
    exact mem_iUnion.mpr ⟨i, hx⟩
  by_cases hr : r.val < k e
  · let i : Fin (k e) := ⟨r.val, hr⟩
    have heq : i.castSucc = r := Fin.ext rfl
    have hmem := (hline e i).left_mem
    rw [heq] at hmem
    exact hsub i hmem
  · let i : Fin (k e) := ⟨k e - 1, by have := hk e; omega⟩
    have heq : i.succ = r := by
      apply Fin.ext
      change k e - 1 + 1 = r.val
      have := hk e
      have := r.isLt
      omega
    have hmem := (hline e i).right_mem
    rw [heq] at hmem
    exact hsub i hmem

/-- An internal cut is not an original vertex. This uses the
original edges' exact vertex incidence and injectivity of their cut
maps, as in the subdivision of XII (4.5), page 252. -/
theorem internal_family_cut_not_mem_vertices {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (w : ∀ e, Fin (k e + 1) → ℂ)
    (hwinj : ∀ e, Function.Injective (w e))
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hmem : ∀ e i, w e i ∈ E e)
    (hvertex : ∀ e v, V v ∈ E e ↔ v = κ (e, false) ∨ v = κ (e, true))
    (e : Fin n) (j : Fin (k e - 1)) :
    w e ⟨j.val + 1, by have := j.isLt; omega⟩ ∉ range V := by
  let r : Fin (k e + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
  rintro ⟨v, hv⟩
  have hvE : V v ∈ E e := hv ▸ hmem e r
  rcases (hvertex e v).mp hvE with hleft | hright
  · have heq : w e r = w e 0 := hv.symm.trans ((congrArg V hleft).trans (hw0 e).symm)
    have hval := congrArg Fin.val (hwinj e heq)
    change j.val + 1 = 0 at hval
    omega
  · have heq : w e r = w e (Fin.last (k e)) :=
      hv.symm.trans ((congrArg V hright).trans (hwlast e).symm)
    have hval := congrArg Fin.val (hwinj e heq)
    change j.val + 1 = k e at hval
    have := j.isLt
    omega

/-- The global subdivision vertices lying on an original edge
are exactly the cuts of that edge. Internal cuts of other edges
cannot occur there, because they would be old meetings. -/
theorem original_edge_inter_subdivisionPositions {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e) (w : ∀ e, Fin (k e + 1) → ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hmem : ∀ e i, w e i ∈ E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hvertex : ∀ e v, V v ∈ E e ↔ v = κ (e, false) ∨ v = κ (e, true))
    (hinterior : ∀ e (j : Fin (k e - 1)),
      w e ⟨j.val + 1, by have := j.isLt; omega⟩ ∉ range V) (e : Fin n) :
    E e ∩ range (subdivisionPosition V k w) = range (w e) := by
  ext x
  constructor
  · rintro ⟨hxE, z, rfl⟩
    cases z with
    | inl v =>
      rcases (hvertex e v).mp hxE with hleft | hright
      · exact ⟨0, (hw0 e).trans (congrArg V hleft).symm⟩
      · exact ⟨Fin.last (k e), (hwlast e).trans (congrArg V hright).symm⟩
    | inr q =>
      obtain ⟨f, j⟩ := q
      let r : Fin (k f + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
      by_cases hfe : f = e
      · subst f
        exact ⟨r, rfl⟩
      · have hmeeting : w f r ∈ edgeMeetingPoints V E :=
          ⟨f, e, hfe, ⟨hmem f r, hxE⟩, hinterior f j⟩
        exact False.elim (havoid f r ⟨hmem f r, hmeeting⟩)
  · rintro ⟨r, rfl⟩
    exact ⟨hmem e r, subdivisionVertexAt κ k e r,
      subdivisionPosition_vertexAt V κ k hk w hw0 hwlast e r⟩

end GraphMinor.GM12
