/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Set.Card

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex

-- [TABLET NODE: BoundaryFootprintVertexDegreeTwo]

/-!
# BoundaryFootprintVertexDegreeTwo

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BoundaryFootprintVertexDegreeTwo (T : ProtoTile) (hne : T.cells.Nonempty)
    (hchecker : NoCheckerboardCellVertex (T.cells : Set LatticeCell))
    (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices T) :
    Set.ncard {e : Finset GaussianInt |
      e ∈ BoundaryFootprintEdges T ∧ v ∈ e} = 2 := by
-- BODY
  classical
  have incident_classify (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) (hve : v ∈ e) :
      e = {v, v + 1} ∨ e = {v - 1, v} ∨
        e = {v, v + ⟨0, 1⟩} ∨ e = {v - ⟨0, 1⟩, v} := by
    as_aux_lemma =>
    rcases he with ⟨z, (⟨rfl, hz⟩ | ⟨rfl, hz⟩)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hve
      rcases hve with rfl | hve
      · exact Or.inl rfl
      · subst v
        right; left
        congr 1; apply Zsqrtd.ext <;> simp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hve
      rcases hve with rfl | hve
      · exact Or.inr (Or.inr (Or.inl rfl))
      · subst v
        right; right; right
        congr 1; apply Zsqrtd.ext <;> simp
  have horizontal_unique (a b : GaussianInt)
      (h : {a, a + 1} = ({b, b + 1} : Finset GaussianInt)) : a = b := by
    as_aux_lemma =>
    have ha : a ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + 1 ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    · exact hab
    · exact hab
    · exfalso
      apply_fun Zsqrtd.re at hab ha1b
      simp at hab ha1b
      omega
    · exfalso
      apply_fun Zsqrtd.re at hab ha1b
      simp at hab ha1b
      omega
  have vertical_unique (a b : GaussianInt)
      (h : {a, a + ⟨0, 1⟩} =
        ({b, b + ⟨0, 1⟩} : Finset GaussianInt)) : a = b := by
    as_aux_lemma =>
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + ⟨0, 1⟩ ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    · exact hab
    · exact hab
    · exfalso
      apply_fun Zsqrtd.im at hab ha1b
      simp at hab ha1b
      omega
    · exfalso
      apply_fun Zsqrtd.im at hab ha1b
      simp at hab ha1b
      omega
  have horizontal_vertical_ne (a b : GaussianInt) :
      ({a, a + 1} : Finset GaussianInt) ≠ {b, b + ⟨0, 1⟩} := by
    as_aux_lemma =>
    intro h
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + 1 ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    all_goals apply_fun Zsqrtd.re at hab ha1b; simp at hab ha1b; omega
  have horizontal_mem_iff (z : GaussianInt) :
      ({z, z + 1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨
         (z ∉ T.cells ∧ z - ⟨0, 1⟩ ∈ T.cells)) := by
    as_aux_lemma =>
    constructor
    · rintro ⟨a, (⟨ha, hocc⟩ | ⟨ha, hocc⟩)⟩
      · have haz := horizontal_unique a z ha.symm
        simpa [haz] using hocc
      · exact False.elim (horizontal_vertical_ne z a ha)
    · intro h
      exact ⟨z, Or.inl ⟨rfl, h⟩⟩
  have vertical_mem_iff (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
         (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := by
    as_aux_lemma =>
    constructor
    · rintro ⟨a, (⟨ha, hocc⟩ | ⟨ha, hocc⟩)⟩
      · exact False.elim (horizontal_vertical_ne a z ha.symm)
      · have haz := vertical_unique a z ha.symm
        simpa [haz] using hocc
    · intro h
      exact ⟨z, Or.inr ⟨rfl, h⟩⟩
  rw [BoundaryFootprintVertices, ite_eq_left hne] at hv
  rcases hv with ⟨e0, he0, hve0⟩
  let F : Finset (Finset GaussianInt) :=
    {{v, v + 1}, {v - 1, v}, {v, v + ⟨0, 1⟩}, {v - ⟨0, 1⟩, v}}
  have hinc : {e : Finset GaussianInt |
      e ∈ BoundaryFootprintEdges T ∧ v ∈ e} =
      (↑(F.filter fun e => e ∈ BoundaryFootprintEdges T) :
        Set (Finset GaussianInt)) := by
    as_aux_lemma =>
    ext e
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨he, hve⟩
      refine ⟨?_, he⟩
      rcases incident_classify e he hve with h | h | h | h <;> simp [F, h]
    · rintro ⟨heF, he⟩
      refine ⟨he, ?_⟩
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at heF
      rcases heF with h | h | h | h <;> subst e <;> simp
  rw [hinc, Set.ncard_coe_finset]
  have hno := hchecker v
  have he0cases := incident_classify e0 he0 hve0
  have hHm : ({v - 1, v} : Finset GaussianInt) = {v - 1, (v - 1) + 1} := by
    simp
  have hVm : ({v - ⟨0, 1⟩, v} : Finset GaussianInt) =
      {v - ⟨0, 1⟩, (v - ⟨0, 1⟩) + ⟨0, 1⟩} := by
    simp
  have hHH : ({v, v + 1} : Finset GaussianInt) ≠ {v - 1, v} := by
    intro h
    have hvv := horizontal_unique v (v - 1) (h.trans hHm)
    apply_fun Zsqrtd.re at hvv
    simp at hvv
    omega
  have hVV : ({v, v + ⟨0, 1⟩} : Finset GaussianInt) ≠
      {v - ⟨0, 1⟩, v} := by
    intro h
    have hvv := vertical_unique v (v - ⟨0, 1⟩) (h.trans hVm)
    apply_fun Zsqrtd.im at hvv
    simp at hvv
    omega
  have hHV00 : ({v, v + 1} : Finset GaussianInt) ≠
      {v, v + ⟨0, 1⟩} := horizontal_vertical_ne v v
  have hHV01 : ({v, v + 1} : Finset GaussianInt) ≠
      {v - ⟨0, 1⟩, v} := by
    rw [hVm]
    exact horizontal_vertical_ne v (v - ⟨0, 1⟩)
  have hHV10 : ({v - 1, v} : Finset GaussianInt) ≠
      {v, v + ⟨0, 1⟩} := by
    rw [hHm]
    exact horizontal_vertical_ne (v - 1) v
  have hHV11 : ({v - 1, v} : Finset GaussianInt) ≠
      {v - ⟨0, 1⟩, v} := by
    rw [hHm, hVm]
    exact horizontal_vertical_ne (v - 1) (v - ⟨0, 1⟩)
  have hER := horizontal_mem_iff v
  have hEL : ({v - 1, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
      ((v - 1 ∈ T.cells ∧ v - 1 - ⟨0, 1⟩ ∉ T.cells) ∨
       (v - 1 ∉ T.cells ∧ v - 1 - ⟨0, 1⟩ ∈ T.cells)) := by
    simpa only [hHm] using horizontal_mem_iff (v - 1)
  have hEU := vertical_mem_iff v
  have hED : ({v - ⟨0, 1⟩, v} : Finset GaussianInt) ∈
      BoundaryFootprintEdges T ↔
      ((v - ⟨0, 1⟩ ∈ T.cells ∧ v - 1 - ⟨0, 1⟩ ∉ T.cells) ∨
       (v - ⟨0, 1⟩ ∉ T.cells ∧ v - 1 - ⟨0, 1⟩ ∈ T.cells)) := by
    rw [hVm]
    simpa only [sub_sub, add_comm] using vertical_mem_iff (v - ⟨0, 1⟩)
  have hsome :
      ({v, v + 1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∨
      ({v - 1, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∨
      ({v, v + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∨
      ({v - ⟨0, 1⟩, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    rcases he0cases with h | h | h | h
    · exact Or.inl (h ▸ he0)
    · exact Or.inr (Or.inl (h ▸ he0))
    · exact Or.inr (Or.inr (Or.inl (h ▸ he0)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ he0)))
  by_cases hA : v ∈ T.cells
  all_goals by_cases hB : v - 1 ∈ T.cells
  all_goals by_cases hC : v - ⟨0, 1⟩ ∈ T.cells
  all_goals by_cases hD : v - 1 - ⟨0, 1⟩ ∈ T.cells
  all_goals simp [hER, hEL, hEU, hED, hA, hB, hC, hD] at hno hsome
  all_goals simp only [F, Finset.filter_insert, Finset.filter_singleton]
  all_goals simp [hER, hEL, hEU, hED, hA, hB, hC, hD,
    hHH, hVV, hHV00, hHV01, hHV10, hHV11]

end ApollonianSuperharmonic

end
