/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3102T2PeriodicFourSectorObstruction
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionPaths

-- [TABLET NODE: P3102T2OppositeOwnersCommonEdge]

/-!
# P3102T2OppositeOwnersCommonEdge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3102T2OppositeOwnersCommonEdge
    {ι : Type} (P : PeriodicTileComplex ι)
    (hpartition : ∀ c : LatticeCell, ∃! o : ι, c ∈ (P.tile o).cells)
    (a b : ι) (hab : a ≠ b) (x : GaussianInt) (j : Fin 4)
    (hma : LatticeVertexIncidentCell x j ∈ (P.tile a).cells)
    (hmb : LatticeVertexIncidentCell x (j + 2) ∈ (P.tile b).cells) :
    ∃ e : Finset GaussianInt, x ∈ e ∧
      e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b) := by
-- BODY
  classical
  let owner : Fin 4 → ι := fun k =>
    (hpartition (LatticeVertexIncidentCell x k)).choose
  have howner (k : Fin 4) :
      LatticeVertexIncidentCell x k ∈ (P.tile (owner k)).cells :=
    (hpartition _).choose_spec.1
  have own_a : owner j = a := (hpartition _).unique (howner j) hma
  have own_b : owner (j + 2) = b := (hpartition _).unique (howner (j + 2)) hmb
  let edgeAt : Fin 4 → Finset GaussianInt :=
    ![{x, x + ⟨0, 1⟩}, {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}]
  have radial (k : Fin 4) : x ∈ edgeAt k ∧
      edgeAt k ∈ FootprintEdges (P.tile (owner k)) ∩
        FootprintEdges (P.tile (owner (k + 1))) := by
    refine ⟨?_, ?_, ?_⟩
    · fin_cases k <;> simp [edgeAt]
    · refine ⟨LatticeVertexIncidentCell x k, howner k, ?_⟩
      fin_cases k <;> simp [LatticeVertexIncidentCell, edgeAt,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Finset.pair_comm]
    · refine ⟨LatticeVertexIncidentCell x (k + 1), howner (k + 1), ?_⟩
      fin_cases k <;> simp [LatticeVertexIncidentCell, edgeAt,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Finset.pair_comm]
  by_contra hnone
  have prohibit (k : Fin 4)
      (hk : (owner k = a ∧ owner (k + 1) = b) ∨
        (owner k = b ∧ owner (k + 1) = a)) : False := by
    obtain ⟨hxe, he⟩ := radial k
    apply hnone
    refine ⟨edgeAt k, hxe, ?_⟩
    rcases hk with h | h
    · simpa only [h.1, h.2] using he
    · exact ⟨by simpa only [h.2] using he.2, by simpa only [h.1] using he.1⟩
  have hadd : j + 1 + 1 = j + 2 ∧ j + 2 + 1 = j + 3 ∧ j + 3 + 1 = j := by
    fin_cases j <;> decide +kernel
  have hc_a : owner (j + 1) ≠ a := by
    intro h
    exact prohibit (j + 1) (Or.inl ⟨h, by rw [hadd.1, own_b]⟩)
  have hc_b : owner (j + 1) ≠ b := by
    intro h
    exact prohibit j (Or.inl ⟨own_a, h⟩)
  have hd_a : owner (j + 3) ≠ a := by
    intro h
    exact prohibit (j + 2) (Or.inr ⟨own_b, by rw [hadd.2.1]; exact h⟩)
  have hd_b : owner (j + 3) ≠ b := by
    intro h
    exact prohibit (j + 3) (Or.inr ⟨h, by rw [hadd.2.2, own_a]⟩)
  have hcd : owner (j + 1) ≠ owner (j + 3) := by
    intro h
    have hm1 := howner (j + 1)
    have hm3 : LatticeVertexIncidentCell x (j + 3) ∈
        (P.tile (owner (j + 1))).cells := by
      simpa only [h] using howner (j + 3)
    have hn0 : LatticeVertexIncidentCell x j ∉ (P.tile (owner (j + 1))).cells := by
      intro hc
      exact hc_a ((hpartition _).unique hc (by simpa only [own_a] using howner j))
    have hn2 : LatticeVertexIncidentCell x (j + 2) ∉
        (P.tile (owner (j + 1))).cells := by
      intro hc
      exact hc_b ((hpartition _).unique hc
        (by simpa only [own_b] using howner (j + 2)))
    have hcheck := (LatticeTileGridStructure _ (P.tiles_are_disks (owner (j + 1)))).2.1 x
    fin_cases j <;>
      simp [LatticeVertexIncidentCell] at hm1 hm3 hn0 hn2 hcheck <;>
      tauto
  have hinjective : Function.Injective owner := by
    have h02 : owner j ≠ owner (j + 2) := by simpa only [own_a, own_b] using hab
    have h10 : owner (j + 1) ≠ owner j := by simpa only [own_a] using hc_a
    have h12 : owner (j + 1) ≠ owner (j + 2) := by simpa only [own_b] using hc_b
    have h30 : owner (j + 3) ≠ owner j := by simpa only [own_a] using hd_a
    have h32 : owner (j + 3) ≠ owner (j + 2) := by simpa only [own_b] using hd_b
    intro r s hrs
    have positions (k : Fin 4) : k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = j + 3 := by
      fin_cases j <;> fin_cases k <;> decide +kernel
    rcases positions r with rfl | rfl | rfl | rfl <;>
      rcases positions s with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exact (h02 hrs).elim
      | exact (h02 hrs.symm).elim
      | exact (h10 hrs).elim
      | exact (h10 hrs.symm).elim
      | exact (h12 hrs).elim
      | exact (h12 hrs.symm).elim
      | exact (h30 hrs).elim
      | exact (h30 hrs.symm).elim
      | exact (h32 hrs).elim
      | exact (h32 hrs.symm).elim
      | exact (hcd hrs).elim
      | exact (hcd hrs.symm).elim
  have hregular := (PeriodicTileIntersectionClassification P).2
  obtain ⟨_, f, g, _, hf, hg, _, hpath⟩ :=
    (PeriodicTileIntersectionPaths P hregular (owner 0) (owner 1)
      (hinjective.ne (by decide +kernel))).1.mpr ⟨edgeAt 0, (radial 0).2⟩
  exact P3102T2PeriodicFourSectorObstruction P hregular hpartition x owner
    howner hinjective f g hf hg hpath

end ApollonianSuperharmonic

end
