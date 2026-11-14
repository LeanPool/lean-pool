/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementBoundaryAtLeastThree
public import LeanPool.GoldbergSeymour.ScheideReplacementBoundaryAtMostThree

public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementTreeSplice

/-!
# Scheide Replacement Family Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ScheideReplacementFamilyExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    Nonempty (∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) := by
  classical
  refine ⟨fun d => ?_⟩
  let X := TreeSequenceVertexSet T
  let Z := X \ {C.blockVertex (D.gammaIndex d) 0,
    C.blockVertex (D.gammaIndex d) 1}
  letI outsideDec : DecidablePred (fun f : E =>
      ∃ w, w ∉ X ∧ Incident G w f) :=
    fun _ => Classical.propDecidable _
  let B := (BoundaryColorEdges G phi Z d.1).filter
    (fun f => ∃ w, w ∉ X ∧ Incident G w f)
  have hparity := ScheideReplacementBoundaryParity G k e0 phi T C D d
  have hupper := ScheideReplacementBoundaryAtMostThree G k e0 phi T C D d
  have hlower := ScheideReplacementBoundaryAtLeastThree G k e0 phi T C D d
  dsimp only at hparity hupper hlower
  have hv0Z : D.v0 d ∈ Z := by simpa [X, Z] using hparity.1
  have hf0B : D.f0 d ∈ B := by simpa [X, Z, B] using hparity.2.2.2.1
  change B.card ≤ 3 at hupper
  change 3 ≤ B.card at hlower
  have hupperB : B.card ≤ 3 := hupper
  have hlowerB : 3 ≤ B.card := hlower
  have hBcard : B.card = 3 := by omega
  have hEraseCard : (B.erase (D.f0 d)).card = 2 := by
    rw [Finset.card_erase_of_mem hf0B, hBcard]
  have hpair := Finset.card_eq_two.mp hEraseCard
  let f1 : E := Classical.choose hpair
  have hpair1 := Classical.choose_spec hpair
  let f2 : E := Classical.choose hpair1
  have hpair2 := Classical.choose_spec hpair1
  have hf1f2 : f1 ≠ f2 := hpair2.1
  have hErase : B.erase (D.f0 d) = {f1, f2} := hpair2.2
  have hf1Erase : f1 ∈ B.erase (D.f0 d) := by
    rw [hErase]
    simp
  have hf2Erase : f2 ∈ B.erase (D.f0 d) := by
    rw [hErase]
    simp
  have hf1B : f1 ∈ B := (Finset.mem_erase.mp hf1Erase).2
  have hf2B : f2 ∈ B := (Finset.mem_erase.mp hf2Erase).2
  have hf0f1 : D.f0 d ≠ f1 := (Finset.mem_erase.mp hf1Erase).1.symm
  have hf0f2 : D.f0 d ≠ f2 := (Finset.mem_erase.mp hf2Erase).1.symm
  have hB : B = {D.f0 d, f1, f2} := by
    simpa [hErase] using (Finset.insert_erase hf0B).symm
  have orient (f : E) (hf : f ∈ B) :
      ∃ v ∈ Z, ∃ u ∉ X,
        G.ends f = s(v, u) ∧ phi f = some d.1 := by
    have hfFilter := Finset.mem_filter.mp hf
    rcases hfFilter.2 with ⟨w, hwX, hwf⟩
    have hfColor := (Finset.mem_filter.mp hfFilter.1).2
    have hfBoundary := (Finset.mem_filter.mp hfFilter.1).1
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hfBoundary
    rcases hfBoundary with ⟨v, hvZ, u, huZ, hends⟩
    have hwPair : w = v ∨ w = u := by
      simpa [Incident, hends] using hwf
    have hwv : w ≠ v := by
      intro heq
      apply hwX
      rw [heq]
      exact (Finset.mem_sdiff.mp hvZ).1
    have hwu : w = u := hwPair.resolve_left hwv
    refine ⟨v, hvZ, u, ?_, hends, hfColor⟩
    simpa [hwu] using hwX
  have hf1Orient := orient f1 hf1B
  let v1 : V := Classical.choose hf1Orient
  have hf1Orient1 := Classical.choose_spec hf1Orient
  have hv1Z : v1 ∈ Z := hf1Orient1.1
  let u1 : V := Classical.choose hf1Orient1.2
  have hf1Orient2 := Classical.choose_spec hf1Orient1.2
  have hu1X : u1 ∉ X := hf1Orient2.1
  have hf1Ends : G.ends f1 = s(v1, u1) := hf1Orient2.2.1
  have hf1Color : phi f1 = some d.1 := hf1Orient2.2.2
  have hf2Orient := orient f2 hf2B
  let v2 : V := Classical.choose hf2Orient
  have hf2Orient1 := Classical.choose_spec hf2Orient
  have hv2Z : v2 ∈ Z := hf2Orient1.1
  let u2 : V := Classical.choose hf2Orient1.2
  have hf2Orient2 := Classical.choose_spec hf2Orient1.2
  have hu2X : u2 ∉ X := hf2Orient2.1
  have hf2Ends : G.ends f2 = s(v2, u2) := hf2Orient2.2.1
  have hf2Color : phi f2 = some d.1 := hf2Orient2.2.2
  have hu1u2 : u1 ≠ u2 := by
    intro hu
    have hi1 : Incident G u1 f1 := by
      simp [Incident, hf1Ends]
    have hi2 : Incident G u1 f2 := by
      simp [Incident, hf2Ends, hu]
    have hadj : AdjacentEdges G f1 f2 := ⟨u1, hi1, hi2⟩
    have hproper : IsProperEdgeColoring G phi :=
      C.globally_maximum.1.2.2.2.1
    exact (hproper hf1f2 hadj hf1Color) hf2Color
  have hExactThree :
    ∀ f : E, (f ∈ BoundaryColorEdges G phi Z d.1 ∧
    ∃ w, w ∉ X ∧ Incident G w f) ↔ f = D.f0 d ∨ f = f1 ∨ f = f2 := by
    intro f
    have hmem :
        (f ∈ BoundaryColorEdges G phi Z d.1 ∧
          ∃ w, w ∉ X ∧ Incident G w f) ↔ f ∈ B := by
      simp [B]
    rw [hmem, hB]
    simp
  have hsplice := ScheideReplacementTreeSplice G k e0 phi T C D d
      f1 f2 v1 v2 u1 u2 hf1f2 hu1u2 hv1Z hv2Z hu1X hu2X
      hf1Ends hf2Ends
  let replacementTree : TreeSequence G e0 := Classical.choose hsplice
  have hsplice1 := Classical.choose_spec hsplice
  let replacementLength : replacementTree.length = T.length :=
    Classical.choose hsplice1
  have hsplice2 := Classical.choose_spec hsplice1
  exact {
    f1 := f1
    f2 := f2
    v1 := v1
    v2 := v2
    u1 := u1
    u2 := u2
    f0_ne_f1 := hf0f1
    f0_ne_f2 := hf0f2
    f1_ne_f2 := hf1f2
    v1_in_remainder := hv1Z
    v2_in_remainder := hv2Z
    u1_outside := hu1X
    u2_outside := hu2X
    f1_ends := hf1Ends
    f2_ends := hf2Ends
    f1_color := hf1Color
    f2_color := hf2Color
    exact_three := by simpa [X, Z] using hExactThree
    replacementTree := replacementTree
    replacement_length := replacementLength
    retained_edges_before := hsplice2.1
    retained_vertices_before := hsplice2.2.1
    retained_edges_after := hsplice2.2.2.1
    retained_vertices_after := hsplice2.2.2.2.1
    replacement_last_edges := hsplice2.2.2.2.2.1
    replacement_last_vertices := hsplice2.2.2.2.2.2.1
    replacement_vertices := hsplice2.2.2.2.2.2.2.1
    replacement_edges := hsplice2.2.2.2.2.2.2.2 }

end GoldbergSeymour

end
