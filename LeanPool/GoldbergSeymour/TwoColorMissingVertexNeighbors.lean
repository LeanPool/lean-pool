/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Missing Colors Give Incidence Leaves

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- If one color is missing, a proper two-color incidence graph has at most one neighbor. -/
theorem TwoColorMissingVertexNeighborsSubsingleton.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype E] (G :
    LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k), IsProperEdgeColoring G
    phi → ∀ (a b : Fin k), let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b; ∀
    (v : V), a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v → (H.neighborSet (Sum.inl
    v)).Subsingleton := by
  classical
  intro V E _ G k phi hproper a b H v hmissing z hz w hw
  cases hzv : z with
  | inl u =>
      rw [hzv] at hz
      simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
  | inr e =>
      cases hwv : w with
      | inl u =>
          rw [hwv] at hw
          simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
      | inr f =>
          rw [hzv] at hz
          rw [hwv] at hw
          have he : Incident G v e ∧
              (phi e = some a ∨ phi e = some b) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hz
          have hf : Incident G v f ∧
              (phi f = some a ∨ phi f = some b) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hw
          apply congrArg Sum.inr
          by_contra hef
          rcases hmissing with ha | hb
          · have hna : a ∉ PresentColors G phi v := by
              simpa [MissingColors] using ha
            have hea : phi e = some b := he.2.resolve_left (by
              intro hea
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some a from
                  ⟨e, he.1, hea⟩))
            have hfa : phi f = some b := hf.2.resolve_left (by
              intro hfa
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some a from
                  ⟨f, hf.1, hfa⟩))
            exact (hproper hef ⟨v, he.1, hf.1⟩ hea) hfa
          · have hnb : b ∉ PresentColors G phi v := by
              simpa [MissingColors] using hb
            have heb : phi e = some a := he.2.resolve_right (by
              intro heb
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some b from
                  ⟨e, he.1, heb⟩))
            have hfb : phi f = some a := hf.2.resolve_right (by
              intro hfb
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some b from
                  ⟨f, hf.1, hfb⟩))
            exact (hproper hef ⟨v, he.1, hf.1⟩ heb) hfb

/-- A vertex with at most one incidence neighbor must miss one of two distinct colors. -/
theorem TwoColorMissingOfVertexNeighborsSubsingleton.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
      (phi : PartialEdgeColoring E k) (a b : Fin k),
      a ≠ b →
        let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
        ∀ (v : V), (H.neighborSet (Sum.inl v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈
            MissingColors G phi v := by
  classical
  intro V E _ G k phi a b hne H v hleaf
  by_cases ha : a ∈ MissingColors G phi v
  · exact Or.inl ha
  · right
    have hap : a ∈ PresentColors G phi v := by
      simpa [MissingColors] using ha
    by_contra hb
    have hbp : b ∈ PresentColors G phi v := by
      simpa [MissingColors] using hb
    obtain ⟨ea, hea, hca⟩ := by simpa [PresentColors] using hap
    obtain ⟨eb, heb, hcb⟩ := by simpa [PresentColors] using hbp
    have hada : H.Adj (Sum.inl v) (Sum.inr ea) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G v ea ∧
            (phi ea = some a ∨ phi ea = some b) from
          ⟨hea, Or.inl hca⟩)
    have hadb : H.Adj (Sum.inl v) (Sum.inr eb) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G v eb ∧
            (phi eb = some a ∨ phi eb = some b) from
          ⟨heb, Or.inr hcb⟩)
    have heab : ea = eb := Sum.inr.inj (hleaf hada hadb)
    subst eb
    exact hne (Option.some.inj (hca.symm.trans hcb))

end GoldbergSeymour

end
