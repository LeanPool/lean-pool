/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveTailExternal

/-!
# Scheide Defective Switch Effect

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ScheideDefectiveSwitchEffect_present_v0_159.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
          TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
      let alpha := C.gamma (D.gammaIndex d);
      let beta := (↑d : Fin k);
      let z := Sum.inl (D.v0 d);
      let component := TwoColorComponent G phi alpha beta z;
      let phiD := TwoColorComponentSwap G phi alpha beta z;
      IsProperEdgeColoring G phi →
        phi (D.f0 d) = some beta →
          Incident G (D.v0 d) (D.f0 d) →
            alpha ≠ beta →
              Sum.inr (D.f0 d) ∈ component →
                (∀ (e : E), Incident G (D.v0 d) e → Sum.inr e ∈ component → e = D.f0 d) →
                  PresentColors G phiD (D.v0 d) = insert alpha ((PresentColors G phi (D.v0
                      d)).erase beta) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d alpha beta z component phiD proper f0_color f0_incident
      colors_ne f0_component f0_unique
  ext c
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨e, he, hec⟩
    by_cases em : Sum.inr e ∈ component
    · have eeq := f0_unique e he em
      subst e
      simp [phiD, component, TwoColorComponentSwap, f0_component,
        f0_color, colors_ne.symm] at hec
      exact Or.inl hec.symm
    · have old : phi e = some c := by
        simpa [phiD, component, TwoColorComponentSwap, em] using hec
      have cne : c ≠ beta := by
        intro ceq
        have bad := proper (by
          intro eqe
          exact em (eqe ▸ f0_component)) ⟨D.v0 d, he, f0_incident⟩ old
        exact bad (by simpa [ceq] using f0_color)
      exact Or.inr ⟨cne, ⟨e, he, old⟩⟩
  · intro hc
    rcases hc with rfl | ⟨cne, ⟨e, he, hold⟩⟩
    · refine ⟨D.f0 d, f0_incident, ?_⟩
      simp [phiD, component, TwoColorComponentSwap, f0_component,
        f0_color]
    · have em : Sum.inr e ∉ component := by
        intro em
        have eeq := f0_unique e he em
        subst e
        exact cne (Option.some.inj (f0_color.symm.trans hold)).symm
      refine ⟨e, he, ?_⟩
      simpa [phiD, component, TwoColorComponentSwap, em] using hold

theorem ScheideDefectiveSwitchEffect {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      let phiD := TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      IsProperEdgeColoring G phiD ∧ IsOneEdgeUncolored phiD e0 ∧
        phiD (D.f0 d) = some (C.gamma (D.gammaIndex d)) ∧
        MissingColors G phiD (D.v0 d) =
          insert d.1 ((MissingColors G phi (D.v0 d)).erase
            (C.gamma (D.gammaIndex d))) ∧
        (∀ f : E, (∃ v ∈ TreeSequenceVertexSet T, Incident G v f) →
          f ≠ D.f0 d → phiD f = phi f) ∧
        (∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d →
          MissingColors G phiD v = MissingColors G phi v) ∧
        ∀ v : V,
          Sum.inl v ∉ TwoColorComponent G phi
            (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d)) →
          MissingColors G phiD v = MissingColors G phi v := by
  classical
  intro d
  dsimp
  let alpha := C.gamma (D.gammaIndex d)
  let beta := d.1
  let z : Sum V E := Sum.inl (D.v0 d)
  let component := TwoColorComponent G phi alpha beta z
  let phiD := TwoColorComponentSwap G phi alpha beta z
  have proper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have gamma_missing : alpha ∈ MissingColors G phi (D.v0 d) :=
    D.gamma_missing_at_v0 d
  have f0_color : phi (D.f0 d) = some beta := D.f0_color d
  have f0_incident : Incident G (D.v0 d) (D.f0 d) := by
    change D.v0 d ∈ G.ends (D.f0 d)
    rw [D.f0_ends]
    simp []
  have colors_ne : alpha ≠ beta := by
    intro same
    have no_alpha : alpha ∉ PresentColors G phi (D.v0 d) := by
      simpa [MissingColors] using gamma_missing
    apply no_alpha
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.f0 d, f0_incident, by simpa [same] using f0_color⟩
  have f0_component : Sum.inr (D.f0 d) ∈ component := by
    change Sum.inr (D.f0 d) ∈
      TwoColorComponent G phi alpha beta (Sum.inl (D.v0 d))
    change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inr (D.f0 d)) =
      (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inl (D.v0 d))
    have link : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (Sum.inl (D.v0 d)) (Sum.inr (D.f0 d)) := by
      simp [TwoColorIncidenceGraph, f0_incident, f0_color]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj link).symm
  have vertex_step : ∀ v e, Incident G v e →
      Sum.inr e ∈ component → Sum.inl v ∈ component := by
    intro v e incident edge_member
    exact TwoColorComponent.vertex_mem_of_incident edge_member incident
  have outside_edge : ∀ v e, Incident G v e → Sum.inl v ∉ component →
      Sum.inr e ∉ component := by
    intro v e incident vertex_not edge_member
    exact vertex_not (vertex_step v e incident edge_member)
  have component_tree : ∀ v, v ∈ TreeSequenceVertexSet T →
      Sum.inl v ∈ component → v = D.v0 d := by
    intro v vt vc
    exact ScheideDefectiveTailExternal G k e0 phi T C D d v vt vc
  have alpha_not_present : alpha ∉ PresentColors G phi (D.v0 d) := by
    simpa [MissingColors] using gamma_missing
  have f0_unique : ∀ e, Incident G (D.v0 d) e → Sum.inr e ∈ component → e = D.f0 d := by
    intro e incident edge_member
    have color_choice : phi e = some alpha ∨ phi e = some beta := by
      exact TwoColorComponent.edge_colors edge_member
    rcases color_choice with ca | cb
    · exact False.elim (alpha_not_present (by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, incident, ca⟩))
    · by_contra unequal
      have bad := proper unequal ⟨D.v0 d, incident, f0_incident⟩ cb
      exact bad f0_color
  have one : IsOneEdgeUncolored phi e0 := C.globally_maximum.1.2.2.2.2
  have tree_edge_not : ∀ f, (∃ v ∈ TreeSequenceVertexSet T, Incident G v f) →
      f ≠ D.f0 d → Sum.inr f ∉ component := by
    intro f hf hne mem
    obtain ⟨v, vt, hvf⟩ := hf
    have vc := vertex_step v f hvf mem
    have veq := component_tree v vt vc
    apply hne
    exact f0_unique f (veq ▸ hvf) mem
  have present_outside : ∀ v, Sum.inl v ∉ component →
      PresentColors G phiD v = PresentColors G phi v := by
    intro v vout
    ext c
    constructor
    · intro hc
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨e, he, hec⟩ := hc
      refine ⟨e, he, ?_⟩
      have emem : Sum.inr e ∉ component := outside_edge v e he vout
      simpa [phiD, component, TwoColorComponentSwap, emem] using hec
    · intro hc
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨e, he, hec⟩ := hc
      refine ⟨e, he, ?_⟩
      have emem : Sum.inr e ∉ component := outside_edge v e he vout
      simpa [phiD, component, TwoColorComponentSwap, emem] using hec
  have fixed_tree : ∀ f, (∃ v ∈ TreeSequenceVertexSet T, Incident G v f) →
      f ≠ D.f0 d → phiD f = phi f := by
    intro f hf hne
    have mem : Sum.inr f ∉ component := tree_edge_not f hf hne
    simp [phiD, component, TwoColorComponentSwap, mem]
  have present_v0 : PresentColors G phiD (D.v0 d) =
      insert alpha ((PresentColors G phi (D.v0 d)).erase beta) := by
    exact @ScheideDefectiveSwitchEffect_present_v0_159 V E inferInstance inferInstance
        inferInstance G k e0 phi T C D d proper f0_color f0_incident colors_ne f0_component
        f0_unique
  have properD : IsProperEdgeColoring G phiD := by
    exact TwoColorComponentSwapProper G phi alpha beta colors_ne proper z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [phiD] using properD
  · unfold IsOneEdgeUncolored
    constructor
    · change phiD e0 = none
      simp [phiD, TwoColorComponentSwap, one.1]
    · intro e he
      obtain ⟨c, hc⟩ := one.2 e he
      by_cases mem : Sum.inr e ∈ component
      · have mem' : Sum.inr e ∈ TwoColorComponent G phi alpha beta z := by
          simpa [component] using mem
        refine ⟨if c = alpha then beta else if c = beta then alpha else c, ?_⟩
        by_cases ca : c = alpha <;> by_cases cb : c = beta <;>
          simp [TwoColorComponentSwap, alpha, beta, z, mem', hc, ca, cb,
            colors_ne.symm]
      · have mem' : Sum.inr e ∉ TwoColorComponent G phi alpha beta z := by
          simpa [component] using mem
        exact ⟨c, by simpa [phiD, TwoColorComponentSwap, alpha, beta, z, mem'] using hc⟩
  · change phiD (D.f0 d) = some alpha
    have mem' : Sum.inr (D.f0 d) ∈ TwoColorComponent G phi alpha beta z := by
      simpa [component] using f0_component
    simp [phiD, TwoColorComponentSwap, alpha, beta, z, mem', f0_color]
  · have missing_v0 : MissingColors G phiD (D.v0 d) =
        insert beta ((MissingColors G phi (D.v0 d)).erase alpha) := by
      simp only [MissingColors]
      rw [present_v0]
      ext c
      by_cases ca : c = alpha <;> by_cases cb : c = beta <;>
      simp [ca, cb, colors_ne, colors_ne.symm]
    change MissingColors G phiD (D.v0 d) =
      insert beta ((MissingColors G phi (D.v0 d)).erase alpha)
    exact missing_v0
  · intro f hf hne
    exact fixed_tree f hf hne
  · intro v vt hne
    have vout : Sum.inl v ∉ component := by
      intro vc
      exact hne (component_tree v vt vc)
    change MissingColors G phiD v = MissingColors G phi v
    simp only [MissingColors]
    rw [present_outside v vout]
  · intro v hv
    have vout : Sum.inl v ∉ component := hv
    change MissingColors G phiD v = MissingColors G phi v
    simp only [MissingColors]
    rw [present_outside v vout]

end GoldbergSeymour

end
