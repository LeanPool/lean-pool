/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Two Color Component Swap Proper

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorComponentSwapProper {V E : Type*}
      (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (z : Sum V E) :
    IsProperEdgeColoring G (TwoColorComponentSwap G phi alpha beta z) := by
  classical
  let changeColor : Option (Fin k) → Option (Fin k) := fun value =>
    if value = some alpha then some beta
    else if value = some beta then some alpha else value
  have changeColor_injective : Function.Injective changeColor := by
    intro x y hxy
    cases x <;> cases y <;>
      simp_all [changeColor] <;>
      aesop
  have changeColor_cases : ∀ x y, changeColor x = y →
      x = y ∨ (x = some alpha ∧ y = some beta) ∨
        (x = some beta ∧ y = some alpha) := by
    intro x y hxy
    by_cases h : x = y
    · exact Or.inl h
    · right
      cases x <;> cases y <;>
        simp_all [changeColor] <;> aesop
  intro e f c hef hadj he hf
  rcases hadj with ⟨v, hev, hfv⟩
  have component_transfer :
    ∀ (e f : E) (v : V), Incident G v e → Incident G v f → (phi e = some alpha ∧ phi f = some
        beta) ∨ (phi e = some beta ∧ phi f = some alpha) → Sum.inr e ∈ TwoColorComponent G phi
        alpha beta z → Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
    intro e f v hev hfv hcolors heK
    let H := TwoColorIncidenceGraph G phi alpha beta
    have p : H.Adj (Sum.inr e) (Sum.inl v) := by
      rcases hcolors with ⟨hea, hfb⟩ | ⟨heb, hfa⟩
      · simp [H, TwoColorIncidenceGraph, hev, hea]
      · simp [H, TwoColorIncidenceGraph, hev, heb]
    have q : H.Adj (Sum.inl v) (Sum.inr f) := by
      rcases hcolors with ⟨hea, hfb⟩ | ⟨heb, hfa⟩
      · simp [H, TwoColorIncidenceGraph, hfv, hfb]
      · simp [H, TwoColorIncidenceGraph, hfv, hfa]
    have hp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj p
    have hq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj q
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z at heK
    change H.connectedComponentMk (Sum.inr f) = H.connectedComponentMk z
    exact hq.symm.trans (hp.symm.trans heK)
  by_cases heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
  · by_cases hfK : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · have hs : changeColor (phi e) = changeColor (phi f) := by
        simpa [TwoColorComponentSwap, changeColor, heK, hfK] using he.trans hf.symm
      have ho := changeColor_injective hs
      cases pe : phi e with
      | none => simp [TwoColorComponentSwap, pe, heK] at he
      | some d =>
        have pf : phi f = some d := ho.symm.trans pe
        exact (hproper hef ⟨v, hev, hfv⟩ pe) pf
    · have hs : changeColor (phi e) = phi f := by
        simpa [TwoColorComponentSwap, changeColor, heK, hfK] using he.trans hf.symm
      rcases changeColor_cases (phi e) (phi f) hs with hsame | ⟨hea, hfb⟩ | ⟨heb, hfa⟩
      · have hfix : changeColor (phi e) = phi e := by simpa [hsame] using hs
        have he0 : changeColor (phi e) = some c := by
          simpa [TwoColorComponentSwap, changeColor, heK] using he
        have he1 : phi e = some c := hfix.symm.trans he0
        exact (hproper hef ⟨v, hev, hfv⟩ he1) (by simpa [hsame] using he1)
      · exact hfK (component_transfer e f v hev hfv (Or.inl ⟨hea, hfb⟩) heK)
      · exact hfK (component_transfer e f v hev hfv (Or.inr ⟨heb, hfa⟩) heK)
  · by_cases hfK : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · have hs : phi e = changeColor (phi f) := by
        simpa [TwoColorComponentSwap, changeColor, heK, hfK] using he.trans hf.symm
      rcases changeColor_cases (phi f) (phi e) hs.symm with hsame | ⟨hfa, heb⟩ | ⟨hfb, hea⟩
      · have hfix : changeColor (phi f) = phi f := by simpa [hsame] using hs.symm
        have hf0 : changeColor (phi f) = some c := by
          simpa [TwoColorComponentSwap, changeColor, hfK] using hf
        have hf1 : phi f = some c := hfix.symm.trans hf0
        exact (hproper hef ⟨v, hev, hfv⟩ (by simpa [hsame] using hf1)) hf1
      · exact heK (component_transfer f e v hfv hev (Or.inl ⟨hfa, heb⟩) hfK)
      · exact heK (component_transfer f e v hfv hev (Or.inr ⟨hfb, hea⟩) hfK)
    · have he0 : phi e = some c := by simpa [TwoColorComponentSwap, heK] using he
      have hf0 : phi f = some c := by simpa [TwoColorComponentSwap, hfK] using hf
      exact (hproper hef ⟨v, hev, hfv⟩ he0) hf0

end GoldbergSeymour

end
