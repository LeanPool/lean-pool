/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import LeanPool.BalancedEdgeColourings.Balanced.Bridge
public import LeanPool.BalancedEdgeColourings.Bkls.Cor12

/-!
# Balanced and vertex-distinguishing edge colourings

Source: doi:10.1016/S0095-8956(03)00073-X, url:https://github.com/jtraverso/balanced-edge-colourings
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `LeanPool.BalancedEdgeColourings.BklsPalomar.theorem1`,
  `LeanPool.BalancedEdgeColourings.BklsPalomar.theorem6`,
  `LeanPool.BalancedEdgeColourings.BklsPalomar.theorem10`,
  `LeanPool.BalancedEdgeColourings.BklsPalomar.corollary12`
Tags: graph-theory, edge-colouring, vertex-distinguishing-colouring, kempe-chains, combinatorics
MSC: 05C15
-/

/-!
# Mathematical scope and source closure

The four public results below formalize BKLS (2004), Theorems 1, 6, 10(2) and Corollary 12.
Theorem 10(2) retains the upstream additional hypothesis `3 ≤ k`.

The proof sources are Juan Pablo Traverso Gianini's AI-authored Apache-2.0 developments:
* https://github.com/jtraverso/balanced-edge-colourings at
  `736c78e6addcdb77e95cd83e4e44c5c0700f13ef` (proof completed 2026-11-05);
* the needed palette and Kempe-exchange closure from
  https://github.com/jtraverso/plantholt-overfull-criterion at
  `f8900944da7743b1facd771139c9ebdbfd8aaa28`;
* the needed multifan and adjacency-lemma closure from
  https://github.com/jtraverso/overfull-critical-graphs at
  `b85da9ac66e0fb8b9873a8bea0c057f78c9d186c`.

The import reuses `LeanPool.Vizing` instead of copying its partial-edge-colouring library.
The upstream author directed Claude Opus 5.5; the authors of the mathematical paper were not
involved in the formalization. The hexagon certificate retains the 32,768 upstream witnesses,
partitioned into eight kernel-checked blocks with readable hexadecimal fragments.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace BklsPalomar

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Balanced

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

open Classical in
/-- `n_S`: the number of vertices with palette `S`. -/
noncomputable def numPal (C : G.lineGraph.Coloring (Fin k)) (S : Finset (Fin k)) : ℕ :=
  #(univ.filter fun v => palette C v = ↑S)

/-- `Σ_S n_S²`. -/
noncomputable def cost (C : G.lineGraph.Coloring (Fin k)) : ℕ :=
  ∑ S : Finset (Fin k), numPal C S ^ 2

omit [Fintype V] in
theorem palette_ofColoring [Finite V] [DecidableRel G.Adj]
    (C : G.lineGraph.Coloring (Fin k)) (v : V) :
    palette C v = ↑(colSet (ofColoring C) v) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ; rw [mem_coe, mem_colSet_ofColoring]

omit [DecidableEq V] [Fintype V] in
theorem palette_lineGraphColoring [Finite V] {c : PEC G (Fin k)} (htot : Total c) (v : V) :
    palette (c.lineGraphColoring htot) v = ↑(colSet c v) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ; rw [mem_coe, mem_palette_lineGraphColoring]

omit [DecidableEq V] in
theorem numPal_eq_cnt {C : G.lineGraph.Coloring (Fin k)} {c : PEC G (Fin k)}
    (h : ∀ v, palette C v = ↑(colSet c v)) (S : Finset (Fin k)) : numPal C S = cnt c S := by
  classical
  unfold numPal cnt
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, h v, coe_inj]

omit [DecidableEq V] in
theorem cost_eq {C : G.lineGraph.Coloring (Fin k)} {c : PEC G (Fin k)}
    (h : ∀ v, palette C v = ↑(colSet c v)) : cost C = Balanced.cost c := by
  classical
  unfold cost Balanced.cost
  exact sum_congr rfl fun S _ => by rw [numPal_eq_cnt h]

omit [DecidableEq V] [Fintype V] in
theorem strong_lineGraphColoring [Finite V] {c : PEC G (Fin k)} (h : Strong c) :
    IsStrong (c.lineGraphColoring h.1) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro u v e
  apply h.2
  rw [palette_lineGraphColoring, palette_lineGraphColoring] at e
  exact_mod_cast e

omit [DecidableEq V] in
/-- **BKLS 2004, Theorem 1.** -/
theorem theorem1 (C : G.lineGraph.Coloring (Fin k))
    (hC : ∀ C' : G.lineGraph.Coloring (Fin k), cost C ≤ cost C') {P Q : Finset (Fin k)}
    (h : #P = #Q) : numPal C P ≤ numPal C Q + 2 := by
  classical
  set c := ofColoring C
  have hP := palette_ofColoring C
  have hopt : IsOptimal c := by
    refine ⟨total_ofColoring C, fun c' htot' => ?_⟩
    have := hC (c'.lineGraphColoring htot')
    rwa [cost_eq hP, cost_eq (palette_lineGraphColoring htot')] at this
  rw [numPal_eq_cnt hP, numPal_eq_cnt hP]
  exact Bkls.theorem1 c hopt h

omit [DecidableEq V] in
/-- **BKLS 2004, Theorem 6.** -/
theorem theorem6 [DecidableRel G.Adj] {κ : Type*} (c : Sym2 V → Fin 3) (key : V → κ)
    (hc : ∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → c e ≠ c e')
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v →
      (G.incidenceFinset u).image c = (G.incidenceFinset v).image c → G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ col : Sym2 V → Fin 4,
      (∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → col e ≠ col e') ∧
      ∀ u v, u ≠ v → key u = key v →
        (G.incidenceFinset u).image col ≠ (G.incidenceFinset v).image col := by
  classical
  exact Bkls.T6.thm6 (key := key) hc h1 h2

omit [DecidableEq V] in
/-- **BKLS 2004, Theorem 10 (part 2).** -/
theorem theorem10 [DecidableRel G.Adj] (hk3 : 3 ≤ k) (hΔ : G.maxDegree ≤ k)
    (h012 : ∀ d, d ≤ 2 → #(univ.filter fun v => G.degree v = d) ≤ 1)
    (h3 : #(univ.filter fun v => G.degree v = 3) ≤ 2)
    (h4 : #(univ.filter fun v => G.degree v = 4) ≤ 2)
    (hkk : #(univ.filter fun v => G.degree v = k) ≤ 2)
    (hk1 : #(univ.filter fun v => G.degree v = k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (#(univ.filter fun v => G.degree v = d) : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) - 2) :
    ∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C := by
  classical
  obtain ⟨c, hc⟩ := Bkls.T10.thm10_2 hk3 hΔ h012 h3 h4 hkk hk1 h6
  exact ⟨c.lineGraphColoring hc.1, strong_lineGraphColoring hc⟩

omit [DecidableEq V] in
/-- **BKLS 2004, Corollary 12.** -/
theorem corollary12 [DecidableRel G.Adj] (hn : Real.sqrt (2 * Fintype.card V) + 4 ≤ G.maxDegree)
    (hδ : 5 ≤ G.minDegree) {k : ℕ}
    (hk : ∀ d, #(univ.filter fun v => G.degree v = d) ≤ k.choose d)
    (hkmin : ∀ k' < k, ∃ d, k'.choose d < #(univ.filter fun v => G.degree v = d)) :
    (∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C) ∧
      ∀ m (C : G.lineGraph.Coloring (Fin m)), IsStrong C → k ≤ m := by
  classical
  obtain ⟨⟨c, hc⟩, hlow⟩ := Bkls.C12.cor12 hn hδ hk hkmin
  exact ⟨⟨c.lineGraphColoring hc.1, strong_lineGraphColoring hc⟩,
    fun m C hC => hlow m (ofColoring C) (strong_ofColoring hC)⟩
end BklsPalomar

end LeanPool.BalancedEdgeColourings
