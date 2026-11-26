/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM16.Defs

/-!
# Restricting a controlled complete-graph minor

The small-parameter reduction in XII (4.5), page 252, can use
a larger complete graph. Retain the branches indexed by the
first vertices and the joining edges between those branches.
The smaller vertex count preserves the separation exclusion.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph

/-- Restrict the branches of a controlled clique minor to its
first vertices. This supplies the small-parameter reduction
in XII (4.5), page 252. -/
theorem controlsMinor_completeGraph_mono
    {α β : Type*} {G : Hypergraph α β} {θ p q : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hpq : p ≤ q)
    (hc : ControlsMinor G θ T (GM16.completeGraph q)) :
    ControlsMinor G θ T (GM16.completeGraph p) := by
  obtain ⟨A, b, hA, hAA, hlink, hloop, hbinj, hθ, hcontrol⟩ := hc
  let f : Fin p → Fin q := Fin.castLE hpq
  have hf : Function.Injective f := Fin.castLE_injective hpq
  have hmapE : ∀ e ∈ (GM16.completeGraph p).edgeSet,
      Sym2.map f e ∈ (GM16.completeGraph q).edgeSet := by
    rintro e ⟨x, y, hxy, rfl⟩
    exact ⟨f x, f y, (fun h => hxy (hf h)), rfl⟩
  have hcardp : (GM16.completeGraph p).vertexSet.ncard = p := by
    change (univ : Set (Fin p)).ncard = p
    simp
  have hcardq : (GM16.completeGraph q).vertexSet.ncard = q := by
    change (univ : Set (Fin q)).ncard = q
    simp
  refine ⟨fun v => A (f v), fun e => b (Sym2.map f e),
    fun v _ => hA (f v) (mem_univ _),
    fun v _ w _ hvw => hAA (f v) (mem_univ _) (f w) (mem_univ _)
      (fun h => hvw (hf h)), ?_, ?_, ?_, ?_, ?_⟩
  · intro e u v hl huv
    exact hlink (Sym2.map f e) (f u) (f v)
      ⟨(fun h => hl.1 (hf h)), congrArg (Sym2.map f) hl.2⟩ (fun h => huv (hf h))
  · intro e v hl
    exact False.elim (hl.1 rfl)
  · intro e he g hg heg heq
    have h := hbinj _ (hmapE e he) _ (hmapE g hg)
      (fun h => heg (Sym2.map.injective hf h))
    exact h heq
  · rw [hcardp]
    exact hpq.trans (hcardq ▸ hθ)
  · intro C D hCD hord v hv
    apply hcontrol C D hCD
    · rw [hcardq]
      rw [hcardp] at hord
      exact hord.trans_le hpq
    · exact mem_univ _

end GraphMinor.GM12
