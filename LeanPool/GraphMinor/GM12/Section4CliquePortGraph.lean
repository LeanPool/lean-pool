/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePorts
public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM12.Section4SubdivisionGraph
import LeanPool.GraphMinor.GM12.Section4SubdivisionMinor
import LeanPool.GraphMinor.Minor.Basic

/-!
# The complete graph encoded by the clique ports

The source arc construction of XII (4.5), page 252, labels its
edge ends by ordered pairs of distinct vertices. Identify each
edge with the unordered pair of its two ports. Reversing the port
choice reverses the pair, and the port bijection proves that this
is a bijection with the actual edges of the complete graph.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- The graph encoded by the finite clique port labels is
isomorphic to the actual complete graph, with the identity map on
vertices and the unordered endpoint-pair map on edges. This matches
the source graph in XII (4.5), page 252. -/
theorem exists_clique_graph_of_ports {p : ℕ}
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1)) :
    ∃ H : Graph (Fin p) (Fin (p * (p - 1) / 2)),
      H.vertexSet = univ ∧ H.edgeSet = univ ∧ Nonempty (Iso H (GM16.completeGraph p)) ∧
      ∀ e, H.IsLink e (ψ (e, false)).val.1 (ψ (e, true)).val.1 := by
  let f : Fin (p * (p - 1) / 2) → (GM16.completeGraph p).edgeSet := fun e =>
    ⟨s((ψ (e, false)).val.1, (ψ (e, false)).val.2),
      (ψ (e, false)).val.1, (ψ (e, false)).val.2, (ψ (e, false)).property, rfl⟩
  have hf : Function.Injective f := by
    intro e e' heq
    have hpair := congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hports : ψ (e, false) = ψ (e', false) := Subtype.ext (Prod.ext hu hv)
      exact congrArg Prod.fst (ψ.injective hports)
    · have hflip := hψ e' false
      change (ψ (e', true)).val = ((ψ (e', false)).val.2, (ψ (e', false)).val.1) at hflip
      have hports : ψ (e, false) = ψ (e', true) :=
        Subtype.ext ((Prod.ext hu hv).trans hflip.symm)
      exact False.elim (Bool.false_ne_true (congrArg Prod.snd (ψ.injective hports)))
  have hs : Function.Surjective f := by
    rintro ⟨e, v, w, hvw, he⟩
    subst e
    let q := ψ.symm ⟨(v, w), hvw⟩
    let i := q.1
    let b := q.2
    have hpair : (ψ (i, b)).val = (v, w) :=
      congrArg Subtype.val (ψ.apply_symm_apply ⟨(v, w), hvw⟩)
    refine ⟨i, Subtype.ext ?_⟩
    change s((ψ (i, false)).val.1, (ψ (i, false)).val.2) = s(v, w)
    cases hb : b
    · rw [hb] at hpair
      exact congrArg (fun z : Fin p × Fin p => s(z.1, z.2)) hpair
    · rw [hb] at hpair
      have hflip := hψ i true
      change (ψ (i, false)).val = ((ψ (i, true)).val.2, (ψ (i, true)).val.1) at hflip
      rw [show (ψ (i, true)).val.1 = v from congrArg Prod.fst hpair,
        show (ψ (i, true)).val.2 = w from congrArg Prod.snd hpair] at hflip
      exact (congrArg (fun z : Fin p × Fin p => s(z.1, z.2)) hflip).trans Sym2.eq_swap
  let ε := Equiv.ofBijective f ⟨hf, hs⟩
  let H : Graph (Fin p) (Fin (p * (p - 1) / 2)) := {
    vertexSet := univ
    edgeSet := univ
    IsLink e u v := (GM16.completeGraph p).IsLink (ε e).val u v
    isLink_symm := by intro e he; exact ⟨fun _ _ h => h.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y v w hxy hvw
      exact (GM16.completeGraph p).eq_or_eq_of_isLink_of_isLink hxy hvw
    edge_mem_iff_exists_isLink := by
      intro e
      exact ⟨fun _ => (GM16.completeGraph p).exists_isLink_of_mem_edgeSet (ε e).property,
        fun _ => mem_univ e⟩
    left_mem_of_isLink := by intro e x y h; exact mem_univ x }
  let eEquiv : H.edgeSet ≃ (GM16.completeGraph p).edgeSet := {
    toFun := fun e => ε e.val
    invFun := fun e => ⟨ε.symm e, mem_univ _⟩
    left_inv := fun e => Subtype.ext (ε.symm_apply_apply e.val)
    right_inv := fun e => ε.apply_symm_apply e }
  let φ : Iso H (GM16.completeGraph p) := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := eEquiv
    isLink_iff := fun _ _ _ => Iff.rfl }
  refine ⟨H, rfl, rfl, ⟨φ⟩, ?_⟩
  intro e
  have hflip := congrArg Prod.fst (hψ e false)
  change (ψ (e, true)).val.1 = (ψ (e, false)).val.2 at hflip
  change (GM16.completeGraph p).IsLink (ε e).val (ψ (e, false)).val.1 (ψ (e, true)).val.1
  rw [hflip]
  exact ⟨(ψ (e, false)).property, rfl⟩

/-- The actual complete graph is isomorphic to a minor of the
subdivision encoded by the clique ports. This is the clique-minor
assertion in XII (4.5), page 252. -/
theorem completeGraph_isIsoMinor_port_subdivision {p : ℕ}
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (k : Fin (p * (p - 1) / 2) → ℕ) (hk : ∀ e, 0 < k e) :
    IsIsoMinor (GM16.completeGraph p) (subdivisionGraph (fun x => (ψ x).val.1) k) := by
  obtain ⟨H, _, _, ⟨φ⟩, hlink⟩ := exists_clique_graph_of_ports ψ hψ
  exact φ.symm.isIsoMinor_left
    (isIsoMinor_subdivision H (fun x => (ψ x).val.1) hlink k hk)

end GraphMinor.GM12
