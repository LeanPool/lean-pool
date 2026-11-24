/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM12.Section4EyeConnections
import LeanPool.GraphMinor.GM12.Section4EyeBranchControl
import LeanPool.GraphMinor.GM12.Section4EyePathReindex
import LeanPool.GraphMinor.GM12.Section4Monotone
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.5): the construction for large cliques

Use the source subdivision, ordered eye discs, and endpoint
connections of page 253. Renumber the two external paths at
each eye by the source edges. The connected classes and those
paths give a controlled source minor by the two-region branch
estimate. Apply (4.2) to its complete-graph minor.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph Hypergraph GM14 GM15

universe u

/-- XII (4.5), pages 252--253, for `p ≥ 4`, in the independent-eye
span formulation used by XV. The only statement hypotheses are
VII (7.5), (5.1), and (5.5). The paper reduces to `p ≥ 5`.
A larger threshold includes the source vertex-count bound
explicitly before applying the final separation estimate. -/
theorem theorem_4_5_span_large
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) (hp : 4 ≤ p) :
    ∃ k N : ℕ, 1 ≤ N ∧ ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β)) (Γ : Drawing S)
      (η : SpanEmbedding Γ G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (r : Fin k → Set S) (P Q : Fin k → Graph α β),
      Function.Injective r → (∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
      (∀ i j, i ≠ j → N ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  classical
  obtain ⟨W, E, L, κ, t, σ, N, hW, hE, hminor, hlink, hκne, ht, hNW, htwo, hconnect⟩ :=
    exists_eye_connections hS hp
  let : Finite W := hW
  let : Finite E := hE
  let : Fintype W := Fintype.ofFinite W
  let : Fintype E := Fintype.ofFinite E
  refine ⟨t, N, (by omega), ?_⟩
  intro α β G θstar θ Tstar Γ η T d hCtrl hm hN r P Q hri heye hfar hdisj
  have hex := fun i => (heye i).2
  choose C a b c d' hC hCG hCr ha hb hc hd hnodup horder hfree hPQ hP hQ using hex
  have hr : ∀ i, r i ∈ Γ.R := fun i => (heye i).1
  obtain ⟨ends, H, hinj, hends, hinc, hH, hHc, hHH, hclass, hp0, hp1⟩ :=
    hconnect Γ θ T d r C a b c d' hm.1.1 hm hN hr hri hfar hC hCG hCr
      (fun i => ⟨ha i, hb i, hc i, hd i⟩) horder hfree
  let R₀ : Fin t × Bool → Graph α β := fun x => if x.2 then Q x.1 else P x.1
  let s : Fin t × Bool → S := fun x => if x.2 then b x.1 else a x.1
  let z : Fin t × Bool → S := fun x => if x.2 then d' x.1 else c x.1
  have hR₀ : ∀ x, IsHPathWithEnds G η.imageGraph (R₀ x) (η.vMap (s x)) (η.vMap (z x)) := by
    rintro ⟨i, b'⟩
    cases b'
    · exact hP i
    · exact hQ i
  have hR₀R₀ : Pairwise (fun x y => Disjoint (R₀ x).vertexSet (R₀ y).vertexSet) := by
    rintro ⟨i, b'⟩ ⟨j, c'⟩ hneq
    by_cases hij : i = j
    · subst j
      cases b' <;> cases c'
      · exact False.elim (hneq rfl)
      · exact hPQ i
      · exact (hPQ i).symm
      · exact False.elim (hneq rfl)
    · have hi : (R₀ (i, b')).vertexSet ⊆ (P i).vertexSet ∪ (Q i).vertexSet := by
        cases b'
        · exact subset_union_left
        · exact subset_union_right
      have hj : (R₀ (j, c')).vertexSet ⊆ (P j).vertexSet ∪ (Q j).vertexSet := by
        cases c'
        · exact subset_union_left
        · exact subset_union_right
      exact (hdisj i j hij).mono hi hj
  have hpairs : ∀ x, ({ends (σ x, false), ends (σ x, true)} : Set S) = {s x, z x} := by
    rintro ⟨i, b'⟩
    cases b'
    · exact hp0 i
    · exact hp1 i
  obtain ⟨R, hR, hRR⟩ := exists_external_paths_reindexed η.vMap σ ends s z R₀ hR₀ hR₀R₀ hpairs
  have hEΓ : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  have hcardW : Fintype.card W = Nat.card W := Nat.card_eq_fintype_card.symm
  have hfar' : ∀ i j, i ≠ j → 2 * Fintype.card W + 2 ≤ d (r i) (r j) := by
    intro i j hij
    rw [hcardW]
    exact (by omega : 2 * Nat.card W + 2 ≤ N).trans (hfar i j hij)
  have hθ : Fintype.card W ≤ θ := by rw [hcardW]; omega
  have hcL := controlsMinor_of_eye_connections hS η hm hCtrl hEΓ L κ σ hlink hκne htwo
    r hr hfar' hθ ends hends hinc H hH hHc hHH hclass R hR hRR
  obtain ⟨e, _⟩ := hEΓ
  let : Nonempty β := ⟨η.eMap e⟩
  exact theorem_4_2_proof hCtrl.isTangle_star.finite_V hCtrl.isTangle_star.finite_E
    (Set.toFinite L.vertexSet) (Set.toFinite L.edgeSet) hminor hcL

end GraphMinor.GM12
