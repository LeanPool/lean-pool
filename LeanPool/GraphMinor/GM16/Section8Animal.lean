/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8Hairs
public import LeanPool.GraphMinor.GM16.Section8HornSelection
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM16.DrawingAtoms
import LeanPool.GraphMinor.GM09.Basic

import LeanPool.GraphMinor.GM11.CitedResults

/-!
# The animal after rearrangement

Claims (6)–(12) of XVI (8.3) now assemble into an animal. The old horns keep
their selected paths. At most one old hair is lost and two new hairs come
from the new long path, so one can select exactly one more hair than before.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The last step of the proof of Graph Minors XVI, (8.3), page 68:
Claims (6)–(12) give an animal with one more hair. -/
theorem animal_of_rearrangement (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam ψ ζ τ χ δ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S} {X : Set α} {Y : Set S}
    (hAnim : IsAnimal G T_star θ_star H η θ T d X Y χ δ θ (ζ + τ))
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    {Z : Set α} (hZfin : Z.Finite) (hXZ : X ⊆ Z) (hZcard : Z.ncard ≤ ζ)
    (hnewZ : Disjoint V(η'.imageGraph) Z)
    (hshort : ∀ (L : Graph α β) (s t : S), s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph L (η.vMap s) (η.vMap t) →
      Disjoint V(L) Z → d {s} {t} < 2 * ψ)
    {P : Graph α β} {s t : S} (hs : s ∈ H'.V) (ht : t ∈ H'.V)
    (hP : IsHPathWithEnds G η'.imageGraph P (η'.vMap s) (η'.vMap t))
    (hPZ : Disjoint V(P) Z) (hst : 2 * ψ ≤ d' {s} {t})
    (hsnear : pointAtomDist H d s z ≤ lam) (htnear : pointAtomDist H d t z ≤ lam)
    (hψ : 3 ≤ ψ) (hθ : ψ + (4 * lam + 2) ≤ θ)
    (hHornRadius : 2 * (lam + 2 + 2 * ψ) ≤ θ)
    (hHairRadius : 2 * (ψ + 5 * lam + 4) ≤ θ) :
    HasAnimal S G T_star θ_star χ (δ + 1) ψ τ := by
  classical
  obtain ⟨hpos, _, hSpan, hMet, hX, hXcard, hY, hYcard, hHorns, hHairs, hYdist⟩ := hAnim
  obtain ⟨_, hself, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS
    hSpan.isConnected hMet
  obtain ⟨_, hself', _, hsymm', _, _⟩ :=
    GraphMinor.GM11.gm15_theorem_9_1.{w} H' (θ - (4 * lam + 2)) T' d' hS h.isSpan'.isConnected
      h.isCompression.hasMetric'
  have hprox := vertex_atom_dist_le_two hS hMet
  let far : Set S := {y ∈ Y | ψ + 5 * lam + 4 ≤ d z {y}}
  have hFarCount := theorem_8_3_claim_10 h hY hYcard hYdist hHairRadius (by omega) hsymm htri
  have hfarNew : far ⊆ H'.V := fun _ hy => (hFarCount.2 _ hy).1
  have hfarOld : far ⊆ H.V := fun _ hy => hY hy.1
  have hfarFin : far.Finite := H.finite_V.subset hfarOld
  have hsnot : s ∉ far := by
    intro hsfar
    have hsA := singleton_mem_A_of_mem_V (hfarOld hsfar)
    rw [pointAtomDist_of_mem_vertex d (hfarOld hsfar) z,
      hsymm {s} hsA z h.z_mem] at hsnear
    have hdist := hsfar.2
    omega
  have htnot : t ∉ far := by
    intro htfar
    have htA := singleton_mem_A_of_mem_V (hfarOld htfar)
    rw [pointAtomDist_of_mem_vertex d (hfarOld htfar) z,
      hsymm {t} htA z h.z_mem] at htnear
    have hdist := htfar.2
    omega
  have hstne : s ≠ t := fun heq => hP.2.2.1 (congrArg η'.vMap heq)
  let hairs : Set S := far ∪ {s, t}
  have hHairCount : δ + 1 ≤ hairs.ncard := by
    have hEq : hairs = insert s (insert t far) := by ext x; simp [hairs]
    rw [hEq, ncard_insert_of_notMem (by simpa using And.intro hstne hsnot)
      (hfarFin.insert t), ncard_insert_of_notMem htnot hfarFin]
    have hc : δ - 1 ≤ far.ncard := hFarCount.1
    omega
  obtain ⟨chosen, hchosen, hchosenCard⟩ := exists_subset_card_eq hHairCount
  have hHornsNew : ∀ v ∈ X, ∃ (P : Fin τ → Graph α β) (u : Fin τ → S),
      IsHorn G H' η' d' v ψ τ P u := by
    intro v hv
    obtain ⟨Pv, ends, hHorn⟩ := hHorns v hv
    obtain ⟨f, hf⟩ := theorem_8_3_claim_6 hHorn hZfin (hXZ hv) hZcard h.z_mem
      hHornRadius hsymm htri
    have hEnds := theorem_8_3_claim_8 h (fun i => hHorn.2.1 (f i))
      (fun i => by have hb := (hf i).1; omega)
      (fun i j hij => hHorn.2.2.2.2.2 (f i) (f j) (fun heq => hij (f.injective heq))) hθ
    have hinter : ∀ i, V(Pv (f i)) ∩ V(η'.imageGraph) = {η'.vMap (ends (f i))} := by
      intro i
      rw [(hEnds.1 i).2]
      apply subset_antisymm
      · exact theorem_8_3_claim_7 hS h hsymm htri hprox hself (by omega) hnewZ hshort
          (hHorn.2.1 (f i)) (hXZ hv) (hHorn.2.2.1 (f i)) (hHorn.2.2.2.1 (f i))
          (hf i).2 (hf i).1
      · rintro a rfl
        refine ⟨(hHorn.2.2.1 (f i)).right_mem, ?_⟩
        rw [← (hEnds.1 i).2]
        exact η'.bijOn_v.mapsTo (hEnds.1 i).1
    refine ⟨_, _, theorem_8_3_claim_9 hHorn f ?_ hEnds.1 hinter hEnds.2⟩
    exact fun hvNew => hnewZ.notMem_of_mem_left hvNew (hXZ hv)
  have hHairsNew : ∀ y ∈ hairs, ∃ (v : S) (Q : Graph α β), v ∈ H'.V ∧ y ≠ v ∧
      IsHPathWithEnds G η'.imageGraph Q (η'.vMap y) (η'.vMap v) ∧
      Disjoint X V(Q) ∧ ψ ≤ d' {y} {v} := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨x, Q, hx, _, hQ, hQX, hdist⟩ := hHairs y hy.1
      have hXold : Disjoint X V(η.imageGraph) := disjoint_left.mpr fun v hv hvOld => (hX hv).2 hvOld
      exact theorem_8_3_claim_12 hS h hsymm htri hprox hself'
        hXold (hY hy.1) hx hQ hQX hy.2 hψ hθ hdist
    · have hPX : Disjoint X V(P) := disjoint_left.mpr fun v hv hvP => hPZ.notMem_of_mem_left hvP
        (hXZ hv)
      rcases hy with rfl | hy
      · exact ⟨t, P, ht, hstne, hP, hPX, by omega⟩
      · rw [mem_singleton_iff] at hy
        subst y
        have hRev : IsHPathWithEnds G η'.imageGraph P (η'.vMap t) (η'.vMap s) := by
          obtain ⟨hle, hp, hne, ha, hb, hv, he⟩ := hP
          exact ⟨hle, hp.symm, hne.symm, hb, ha, by rw [hv, pair_comm], he⟩
        have hdist : ψ ≤ d' {t} {s} := by
          rw [hsymm' {t} (singleton_mem_A_of_mem_V ht) {s} (singleton_mem_A_of_mem_V hs)]
          omega
        exact ⟨s, P, hs, hstne.symm, hRev, hPX, hdist⟩
  refine ⟨H', η', θ - (4 * lam + 2), T', d', X, chosen, by omega, by omega,
    h.isSpan', h.isCompression.hasMetric', ?_, hXcard, ?_, hchosenCard,
    hHornsNew, fun y hy => hHairsNew y (hchosen hy), ?_⟩
  · intro v hv
    exact ⟨(hX hv).1, fun hvNew => hnewZ.notMem_of_mem_left hvNew (hXZ hv)⟩
  · intro y hy
    rcases hchosen hy with hy | hy
    · exact hfarNew hy
    · rcases hy with rfl | hy
      · exact hs
      · exact mem_singleton_iff.mp hy ▸ ht
  · have hsep := theorem_8_3_claim_11 h hfarOld hfarNew
      (fun a ha b hb hne => hYdist a ha.1 b hb.1 hne)
      (fun y hy => by have hb := hy.2; omega) hs ht hsnear htnear
      (by omega) hθ hsymm hsymm' htri
    exact fun a ha b hb hne => hsep a (hchosen ha) b (hchosen hb) hne

end GraphMinor.GM16
