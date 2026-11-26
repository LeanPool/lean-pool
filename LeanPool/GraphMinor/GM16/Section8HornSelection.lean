/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8
import Mathlib.Data.Fintype.EquivFin
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.MetricPoints

/-!
# Choosing horn paths in Graph Minors XVI

In Claim (6) of the proof of (8.3), at most one horn end is near the
rearrangement centre. Each other excluded path uses a different vertex of the
deleted set apart from the horn vertex. These two bounds leave the required
number of paths.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Graph Minors XVI, proof of (8.3), Claim (6), page 67.
From a horn with `ζ + τ` paths one can choose `τ` paths whose ends are far from
the centre and whose only deleted vertex is their common end. -/
theorem theorem_8_3_claim_6 {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {v : α} {θ ζ τ r : ℕ}
    {P : Fin (ζ + τ) → Graph α β} {ends : Fin (ζ + τ) → S}
    (h : IsHorn G H η d v θ (ζ + τ) P ends)
    {Z : Set α} (hZfin : Z.Finite) (hvZ : v ∈ Z) (hZcard : Z.ncard ≤ ζ)
    {z : Set S} (hz : z ∈ H.A) (hr : 2 * r ≤ θ)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c) :
    ∃ f : Fin τ ↪ Fin (ζ + τ), ∀ i,
      r ≤ d z {ends (f i)} ∧ V(P (f i)) ∩ Z = {v} := by
  classical
  let bad : Set (Fin (ζ + τ)) := {i | ∃ x ∈ Z, x ∈ V(P i) ∧ x ≠ v}
  let near : Set (Fin (ζ + τ)) := {i | d z {ends i} < r}
  have hbad : bad.ncard ≤ ζ - 1 := by
    let witness : Fin (ζ + τ) → α := fun i =>
      if hi : i ∈ bad then (show ∃ x ∈ Z, x ∈ V(P i) ∧ x ≠ v from hi).choose else v
    have hw : ∀ i ∈ bad, witness i ∈ Z ∧ witness i ∈ V(P i) ∧ witness i ≠ v := by
      intro i hi
      dsimp only [witness]
      rw [dite_eq_left hi]
      exact (show ∃ x ∈ Z, x ∈ V(P i) ∧ x ≠ v from hi).choose_spec
    have hinj : InjOn witness bad := by
      intro i hi j hj heq
      by_contra hne
      have hx : witness i ∈ V(P i) ∩ V(P j) := ⟨(hw i hi).2.1, heq ▸ (hw j hj).2.1⟩
      rw [(h.2.2.2.2.1 i j hne).1] at hx
      exact (hw i hi).2.2 (mem_singleton_iff.mp hx)
    have hbound := ncard_le_ncard_of_injOn witness
      (fun i hi => show witness i ∈ Z \ {v} from ⟨(hw i hi).1, (hw i hi).2.2⟩)
      hinj (hZfin.sdiff)
    have hcount := ncard_sdiff' (singleton_subset_iff.mpr hvZ) hZfin
    rw [ncard_singleton] at hcount
    omega
  have hnear : near.ncard ≤ 1 := by
    apply (ncard_le_one (toFinite near)).2
    intro i hi j hj
    by_contra hne
    have hiA := singleton_mem_A_of_mem_V (h.2.1 i)
    have hjA := singleton_mem_A_of_mem_V (h.2.1 j)
    have hbound := htri {ends i} hiA z hz {ends j} hjA
    rw [hsymm {ends i} hiA z hz] at hbound
    have hdist := h.2.2.2.2.2 i j hne
    change d z {ends i} < r at hi
    change d z {ends j} < r at hj
    omega
  let good : Set (Fin (ζ + τ)) := univ \ (bad ∪ near)
  have hζ : 1 ≤ ζ := (ncard_pos hZfin).mpr ⟨v, hvZ⟩ |>.trans_le hZcard
  have hgood : τ ≤ good.ncard := by
    have hunion := ncard_union_le bad near
    have hcount := ncard_sdiff' (subset_univ (bad ∪ near)) (toFinite univ)
    have hall : (univ : Set (Fin (ζ + τ))).ncard = ζ + τ := by simp
    change τ ≤ (univ \ (bad ∪ near)).ncard
    omega
  let : Fintype good := Fintype.ofFinite good
  have hcard : Fintype.card (Fin τ) ≤ Fintype.card good := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hgood
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f.trans ⟨Subtype.val, Subtype.val_injective⟩, ?_⟩
  intro i
  have hi : (f i).val ∉ bad ∧ (f i).val ∉ near := by
    simpa only [good, mem_sdiff, mem_univ, true_and, mem_union, not_or] using (f i).property
  have hfar : r ≤ d z {ends (f i).val} := Nat.le_of_not_gt hi.2
  refine ⟨hfar, ?_⟩
  apply subset_antisymm
  · rintro x ⟨hxP, hxZ⟩
    apply mem_singleton_iff.mpr
    by_contra hne
    exact hi.1 ⟨x, hxZ, hxP, hne⟩
  · rintro x rfl
    exact ⟨(GM09.IsGraphPathWithEnds.left_mem (h.2.2.1 (f i).val)), hvZ⟩

/-- Graph Minors XVI, proof of (8.3), Claim (8), page 67.
The selected ends survive the rearrangement, and compression preserves the
required breadth after subtracting `4λ + 2`. -/
theorem theorem_8_3_claim_8 {α : Type u} {β : Type v}
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam ψ τ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    {ends : Fin τ → S} (hends : ∀ i, ends i ∈ H.V)
    (hfar : ∀ i, lam < d z {ends i})
    (hsep : ∀ i j, i ≠ j → θ ≤ d {ends i} {ends j})
    (hψ : ψ + (4 * lam + 2) ≤ θ) :
    (∀ i, ends i ∈ H'.V ∧ η'.vMap (ends i) = η.vMap (ends i)) ∧
    ∀ i j, i ≠ j → ψ ≤ d' {ends i} {ends j} := by
  have hkeep := fun i => h.vMap_eq (ends i) (hends i) (hfar i)
  refine ⟨hkeep, ?_⟩
  intro i j hij
  have hbound := compression_vertex_dist_le h.isCompression
    (hends i) (hends j) (hkeep i).1 (hkeep j).1
  have hdist := hsep i j hij
  omega

/-- Graph Minors XVI, proof of (8.3), Claim (10), page 67.
At most one hair is discarded. Every retained hair is a vertex of the new
drawing and has the same image in the ambient graph. -/
theorem theorem_8_3_claim_10 {α : Type u} {β : Type v}
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam r δ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    {Y : Set S} (hY : Y ⊆ H.V) (hcard : Y.ncard = δ)
    (hsep : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂})
    (hr : 2 * r ≤ θ) (hlam : lam < r)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c) :
    δ - 1 ≤ {y ∈ Y | r ≤ d z {y}}.ncard ∧
      ∀ y ∈ {y ∈ Y | r ≤ d z {y}}, y ∈ H'.V ∧ η'.vMap y = η.vMap y := by
  refine ⟨?_, ?_⟩
  · rw [← hcard]
    exact theorem_8_3_claim_10_card hY h.z_mem hr hsep hsymm htri
  · intro y hy
    exact h.vMap_eq y (hY hy.1) (hlam.trans_le hy.2)

/-- Graph Minors XVI, proof of (8.3), Claim (11), pages 67–68.
The retained hairs and the two ends of the new path remain pairwise far apart.
The retained hairs are far from the centre, whereas both new ends are near it. -/
theorem theorem_8_3_claim_11 {α : Type u} {β : Type v}
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    {Y : Set S} (hY : Y ⊆ H.V) (hY' : Y ⊆ H'.V)
    (hsep : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂})
    (hfar : ∀ y ∈ Y, ψ + 5 * lam + 2 ≤ d z {y})
    {s t : S} (hs : s ∈ H'.V) (ht : t ∈ H'.V)
    (hsnear : pointAtomDist H d s z ≤ lam) (htnear : pointAtomDist H d t z ≤ lam)
    (hst : ψ ≤ d' {s} {t}) (hθ : ψ + (4 * lam + 2) ≤ θ)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hsymm' : ∀ a ∈ H'.A, ∀ b ∈ H'.A, d' a b = d' b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c) :
    ∀ y₁ ∈ Y ∪ {s, t}, ∀ y₂ ∈ Y ∪ {s, t}, y₁ ≠ y₂ → ψ ≤ d' {y₁} {y₂} := by
  have hcross : ∀ y ∈ Y, ∀ x ∈ ({s, t} : Set S), ψ ≤ d' {y} {x} := by
    intro y hy x hx
    have hxV : x ∈ H'.V := by rcases hx with rfl | rfl <;> assumption
    have hxnear : pointAtomDist H d x z ≤ lam := by rcases hx with rfl | rfl <;> assumption
    have hbound := pointAtomDist_triangle htri y x h.z_mem
    rw [pointAtomDist_of_mem_vertex d (hY hy) z,
      hsymm {y} (singleton_mem_A_of_mem_V (hY hy)) z h.z_mem] at hbound
    have hcompressed := h.isCompression.dist_le y x
    rw [pointDist_of_mem_vertices d' (hY' hy) hxV] at hcompressed
    have hdist := hfar y hy
    omega
  intro a ha b hb hne
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · have hbound := compression_vertex_dist_le h.isCompression (hY ha) (hY hb) (hY' ha) (hY' hb)
      have hdist := hsep a ha b hb hne
      omega
    · exact hcross a ha b hb
  · rcases hb with hb | hb
    · have haV : a ∈ H'.V := by rcases ha with rfl | rfl <;> assumption
      rw [hsymm' {a} (singleton_mem_A_of_mem_V haV) {b} (singleton_mem_A_of_mem_V (hY' hb))]
      exact hcross b hb a ha
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hne rfl).elim
      · exact hst
      · rw [hsymm' _ (singleton_mem_A_of_mem_V ht) _ (singleton_mem_A_of_mem_V hs)]
        exact hst
      · exact (hne rfl).elim

omit [T2Space S] in
/-- Graph Minors XVI, proof of (8.3), Claim (9), page 67.
The paths preserved in Claim (7), with the ends and breadth from Claim (8),
form a horn over the rearranged span. -/
theorem theorem_8_3_claim_9 {α : Type u} {β : Type v}
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G} {η' : SpanEmbedding H' G}
    {d d' : Set S → Set S → ℕ} {v : α} {θ ψ σ τ : ℕ}
    {P : Fin σ → Graph α β} {ends : Fin σ → S}
    (h : IsHorn G H η d v θ σ P ends) (f : Fin τ ↪ Fin σ)
    (hv : v ∉ V(η'.imageGraph))
    (hends : ∀ i, ends (f i) ∈ H'.V ∧ η'.vMap (ends (f i)) = η.vMap (ends (f i)))
    (hinter : ∀ i, V(P (f i)) ∩ V(η'.imageGraph) = {η'.vMap (ends (f i))})
    (hsep : ∀ i j, i ≠ j → ψ ≤ d' {ends (f i)} {ends (f j)}) :
    IsHorn G H' η' d' v ψ τ (fun i => P (f i)) (fun i => ends (f i)) := by
  refine ⟨⟨h.1.1, hv⟩, fun i => (hends i).1, ?_, hinter, ?_, hsep⟩
  · intro i
    rw [(hends i).2]
    exact h.2.2.1 (f i)
  · intro i j hij
    exact h.2.2.2.2.1 (f i) (f j) (fun heq => hij (f.injective heq))

end GraphMinor.GM16
