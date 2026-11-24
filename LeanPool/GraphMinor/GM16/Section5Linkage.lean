/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM16.Section5HornSelection
import LeanPool.GraphMinor.GM16.Section5Reroute
import LeanPool.GraphMinor.GM09.Basic

/-!
# Building the disjoint paths in XVI (5.5)

Claim (1) builds the paths one at a time. An unused horn vertex exists
because the old paths meet at most `m` horn vertices. Select spokes far
from the old ends, reroute by (5.4), and keep the metric separation since
all new ends are among the selected and old ends.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, proof of (5.5), Claim (1), pages 57–58. -/
theorem theorem_5_5_claim_1
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {X : Set α} {μ r : ℕ}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hX : X.Finite) (hXcard : X.ncard = μ)
    (hhorns : ∀ x ∈ X, ∃ (P : Fin (8 * μ) → Graph α β) (ends : Fin (8 * μ) → S),
      IsHorn G H η d x (2 * r) (8 * μ) P ends)
    (hsymm : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a})
    (htri : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c}) :
    ∀ m, m ≤ μ → ∃ (Q : Fin m → Graph α β) (s t : Fin m → S),
      (∀ i, s i ∈ H.V ∧ t i ∈ H.V ∧ s i ≠ t i) ∧
      (∀ i, IsHPathWithEnds G η.imageGraph (Q i) (η.vMap (s i)) (η.vMap (t i))) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ((⋃ i, V(Q i)) ∩ X).ncard ≤ m ∧
      ∀ a ∈ range s ∪ range t, ∀ b ∈ range s ∪ range t,
        a ≠ b → r ≤ d {a} {b} := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
    · simp
    · rintro a (⟨i, _⟩ | ⟨i, _⟩) <;> exact i.elim0
  | succ m ih =>
    intro hmμ
    have hm : m < μ := by omega
    obtain ⟨Q, s, t, hst, hQ, hQQ, hcount, hdist⟩ := ih (by omega)
    have hex : ∃ x ∈ X, x ∉ ⋃ j, V(Q j) := by
      by_contra h
      have hsub : X ⊆ (⋃ j, V(Q j)) ∩ X := by
        intro x hx
        refine ⟨?_, hx⟩
        by_contra hxQ
        exact h ⟨x, hx, hxQ⟩
      have hc := ncard_le_ncard hsub (hX.subset inter_subset_right)
      omega
    obtain ⟨x, hxX, hxQ⟩ := hex
    obtain ⟨P, ends, hhorn⟩ := hhorns x hxX
    let W := range s ∪ range t
    have hW : W.Finite := (finite_range s).union (finite_range t)
    have hWH : W ⊆ H.V := by
      rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact (hst i).1
      · exact (hst i).2.1
    have hWcard : W.ncard ≤ 2 * m := by
      have hs : (range s).ncard ≤ m := by
        rw [← image_univ]
        simpa using (ncard_image_le (f := s) (s := univ))
      have ht : (range t).ncard ≤ m := by
        rw [← image_univ]
        simpa using (ncard_image_le (f := t) (s := univ))
      have hc := ncard_union_le (range s) (range t)
      change (range s ∪ range t).ncard ≤ 2 * m
      omega
    obtain ⟨f, hf⟩ := theorem_5_5_select_spokes hhorn hX hxX hXcard hW hWH hWcard hm hsymm htri
    have hendsH : ∀ i, ends (f i) ∈ H.V := fun i => hhorn.2.1 (f i)
    have hPne : ∀ i, η.vMap (ends (f i)) ≠ x := by
      intro i h
      exact hhorn.1.2 (h ▸ η.bijOn_v.mapsTo (hendsH i))
    have hpair : ∀ i j, i ≠ j → V(P (f i)) ∩ V(P (f j)) = {x} ∧
        Disjoint E(P (f i)) E(P (f j)) := by
      intro i j hij
      exact hhorn.2.2.2.2.1 (f i) (f j) (f.injective.ne hij)
    have hxQi : ∀ j, x ∉ V(Q j) := fun j h => hxQ (mem_iUnion.mpr ⟨j, h⟩)
    obtain ⟨R, a, b, hR, hRR, hnewcount, hnewends⟩ := theorem_5_5_reroute
      hV hE η.imageGraph_le hX hhorn.1.1
      (fun i => ⟨hPne i, hhorn.2.2.1 (f i)⟩)
      (fun i => η.bijOn_v.mapsTo (hendsH i))
      (fun i => hhorn.2.2.2.1 (f i)) hpair (fun i => (hf i).1)
      hQ hQQ hxQi hcount (by omega : 5 * m + 2 ≤ 5 * μ)
    let A := range (fun i : Fin (5 * μ) => ends (f i)) ∪ W
    have hAH : A ⊆ H.V := by
      rintro z (⟨i, rfl⟩ | hz)
      · exact hendsH i
      · exact hWH hz
    have hAsep : ∀ z ∈ A, ∀ w ∈ A, z ≠ w → r ≤ d {z} {w} := by
      rintro z (⟨i, rfl⟩ | hz) w (⟨j, rfl⟩ | hw) hne
      · have hij : f i ≠ f j := fun h => hne (congrArg ends h)
        have hd := hhorn.2.2.2.2.2 (f i) (f j) hij
        change r ≤ d {ends (f i)} {ends (f j)}
        omega
      · exact (hf i).2 w hw
      · rw [hsymm z (hWH hz) (ends (f j)) (hendsH j)]
        exact (hf j).2 z hz
      · exact hdist z hz w hw hne
    have hlabels : ∀ z ∈ range (fun i : Fin (5 * μ) => η.vMap (ends (f i))) ∪
        range (fun j => η.vMap (s j)) ∪ range (fun j => η.vMap (t j)),
        ∃ y ∈ A, η.vMap y = z := by
      rintro z ((⟨i, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
      · exact ⟨ends (f i), Or.inl ⟨i, rfl⟩, rfl⟩
      · exact ⟨s j, Or.inr (Or.inl ⟨j, rfl⟩), rfl⟩
      · exact ⟨t j, Or.inr (Or.inr ⟨j, rfl⟩), rfl⟩
    have hsa := fun i => hlabels (a i) (hnewends i).1
    have htb := fun i => hlabels (b i) (hnewends i).2
    choose s' hs'A hs'a using hsa
    choose t' ht'A ht'b using htb
    have hR' : ∀ i, IsHPathWithEnds G η.imageGraph (R i)
        (η.vMap (s' i)) (η.vMap (t' i)) := by
      intro i
      rw [hs'a i, ht'b i]
      exact hR i
    refine ⟨R, s', t', ?_, hR', hRR, hnewcount, ?_⟩
    · intro i
      refine ⟨hAH (hs'A i), hAH (ht'A i), ?_⟩
      intro heq
      exact (hR' i).2.2.1 (congrArg η.vMap heq)
    · intro z hz w hw hne
      have hzA : z ∈ A := by
        rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact hs'A i
        · exact ht'A i
      have hwA : w ∈ A := by
        rcases hw with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact hs'A i
        · exact ht'A i
      exact hAsep z hzA w hwA hne

end GraphMinor.GM16
