/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section4a

/-!
# Section 4 of "Quickly excluding a planar graph": (4.1)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), (4.1), pages 335–337.

The paper's `C` is a connected subgraph, and here it is a connected set of vertices. The paper's
Case 1 is then: some edge outside `E(A)` has two
different ends in `C`. In the paper's form, a parallel edge of `C` becomes a loop of `C/e` at a
vertex outside `Z` that the induction cannot remove. In
the form here this cannot happen, since a loop has only one end.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G H A B : Hypergraph α β} {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α
  β)}
  {e : β} {u v : α} {hu : u ∈ G.vertexSet} {huv : u ≠ v}

/-- The claim in Case 1 of (4.1) (pages 335–336): `Z` stays free in `G/e`. -/
theorem free_contract (hG : G.IsGraph) (heu : G.Inc e u) (hev : G.Inc e v) (hH : H ≤ G)
    (hHc : H ≤ contract G e u v hu huv) (hvH : v ∉ H.vertexSet) (heH : e ∉ H.edgeSet)
      (hT : IsTangle H θ T) {Z : Set α}
    (hfree : IsFreeSet G (inducedTangle G H T θ) θ Z) (hvZ : v ∉ Z) (hlt : Z.ncard < θ)
    (hAB : (A, B) ∈ inducedTangle G H T θ) (ho : separationOrder A B = Z.ncard)
      (hZ : Z ⊆ A.vertexSet)
    (heA : e ∉ A.edgeSet)
    (hmax : ∀ A' B', (A', B') ∈ inducedTangle G H T θ → separationOrder A' B' = Z.ncard
      → Z ⊆ A'.vertexSet → size A' ≤ size A) :
    IsFreeSet (contract G e u v hu huv) (inducedTangle (contract G e u v hu huv) H T θ) θ Z := by
  have hT₀ := isTangle_inducedTangle hH hT
  have hs := hT₀.isSeparation hAB
  refine ⟨fun x hx => ⟨hfree.1 hx, fun h => hvZ (h ▸ hx)⟩, hfree.2.1, ?_⟩
  rintro A₀ B₀ ⟨hs₀, ho₀, hm₀⟩ hZ₀
  by_contra hcon
  push Not at hcon
  have hcon' : separationOrder A₀ B₀ < Z.ncard := hcon
  have ho₀' : separationOrder A₀ B₀ < θ := ho₀
  have hs₀' : (contract G e u v hu huv).IsSeparation A₀ B₀ := hs₀
  obtain ⟨A', B', hs', hsub, ho₁, ho₂, hVA, hVB, hEA, hEB⟩ := contract_lift_up hG heu hev hs₀'
  have hagA : A' ∩ H = A₀ ∩ H := inter_eq_of_agree hs'.left_le hs₀'.left_le hH hHc
    (fun x hx => hVA x fun h => hvH (h ▸ hx)) fun f hf => hEA f fun h => heH (h ▸ hf)
  have hagB : B' ∩ H = B₀ ∩ H := inter_eq_of_agree hs'.right_le hs₀'.right_le hH hHc
    (fun x hx => hVB x fun h => hvH (h ▸ hx)) fun f hf => hEB f fun h => heH (h ▸ hf)
  have hm' : (A', B') ∈ inducedTangle G H T θ := by
    refine ⟨hs', lt_of_le_of_lt ho₁ (by omega), ?_⟩
    change (A' ∩ H, B' ∩ H) ∈ T
    rw [hagA, hagB]
    exact hm₀
  have hle := hfree.2.2 hm' (hZ₀.trans hsub)
  have heA' : e ∈ A'.edgeSet := ho₂ (by omega)
  have hoeq : separationOrder A' B' = Z.ncard := by omega
  have hsU : G.IsSeparation (A ∪ A') (B ∩ B') := hs.union_inter hs'
  have hAU : A ≤ A ∪ A' := le_union_left hs.left_le hs'.left_le
  have hneU : A ∪ A' ≠ A := fun h => heA (h ▸ (Or.inr heA' : e ∈ (A ∪ A').edgeSet))
  have hbig : Z.ncard < separationOrder (A ∪ A') (B ∩ B') := by
    by_contra hsmall
    push Not at hsmall
    have hmU : (A ∪ A', B ∩ B') ∈ inducedTangle G H T θ := by
      refine (hT₀.axiom1 hsU (by omega)).resolve_right fun hm => hT₀.axiom2 hAB hm' hm ?_
      rw [GM10.union_comm A A'] at hsU
      exact (GM10.union_comm A A') ▸ hsU.union_eq
    have h₁ := hfree.2.2 hmU fun x hx => Or.inl (hZ hx)
    have h₂ := hmax _ _ hmU (by omega) fun x hx => Or.inl (hZ hx)
    exact absurd (size_lt_of_lt hAU hneU.symm) (by omega)
  have hsum := separationOrder_add_separationOrder hs hs'
  have hsI : G.IsSeparation (A ∩ A') (B ∪ B') := (hs.symm.union_inter hs'.symm).symm
  have hmI : (A ∩ A', B ∪ B') ∈ inducedTangle G H T θ :=
    GraphMinor.GM10.theorem_2_9_proof hT₀ hAB hsI (by omega) (Or.inr (Or.inl fun x hx => hx.1))
  have := hfree.2.2 hmI fun x hx => ⟨hZ hx, hsub (hZ₀ hx)⟩
  omega

/-- The end of Case 1 of (4.1) (page 336): a residual nodule of `G/e` is a residual nodule of `G`.
-/
theorem residual_of_contract [Finite ι] {z z' : ι → α} {G' : Hypergraph α β} {T' : Set
  (Hypergraph α β × Hypergraph α β)} {θ' : ℕ}
    (heu : G.Inc e u) (hev : G.Inc e v) (hH : H ≤ G) (hHc : H ≤ contract G e u v hu huv)
      (hvH : v ∉ H.vertexSet)
    (huH : u ∉ H.vertexSet) (heH : e ∉ H.edgeSet) (hzc : ∀ i, z i ∈ (contract G e u v hu
      huv).vertexSet)
    (hR : Residual (contract G e u v hu huv) (inducedTangle (contract G e u v hu huv) H T θ) θ z G'
      T' θ' z')
    (huG' : u ∉ G'.vertexSet) : Residual G (inducedTangle G H T θ) θ z G' T' θ' z' := by
  classical
  let fintypeIndices := Fintype.ofFinite ι
  obtain ⟨hG'G, hvG', heG', -⟩ := le_of_le_contract hR.le huG'
  have hθ' := hR.conformal.1
  refine ⟨hR.nodule, hG'G, hR.avoid, ⟨hθ', ?_⟩, ?_⟩
  · rintro ⟨A', B'⟩ ⟨hs', ho', hm'⟩
    obtain ⟨A₁, B₁, hs₁, ho₁, hVA, hVB, hEA, hEB⟩ := contract_lift_down (hu := hu) (huv
      := huv) heu hev hs'
    have hag : ∀ {K : Hypergraph α β}, K ≤ G → K ≤ contract G e u v hu huv → v ∉ K.vertexSet
      → u ∉ K.vertexSet → e ∉ K.edgeSet →
        A' ∩ K = A₁ ∩ K ∧ B' ∩ K = B₁ ∩ K := fun {K} h₁ h₂ h₃ h₄ h₅ =>
      ⟨inter_eq_of_agree hs'.left_le hs₁.left_le h₁ h₂
          (fun x hx => (hVA x (fun h => h₃ (h ▸ hx)) fun h => h₄ (h ▸ hx)).symm) fun f hf =>
            (hEA f fun h => h₅ (h ▸ hf)).symm,
        inter_eq_of_agree hs'.right_le hs₁.right_le h₁ h₂
          (fun x hx => (hVB x (fun h => h₃ (h ▸ hx)) fun h => h₄ (h ▸ hx)).symm) fun f hf =>
            (hEB f fun h => h₅ (h ▸ hf)).symm⟩
    obtain ⟨hag₁, hag₂⟩ := hag hG'G hR.le hvG' huG' heG'
    obtain ⟨hag₃, hag₄⟩ := hag hH hHc hvH huH heH
    have hm₁ : (A₁, B₁) ∈ inducedTangle (contract G e u v hu huv) H T θ := hR.conformal.2 (by
      refine ⟨hs₁, lt_of_le_of_lt ho₁ ho', ?_⟩
      change (A₁ ∩ G', B₁ ∩ G') ∈ T'
      rw [← hag₁, ← hag₂]
      exact hm')
    refine ⟨hs', lt_of_lt_of_le ho' hθ', ?_⟩
    change (A' ∩ H, B' ∩ H) ∈ T
    rw [hag₃, hag₄]
    exact hm₁.2.2
  · obtain ⟨P, hpath, hlast, hdis⟩ := hR.link
    have hlift := fun i => exists_walk_lift heu hev (P i)
    choose w hw using hlift
    have hQ : ∀ i t, t ∈ (w i).bypass.support → t ∈ (P i).support ∨ (t = v ∧ u ∈ (P i).support)
      := fun i t ht =>
      hw i t ((w i).support_bypass_subset_support ht)
    have hPv : ∀ i, v ∉ (P i).support := fun i hi => (support_mem (P i) (hzc i) hi).2 rfl
    refine ⟨fun i => (w i).bypass, fun i => (w i).bypass_isPath, fun i t ht htG => ?_, fun i j hij
      => disjoint_left.2 fun t ht ht' => ?_⟩
    · rcases hQ i t ht with h | ⟨rfl, -⟩
      · exact hlast i t h htG
      · exact absurd htG hvG'
    · rcases hQ i t ht with h₁ | ⟨rfl, h₁⟩ <;> rcases hQ j _ ht' with h₂ | ⟨h₃, h₂⟩
      · exact disjoint_left.1 (hdis hij) h₁ h₂
      · exact hPv i (h₃ ▸ h₁)
      · exact hPv j h₂
      · exact disjoint_left.1 (hdis hij) h₁ h₂

/-- A connected set projects to a connected set of `G/e`. -/
theorem conn_contract (hG : G.IsGraph) (heu : G.Inc e u) (hev : G.Inc e v) {C : Set α}
  (hC : Conn G C) (huC : u ∈ C) :
    Conn (contract G e u v hu huv) (C \ {v}) := by
  classical
  refine ⟨⟨u, huC, huv⟩, fun a ha b hb => ?_⟩
  obtain ⟨w, hw⟩ := hC.2 a ha.1 b hb.1
  have hproj := exists_walk_project (hu := hu) (huv := huv) w heu hev hG
  rw [contractMap_of_ne ha.2, contractMap_of_ne hb.2] at hproj
  obtain ⟨p, hp⟩ := hproj
  refine ⟨p, fun t ht => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hp t ht
  by_cases hyv : y = v
  · subst hyv
    rw [contractMap_self]
    exact ⟨huC, huv⟩
  · rw [contractMap_of_ne hyv]
    exact ⟨hw y hy, hyv⟩

/-- **(4.1)** (page 335). `T` is a tangle of `H = G \ V(C)`, and `inducedTangle G H T θ` is the
paper's `𝒯₀`. The number `n` is the paper's `|V(C) - Z|`,
on which the proof is by induction. -/
theorem theorem_4_1 [Fintype ι] (n : ℕ) : ∀ (G : Hypergraph α β), G.IsGraph → ∀ (z : ι
  → α), Function.Injective z →
    ∀ (C : Set α), Conn G C → C ⊆ G.vertexSet → (∃ i, z i ∈ C) → ∀ (H : Hypergraph α β) (θ : ℕ)
      (T : Set (Hypergraph α β × Hypergraph α β)),
    H ≤ G → (∀ x, x ∈ H.vertexSet ↔ x ∈ G.vertexSet ∧ x ∉ C) → (∀ f ∈ G.edgeSet,
      (∀ x ∈ C, ¬ G.Inc f x) → f ∈ H.edgeSet) →
    IsTangle H θ T → 2 * Fintype.card ι ≤ θ → IsFreeSet G (inducedTangle G H T θ) θ (range z) →
      (C \ range z).ncard = n →
    ∃ G' T' z', Residual G (inducedTangle G H T θ) θ z G' T' (θ - Fintype.card ι) z'
      ∧ ∀ x ∈ C, x ∉ G'.vertexSet := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hG z hz C hC hCV hmeet H θ T hH hVH hEH hT hθ hfree hn
  have hT₀ := isTangle_inducedTangle hH hT
  obtain ⟨i₀, hi₀⟩ := hmeet
  have hZc := ncard_range hz
  have hh : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
  have hZlt : (range z).ncard < θ := by omega
  -- The choice of `(A, B)`.
  have hex : ∃ A B, (A, B) ∈ inducedTangle G H T θ ∧ separationOrder A B = (range z).ncard
    ∧ range z ⊆ A.vertexSet := by
    let A₀ := subOf G (range z) ∅ hfree.1 fun _ he => he.elim
    have hle : A₀ ≤ G := subOf_le
    have hsep : G.IsSeparation A₀ G := sep_of_sets hle le_rfl (fun _ h => Or.inr h) (fun _ h
      => Or.inr h) fun _ he => he.elim
    have hV : (A₀ ∩ G).vertexSet = range z := subset_antisymm (fun _ h => h.1) fun x hx
      => ⟨hx, hfree.1 hx⟩
    have ho : separationOrder A₀ G = (range z).ncard := by
      unfold separationOrder
      rw [hV]
    have hm : (A₀, G) ∈ inducedTangle G H T θ := (hT₀.axiom1 hsep (by omega)).resolve_right fun h
      => hT₀.axiom3 h rfl
    exact ⟨A₀, G, hm, ho, subset_rfl⟩
  obtain ⟨A, ⟨B, hAB, ho, hZ⟩, hmaxA⟩ := exists_max_measure
    (P := fun A => ∃ B, (A, B) ∈ inducedTangle G H T θ ∧ separationOrder A B = (range z).ncard
      ∧ range z ⊆ A.vertexSet) size (size G)
    (fun _ ⟨_, h, _⟩ => size_le_of_le (hT₀.isSeparation h).left_le) (by
      obtain ⟨A, B, h⟩ := hex
      exact ⟨A, B, h⟩)
  have hmax : ∀ A' B', (A', B') ∈ inducedTangle G H T θ → separationOrder A' B' = (range z).ncard
    → range z ⊆ A'.vertexSet →
      size A' ≤ size A := fun A' B' h₁ h₂ h₃ => hmaxA A' ⟨B', h₁, h₂, h₃⟩
  have hs := hT₀.isSeparation hAB
  by_cases hcase : ∃ e ∈ G.edgeSet, e ∉ A.edgeSet ∧ ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ G.Inc e u ∧ G.Inc e v
  · -- Case 1.
    obtain ⟨e, heG, heA, u₁, hu₁, v₁, hv₁, hne, hi₁, hi₂⟩ := hcase
    have heB : e ∈ B.edgeSet := (mem_E_or hs heG).resolve_left heA
    -- Not both ends of `e` are in `Z`, by the maximality of `A` and (2.8).
    have hnotboth : ¬ (u₁ ∈ range z ∧ v₁ ∈ range z) := by
      rintro ⟨h₁, h₂⟩
      obtain ⟨A₁, B₁, hm, hVA, hEA, hVB, -⟩ := exists_move (F := {e}) hT₀ hAB (by
        rintro f rfl
        refine ⟨heB, fun x hx => ?_⟩
        rcases end_eq_or hG hi₁ hi₂ hne hx with rfl | rfl
        · exact hZ h₁
        · exact hZ h₂)
      have hs₁ := hT₀.isSeparation hm
      have hle : A ≤ A₁ := le_of_sets hs.left_le hs₁.left_le hVA.symm.subset
        (hEA ▸ subset_union_left)
      have hne₁ : A₁ ≠ A := fun h => heA (h ▸ (hEA ▸ Or.inr rfl : e ∈ A₁.edgeSet))
      have ho₁ : separationOrder A₁ B₁ = (range z).ncard := by
        rw [← ho]
        change (A₁.vertexSet ∩ B₁.vertexSet).ncard = (A.vertexSet ∩ B.vertexSet).ncard
        rw [hVA, hVB]
      have := hmax A₁ B₁ hm ho₁ (hVA ▸ hZ)
      exact absurd (size_lt_of_lt hle hne₁.symm) (by omega)
    obtain ⟨u, v, huC, hvC, huv, heu, hev, hvZ⟩ : ∃ u v, u ∈ C ∧ v ∈ C ∧ u ≠ v ∧ G.Inc e u
      ∧ G.Inc e v ∧ v ∉ range z := by
      by_cases h : v₁ ∈ range z
      · exact ⟨v₁, u₁, hv₁, hu₁, hne.symm, hi₂, hi₁, fun h' => hnotboth ⟨h', h⟩⟩
      · exact ⟨u₁, v₁, hu₁, hv₁, hne, hi₁, hi₂, h⟩
    have hu : u ∈ G.vertexSet := hCV huC
    have hvH : v ∉ H.vertexSet := fun h => ((hVH v).1 h).2 hvC
    have huH : u ∉ H.vertexSet := fun h => ((hVH u).1 h).2 huC
    have heH : e ∉ H.edgeSet := fun h => huH (end_mem hH h heu)
    have hno : ∀ f ∈ H.edgeSet, ¬ G.Inc f v := fun f hf hi => hvH (end_mem hH hf hi)
    have hHc : H ≤ contract G e u v hu huv := le_contract hH hvH heH hno
    have hfree' := free_contract (hu := hu) (huv := huv) hG heu hev hH hHc hvH heH hT hfree hvZ
      hZlt hAB ho hZ heA hmax
    have hsubC : (C \ {v}) \ range z ⊂ C \ range z := by
      refine ⟨fun x hx => ⟨hx.1.1, hx.2⟩, fun h => ?_⟩
      exact (h ⟨hvC, hvZ⟩).1.2 rfl
    have hfinC : (C \ range z).Finite := (G.vertexSet_finite.subset hCV).sdiff
    have hlt : ((C \ {v}) \ range z).ncard < n := hn ▸ ncard_lt_ncard hsubC hfinC
    obtain ⟨G', T', z', hR, havoid⟩ := ih _ hlt (contract G e u v hu huv)
      (isGraph_contract hG) z hz (C \ {v})
      (conn_contract hG heu hev hC huC) (fun x hx => ⟨hCV hx.1, hx.2⟩)
      ⟨i₀, hi₀, fun h => hvZ (h ▸ mem_range_self i₀)⟩ H θ T hHc
      (fun x => ⟨fun h => by
        obtain ⟨h₁, h₂⟩ := (hVH x).1 h
        exact ⟨⟨h₁, fun h' => hvH (h' ▸ h)⟩, fun h' => h₂ h'.1⟩, fun ⟨h₁, h₂⟩ =>
        (hVH x).2 ⟨h₁.1, fun h' => h₂ ⟨h', h₁.2⟩⟩⟩)
      (fun f hf hno' => hEH f hf.1 fun x hx hi => by
        by_cases hxv : x = v
        · subst hxv
          exact hno' u ⟨huC, huv⟩ ⟨hf.2, huv, Or.inr ⟨rfl, hi⟩⟩
        · exact hno' x ⟨hx, hxv⟩ ⟨hf.2, hxv, Or.inl hi⟩)
      hT hθ hfree' rfl
    have huG' : u ∉ G'.vertexSet := havoid u ⟨huC, huv⟩
    have hR' := residual_of_contract heu hev hH hHc hvH huH heH (fun i => hfree'.1
      (mem_range_self i)) hR huG'
    refine ⟨G', T', z', hR', fun x hx => ?_⟩
    by_cases hxv : x = v
    · subst hxv
      exact (le_of_le_contract hR.le huG').2.1
    · exact havoid x ⟨hx, hxv⟩
  · -- Case 2.
    push Not at hcase
    have hCA : ∀ {a b : α} (w : G.skeleton.Walk a b), (∀ t ∈ w.support, t ∈ C) → a ∈ A.vertexSet
      → b ∈ A.vertexSet := by
      intro a b w
      induction w with
      | nil => exact fun _ h => h
      | @cons x y c hadj q ih' =>
        intro hsup hx
        apply ih' fun t ht => hsup t (by simp [ht])
        obtain ⟨hxy, f, h₁, h₂⟩ := id hadj
        have hxC := hsup x (by simp)
        have hyC := hsup y (by simp)
        by_cases hfA : f ∈ A.edgeSet
        · exact end_mem hs.left_le hfA h₂
        · exact (hcase f (G.edge_mem_of_inc h₁) hfA x hxC y hyC hxy h₁ h₂).elim
    obtain ⟨T', z', hR⟩ := residual_of_sep hG hT₀ hz hfree hθ hAB (ho.trans hZc) hZ
    refine ⟨_, T', z', hR, fun x hx hxG => ?_⟩
    obtain ⟨w, hw⟩ := hC.2 _ hi₀ x hx
    have hxA := hCA w hw (hZ (mem_range_self i₀))
    exact hxG.2 ⟨hxA, hxG.1⟩

end GraphMinor.RST94
