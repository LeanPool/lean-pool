/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section3a
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Section 3 of "Quickly excluding a planar graph": the proof of (3.1)

The counting in the proof of (3.1), pages 331–332, and (3.1) itself, `theorem_3_1`.

There are two small changes.
- The paper's proof of (2) counts paths. We use the same idea on separations (`not_both_splits`):
  two separations, one of
  `G \\ V(P₂)` and one of `G \\ V(P₃)`, combine to a separation of `G` of order less than `2k`
  between `V(P₁)` and `V(P₂)`.
  A path `P₂` splits `P₁` and `P₃` when `G \\ V(P₂)` has such a separation; by Menger's theorem this
  is the paper's meaning.
- The paper counts `a` paths in `V(A)` and `b` paths in `V(B)`. A path may be in both, inside `V(A ∩
  B)`, and then the pairs
  counted by `ab` are not all pairs of different paths. So we put in `b` only the paths not in
  `V(A)`, and all the paper's
  inequalities still hold.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G H A B C D : Hypergraph α β} {Z : Set α} {k : ℕ}

/-- **(2)** in the proof of (3.1) (page 331), in the form of separations. -/
theorem not_both_splits (hG : G.IsGraph) (hZf : Z.Finite) (hl : Linked G Z) {a b c : Set α}
    (hb : b ⊆ G.vertexSet) (hc : c ⊆ G.vertexSet) (hbc : Disjoint b c) (hLa : ¬ Light G Z k a)
    (hLb : ¬ Light G Z k b)
    (h₁ : ∃ A B, (G.deleteVertices b).IsSeparation A B ∧ a ⊆ A.vertexSet ∧ c ⊆ B.vertexSet ∧
      separationOrder A B < k)
    (h₂ : ∃ A B, (G.deleteVertices c).IsSeparation A B ∧ a ⊆ A.vertexSet ∧ b ⊆ B.vertexSet ∧
      separationOrder A B < k) : False := by
  obtain ⟨A₁', B₁', hs₁', ha₁, hc₁, ho₁⟩ := h₁
  obtain ⟨A₂', B₂', hs₂', ha₂, hb₂, ho₂⟩ := h₂
  obtain ⟨A₁, B₁, hs₁, hV₁, hW₁, -, -⟩ := exists_lift hG hb hs₁'
  obtain ⟨A₂, B₂, hs₂, hV₂, hW₂, -, -⟩ := exists_lift hG hc hs₂'
  have hs := (hs₁.symm.union_inter hs₂.symm).symm
  have hsub : ((A₁ ∩ A₂) ∩ (B₁ ∪ B₂)).vertexSet ⊆ (A₁' ∩ B₁').vertexSet ∪ (A₂' ∩ B₂').vertexSet
    := by
    rintro x ⟨⟨hx₁, hx₂⟩, hx₃⟩
    rw [hV₁] at hx₁
    rw [hV₂] at hx₂
    have hx₃' : x ∈ B₁'.vertexSet ∪ b ∨ x ∈ B₂'.vertexSet ∪ c := by
      rcases hx₃ with h | h
      · exact Or.inl (hW₁ ▸ h)
      · exact Or.inr (hW₂ ▸ h)
    by_cases hxb : x ∈ b
    · have hxc : x ∉ c := disjoint_left.1 hbc hxb
      exact Or.inr ⟨hx₂.resolve_right hxc, hb₂ hxb⟩
    · by_cases hxc : x ∈ c
      · exact Or.inl ⟨hx₁.resolve_right hxb, hc₁ hxc⟩
      · have h₁' := hx₁.resolve_right hxb
        have h₂' := hx₂.resolve_right hxc
        rcases hx₃' with (h | h) | (h | h)
        · exact Or.inl ⟨h₁', h⟩
        · exact absurd h hxb
        · exact Or.inr ⟨h₂', h⟩
        · exact absurd h hxc
  have ho : separationOrder (A₁ ∩ A₂) (B₁ ∪ B₂) < 2 * k := by
    have := (ncard_le_ncard hsub ((A₁' ∩ B₁').vertexSet_finite.union (A₂' ∩
      B₂').vertexSet_finite)).trans
      (ncard_union_le _ _)
    unfold separationOrder at ho₁ ho₂ ⊢
    omega
  rcases min_le_order hZf hl hs with h | h
  · exact hLa ⟨_, _, hs, fun x hx => ⟨hV₁ ▸ Or.inl (ha₁ hx), hV₂ ▸ Or.inl (ha₂ hx)⟩, by omega, h⟩
  · refine hLb ⟨_, _, hs.symm, fun x hx => Or.inl (hW₁ ▸ Or.inr hx), ?_, ?_⟩
    · rw [separationOrder_comm]
      omega
    · rwa [separationOrder_comm]

section Count

variable {n : ℕ} (R : Fin n → Fin n → Fin n → Prop)

open Classical in
/-- The number of ordered pairs of different paths, other than `b`, split by `b`. -/
noncomputable def splitCount (b : Fin n) : ℕ :=
  ((Finset.univ.erase b).offDiag.filter fun p => R b p.1 p.2).card

private theorem card_fiber (Q : Fin n → Fin n → Fin n → Prop) [∀ a b c, Decidable (Q a b c)] :
    (Finset.univ.filter fun t : Fin n × Fin n × Fin n => Q t.1 t.2.1 t.2.2).card =
      ∑ b, (Finset.univ.filter fun p : Fin n × Fin n => Q b p.1 p.2).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _
    => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.card_image_of_injective (Finset.univ.filter fun p : Fin n × Fin n => Q b p.1 p.2)
    (f := fun p => (b, p.1, p.2)) (fun p q h => by simpa [Prod.ext_iff] using h)]
  congr 1
  ext ⟨x, y, z⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨y, z, h, rfl, rfl, rfl⟩
  · rintro ⟨a, c, h, rfl, rfl, rfl⟩
    exact ⟨h, rfl⟩

/-- The averaging step of (3.1) (page 332): if each triple has at most one member that splits the
other two, then some `b`
splits at most a third of the ordered pairs. -/
theorem exists_few_splits (hn : 0 < n) (hsym : ∀ a b c, R b a c → R b c a)
    (hasym : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → R b a c → ¬ R c a b) :
    ∃ b, 3 * splitCount R b ≤ (n - 1) * (n - 2) := by
  classical
  let dist : Fin n → Fin n → Fin n → Prop := fun b a c => a ≠ b ∧ c ≠ b ∧ a ≠ c
  let Q : Fin n → Fin n → Fin n → Prop := fun b a c => dist b a c ∧ R b a c
  let D := Finset.univ.filter fun t : Fin n × Fin n × Fin n => dist t.1 t.2.1 t.2.2
  let T := Finset.univ.filter fun t : Fin n × Fin n × Fin n => Q t.1 t.2.1 t.2.2
  let rot : Fin n × Fin n × Fin n → Fin n × Fin n × Fin n := fun t => (t.2.1, t.2.2, t.1)
  have hrot : Function.Injective rot := fun s t h => by
    obtain ⟨h₁, h₂, h₃⟩ := (by simpa [rot, Prod.ext_iff] using h : s.2.1 = t.2.1 ∧ s.2.2 = t.2.2
      ∧ s.1 = t.1)
    exact Prod.ext h₃ (Prod.ext h₁ h₂)
  have hrot' : Function.Injective (rot ∘ rot) := hrot.comp hrot
  have hT₀ : T ⊆ D := fun t ht => by
    simp only [T, D, Q, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.1
  have hrD : ∀ t ∈ D, rot t ∈ D := fun t ht => by
    simp only [D, dist, rot, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.2.2.symm, ht.1.symm, ht.2.1⟩
  have hT₁ : T.image rot ⊆ D := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact hrD s (hT₀ hs)
  have hT₂ : T.image (rot ∘ rot) ⊆ D := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact hrD _ (hrD s (hT₀ hs))
  have hmem : ∀ {t}, t ∈ T → (t.2.1 ≠ t.1 ∧ t.2.2 ≠ t.1 ∧ t.2.1 ≠ t.2.2) ∧ R t.1 t.2.1 t.2.2
    := fun {t} ht => by
    simpa [T, Q, dist] using ht
  -- Rotating a triple once or twice leaves `T`.
  have hd₁ : ∀ t, t ∈ T → rot t ∉ T := by
    rintro ⟨b, a, c⟩ h h'
    obtain ⟨⟨hab, hcb, hac⟩, hR⟩ := hmem h
    obtain ⟨-, hR'⟩ := hmem h'
    have hR₂ : R b a c := hR
    have hR₃ : R a c b := hR'
    exact hasym c b a hcb (Ne.symm hab) (Ne.symm hac) (hsym _ _ _ hR₂) hR₃
  have hd₂ : ∀ t, t ∈ T → rot (rot t) ∉ T := by
    rintro ⟨b, a, c⟩ h h'
    obtain ⟨⟨hab, hcb, hac⟩, hR⟩ := hmem h
    obtain ⟨-, hR'⟩ := hmem h'
    have hR₂ : R b a c := hR
    have hR₃ : R c b a := hR'
    exact hasym a b c hab (Ne.symm hcb) hac hR₂ (hsym _ _ _ hR₃)
  have hdis₁ : Disjoint T (T.image rot) := Finset.disjoint_left.2 fun t ht ht' => by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht'
    exact hd₁ s hs ht
  have hdis₂ : Disjoint (T ∪ T.image rot) (T.image (rot ∘ rot)) := Finset.disjoint_left.2 fun t ht
    ht' => by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht'
    rcases Finset.mem_union.1 ht with h | h
    · exact hd₂ s hs h
    · obtain ⟨s', hs', he⟩ := Finset.mem_image.1 h
      exact hd₁ s hs (hrot he ▸ hs')
  have hcard : 3 * T.card ≤ D.card := by
    have := Finset.card_le_card (Finset.union_subset (Finset.union_subset hT₀ hT₁) hT₂)
    rw [Finset.card_union_of_disjoint hdis₂, Finset.card_union_of_disjoint hdis₁,
      Finset.card_image_of_injective _ hrot, Finset.card_image_of_injective _ hrot'] at this
    omega
  have hTs : T.card = ∑ b, splitCount R b := by
    rw [show T = _ from rfl, card_fiber Q]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold splitCount
    congr 1
    ext ⟨a, c⟩
    simp [Q, dist, Finset.mem_offDiag]
  have hDs : D.card = ∑ _b : Fin n, (n - 1) * (n - 2) := by
    rw [show D = _ from rfl, card_fiber dist]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (Finset.univ.filter fun p : Fin n × Fin n => dist b p.1 p.2) =
      (Finset.univ.erase b).offDiag := by
      ext ⟨a, c⟩
      simp [dist, Finset.mem_offDiag]
    rw [this, Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
      Fintype.card_fin,
      show n - 2 = n - 1 - 1 by omega, Nat.mul_sub_one (n - 1) (n - 1)]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun b => 3 * splitCount R b) (g := fun _ => (n - 1) * (n - 2)) (by
      rw [← Finset.mul_sum, ← hTs, ← hDs]
      exact hcard)
  exact ⟨b, hb⟩

/-- Pairs from two disjoint sets give a lower bound for `splitCount`. -/
theorem two_mul_le_splitCount {b : Fin n} (X Y : Finset (Fin n)) (hXY : Disjoint X Y) (hX : b ∉ X)
  (hY : b ∉ Y)
    (h : ∀ a ∈ X, ∀ c ∈ Y, R b a c) (hsym : ∀ a b c, R b a c → R b c a) :
    2 * (X.card * Y.card) ≤ splitCount R b := by
  classical
  have hdisj : Disjoint (X ×ˢ Y) (Y ×ˢ X) := Finset.disjoint_left.2 fun p h₁ h₂ =>
    Finset.disjoint_left.1 hXY (Finset.mem_product.1 h₁).1 (Finset.mem_product.1 h₂).1
  have hsub : (X ×ˢ Y) ∪ (Y ×ˢ X) ⊆ (Finset.univ.erase b).offDiag.filter fun p => R b p.1 p.2 := by
    have hne : ∀ {a c}, a ∈ X → c ∈ Y → a ≠ c := fun h₁ h₂ e => Finset.disjoint_left.1 hXY h₁
      (e ▸ h₂)
    have hne' : ∀ {a}, a ∈ X ∨ a ∈ Y → a ≠ b := fun h e => h.elim (fun h' => hX (e ▸ h')) fun h'
      => hY (e ▸ h')
    rintro ⟨a, c⟩ hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨⟨hne' (Or.inl h₁), hne' (Or.inr h₂), hne h₁ h₂⟩, h a h₁ c h₂⟩
    · obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨⟨hne' (Or.inr h₁), hne' (Or.inl h₂), fun e => hne h₂ h₁ e.symm⟩, hsym _ _ _
        (h c h₂ a h₁)⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product] at this
  unfold splitCount
  convert this using 1
  rw [Nat.mul_comm Y.card, Nat.two_mul]

end Count

/-- A path that is not inside `V(A)` has at least as many vertices in `V(A ∩ B)` as it has ends in
`V(A)`. This is the
paper's count of the paths that leave `V(A)`, on page 332. -/
theorem ends_le_of_leaves (hs : G.IsSeparation A B) {u v : α} (huv : u ≠ v)
  (w : G.skeleton.Walk u v) (hw : w.IsPath)
    (hV : {y | y ∈ w.support} ⊆ G.vertexSet) {x : α} (hx : x ∈ w.support) (hxA : x ∉ A.vertexSet) :
    (({u, v} : Set α) ∩ A.vertexSet).ncard ≤ ({y | y ∈ w.support} ∩ (A ∩ B).vertexSet).ncard := by
  classical
  have hfin : ({y | y ∈ w.support} ∩ (A ∩ B).vertexSet).Finite := (A ∩ B).vertexSet_finite.subset
    inter_subset_right
  have hxB : x ∈ B.vertexSet := (mem_V_or hs (hV hx)).resolve_left hxA
  have hmeet : ∀ {a : α} (q : G.skeleton.Walk a x), a ∈ A.vertexSet → ∃ y ∈ q.support, y ∈
    (A ∩ B).vertexSet :=
    fun q ha => (conn_support q).meets_sep hs q.start_mem_support q.end_mem_support ha hxB
  have hsplit : ∀ y ∈ (w.takeUntil x hx).support, ∀ y' ∈ (w.dropUntil x hx).reverse.support, y' ≠ x
    → y ≠ y' := by
    intro y hy y' hy' hne
    have hn : ((w.takeUntil x hx).append (w.dropUntil x hx)).support.Nodup := by
      rw [w.take_spec hx]
      exact hw.support_nodup
    rw [SimpleGraph.Walk.support_append, List.nodup_append] at hn
    refine hn.2.2 y hy y' ?_
    have h₁ : y' ∈ (w.dropUntil x hx).support := by simpa using hy'
    rw [← SimpleGraph.Walk.cons_tail_support] at h₁
    exact (List.mem_cons.1 h₁).resolve_left hne
  by_cases hu : u ∈ A.vertexSet
  · obtain ⟨y, hy, hyS⟩ := hmeet (w.takeUntil x hx) hu
    have hyw : y ∈ w.support := w.support_takeUntil_subset_support hx hy
    by_cases hv' : v ∈ A.vertexSet
    · obtain ⟨y', hy', hyS'⟩ := hmeet (w.dropUntil x hx).reverse hv'
      have hyw' : y' ∈ w.support := w.support_dropUntil_subset_support hx (by simpa using hy')
      have hne : y ≠ y' := hsplit y hy y' hy' fun h => hxA (h ▸ hyS'.1)
      have hsub : ({y, y'} : Set α) ⊆ {y | y ∈ w.support} ∩ (A ∩ B).vertexSet := by
        rintro z (rfl | rfl)
        · exact ⟨hyw, hyS⟩
        · exact ⟨hyw', hyS'⟩
      have := ncard_le_ncard hsub hfin
      rw [ncard_pair hne] at this
      exact (ncard_le_ncard inter_subset_left (toFinite _)).trans ((ncard_pair huv).le.trans this)
    · have hsub : ({u, v} : Set α) ∩ A.vertexSet ⊆ {u} := by
        rintro z ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz hv'
      have h₁ := ncard_le_ncard hsub (toFinite _)
      rw [ncard_singleton] at h₁
      exact h₁.trans ((ncard_pos hfin).2 ⟨y, hyw, hyS⟩)
  · by_cases hv' : v ∈ A.vertexSet
    · obtain ⟨y', hy', hyS'⟩ := hmeet (w.dropUntil x hx).reverse hv'
      have hyw' : y' ∈ w.support := w.support_dropUntil_subset_support hx (by simpa using hy')
      have hsub : ({u, v} : Set α) ∩ A.vertexSet ⊆ {v} := by
        rintro z ⟨rfl | rfl, hz⟩
        · exact absurd hz hu
        · rfl
      have h₁ := ncard_le_ncard hsub (toFinite _)
      rw [ncard_singleton] at h₁
      exact h₁.trans ((ncard_pos hfin).2 ⟨y', hyw', hyS'⟩)
    · have : ({u, v} : Set α) ∩ A.vertexSet = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        rintro z ⟨rfl | rfl, hz⟩
        · exact hu hz
        · exact hv' hz
      rw [this, ncard_empty]
      exact Nat.zero_le _

/-- The sizes of disjoint finite sets add up to the size of their union. -/
theorem sum_ncard_eq {ι : Type*} (s : Finset ι) (f : ι → Set α) (hf : ∀ i, (f i).Finite)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) : ∑ i ∈ s, (f i).ncard =
      (⋃ i ∈ s, f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfi : (⋃ x ∈ s, f x).Finite := s.finite_toSet.biUnion fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, ih fun i hi j hj => hd i
      (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj), ncard_union_eq ?_ (hf a) hfi]
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact disjoint_left.1 (hd a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
      fun e => ha (e ▸ hi)) hx hxi

/-- The numbers at the end of the proof of (3.1) (page 332). -/
theorem count_contra {a b k : ℕ} (hk : 1 ≤ k) (ha : 5 * k + 1 ≤ 2 * a) (hb : 5 * k + 1 ≤ 2 * b)
    (hab : 8 * k ≤ a + b) (h : 3 * (2 * (a * b)) ≤ (9 * k - 1) * (9 * k - 2)) : False := by
  have h₁ : (9 * k - 1) * (9 * k - 2) ≤ (9 * k) * (9 * k) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hb
  have h₂ : (2 * a) * (2 * b) = (5 * k + 1 + p) * (5 * k + 1 + q) := by rw [hp, hq]
  have hpq : 6 * k ≤ p + q + 2 := by omega
  nlinarith [Nat.zero_le (p * q), Nat.zero_le (k * p), Nat.zero_le (k * q), Nat.mul_le_mul_left k
    hpq]

/-- The count on page 332: the vertices of `Z` on one side are at most the two on `P`, the two on
each path of `I`, and those on
the other paths, which cost one vertex of `V(A ∩ B) - V(P)` each. -/
private theorem side_count {n : ℕ} {V : Fin n → Set α} (hVf : ∀ i, (V i).Finite)
    (hd : Pairwise fun i j => Disjoint (V i) (V j)) {b : Fin n} {D U : Set α} (hUf : U.Finite)
      (I : Finset (Fin n))
    (hI : b ∉ I) (hZV : D ∩ Z ⊆ ⋃ i, V i ∩ D ∩ Z) (h2 : ∀ i, (V i ∩ D ∩ Z).ncard ≤ 2)
    (hrest : ∀ i, i ≠ b → i ∉ I → (V i ∩ D ∩ Z).ncard ≤ (V i ∩ U).ncard) :
    (D ∩ Z).ncard ≤ 2 + 2 * I.card + U.ncard := by
  classical
  have hle₁ : (D ∩ Z).ncard ≤ ∑ i, (V i ∩ D ∩ Z).ncard := by
    rw [sum_ncard_eq _ (fun i => V i ∩ D ∩ Z) (fun i => (hVf i).subset fun _ h
      => h.1.1) fun i _ j _ hij =>
      (hd hij).mono (fun _ h => h.1.1) fun _ h => h.1.1]
    refine ncard_le_ncard (hZV.trans fun x hx => ?_) ((Finset.univ.finite_toSet).biUnion fun i _ =>
      (hVf i).subset fun _ h => h.1.1)
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact mem_iUnion₂.2 ⟨i, Finset.mem_univ i, hi⟩
  have hsum : ∑ i ∈ Finset.univ.erase b, (V i ∩ U).ncard ≤ U.ncard := by
    rw [sum_ncard_eq _ (fun i => V i ∩ U) (fun i => (hVf i).subset inter_subset_left) fun i _ j _
      hij =>
      (hd hij).mono inter_subset_left inter_subset_left]
    exact ncard_le_ncard (iUnion₂_subset fun _ _ => inter_subset_right) hUf
  have hle₂ : ∑ i ∈ Finset.univ.erase b, (V i ∩ D ∩ Z).ncard ≤
      ∑ i ∈ Finset.univ.erase b, ((if i ∈ I then 2 else 0) + (V i ∩ U).ncard) := by
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hiI : i ∈ I
    · rw [ite_eq_left hiI]
      exact (h2 i).trans (Nat.le_add_right _ _)
    · rw [ite_eq_right hiI, Nat.zero_add]
      exact hrest i (Finset.ne_of_mem_erase hi) hiI
  have hI2 : ∑ i ∈ Finset.univ.erase b, (if i ∈ I then 2 else 0) = 2 * I.card := by
    rw [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    congr 2
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨fun e => hI (e ▸ h), h⟩⟩
  rw [Finset.sum_add_distrib, hI2] at hle₂
  have hb := Finset.add_sum_erase Finset.univ (fun i => (V i ∩ D ∩ Z).ncard) (Finset.mem_univ b)
  have := h2 b
  omega

/-- **(3.1)** (page 330). -/
theorem theorem_3_1 (hG : G.IsGraph) (hk : 1 ≤ k) (hZ : Z ⊆ G.vertexSet) (hZc : Z.ncard = 18 * k)
  (hl : Linked G Z)
    {S T : Set α} (hST : S ∪ T = Z) (hd : Disjoint S T) (hS : S.ncard = 9 * k) (hT : T.ncard
      = 9 * k) :
    ∃ p : PathFromTo G.skeleton S T, (∀ x ∈ Z, x ∈ pathV p → x = p.first ∨ x = p.last) ∧ Good G Z k
      (pathV p) := by
  classical
  have hZf : Z.Finite := G.vertexSet_finite.subset hZ
  have hSZ : S ⊆ Z := hST ▸ subset_union_left
  have hTZ : T ⊆ Z := hST ▸ subset_union_right
  have hSf : S.Finite := hZf.subset hSZ
  have hTf : T.Finite := hZf.subset hTZ
  obtain ⟨P, hP⟩ : HasDisjointPaths G.skeleton S T (9 * k) := hS ▸ hl S T hSZ hTZ (hS.trans hT.symm)
  let V : Fin (9 * k) → Set α := fun i => pathV (P i)
  have hPdis : Pairwise fun i j => Disjoint (V i) (V j) := hP
  have hVf : ∀ i, (V i).Finite := fun i => (P i).walk.support.finite_toSet
  have hfirst : ∀ i, (P i).first ∈ V i := fun i => (P i).walk.start_mem_support
  have hlast : ∀ i, (P i).last ∈ V i := fun i => (P i).walk.end_mem_support
  have hne : ∀ i, (P i).first ≠ (P i).last := fun i e =>
    disjoint_left.1 hd (P i).first_mem (e ▸ (P i).last_mem)
  have hinj₁ : Function.Injective fun i => (P i).first := fun i j h => by
    by_contra hij
    exact disjoint_left.1 (hPdis hij) (hfirst i) ((show (P i).first =
      (P j).first from h) ▸ hfirst j)
  have hinj₂ : Function.Injective fun i => (P i).last := fun i j h => by
    by_contra hij
    exact disjoint_left.1 (hPdis hij) (hlast i) ((show (P i).last = (P j).last from h) ▸ hlast j)
  -- Each vertex of `S` and of `T` is an end of a path, since there are as many paths as vertices of
  -- `S` and of `T`.
  have hends : ∀ i, ∀ x ∈ Z, x ∈ V i → x = (P i).first ∨ x = (P i).last := fun i x hx hxi => by
    rw [← hST] at hx
    rcases hx with hx | hx
    · obtain ⟨j, rfl⟩ := exists_index _ hSf hS hinj₁ (fun i => (P i).first_mem) hx
      by_cases hij : i = j
      · exact Or.inl (hij ▸ rfl)
      · exact (disjoint_left.1 (hPdis hij) hxi (hfirst j)).elim
    · obtain ⟨j, rfl⟩ := exists_index _ hTf hT hinj₂ (fun i => (P i).last_mem) hx
      by_cases hij : i = j
      · exact Or.inr (hij ▸ rfl)
      · exact (disjoint_left.1 (hPdis hij) hxi (hlast j)).elim
  have hVG : ∀ i, V i ⊆ G.vertexSet := fun i _ hx => support_mem (P i).walk (hZ (hSZ
    (P i).first_mem)) hx
  by_contra hno
  push Not at hno
  have hbad : ∀ i, ¬ Good G Z k (V i) := fun i h => hno (P i) (hends i) h
  have hse : ∀ i, (P i).first ∈ Z ∩ V i := fun i => ⟨hSZ (P i).first_mem, hfirst i⟩
  have hte : ∀ i, (P i).last ∈ Z ∩ V i := fun i => ⟨hTZ (P i).last_mem, hlast i⟩
  have hlight : ∀ i, ¬ Light G Z k (V i) := fun i h =>
    hbad i (good_of_light hG hZ hZf hZc hl hk (hVG i) (hne i) (hse i) (hte i) h)
  have hn : 0 < 9 * k := by omega
  let R : Fin (9 * k) → Fin (9 * k) → Fin (9 * k) → Prop := fun b a c => ∃ A B,
    (G.deleteVertices (V b)).IsSeparation A B ∧ V a ⊆ A.vertexSet ∧ V c ⊆ B.vertexSet
      ∧ separationOrder A B < k
  have hsym : ∀ a b c, R b a c → R b c a := by
    rintro a b c ⟨A, B, h₁, h₂, h₃, h₄⟩
    exact ⟨B, A, h₁.symm, h₃, h₂, by rwa [separationOrder_comm]⟩
  have hasym : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → R b a c → ¬ R c a b := fun a b c _ hbc _ h₁ h₂ =>
    not_both_splits hG hZf hl (hVG b) (hVG c) (hPdis hbc) (hlight a) (hlight b) h₁ h₂
  obtain ⟨b, hb⟩ := exists_few_splits R hn hsym hasym
  obtain ⟨A, B, A', B', hs, hWA, hWB, hR, hAZ, hBZ, hs', hVA, hVB, ho⟩ :=
    exists_sep_of_not_good hG hZf (hVG b) (hne b) (hse b) (hte b) (hbad b)
  let U : Set α := (A ∩ B).vertexSet \ V b
  have hUf : U.Finite := (A ∩ B).vertexSet_finite.sdiff
  let X : Finset (Fin (9 * k)) := Finset.univ.filter fun i => i ≠ b ∧ V i ⊆ A.vertexSet
  let Y : Finset (Fin (9 * k)) := Finset.univ.filter fun i => i ≠ b ∧ ¬ V i ⊆ A.vertexSet
    ∧ V i ⊆ B.vertexSet
  let M : Finset (Fin (9 * k)) := Finset.univ.filter fun i => i ≠ b ∧ ¬ V i ⊆ A.vertexSet
    ∧ ¬ V i ⊆ B.vertexSet
  have hXY : Disjoint X Y := Finset.disjoint_filter.2 fun i _ h₁ h₂ => h₂.2.1 h₁.2
  have hbX : b ∉ X := fun h => (Finset.mem_filter.1 h).2.1 rfl
  have hbY : b ∉ Y := fun h => (Finset.mem_filter.1 h).2.1 rfl
  have hUV : ∀ i, i ≠ b → ∀ x ∈ V i, x ∈ (A ∩ B).vertexSet → x ∈ V i ∩ U := fun i hi x hx hxS =>
    ⟨hx, hxS, disjoint_left.1 (hPdis hi) hx⟩
  -- The ends count.
  have hend : ∀ i (D : Set α), V i ∩ D ∩ Z ⊆ ({(P i).first, (P i).last} : Set α) ∩ D
    := fun i D x hx =>
    ⟨(hends i x hx.2 hx.1.1).imp id id, hx.1.2⟩
  have h2 : ∀ i (D : Set α), (V i ∩ D ∩ Z).ncard ≤ 2 := fun i D => by
    refine (ncard_le_ncard ((hend i D).trans inter_subset_left) (toFinite _)).trans ?_
    rw [ncard_pair (hne i)]
  have hleave : ∀ {C E : Hypergraph α β}, G.IsSeparation C E → (C ∩ E).vertexSet =
    (A ∩ B).vertexSet → ∀ i, i ≠ b →
      ¬ V i ⊆ C.vertexSet → (V i ∩ C.vertexSet ∩ Z).ncard ≤ (V i ∩ U).ncard
        := fun {C E} hCE hS i hi hn => by
    obtain ⟨x, hx, hxC⟩ := not_subset.1 hn
    have h₁ := ends_le_of_leaves hCE (hne i) (P i).walk (P i).isPath (hVG i) hx hxC
    refine (ncard_le_ncard (hend i _) (toFinite _)).trans (h₁.trans (ncard_le_ncard ?_
      ((hVf i).subset inter_subset_left)))
    rintro y ⟨hy, hyS⟩
    exact hUV i hi y hy (hS ▸ hyS)
  have hZcov : ∀ D : Set α, D ∩ Z ⊆ ⋃ i, V i ∩ D ∩ Z := fun D x hx => by
    have hxZ := hx.2
    rw [← hST] at hxZ
    rcases hxZ with h | h
    · obtain ⟨j, rfl⟩ := exists_index _ hSf hS hinj₁ (fun i => (P i).first_mem) h
      exact mem_iUnion.2 ⟨j, ⟨hfirst j, hx.1⟩, hx.2⟩
    · obtain ⟨j, rfl⟩ := exists_index _ hTf hT hinj₂ (fun i => (P i).last_mem) h
      exact mem_iUnion.2 ⟨j, ⟨hlast j, hx.1⟩, hx.2⟩
  have hcA := side_count (Z := Z) hVf hPdis (b := b) (D := A.vertexSet) hUf X hbX (hZcov _) (fun i
    => h2 i _) fun i hi hiX =>
    hleave hs rfl i hi fun hsub => hiX (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi, hsub⟩)
  have hcB := side_count (Z := Z) hVf hPdis (b := b) (D := B.vertexSet) hUf Y hbY (hZcov _) (fun i
    => h2 i _) fun i hi hiY => by
    by_cases hsub : V i ⊆ B.vertexSet
    · have hsubA : V i ⊆ A.vertexSet := by
        by_contra hnA
        exact hiY (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi, hnA, hsub⟩)
      exact ncard_le_ncard (fun x hx => hUV i hi x hx.1.1 ⟨hsubA hx.1.1, hsub hx.1.1⟩)
        ((hVf i).subset inter_subset_left)
    · exact hleave hs.symm (GM10.inter_comm B A ▸ rfl) i hi hsub
  -- Each path in `M` meets `U`.
  have hMU : ∀ i ∈ M, 1 ≤ (V i ∩ U).ncard := fun i hi => by
    obtain ⟨-, hib, hnA, hnB⟩ := Finset.mem_filter.1 hi
    obtain ⟨x, hx, hxA⟩ := not_subset.1 hnA
    obtain ⟨y, hy, hyB⟩ := not_subset.1 hnB
    have hyA := (mem_V_or hs (hVG i hy)).resolve_right hyB
    have hxB := (mem_V_or hs (hVG i hx)).resolve_left hxA
    obtain ⟨z, hz, hzS⟩ := (conn_support (P i).walk).meets_sep hs hy hx hyA hxB
    exact (ncard_pos ((hVf i).subset inter_subset_left)).2 ⟨z, hUV i hib z hz hzS⟩
  have hMc : M.card ≤ U.ncard := by
    calc M.card = ∑ _i ∈ M, 1 := by simp
      _ ≤ ∑ i ∈ M, (V i ∩ U).ncard := Finset.sum_le_sum hMU
      _ = (⋃ i ∈ M, V i ∩ U).ncard := sum_ncard_eq _ _ (fun i => (hVf i).subset inter_subset_left)
        fun i _ j _ hij =>
        (hPdis hij).mono inter_subset_left inter_subset_left
      _ ≤ U.ncard := ncard_le_ncard (iUnion₂_subset fun _ _ => inter_subset_right) hUf
  have hall : Finset.univ.erase b ⊆ X ∪ Y ∪ M := fun i hi => by
    have hib := Finset.ne_of_mem_erase hi
    simp only [X, Y, M, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h₁ : V i ⊆ A.vertexSet <;> by_cases h₂ : V i ⊆ B.vertexSet <;> simp [hib, h₁, h₂]
  have hc₃ : 9 * k - 1 ≤ X.card + Y.card + M.card := by
    have := Finset.card_le_card hall
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin] at this
    exact this.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
      (Finset.card_union_le _ _) _))
  have hsp : 2 * (X.card * Y.card) ≤ splitCount R b := two_mul_le_splitCount R X Y hXY hbX hbY
    (fun a ha c hc => by
    obtain ⟨-, hab, hA⟩ := Finset.mem_filter.1 ha
    obtain ⟨-, hcb, -, hB⟩ := Finset.mem_filter.1 hc
    refine ⟨A', B', hs', fun x hx => ?_, fun x hx => ?_, ho⟩
    · have := hA hx
      rw [hVA] at this
      exact this.resolve_right (disjoint_left.1 (hPdis hab) hx)
    · have := hB hx
      rw [hVB] at this
      exact this.resolve_right (disjoint_left.1 (hPdis hcb) hx)) hsym
  have hU : U.ncard < k := hR
  have hAZ' : 6 * k + 2 ≤ (A.vertexSet ∩ Z).ncard := hAZ
  refine count_contra hk (a := X.card) (b := Y.card) (by omega) (by omega) (by omega) ?_
  exact (Nat.mul_le_mul_left 3 hsp).trans hb

end GraphMinor.RST94
