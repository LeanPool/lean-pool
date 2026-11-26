/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5c
import Mathlib.Tactic.Positivity

/-!
# Section 5 of "Quickly excluding a planar graph": (5.5)

The set `C` of (5.5) is made from the shadow of (5.4). It is the union of the sets `C_i \ Z'` that
are not at the chosen leaves, together with a short piece of each chosen leaf.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι κ : Type*} {G : Hypergraph α β}

/-- A connected set with connected sets hanging from it. -/
theorem conn_union_iUnion [Finite κ] {C : Set α} (hC : Conn G C) {E : κ → Set α} (hE : ∀ i, Conn G
  (E i)) (hm : ∀ i, (C ∩ E i).Nonempty) : Conn G (C ∪ ⋃ i, E i) := by
  classical
  let indexFintype := Fintype.ofFinite κ
  have key : ∀ s : Finset κ, Conn G (C ∪ ⋃ i ∈ s, E i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using hC
    | @insert a s _ ih =>
      obtain ⟨x, hx₁, hx₂⟩ := hm a
      have h₁ := ih.union (hE a) ⟨x, Or.inl hx₁, hx₂⟩
      have heq : C ∪ ⋃ i ∈ insert a s, E i = (C ∪ ⋃ i ∈ s, E i) ∪ E a := by
        ext v
        simp only [mem_union, mem_iUnion, Finset.mem_insert]
        constructor
        · rintro (h | ⟨i, rfl | hi, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨i, hi, h⟩)
        · rintro ((h | ⟨i, hi, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨i, Or.inr hi, h⟩
          · exact Or.inr ⟨a, Or.inl rfl, h⟩
      rw [heq]
      exact h₁
  simpa using key Finset.univ

/-- In a tree with at least three vertices, the sets that are not at the chosen leaves form a
connected set. -/
theorem conn_nonleaf [Fintype ι] {S : SimpleGraph ι} (hS : S.IsTree) (hcard : 3
  ≤ Fintype.card ι) {L : Set ι} (hL : L ⊆ leaves S) {D : ι → Set α} (hD : ∀ i, Conn G (D i))
    (ht : ∀ i j, S.Adj i j → ∃ x ∈ D i, ∃ y ∈ D j, G.skeleton.Adj x y) (hR : ∃ v, v ∉ L) :
    Conn G (⋃ v ∈ Lᶜ, D v) ∧ ∀ l ∈ L, ∃ n, n ∉ L ∧ S.Adj l n := by
  classical
  have hnb : ∀ l, ∃ n, l ∈ L → S.neighborSet l = {n} := fun l => by
    by_cases hl : l ∈ L
    · have hdeg : (S.neighborSet l).encard = 1 := hL hl
      obtain ⟨n, hn⟩ := encard_eq_one.mp hdeg
      exact ⟨n, fun _ => hn⟩
    · exact ⟨l, fun h => absurd h hl⟩
  choose nb hnb using hnb
  have hadj : ∀ {l}, l ∈ L → S.Adj l (nb l) := fun {l} hl => by
    have : nb l ∈ S.neighborSet l := by
      rw [hnb l hl]
      rfl
    exact this
  have hnbL : ∀ l, l ∈ L → nb l ∉ L := fun l hl hn => by
    have hN₂ : S.neighborSet (nb l) = {l} := by
      rw [hnb _ hn]
      have : l ∈ S.neighborSet (nb l) := (hadj hl).symm
      rw [hnb _ hn] at this
      rw [show nb (nb l) = l from (this : l = nb (nb l)).symm]
    have hclosed : ∀ {x y} (w : S.Walk x y), x ∈ ({l, nb l} : Set ι) → y ∈ ({l, nb l} : Set ι)
      := fun {x y} w => by
      induction w with
      | nil => exact id
      | @cons x y z h q ih =>
        rintro (rfl | rfl)
        · refine ih ?_
          have hm : y ∈ S.neighborSet x := h
          rw [hnb x hl] at hm
          exact Or.inr hm
        · refine ih ?_
          have hm : y ∈ S.neighborSet (nb l) := h
          rw [hN₂] at hm
          exact Or.inl hm
    have hall : ∀ x, x ∈ ({l, nb l} : Set ι) := fun x => by
      obtain ⟨w⟩ := hS.connected l x
      exact hclosed w (Or.inl rfl)
    have huniv : ({l, nb l} : Set ι) = univ := eq_univ_of_forall hall
    have hle : (univ : Set ι).ncard ≤ 2 := by
      rw [← huniv]
      exact ncard_insert_le _ _ |>.trans (by simp)
    rw [ncard_univ, Nat.card_eq_fintype_card] at hle
    omega
  refine ⟨?_, fun l hl => ⟨nb l, hnbL l hl, hadj hl⟩⟩
  obtain ⟨v₀, hv₀⟩ := hR
  let Rr : ι → ι → Prop := Relation.ReflTransGen fun a b => a ∉ L ∧ b ∉ L ∧ S.Adj a b
  have hwalk : ∀ {x v} (w : S.Walk x v), v ∉ L → (x ∉ L → Rr x v) ∧ (x ∈ L → Rr (nb x) v)
    := fun {x v} w => by
    induction w with
    | nil =>
      intro hv
      exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => absurd h hv⟩
    | @cons x y z h q ih =>
      intro hz
      obtain ⟨h₁, h₂⟩ := ih hz
      by_cases hy : y ∈ L
      · have hm : x ∈ S.neighborSet y := h.symm
        rw [hnb y hy] at hm
        have hxy : x = nb y := hm
        refine ⟨fun _ => hxy ▸ h₂ hy, fun hx => ?_⟩
        exact absurd (hxy ▸ hx) (hnbL y hy)
      · refine ⟨fun hx => Relation.ReflTransGen.head ⟨hx, hy, h⟩ (h₁ hy), fun hx => ?_⟩
        have hm : y ∈ S.neighborSet x := h
        rw [hnb x hx] at hm
        have hyx : y = nb x := hm
        exact hyx ▸ h₁ hy
  obtain ⟨x₀, hx₀⟩ := (hD v₀).1
  have hreach : ∀ u, Rr u v₀ → u ∉ L → ∀ x ∈ D u, ∃ w : G.skeleton.Walk x x₀, ∀ t ∈ w.support, t ∈
    ⋃ v ∈ Lᶜ, D v := by
    intro u hu
    induction hu using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro _ x hx
      obtain ⟨w, hw⟩ := (hD v₀).2 x hx x₀ hx₀
      exact ⟨w, fun t ht' => mem_iUnion₂.2 ⟨v₀, hv₀, hw t ht'⟩⟩
    | @head a c hac _ ih =>
      intro ha x hx
      obtain ⟨p, hp, q, hq, hpq⟩ := ht a c hac.2.2
      obtain ⟨w, hw⟩ := (hD a).2 x hx p hp
      obtain ⟨w', hw'⟩ := ih hac.2.1 q hq
      refine ⟨w.append (SimpleGraph.Walk.cons hpq w'), fun t ht' => ?_⟩
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
        List.mem_cons] at ht'
      rcases ht' with h | h | h
      · exact mem_iUnion₂.2 ⟨a, ha, hw t h⟩
      · exact mem_iUnion₂.2 ⟨a, ha, hw t (by rw [h]; exact w.end_mem_support)⟩
      · exact hw' t h
  refine conn_of_reach (b := x₀) (mem_iUnion₂.2 ⟨v₀, hv₀, hx₀⟩) fun x hx => ?_
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 hx
  obtain ⟨w⟩ := hS.connected u v₀
  exact hreach u ((hwalk w hv₀).1 hu) hu x hxu

/-- The last part of the proof of (5.5): the paths inside the chosen leaves of the shadow, and the
set `C`. -/
theorem shadow_touch [Fintype ι] [Finite κ] {G₂ : Hypergraph α β} {y y' : ι
  → α} {S : SimpleGraph ι} {D : ι → Set α} (hs : Shadow G G₂ y y' S D) (hS : S.IsTree) (hcard : 3
    ≤ Fintype.card ι)
    (hsub : ∀ i, y i ∈ G.vertexSet) (hy'G : range y' ⊆ G₂.vertexSet) (hy' : Function.Injective y')
      {b : κ → ι} (hb : Function.Injective b) (hL : ∀ i, b i ∈ leaves S)
        (hR : ∃ v, v ∉ range b) {z₁ : κ → α} (hz₁ : ∀ i, z₁ i ∈ D (b i)) :
    ∃ (P : ∀ i, G.skeleton.Walk (z₁ i) (y' (b i))) (C : Set α), IsLinkage G G₂ z₁ (fun i => y'
      (b i)) P ∧ Conn G C ∧ C ⊆ G.vertexSet ∧ (∀ x ∈ C, x ∉ G₂.vertexSet) ∧
      ∀ i, (∀ x ∈ (P i).support, x ∉ C) ∧ ∃ x ∈ C, ∃ u ∈ (P i).support, u ≠ y' (b i)
        ∧ G.skeleton.Adj x u := by
  classical
  have hDV : ∀ i, D i ⊆ G.vertexSet := fun i x hx => by
    obtain ⟨w, -⟩ := (hs.conn i).2 (y i) (hs.mem i) x hx
    exact support_mem w (hsub i) w.end_mem_support
  obtain ⟨hC₀, hnb⟩ := conn_nonleaf hS hcard (L := range b) (by rintro _ ⟨i, rfl⟩; exact hL i)
    hs.conn hs.touch hR
  -- The paths: inside `D (b i)`, then one more edge.
  have hpath : ∀ i, ∃ (c : α) (w : G.skeleton.Walk (z₁ i) c), w.IsPath ∧ G.skeleton.Adj c (y'
    (b i)) ∧ ∀ t ∈ w.support, t ∈ D (b i) := fun i => by
    obtain ⟨c, hc, hadj⟩ := hs.attach (b i)
    obtain ⟨w, hw⟩ := (hs.conn (b i)).2 (z₁ i) (hz₁ i) c hc
    exact ⟨c, w.bypass, w.bypass_isPath, hadj, fun t ht => hw t
      (SimpleGraph.Walk.support_bypass_subset_support w ht)⟩
  choose c w hw₁ hw₂ hw₃ using hpath
  have hyoff : ∀ i j, y' i ∉ D j := fun i j h => hs.off j _ h (hy'G (mem_range_self i))
  let P : ∀ i, G.skeleton.Walk (z₁ i) (y' (b i)) := fun i => (w i).concat (hw₂ i)
  have hPs : ∀ i t, t ∈ (P i).support ↔ t ∈ (w i).support ∨ t = y' (b i) := fun i t => by
    simp [P, SimpleGraph.Walk.support_concat, or_comm]
  -- The piece of the leaf.
  have hpiece : ∀ i, ∃ E : Set α, Conn G E ∧ (E ∩ ⋃ v ∈ (range b)ᶜ, D v).Nonempty ∧ E ⊆ D
    (b i) ∪ ⋃ v ∈ (range b)ᶜ, D v ∧ (∀ t ∈ E, t ∉ (w i).support) ∧
      ∃ u ∈ E, ∃ v ∈ (w i).support, G.skeleton.Adj u v := fun i => by
    obtain ⟨n, hn, hadj⟩ := hnb (b i) (mem_range_self i)
    obtain ⟨x, hx, x', hx', hxx⟩ := hs.touch _ _ hadj
    have hx'C : x' ∈ ⋃ v ∈ (range b)ᶜ, D v := mem_iUnion₂.2 ⟨n, hn, hx'⟩
    have hne : Disjoint (D n) (D (b i)) := hs.disj fun e => hn (e ▸ mem_range_self i)
    have hx'w : x' ∉ (w i).support := fun h => disjoint_left.1 hne hx' (hw₃ i x' h)
    by_cases hxw : x ∈ (w i).support
    · refine ⟨{x'}, conn_singleton, ⟨x', rfl, hx'C⟩, ?_, ?_, x', rfl, x, hxw, hxx.symm⟩
      · intro t ht
        exact Or.inr (mem_singleton_iff.1 ht ▸ hx'C)
      · intro t ht
        exact mem_singleton_iff.1 ht ▸ hx'w
    · obtain ⟨r, hr⟩ := (hs.conn (b i)).2 x hx (z₁ i) (hz₁ i)
      have hne₂ : x ≠ z₁ i := fun e => hxw (e ▸ (w i).start_mem_support)
      obtain ⟨t, u, q, h, r', hu, hq, hrr⟩ := exists_run (L := {t | t ∈ (w i).support}) r
        (w i).start_mem_support hne₂
      have hqD : ∀ v ∈ q.support, v ∈ D (b i) := fun v hv => hr v (by rw [hrr]; simp
        [SimpleGraph.Walk.mem_support_append_iff, hv])
      refine ⟨{x'} ∪ {v | v ∈ q.support}, conn_singleton.union_adj (conn_support q) rfl
        q.start_mem_support hxx.symm, ⟨x', Or.inl rfl, hx'C⟩, ?_, ?_, t, Or.inr q.end_mem_support,
          u, hu, h⟩
      · rintro v (hv | hv)
        · exact Or.inr (by rw [mem_singleton_iff.1 hv]; exact hx'C)
        · exact Or.inl (hqD v hv)
      · rintro v (hv | hv)
        · rw [mem_singleton_iff.1 hv]
          exact hx'w
        · by_cases hvx : v = x
          · exact hvx ▸ hxw
          · exact hq v hv hvx
  choose E hE₁ hE₂ hE₃ hE₄ hE₅ using hpiece
  let C₀ : Set α := ⋃ v ∈ (range b)ᶜ, D v
  let C : Set α := C₀ ∪ ⋃ i, E i
  have hCcases : ∀ x ∈ C, x ∈ C₀ ∨ ∃ i, x ∈ D (b i) ∧ x ∈ E i := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      rcases hE₃ i hi with h | h
      · exact Or.inr ⟨i, h, hi⟩
      · exact Or.inl h
  have hCD : ∀ x ∈ C, ∃ v, x ∈ D v := fun x hx => by
    rcases hCcases x hx with h | ⟨i, h, -⟩
    · obtain ⟨v, -, hv⟩ := mem_iUnion₂.1 h
      exact ⟨v, hv⟩
    · exact ⟨_, h⟩
  have hdisj : ∀ {x i}, x ∈ C → x ∉ (w i).support := fun {x i} hx hxw => by
    have hxD := hw₃ i x hxw
    rcases hCcases x hx with h | ⟨j, h₁, h₂⟩
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 h
      exact disjoint_left.1 (hs.disj (i := v) (j := b i) fun e => hv (e ▸ mem_range_self i)) hxv hxD
    · by_cases hij : j = i
      · subst hij
        exact hE₄ j x h₂ hxw
      · exact disjoint_left.1 (hs.disj (i := b j) (j := b i) fun e => hij (hb e)) h₁ hxD
  have hm : ∀ i : κ, (C₀ ∩ E i).Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := hE₂ i
    exact ⟨x, hx.2, hx.1⟩
  have hconn : Conn G C := conn_union_iUnion hC₀ hE₁ hm
  refine ⟨P, C, ⟨fun i => ?_, fun i t ht htG => ?_, fun i j hij => disjoint_left.2 fun t ht ht'
    => ?_⟩, hconn, fun x hx => ?_, fun x hx hxG => ?_, fun i => ⟨fun x hx hxC => ?_, ?_⟩⟩
  · exact (hw₁ i).concat (fun h => hyoff _ _ (hw₃ i _ h)) _
  · rcases (hPs i t).1 ht with h | h
    · exact absurd htG (hs.off _ t (hw₃ i t h))
    · exact h
  · have hbij : b i ≠ b j := fun e => hij (hb e)
    rcases (hPs i t).1 ht with h₁ | h₁ <;> rcases (hPs j t).1 ht' with h₂ | h₂
    · exact disjoint_left.1 (hs.disj hbij) (hw₃ i t h₁) (hw₃ j t h₂)
    · exact hyoff _ _ (h₂ ▸ hw₃ i t h₁)
    · exact hyoff _ _ (h₁ ▸ hw₃ j t h₂)
    · exact hbij (hy' (h₁.symm.trans h₂))
  · obtain ⟨v, hv⟩ := hCD x hx
    exact hDV v hv
  · obtain ⟨v, hv⟩ := hCD x hx
    exact hs.off v x hv hxG
  · rcases (hPs i x).1 hx with h | h
    · exact hdisj hxC h
    · obtain ⟨v, hv⟩ := hCD x hxC
      exact hyoff _ v (h ▸ hv)
  · obtain ⟨u, hu, v, hv, huv⟩ := hE₅ i
    exact ⟨u, Or.inr (mem_iUnion.2 ⟨i, hu⟩), v, (hPs i v).2 (Or.inl hv),
      fun e => hyoff _ _ (e ▸ hw₃ i v hv), huv⟩

/-- **(5.5)** (page 342). -/
theorem theorem_5_5 [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {g m k n : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m)
    (hn : n = (2 * g + 1) * (2 * m - 5) + 2) (hc : Fintype.card ι = m) (hk : n ≤ 2 * k)
      (hθ : k * 20 ^ (2 * g * (m - 2) + n * (m + 1)) ≤ θ) (hno : ¬ HasGrid G T θ g) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α)
      (P : ∀ i, G.skeleton.Walk (z i) (z' i)) (C : Set α),
      Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧ IsLinkage G G' z z' P ∧ Conn G C ∧ C ⊆ G.vertexSet ∧
        (∀ x ∈ C, x ∉ G'.vertexSet) ∧
        ∀ i, (∀ x ∈ (P i).support, x ∉ C) ∧ ∃ x ∈ C, ∃ u ∈ (P i).support, u ≠ z' i
          ∧ G.skeleton.Adj x u := by
  classical
  have hnlarge : m + 1 ≤ n ∧ 3 ≤ n := by
    have h₁ : 5 * (2 * m - 5) ≤ (2 * g + 1) * (2 * m - 5) := Nat.mul_le_mul_right _ (by omega)
    omega
  set K := k * 20 ^ (2 * g * (m - 2) + n) with hK
  have hk₂ : n ≤ 2 * K := hk.trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right k
    (by positivity)))
  have hθ₂ : K * 20 ^ (n * Fintype.card ι) ≤ θ := by
    rw [hK, hc, Nat.mul_assoc, ← pow_add]
    convert hθ using 3
    rw [Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨Y₀, hF, G₁, T₁, θ₁, y, hYc, hN₁, hb₁, hle₁, hconf₁, hzav, hsel⟩ := theorem_4_4 hG hN (k
    := K) (n := n) (by omega) (by omega) hk₂ hθ₂
  have hno₁ : ¬ HasGrid G₁ T₁ θ₁ g := fun h => hno (h.of_conformal hle₁ hN.tangle hN₁.tangle hconf₁)
  obtain ⟨G₂, T₂, θ₂, y', S, D, hR, hb₂, hS, hs, hL⟩ := theorem_5_4 (IsGraph.of_le hG hle₁) hN₁ hg
    hm (hYc.trans hn) (by rw [hYc]; exact hk) (by rw [hYc]; exact hb₁) hno₁
  obtain ⟨L, hLs, hLc⟩ := exists_subset_card_eq (s := leaves S) (n := m) hL
  have hZ : (y '' L).ncard = Fintype.card ι := by
    rw [InjOn.ncard_image (hN₁.inj.injOn), hLc, hc]
  obtain ⟨z₁, hz₁r, hR₁⟩ := hsel (y '' L) (image_subset_range _ _) hZ
  have hch : ∀ i, ∃ l ∈ L, y l = z₁ i := fun i => by
    have : z₁ i ∈ y '' L := hz₁r ▸ mem_range_self i
    exact this
  choose b hbL hby using hch
  have hbinj : Function.Injective b := fun i j he => hR₁.nodule.inj (by rw [← hby i, ← hby j, he])
  have hrb : range b ⊆ L := by
    rintro _ ⟨i, rfl⟩
    exact hbL i
  have hRn : ∃ v, v ∉ range b := by
    by_contra hcon
    push Not at hcon
    have huniv : range b = univ := eq_univ_of_forall hcon
    have : (range b).ncard = n := by
      rw [huniv, ncard_univ, Nat.card_eq_fintype_card, hYc]
    rw [ncard_range hbinj, hc] at this
    omega
  obtain ⟨P', C, hP', hC, hCV, hCoff, hCt⟩ := shadow_touch hs hS (by rw [hYc]; omega) (fun i
    => hN₁.free.1 (mem_range_self i)) hR.nodule.free.1 hR.nodule.inj hbinj (fun i => hLs
      (hbL i)) hRn (z₁ := z₁) (fun i => hby i ▸ hs.mem _)
  have hR₂ : Residual G₁ T₁ θ₁ z₁ G₂ T₂ θ₂ fun i => y' (b i) :=
    ⟨⟨hR.nodule.tangle, hR.nodule.inj.comp hbinj, hR.nodule.free.subset hR.nodule.tangle
      (range_comp_subset_range _ _)⟩, hR.le, fun i => hby i ▸ hR.avoid _, hR.conformal, P', hP'⟩
  obtain ⟨R, hRl⟩ := hR₁.link
  have hst : Stage G T θ z 1 G₁ T₁ θ₁ z₁ R := ⟨hR₁.nodule, hR₁.le, hR₁.conformal, hRl, fun _
    => hR₁.avoid, fun h => absurd h (by omega)⟩
  have hst₂ := hst.step hN.tangle hR₂ hP'
  refine ⟨G₂, T₂, θ₂, _, _, C, hst₂.residual (by omega), ?_, hst₂.link, hC.mono hle₁,
    hCV.trans hle₁.vertexSet_subset, hCoff, fun i => ⟨fun x hx hxC => ?_, ?_⟩⟩
  · exact hb₂
  · have hmem : x ∈ (R i).support ∨ x ∈ (P' i).support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hx
    rcases hmem with h | h
    · have := hRl.2.1 i x h (hCV hxC)
      exact (hCt i).1 x (this ▸ (P' i).start_mem_support) hxC
    · exact (hCt i).1 x h hxC
  · obtain ⟨-, x, hx, u, hu, hne, hadj⟩ := hCt i
    exact ⟨x, hx, u, by simp [SimpleGraph.Walk.mem_support_append_iff, hu], hne,
      skeleton_mono hle₁ hadj⟩

end GraphMinor.RST94
