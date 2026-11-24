/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10d
public import LeanPool.GraphMinor.GM09.Section6
public import LeanPool.GraphMinor.GM09.Section7

/-!
# Graph Minors IX, (10.3)

We delete the points of `ΩBar - X` one at a time. The proof of the paper changes the neighborhood at
each step. We keep the presentation of `(G, Ω, Ω₀)` and work with restrictions of `Ω`, since (10.2)
applied to `Ω` gives a separation of `G` that is good for every restriction.

(5.2) is used for paths that may have internal vertices in `ΩBar`: this is
`Society.theorem_5_2_without_no_internal`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- A path with a separation at it is separating. -/
theorem Society.isSeparatingOmegaPath_of_separation (S : Society α β) {Q H₁ H₂ : Graph α β}
    {a b : α} (hQ : S.IsOmegaPathWithEnds Q a b) (hsep : IsGraphSeparation S.G H₁ H₂)
    (hV : V(H₁) ∩ V(H₂) = V(Q)) (h₁ : S.Ω.interval a b ⊆ V(H₁))
    (h₂ : S.Ω.interval b a ⊆ V(H₂)) : S.IsSeparatingOmegaPath Q := by
  refine ⟨⟨a, b, hQ⟩, ?_⟩
  rintro ⟨P', hdisj, v₁, v₃, v₂, v₄, hP₁, hP₂, hcr⟩
  have hav : Disjoint V(P') (V(H₁) ∩ V(H₂)) := hV ▸ hdisj
  have hpair : ({v₂, v₄} : Set α) = {a, b} := hP₂.1.pair_ends_eq hQ.1
  have hcr' : (v₁ ∈ S.Ω.interval a b ∧ v₃ ∈ S.Ω.interval b a) ∨
      (v₃ ∈ S.Ω.interval a b ∧ v₁ ∈ S.Ω.interval b a) := by
    have hsym : S.Ω.Crosses v₂ v₄ v₁ v₃ := hcr.symm
    rcases (Set.pair_eq_pair_iff.mp hpair) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.Ω.crosses_iff_interval.mp hsym
    · rcases S.Ω.crosses_iff_interval.mp hsym with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
  have hc := hP₁.1.isGraphConnected
  rcases hcr' with ⟨hu, hw⟩ | ⟨hu, hw⟩
  · have := connected_subset_right_of_avoids_inter hsep hP₁.1.le hc hav ⟨v₃, hP₁.1.right_mem, h₂ hw⟩
    exact (this hP₁.1.left_mem).2 (h₁ hu)
  · have := connected_subset_right_of_avoids_inter hsep hP₁.1.le hc hav ⟨v₁, hP₁.1.left_mem, h₂ hw⟩
    exact (this hP₁.1.right_mem).2 (h₁ hu)

theorem Neighborhood.IsWeaklyLinked.mono {N : Neighborhood α β} {X Z : Set α}
    (hX : N.IsWeaklyLinked X) (hZ : Z ⊆ X) : N.IsWeaklyLinked Z := by
  classical
  obtain ⟨hXb, P, hP, hd⟩ := hX
  have hX_fin : X.Finite := N.Ω.finite_bar.subset hXb
  have hZ_fin : Z.Finite := hX_fin.subset hZ
  choose st tm hst using hP
  have hst_X : ∀ i, st i ∈ X := fun i => (hst i).left_mem_X
  have hst_V : ∀ i, st i ∈ V(P i) := fun i => (hst i).1.left_mem
  let f : Fin X.ncard → X := fun i => ⟨st i, hst_X i⟩
  have finj : Injective f := by
    intro i j e
    by_contra hne
    have e' : st i = st j := congrArg Subtype.val e
    exact Set.disjoint_left.mp (hd hne) (hst_V i) (e' ▸ hst_V j)
  have : Finite X := hX_fin
  have hcard : Nat.card X ≤ Nat.card (Fin X.ncard) := by
    rw [Nat.card_coe_set_eq, Nat.card_fin]
  have hf := (Function.Injective.bijective_of_nat_card_le finj hcard).2
  have : Finite Z := hZ_fin
  have e : Fin Z.ncard ≃ Z := (Finite.equivFinOfCardEq (Nat.card_coe_set_eq Z)).symm
  choose idx hidx using fun z : Z => hf ⟨z.1, hZ z.2⟩
  have hidx' : ∀ z : Z, st (idx z) = z.1 := fun z => congrArg Subtype.val (hidx z)
  refine ⟨hZ.trans hXb, fun i => P (idx (e i)), fun i => ?_, fun i j hij => ?_⟩
  · refine ⟨st (idx (e i)), tm (idx (e i)), (hst _).1, ?_, (hst _).2.2⟩
    have h := (hst (idx (e i))).2.1
    apply Subset.antisymm
    · rintro v ⟨hv, hvZ⟩
      have : v ∈ V(P (idx (e i))) ∩ X := ⟨hv, hZ hvZ⟩
      rwa [h] at this
    · rintro _ rfl
      exact ⟨hst_V _, by rw [hidx']; exact (e i).2⟩
  · refine hd fun h => hij ?_
    have : e i = e j := by
      apply Subtype.ext
      rw [← hidx', ← hidx', h]
    exact e.injective this

/-- A sublist of a clockwise list is clockwise. -/
theorem CyclicPerm.IsClockwiseSeq.sublist {Ω : CyclicPerm α} {L M : List α}
    (h : Ω.IsClockwiseSeq L) (hs : M.Sublist L) : Ω.IsClockwiseSeq M := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
  refine CyclicPerm.IsClockwiseSeq.of_isBoundedSubseq h (lo := 0) (hi := L.length)
    ⟨Nat.zero_le _, fun i => if hi : i < M.length then (f ⟨i, hi⟩).1 else 0, ?_, ?_⟩
  · intro i hi
    simp only [hi, ↓reduceDIte]
    refine ⟨(f ⟨i, hi⟩).2, Nat.zero_le _, (f ⟨i, hi⟩).2, ?_⟩
    exact hf ⟨i, hi⟩
  · intro i j hij hj
    have hi : i < M.length := hij.trans hj
    simp only [hi, hj, ↓reduceDIte]
    exact f.strictMono (show (⟨i, hi⟩ : Fin M.length) < ⟨j, hj⟩ from hij)

/-- A fence of `Ω` with the `a_i` on one side and the `b_i` on the other. -/
theorem CyclicPerm.exists_isFence_of_ofFn {Ω : CyclicPerm α} {s : ℕ} {a b : Fin (s + 2) → α}
    (h : Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b)) :
    ∃ A B : Set α, Ω.IsFence A B ∧ (∀ i, a i ∈ A) ∧ ∀ i, b i ∈ B := by
  obtain ⟨hclock, hinj_a, hinj_b, hab, ha_bar, hb_bar⟩ := CyclicPerm.isClockwise3_of_ofFn h
  set l : Fin (s + 2) := Fin.last (s + 1)
  set z : Fin (s + 2) := 0
  have hzl : z < l := by simp [z, l, Fin.lt_def]
  have hne : a l ≠ a z := fun e => hzl.ne (hinj_a e).symm
  refine ⟨_, _, Ω.isFence_interval_compl (ha_bar l) (ha_bar z) hne, fun i => ?_, fun i => ?_⟩
  · by_cases hi0 : i = z
    · subst hi0
      exact Or.inl (Or.inr rfl)
    by_cases hil : i = l
    · subst hil
      exact Or.inl (Or.inl rfl)
    have h1 : z.1 < i.1 := by
      have : i.1 ≠ 0 := fun e => hi0 (Fin.ext e)
      simp only [z, Fin.val_zero]
      omega
    have h2 : i.1 < l.1 := by
      have : i.1 ≠ s + 1 := fun e => hil (Fin.ext e)
      have := i.2
      simp only [l, Fin.val_last]
      omega
    have hi := i.2
    have hl := l.2
    have hm := Ω.mem_interval_of_lt h (i₁ := s + 2 - 1 - l.1) (i₂ := s + 2 - 1 - i.1)
      (i₃ := s + 2 - 1 - z.1) (by omega) (by omega) (by simp; omega)
    rw [CyclicPerm.getElem_ofFn_left a b l, CyclicPerm.getElem_ofFn_left a b i,
      CyclicPerm.getElem_ofFn_left a b z] at hm
    exact Or.inr hm
  · have hi := i.2
    have hl := l.2
    have hzv : z.1 = 0 := rfl
    have hlv : l.1 = s + 1 := rfl
    have hm := Ω.mem_interval_of_lt h (i₁ := s + 2 - 1 - l.1) (i₂ := s + 2 - 1 - z.1)
      (i₃ := s + 2 + i.1) (by omega) (by omega) (by simp; omega)
    rw [CyclicPerm.getElem_ofFn_left a b l, CyclicPerm.getElem_ofFn_left a b z,
      CyclicPerm.getElem_ofFn_right a b i] at hm
    exact Ω.mem_interval_rotate_left hm

/-- A list of known length is a list of values of a function on `Fin`. -/
theorem List.exists_ofFn_eq {s : ℕ} (l : List α) (hl : l.length = s) :
    ∃ f : Fin s → α, List.ofFn f = l := by
  subst hl
  exact ⟨fun i => l[i], List.ofFn_getElem⟩

/-- Elements `a_i`, `b_i` of `X` such that `(a_s, …, a_1, x, b_1, …, b_s)` is clockwise. -/
theorem CyclicPerm.exists_ofFn_around {Ω : CyclicPerm α} {X : Set α} {x : α} {s : ℕ}
    (hX : X ⊆ Ω.bar) (hx : x ∈ Ω.bar) (hxX : x ∉ X) (hcard : 2 * s ≤ X.ncard) :
    ∃ a b : Fin s → α, (∀ i, a i ∈ X) ∧ (∀ i, b i ∈ X) ∧
      Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ x :: List.ofFn b) := by
  have hWb : insert x X ⊆ Ω.bar := insert_subset hx hX
  obtain ⟨L, hlen, hset, h0, hcw⟩ :=
    Ω.exists_isClockwiseSeq_of_subset_bar hWb (mem_insert x X)
  have hXfin : X.Finite := Ω.finite_bar.subset hX
  rw [ncard_insert_of_notMem hxX hXfin] at hlen
  obtain - | ⟨x', T⟩ := L
  · simp at hlen
  obtain rfl : x' = x := h0 (by simp)
  have hT : T.length = X.ncard := by simpa using hlen
  have hTX : ∀ y ∈ T, y ∈ X := by
    intro y hy
    have hyW : y ∈ insert x' X := by
      rw [← hset]
      exact List.mem_cons_of_mem _ hy
    rcases hyW with rfl | h
    · exact absurd hy (List.nodup_cons.mp hcw.1).1
    · exact h
  set T₁ := T.take s
  set R := T.drop s
  have hTeq : T = T₁ ++ R := (List.take_append_drop s T).symm
  have hRlen : R.length = T.length - s := List.length_drop ..
  set T₃ := R.drop (R.length - s)
  have hT₃ : T₃.length = s := by
    rw [List.length_drop]
    omega
  have hT₁ : T₁.length = s := by
    rw [List.length_take]
    omega
  have hcw₁ : Ω.IsClockwiseSeq (R ++ x' :: T₁) := by
    have h : Ω.IsClockwiseSeq ((x' :: T₁) ++ R) := by
      rw [List.cons_append, ← hTeq]
      exact hcw
    exact h.append_comm
  have hcw₂ : Ω.IsClockwiseSeq (T₃ ++ x' :: T₁) :=
    hcw₁.sublist ((List.drop_sublist _ R).append_right _)
  obtain ⟨a, ha⟩ := List.exists_ofFn_eq T₃.reverse (by simpa using hT₃)
  obtain ⟨b, hb⟩ := List.exists_ofFn_eq T₁ hT₁
  refine ⟨a, b, fun i => ?_, fun i => ?_, ?_⟩
  · have : a i ∈ List.ofFn a := (List.mem_ofFn' _ _).mpr ⟨i, rfl⟩
    rw [ha, List.mem_reverse] at this
    exact hTX _ ((List.drop_sublist _ R).subset this |> (List.drop_sublist s T).subset)
  · have : b i ∈ List.ofFn b := (List.mem_ofFn' _ _).mpr ⟨i, rfl⟩
    rw [hb] at this
    exact hTX _ ((List.take_sublist s T).subset this)
  · rw [ha, hb, List.reverse_reverse]
    exact hcw₂

/-- The separation of `G ∪ G₀` given by a separation of `G` with `ΩBar₀` on the second side. -/
theorem Society.IsComposition.isGraphSeparation_union {S_comp S₀ : Society α β}
    {N : Neighborhood α β} (hcomp : S_comp.IsComposition S₀ N) {G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation N.G G₁ G₂) (hbar : N.Ω₀.bar ⊆ V(G₂)) :
    IsGraphSeparation S_comp.G G₁ (subgraphUnion S_comp.G G₂ S₀.G) ∧
      V(G₁) ∩ V(subgraphUnion S_comp.G G₂ S₀.G) = V(G₁) ∩ V(G₂) := by
  obtain ⟨⟨hs, -⟩, -, hΩ₀, hbarS⟩ := hcomp
  have hNG : N.G ≤ S_comp.G := hs.2.1
  have h₀ : S₀.G ≤ S_comp.G := hs.1
  have h₁ : G₁ ≤ S_comp.G := hsep.1.trans hNG
  have h₂ : G₂ ≤ S_comp.G := hsep.2.1.trans hNG
  refine ⟨⟨h₁, subgraphUnion_le h₂ h₀, ?_, ?_, ?_⟩, ?_⟩
  · rw [vertexSet_subgraphUnion, ← union_assoc, hsep.2.2.1, union_comm, hs.2.2.1]
  · rw [edgeSet_subgraphUnion h₂ h₀, ← union_assoc, hsep.2.2.2.1, union_comm, hs.2.2.2.1]
  · rw [edgeSet_subgraphUnion h₂ h₀, disjoint_union_right]
    exact ⟨hsep.2.2.2.2, (hs.2.2.2.2.mono_right hsep.1.edgeSet_mono).symm⟩
  · rw [vertexSet_subgraphUnion]
    apply Subset.antisymm
    · rintro v ⟨hv₁, hv | hv⟩
      · exact ⟨hv₁, hv⟩
      · refine ⟨hv₁, hbar ?_⟩
        rw [hΩ₀, hbarS]
        exact ⟨hv, hsep.1.vertexSet_mono hv₁⟩
    · exact fun v hv => ⟨hv.1, Or.inl hv.2⟩

/-- A subgraph that misses the second side of a separation lies in the first side. -/
theorem IsGraphSeparation.le_left_of_disjoint {G H₁ H₂ P : Graph α β}
    (hsep : IsGraphSeparation G H₁ H₂) (hP : P ≤ G) (hd : Disjoint V(P) V(H₂)) : P ≤ H₁ := by
  refine ((Compatible.of_le_le hP hsep.1).le_iff).mpr ⟨fun v hv => ?_, fun e he => ?_⟩
  · have : v ∈ V(H₁) ∪ V(H₂) := by
      rw [hsep.2.2.1]
      exact hP.vertexSet_mono hv
    exact this.resolve_right (Set.disjoint_left.mp hd hv)
  · have : e ∈ E(H₁) ∪ E(H₂) := by
      rw [hsep.2.2.2.1]
      exact hP.edgeSet_mono he
    refine this.resolve_right fun he₂ => ?_
    obtain ⟨x, y, hl⟩ : ∃ x y, P.IsLink e x y := exists_isLink_of_mem_edgeSet he
    obtain ⟨u, w, hl₂⟩ : ∃ u w, H₂.IsLink e u w := exists_isLink_of_mem_edgeSet he₂
    have hG := hl.mono hP
    rcases hG.left_eq_or_eq (hl₂.mono hsep.2.1) with e' | e'
    · exact Set.disjoint_left.mp hd hl.left_mem (e' ▸ hl₂.left_mem)
    · exact Set.disjoint_left.mp hd hl.left_mem (e' ▸ hl₂.right_mem)

theorem CyclicPerm.mem_interval_of_around {Ω : CyclicPerm α} {s : ℕ} {a b : Fin (s + 1) → α}
    {x : α} (h : Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ x :: List.ofFn b)) :
    x ∈ Ω.interval (a 0) (b 0) := by
  have hm := Ω.mem_interval_of_lt h (i₁ := s) (i₂ := s + 1) (i₃ := s + 2) (by omega) (by omega)
    (by simp)
  have e₁ : ((List.ofFn a).reverse ++ x :: List.ofFn b)[s]'(by simp) = a 0 := by
    rw [List.getElem_append_left (by simp), List.getElem_reverse]
    simp
  have e₂ : ((List.ofFn a).reverse ++ x :: List.ofFn b)[s + 1]'(by simp) = x := by
    rw [List.getElem_append_right (by simp)]
    simp
  have e₃ : ((List.ofFn a).reverse ++ x :: List.ofFn b)[s + 2]'(by simp) = b 0 := by
    rw [List.getElem_append_right (by simp)]
    simp
  rwa [e₁, e₂, e₃] at hm

/-- One step of (10.3): the vertex `x` of `Y - X` can be taken off the ends. -/
theorem theorem_10_3_step {S_comp S₀ : Society α β} {N : Neighborhood α β} {p : ℕ} {X Y : Set α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3) (hrural : N.IsRural) (hbreadth : N.HasBreadthGe (p + 4))
    (hX : N.IsWeaklyLinked X) (hcard : 2 * p + 8 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    (hXY : X ⊆ Y) (hY : Y ⊆ S_comp.Ω.bar) {x : α} (hxY : x ∈ Y) (hxX : x ∉ X)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : p ≤ P₀.ncard)
    (hends : S_comp.transactionEnds P₀ ⊆ Y) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ Y \ {x} := by
  classical
  obtain ⟨P_pres, C, hC⟩ := hbreadth
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hNG : N.G ≤ S_comp.G := hcomp.1.1.2.1
  have hXb : X ⊆ N.Ω.bar := hX.1
  obtain ⟨a, b, ha, hb, hL⟩ := CyclicPerm.exists_ofFn_around (s := p + 4) hXb
    (hΩ ▸ hY hxY : x ∈ N.Ω.bar) hxX (by omega)
  have hL₀ : N.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b) :=
    hL.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have hW : N.IsWeaklyLinked (range a ∪ range b) := hX.mono <| by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ha i
    · exact hb i
  obtain ⟨Q, hQ, hQd, hQs⟩ := theorem_10_2_proof P_pres ⟨C, hC⟩ hW hL₀
  obtain ⟨-, -, -, hab, -, -⟩ := CyclicPerm.isClockwise3_of_ofFn hL₀
  let S' := S_comp.restrictOmega Y hY
  have hR := S_comp.Ω.isRestriction_restrict hY
  have hbarS' : S'.Ω.bar = Y := S_comp.Ω.restrict_bar hY
  have hcw' : S'.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b) := by
    refine hR.isClockwiseSeq_iff.mpr ⟨?_, hΩ ▸ hL₀⟩
    change _ ⊆ S'.Ω.bar
    rw [hbarS']
    rintro v hv
    simp only [mem_ofPred_eq, List.mem_append, List.mem_reverse, List.mem_ofFn'] at hv
    rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hXY (ha i)
    · exact hXY (hb i)
  have hendsQ : ∀ i, S'.IsOmegaPathWithEnds (Q i) (a i) (b i) := fun i =>
    (S_comp.isOmegaPathWithEnds_restrictOmega_iff hY).mpr
      ⟨⟨(hQ i).mono hNG, hab i i, hY (hXY (ha i)), hY (hXY (hb i))⟩, hXY (ha i), hXY (hb i)⟩
  have hinj : Function.Injective Q := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hQd hne) (hQ i).left_mem (e ▸ (hQ i).left_mem)
  have htr : S'.IsTransaction (range Q) := by
    obtain ⟨A, B, hf, hA, hB⟩ := CyclicPerm.exists_isFence_of_ofFn (s := p + 2) hcw'
    refine ⟨A, B, ⟨?_, ?_⟩, hf, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, _, hendsQ i⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      exact hQd fun e => hne (congrArg Q e)
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, hA i, _, hB i, hendsQ i⟩
  have hint : ∀ i, S'.Ω.interval (a i) (b i) ⊆ S_comp.Ω.interval (a i) (b i) ∧
      S'.Ω.interval (b i) (a i) ⊆ S_comp.Ω.interval (b i) (a i) := fun i =>
    ⟨(S_comp.Ω.interval_restrict hY _ _ (hXY (ha i)) (hXY (hb i))).subset.trans inter_subset_left,
      (S_comp.Ω.interval_restrict hY _ _ (hXY (hb i)) (hXY (ha i))).subset.trans inter_subset_left⟩
  have hsep_Q : ∀ i, S'.IsSeparatingOmegaPath (Q i) := by
    intro i
    obtain ⟨G₁, G₂, hsep, hinter, -, h₁, h₂, h₀⟩ := hQs i
    obtain ⟨hs2, hV2⟩ := hcomp.isGraphSeparation_union hsep h₀
    exact S'.isSeparatingOmegaPath_of_separation (hendsQ i) hs2 (hV2.trans hinter)
      ((hint i).1.trans (hΩ ▸ h₁)) ((hint i).2.trans ((hΩ ▸ h₂).trans subset_union_left))
  let t : Fin (p + 4) := ⟨p + 3, by omega⟩
  obtain ⟨G₁, G₂, hsep, hinter, -, h₁, h₂, h₀⟩ := hQs t
  obtain ⟨hs2, hV2⟩ := hcomp.isGraphSeparation_union hsep h₀
  have hs2' : IsGraphSeparation S_comp.G G₁ (subgraphUnion S_comp.G G₂ S₀.G) := hs2
  rcases S'.theorem_5_2_without_no_internal hp2 hp3
    ⟨P₀, (S_comp.isCrookedTransaction_restrictOmega_iff hY).mpr ⟨hP₀, hends⟩, hp⟩ hinj htr hsep_Q
    hendsQ hcw' hs2 (hV2.trans hinter) ((hint t).1.trans (hΩ ▸ h₁))
    ((hint t).2.trans ((hΩ ▸ h₂).trans subset_union_left)) with
    ⟨P₁, P₂, ⟨hdisj, s₁, t₁, s₂, t₂, hP₁, hP₂, hc⟩, hd₁, hd₂⟩ | ⟨P', hcr, hcard', hdis⟩
  · exfalso
    have hlift : ∀ {R : Graph α β} {u w : α}, S'.IsOmegaPathWithEnds R u w →
        Disjoint V(R) V(subgraphUnion S_comp.G G₂ S₀.G) →
        u ≠ w → u ∈ N.Ω.bar → w ∈ N.Ω.bar →
        ({ G := N.G, Ω := N.Ω, finite_V := N.finite_V, finite_E := N.finite_E,
           bar_subset := N.bar_subset } : Society α β).IsOmegaPathWithEnds R u w := by
      intro R u w hR hd hne hu hw
      have hle : R ≤ G₁ := IsGraphSeparation.le_left_of_disjoint hs2' hR.1.le hd
      exact ⟨hR.1.of_le (hle.trans hsep.1), hne, hu, hw⟩
    have hYN : ∀ {v}, v ∈ S'.Ω.bar → v ∈ N.Ω.bar := fun {v} hv => by
      rw [hbarS'] at hv
      exact hΩ ▸ hY hv
    exact not_omegaPathsCross_of_isRural hrural ⟨hdisj, s₁, t₁, s₂, t₂,
      hlift hP₁ hd₁ hP₁.2.1 (hYN hP₁.2.2.1) (hYN hP₁.2.2.2),
      hlift hP₂ hd₂ hP₂.2.1 (hYN hP₂.2.2.1) (hYN hP₂.2.2.2),
      show N.Ω.Crosses s₁ t₁ s₂ t₂ by
        rw [hΩ]
        exact ((S_comp.Ω.crosses_restrict_iff hY).mp hc).2.2.2.2⟩
  · obtain ⟨hcS, hsub⟩ := (S_comp.isCrookedTransaction_restrictOmega_iff hY).mp hcr
    refine ⟨P', hcS, hcard'.ge, fun v hv => ⟨hsub hv, ?_⟩⟩
    rintro rfl
    have hx : v ∈ S_comp.Ω.interval (a 0) (b 0) := hΩ ▸ CyclicPerm.mem_interval_of_around hL
    have hx' : v ∈ S'.Ω.interval (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) := by
      change v ∈ (S_comp.Ω.restrict Y hY).interval _ _
      rw [S_comp.Ω.interval_restrict hY _ _ (hXY (ha _)) (hXY (hb _))]
      exact ⟨hx, hxY⟩
    refine Set.disjoint_left.mp hdis hx' ?_
    rwa [S_comp.transactionEnds_restrictOmega_eq hY hsub]

/-- **Graph Minors IX, (10.3)** (page 64):
"Let $p \ge 2$ with $p \ne 3$. Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge p + 4$, and let $X \subseteq \bar{\Omega}$ be weakly-linked, with $|X| \ge 2p + 8$." -/
theorem theorem_10_3_proof {S_comp S₀ : Society α β} {N : Neighborhood α β} {p : ℕ} {X : Set α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3) (hrural : N.IsRural) (hbreadth : N.HasBreadthGe (p + 4))
    (hX : N.IsWeaklyLinked X) (hcard : 2 * p + 8 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : p ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ X := by
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hXb : X ⊆ S_comp.Ω.bar := hΩ ▸ hX.1
  have hfin : S_comp.Ω.bar.Finite := S_comp.Ω.finite_bar
  have key : ∀ (n : ℕ) (Y : Set α), (Y \ X).ncard = n → X ⊆ Y → Y ⊆ S_comp.Ω.bar →
      ∀ P₁ : Set (Graph α β), S_comp.IsCrookedTransaction P₁ → p ≤ P₁.ncard →
        S_comp.transactionEnds P₁ ⊆ Y →
        ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
          S_comp.transactionEnds P' ⊆ X := by
    intro n
    induction n with
    | zero =>
      intro Y hn _ hY P₁ hP₁ hp₁ hends
      have hYX : Y \ X = ∅ := (ncard_eq_zero (hfin.subset (sdiff_subset.trans hY))).mp hn
      exact ⟨P₁, hP₁, hp₁, hends.trans (sdiff_eq_empty.mp hYX)⟩
    | succ n ih =>
      intro Y hn hXY hY P₁ hP₁ hp₁ hends
      obtain ⟨x, hxY, hxX⟩ : (Y \ X).Nonempty := by
        rw [← Set.ncard_pos (hfin.subset (sdiff_subset.trans hY))]
        omega
      obtain ⟨P₂, hP₂, hp₂, hends₂⟩ := theorem_10_3_step hp2 hp3 hrural hbreadth hX hcard hcomp hXY
        hY hxY hxX hP₁ hp₁ hends
      refine ih (Y \ {x}) ?_ (fun v hv => ⟨hXY hv, fun e => hxX (e ▸ hv)⟩)
        (sdiff_subset.trans hY) P₂ hP₂ hp₂ hends₂
      have hsets : (Y \ {x}) \ X = (Y \ X) \ {x} := by
        ext v
        simp only [mem_sdiff, mem_singleton_iff]
        tauto
      rw [hsets, ncard_sdiff_singleton_of_mem (show x ∈ Y \ X from ⟨hxY, hxX⟩), hn]
      rfl
  exact key _ _ rfl hXb Subset.rfl P₀ hP₀ hp fun v hv => by
    obtain ⟨P, hP, b, hb⟩ := hv
    exact hb.2.2.1

end GraphMinor.GM09
