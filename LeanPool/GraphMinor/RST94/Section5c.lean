/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5b
public import LeanPool.GraphMinor.RST94.Trees
import Mathlib.Tactic.Positivity

/-!
# Section 5 of "Quickly excluding a planar graph": shadows and (5.4)

A shadow (page 341) is defined by connected sets `C_i`, each with one vertex `z_i` of `Z` and one
vertex `z'_i` of `Z'`, such that `C_i \ Z'` and `C_j \ Z'` touch when `z_i` and `z_j` are adjacent.
We ask a little more: that `C_i \ Z'` itself is connected. We write `D i` for `C_i \ Z'`, and `C_i`
is `D i` with `z'_i` attached.

The reason is the last step of (5.5). There a leaf `C_ℓ` must touch the rest at a vertex that can be
joined to `z_ℓ` without using `z'_ℓ`, and the definition on page 341 does not give this: `C_ℓ \ Z'`
may touch the rest only in a part of `C_ℓ` that hangs from `z'_ℓ`. The stronger property holds for
the sets built in (1), and it survives the step of (2), so the proof of (5.4) on pages 341-342 goes
through unchanged.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G : Hypergraph α β}

/-- A shadow of a residual nodule (page 341), with `D i` for `C_i \ Z'`. -/
structure Shadow (G G' : Hypergraph α β) (z z' : ι → α) (S : SimpleGraph ι) (D : ι
  → Set α) : Prop where
  conn : ∀ i, Conn G (D i)
  mem : ∀ i, z i ∈ D i
  attach : ∀ i, ∃ x ∈ D i, G.skeleton.Adj x (z' i)
  off : ∀ i, ∀ x ∈ D i, x ∉ G'.vertexSet
  disj : Pairwise fun i j => Disjoint (D i) (D j)
  touch : ∀ i j, S.Adj i j → ∃ x ∈ D i, ∃ y ∈ D j, G.skeleton.Adj x y

/-- A connected set is the disjoint union of connected sets around given disjoint connected seeds.
These are the sets `C_i` with maximal union in (1) of (5.4). -/
theorem exists_partition [Nonempty ι] {J : Set α} (hJf : J.Finite) (hJ : Conn G J) {B : ι → Set α}
  (hB : ∀ i, Conn G (B i)) (hBJ : ∀ i, B i ⊆ J) (hd : Pairwise fun i j => Disjoint (B i) (B j)) :
    ∃ D : ι → Set α, (∀ i, Conn G (D i)) ∧ (∀ i, B i ⊆ D i) ∧ (∀ i, D i ⊆ J) ∧ (Pairwise fun i j
      => Disjoint (D i) (D j)) ∧ ∀ x ∈ J, ∃ i, x ∈ D i := by
  classical
  let P : (ι → Set α) → Prop := fun D => (∀ i, Conn G (D i)) ∧ (∀ i, B i ⊆ D i) ∧ (∀ i, D i ⊆ J)
    ∧ Pairwise fun i j => Disjoint (D i) (D j)
  obtain ⟨D, hD, hmax⟩ := exists_max_measure (P := P) (fun D => (⋃ i, D i).ncard) J.ncard (fun D hD
    => ncard_le_ncard (iUnion_subset hD.2.2.1) hJf)
    ⟨B, hB, fun _ => subset_rfl, hBJ, hd⟩
  refine ⟨D, hD.1, hD.2.1, hD.2.2.1, hD.2.2.2, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxJ, hx⟩ := hcon
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨y, hy⟩ := (hD.1 i₀).1
  obtain ⟨w, hw⟩ := hJ.2 y (hD.2.2.1 i₀ hy) x hxJ
  have hyx : y ≠ x := fun e => hx i₀ (e ▸ hy)
  have hxL : x ∈ {v | v ∈ J ∧ ∀ i, v ∉ D i} := ⟨hxJ, hx⟩
  obtain ⟨t, y', q, h, w', hy', hq, hwe⟩ := exists_run (L := {v | v ∈ J ∧ ∀ i, v ∉ D i}) w hxL hyx
  have htq : t ∈ w.support := by
    rw [hwe]
    simp [SimpleGraph.Walk.mem_support_append_iff]
  have ht : ∃ i, t ∈ D i := by
    by_cases hts : t = y
    · exact ⟨i₀, hts ▸ hy⟩
    · have := hq t q.end_mem_support hts
      by_contra hno
      push Not at hno
      exact this ⟨hw t htq, hno⟩
  obtain ⟨i, hi⟩ := ht
  have hc₁ : Conn G (D i ∪ {y'}) := (hD.1 i).union_adj conn_singleton hi rfl h
  let D' : ι → Set α := Function.update D i (D i ∪ {y'})
  have hup : ∀ j, j ≠ i → D' j = D j := fun j hj => Function.update_of_ne hj _ _
  have hupi : D' i = D i ∪ {y'} := Function.update_self _ _ _
  have hP : P D' := by
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j l hjl => ?_⟩
    · by_cases hj : j = i
      · rw [hj, hupi]
        exact hc₁
      · rw [hup j hj]
        exact hD.1 j
    · by_cases hj : j = i
      · rw [hj, hupi]
        exact (hD.2.1 i).trans subset_union_left
      · rw [hup j hj]
        exact hD.2.1 j
    · by_cases hj : j = i
      · rw [hj, hupi]
        exact union_subset (hD.2.2.1 i) (singleton_subset_iff.2 hy'.1)
      · rw [hup j hj]
        exact hD.2.2.1 j
    · change Disjoint (D' j) (D' l)
      have hs : ∀ m, Disjoint ({y'} : Set α) (D m) := fun m => disjoint_singleton_left.2 (hy'.2 m)
      by_cases hj : j = i
      · subst hj
        rw [hupi, hup l hjl.symm]
        exact disjoint_union_left.2 ⟨hD.2.2.2 hjl, hs l⟩
      · by_cases hl : l = i
        · subst hl
          rw [hupi, hup j hj]
          exact (disjoint_union_left.2 ⟨hD.2.2.2 hjl.symm, hs j⟩).symm
        · rw [hup j hj, hup l hl]
          exact hD.2.2.2 hjl
  have hlt := hmax D' hP
  have hsub : insert y' (⋃ j, D j) ⊆ ⋃ j, D' j := by
    rintro v (rfl | hv)
    · exact mem_iUnion.2 ⟨i, by rw [hupi]; exact Or.inr rfl⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hv
      by_cases hji : j = i
      · exact mem_iUnion.2 ⟨i, by rw [hupi]; exact Or.inl (hji ▸ hj)⟩
      · exact mem_iUnion.2 ⟨j, by rw [hup j hji]; exact hj⟩
  have hfin : (⋃ j, D' j).Finite := hJf.subset (iUnion_subset hP.2.2.1)
  have h₃ := ncard_le_ncard hsub hfin
  rw [ncard_insert_of_notMem (fun h' => hy'.2 _ (mem_iUnion.1 h').choose_spec)
    (hfin.subset fun v hv => hsub (Or.inr hv))] at h₃
  omega

/-- The graph `S₀` of (1) in (5.4) is connected. -/
theorem touch_connected [Nonempty ι] {J : Set α} (hJ : Conn G J) {D : ι → Set α}
  (hD : ∀ i, D i ⊆ J) (hne : ∀ i, (D i).Nonempty) (hcov : ∀ x ∈ J, ∃ i, x ∈ D i)
    (hd : Pairwise fun i j => Disjoint (D i) (D j)) :
    (SimpleGraph.fromRel fun i j => ∃ x ∈ D i, ∃ y ∈ D j, G.skeleton.Adj x y).Connected := by
  have key : ∀ {x y : α} (w : G.skeleton.Walk x y) (_ : ∀ v ∈ w.support, v ∈ J) (i j : ι), x ∈ D i
    → y ∈ D j →
      (SimpleGraph.fromRel fun i j => ∃ x ∈ D i, ∃ y ∈ D j, G.skeleton.Adj x y).Reachable i j
        := fun {x y} w => by
    induction w with
    | nil =>
      intro _ i j hx hy
      by_cases hij : i = j
      · exact hij ▸ SimpleGraph.Reachable.refl _
      · exact absurd hy (disjoint_left.1 (hd hij) hx)
    | @cons x y z h q ih =>
      intro hw i j hx hz
      obtain ⟨k, hk⟩ := hcov y (hw y (by simp))
      have h₁ := ih (fun v hv => hw v (by simp [hv])) k j hk hz
      by_cases hik : i = k
      · exact hik ▸ h₁
      · refine SimpleGraph.Adj.reachable ?_ |>.trans h₁
        exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hik, Or.inl ⟨x, hx, y, hk, h⟩⟩
  refine ⟨fun i j => ?_⟩
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨y, hy⟩ := hne j
  obtain ⟨w, hw⟩ := hJ.2 x (hD i hx) y (hD j hy)
  exact key w hw i j hx hy

/-- Statement (1) in the proof of (5.4) (page 341). -/
theorem shadow_base [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {k : ℕ} (hn : 2 ≤ Fintype.card ι) (hk : Fintype.card ι
    ≤ 2 * k)
    (hθ : k * 20 ^ Fintype.card ι ≤ θ) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α)
      (S : SimpleGraph ι) (D : ι → Set α),
      Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧ S.IsTree ∧ Shadow G G' z z' S D := by
  classical
  obtain ⟨G', T', θ', z', hR, hb, C, hC, hzC, hCoff⟩ := theorem_4_3 hG hN hn hk hθ
  obtain ⟨P, hP₁, hP₂, hP₃⟩ := hR.link
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hne : ∀ i, z i ≠ z' i := fun i e => hR.avoid i (e ▸ hR.nodule.free.1 (mem_range_self i))
  have hlast := fun i => exists_butlast (P i) (hP₁ i) (hne i)
  choose d q hd hq using hlast
  let B : ι → Set α := fun i => {x | x ∈ (q i).support}
  have hBc : ∀ i, Conn G (B i) := fun i => conn_support (q i)
  have hBz : ∀ i, z i ∈ B i := fun i => (q i).start_mem_support
  have hBoff : ∀ i, ∀ x ∈ B i, x ∉ G'.vertexSet := fun i x hx hxG => ((hq i x).1 hx).2 (hP₂ i x
    ((hq i x).1 hx).1 hxG)
  let J : Set α := C ∪ ⋃ i, B i
  have hJc : Conn G J := by
    have key : ∀ s : Finset ι, Conn G (C ∪ ⋃ i ∈ s, B i) := fun s => by
      induction s using Finset.induction_on with
      | empty => simpa using hC
      | @insert a s _ ih =>
        have h₁ := ih.union (hBc a) ⟨z a, Or.inl (hzC (mem_range_self a)), hBz a⟩
        have heq : C ∪ ⋃ i ∈ insert a s, B i = (C ∪ ⋃ i ∈ s, B i) ∪ B a := by
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
    have := key Finset.univ
    simpa [J] using this
  have hJV : J ⊆ G.vertexSet := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro x hx
    obtain ⟨w, -⟩ := hJc.2 (z i) (Or.inl (hzC (mem_range_self i))) x hx
    exact support_mem w (hN.free.1 (mem_range_self i)) w.end_mem_support
  have hdB : Pairwise fun i j => Disjoint (B i) (B j) := fun i j hij => disjoint_left.2 fun x hx
    hx' =>
    disjoint_left.1 (hP₃ hij) ((hq i x).1 hx).1 ((hq j x).1 hx').1
  obtain ⟨D, hD₁, hD₂, hD₃, hD₄, hD₅⟩ := exists_partition (G.vertexSet_finite.subset hJV) hJc hBc
    (fun i => subset_iUnion B i |>.trans subset_union_right) hdB
  have hDne : ∀ i, (D i).Nonempty := fun i => ⟨z i, hD₂ i (hBz i)⟩
  have hconn := touch_connected hJc hD₃ hDne hD₅ hD₄
  obtain ⟨S, hS, hSt⟩ := hconn.exists_isTree_le
  refine ⟨G', T', θ', z', S, D, hR, hb, hSt, hD₁, fun i => hD₂ i (hBz i), fun i => ⟨d i,
    hD₂ i (q i).end_mem_support, hd i⟩, fun i x hx => ?_, hD₄, fun i j hij => ?_⟩
  · rcases hD₃ i hx with h | h
    · exact hCoff x h
    · obtain ⟨l, hl⟩ := mem_iUnion.1 h
      exact hBoff l x hl
  · have := (SimpleGraph.fromRel_adj _ _ _).1 (hS hij)
    rcases this.2 with h | h
    · exact h
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact ⟨y, hy, x, hx, hxy.symm⟩

/-- The step of (2) in the proof of (5.4) (page 342): after (5.3), the sets `C_i` take in the paths
`P'_i`, and one of them takes in the jump. -/
theorem Shadow.step {G' G₂ : Hypergraph α β} {z z' z₂ : ι → α} {S S' : SimpleGraph ι} {D : ι
  → Set α} (hs : Shadow G G' z z' S D) (hle : G' ≤ G) (hle₂ : G₂ ≤ G')
    (hz' : range z' ⊆ G'.vertexSet)
    (hz₂ : range z₂ ⊆ G₂.vertexSet) (hav : ∀ c, z' c ∉ G₂.vertexSet) {P : ∀ c, G'.skeleton.Walk
      (z' c) (z₂ c)} (hL : IsLinkage G' G₂ z' z₂ P) {a b : ι} {Y : Set α}
    (hJ : JumpData G' (fun l => {t | t ∈ (P l).support}) Y a b) (hY : ∀ t ∈ Y, t ∉ G₂.vertexSet)
      (hS' : ∀ x y, S'.Adj x y → S.Adj x y ∨ s(x, y) = s(a, b)) :
    ∃ D', Shadow G G₂ z z₂ S' D' := by
  classical
  obtain ⟨hP₁, hP₂, hP₃⟩ := hL
  obtain ⟨x, t, y, q, hty, hxa, hyb, hql, hqY, hyY⟩ := hJ
  have hne : ∀ i, z' i ≠ z₂ i := fun i e => hav i (e ▸ hz₂ (mem_range_self i))
  have hlast := fun i => exists_butlast (P i) (hP₁ i) (hne i)
  choose d r hd hr using hlast
  let B : ι → Set α := fun i => {v | v ∈ (r i).support}
  let E : ι → Set α := fun i => {v | i = a ∧ v ∈ q.support}
  let D' : ι → Set α := fun i => D i ∪ B i ∪ E i
  have hpG : ∀ c v, v ∈ (P c).support → v ∈ G'.vertexSet := fun c v hv => support_mem (P c) (hz'
    (mem_range_self c)) hv
  have hxG : x ∈ G'.vertexSet := hpG a x hxa
  have hqG : ∀ v ∈ q.support, v ∈ G'.vertexSet := fun v hv => support_mem q hxG hv
  have hBoff : ∀ i, ∀ v ∈ B i, v ∉ G₂.vertexSet := fun i v hv hvG => ((hr i v).1 hv).2 (hP₂ i v
    ((hr i v).1 hv).1 hvG)
  have hBG : ∀ i, ∀ v ∈ B i, v ∈ G'.vertexSet := fun i v hv => hpG i v ((hr i v).1 hv).1
  have hxB : x ∈ B a := (hr a x).2 ⟨hxa, fun e => hY x (hqY x q.start_mem_support) (e ▸ hz₂
    (mem_range_self a))⟩
  have hyB : y ∈ B b := (hr b y).2 ⟨hyb, fun e => hY y hyY (e ▸ hz₂ (mem_range_self b))⟩
  have hc₁ : ∀ i, Conn G (D i ∪ B i) := fun i => by
    obtain ⟨u, hu, hadj⟩ := hs.attach i
    exact (hs.conn i).union_adj ((conn_support (r i)).mono hle) hu (r i).start_mem_support hadj
  have hconn : ∀ i, Conn G (D' i) := fun i => by
    by_cases hi : i = a
    · subst hi
      have : D' i = D i ∪ B i ∪ {v | v ∈ q.support} := by
        ext v
        simp [D', E]
      rw [this]
      exact (hc₁ i).union ((conn_support q).mono hle) ⟨x, Or.inr hxB, q.start_mem_support⟩
    · have : D' i = D i ∪ B i := by
        ext v
        simp [D', E, hi]
      rw [this]
      exact hc₁ i
  have hdoff : ∀ i, ∀ v ∈ D i, v ∉ G'.vertexSet := hs.off
  refine ⟨D', hconn, fun i => Or.inl (Or.inl (hs.mem i)), fun i => ⟨d i, Or.inl (Or.inr
    (r i).end_mem_support), skeleton_mono hle (hd i)⟩, ?_, fun i j hij
      => disjoint_left.2 fun v hv hv' => ?_, fun i j hij => ?_⟩
  · rintro i v ((hv | hv) | ⟨-, hv⟩) hvG
    · exact hdoff i v hv (hle₂.vertexSet_subset hvG)
    · exact hBoff i v hv hvG
    · exact hY v (hqY v hv) hvG
  · have hlab : ∀ i, v ∈ D' i → v ∈ G'.vertexSet → v ∈ (P i).support ∨ (i = a ∧ v ≠ x ∧ ∀ l, v ∉
    (P l).support) := by
      rintro i ((h | h) | ⟨h₁, h⟩) hvG
      · exact absurd hvG (hdoff i v h)
      · exact Or.inl ((hr i v).1 h).1
      · by_cases he : v = x
        · exact Or.inl (he ▸ h₁ ▸ hxa)
        · exact Or.inr ⟨h₁, he, hql v h he⟩
    have hDcase : ∀ i, v ∈ D' i → v ∉ G'.vertexSet → v ∈ D i := by
      rintro i ((h | h) | ⟨-, h⟩) hvG
      · exact h
      · exact absurd (hBG i v h) hvG
      · exact absurd (hqG v h) hvG
    by_cases hvG : v ∈ G'.vertexSet
    · rcases hlab i hv hvG with h₁ | ⟨rfl, -, h₂⟩ <;> rcases hlab j hv' hvG with h₃ | ⟨h₃, -, h₄⟩
      · exact disjoint_left.1 (hP₃ hij) h₁ h₃
      · exact h₄ _ h₁
      · exact h₂ _ h₃
      · exact hij h₃.symm
    · exact disjoint_left.1 (hs.disj hij) (hDcase i hv hvG) (hDcase j hv' hvG)
  · have hT : t ∈ D' a := Or.inr ⟨rfl, q.end_mem_support⟩
    have hYb : y ∈ D' b := Or.inl (Or.inr hyB)
    rcases hS' i j hij with h | h
    · obtain ⟨u, hu, w, hw, huw⟩ := hs.touch i j h
      exact ⟨u, Or.inl (Or.inl hu), w, Or.inl (Or.inl hw), huw⟩
    · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨t, hT, y, hYb, skeleton_mono hle hty⟩
      · exact ⟨y, hYb, t, hT, (skeleton_mono hle hty).symm⟩

/-- Statement (2) in the proof of (5.4) (page 341), by induction on `r`. -/
theorem exists_shadow [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {g m k : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m)
    (hcard : Fintype.card ι = (2 * g + 1) * (2 * m - 5) + 2) (hk : Fintype.card ι ≤ 2 * k)
      (hθ : k * 20 ^ (2 * g * (m - 2) + Fintype.card ι) ≤ θ) (hno : ¬ HasGrid G T θ g) (d : ℕ)
        (hd : d + 2 ≤ m) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α)
      (S : SimpleGraph ι) (D : ι → Set α),
      Residual G T θ z G' T' θ' z' ∧ k * 20 ^ (2 * g * (m - (d + 2))) ≤ θ' ∧ S.IsTree
        ∧ Shadow G G' z z' S D ∧ d + 2 ≤ (leaves S).ncard := by
  have h2 : 2 ≤ Fintype.card ι := by
    have : 1 ≤ (2 * g + 1) * (2 * m - 5) := Nat.mul_pos (by omega) (by omega)
    omega
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 h2
  induction d with
  | zero =>
    have hk₂ : Fintype.card ι ≤ 2 * (k * 20 ^ (2 * g * (m - 2))) := hk.trans (Nat.mul_le_mul_left 2
      (Nat.le_mul_of_pos_right k (by positivity)))
    obtain ⟨G', T', θ', z', S, D, hR, hb, hS, hs⟩ := shadow_base hG hN h2 hk₂
      (by rw [Nat.mul_assoc, ← pow_add]; exact hθ)
    refine ⟨G', T', θ', z', S, D, hR, hb, hS, hs, ?_⟩
    have h₁ := card_not_two_add_two hS
    have h₂ : (leaves S).ncard ≤ {v | deg S v ≠ 2}.ncard := ncard_le_ncard (fun v (hv : deg S v
      = 1) => by
      change deg S v ≠ 2
      exact fun h => (by decide : (1 : ℕ∞) ≠ 2) (hv.symm.trans h)) (toFinite _)
    omega
  | succ d ih =>
    obtain ⟨G', T', θ', z', S, D, hR, hb, hS, hs, hL⟩ := ih (by omega)
    have hexp : 2 * g * (m - (d + 2)) = 2 * g * (m - (d + 1 + 2)) + 2 * g := by
      obtain ⟨u, hu⟩ : ∃ u, m - (d + 2) = u + 1 := ⟨m - (d + 2) - 1, by omega⟩
      rw [hu, show m - (d + 1 + 2) = u by omega, Nat.mul_succ]
    by_cases hL₂ : d + 1 + 2 ≤ (leaves S).ncard
    · refine ⟨G', T', θ', z', S, D, hR, le_trans (Nat.mul_le_mul_left k ?_) hb, hS, hs, hL₂⟩
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hLe : (leaves S).ncard = d + 2 := by omega
    have hrun : (2 * g + 1) * (2 * (leaves S).ncard - 3) + 1 < Fintype.card ι := by
      rw [hcard, hLe]
      have : (2 * g + 1) * (2 * (d + 2) - 3) ≤ (2 * g + 1) * (2 * m - 5) := Nat.mul_le_mul_left _
        (by omega)
      omega
    obtain ⟨c, hc₁, hc₂, hc₃⟩ := exists_long_run hS hrun
    set K := k * 20 ^ (2 * g * (m - (d + 1 + 2))) with hK
    have hk₂ : Fintype.card ι ≤ 2 * K := hk.trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right k
      (by positivity)))
    have hb₂ : K * 20 ^ (2 * g) ≤ θ' := by
      rw [hK, Nat.mul_assoc, ← pow_add, ← hexp]
      exact hb
    have hno' : ¬ HasGrid G' T' θ' g := fun h => hno (h.of_conformal hR.le hN.tangle
      hR.nodule.tangle hR.conformal)
    obtain ⟨G₂, T₂, θ₂, z₂, P, p, b, Y, hR₂, hk₃, hL₂', hp₁, hp₂, hb₁, hb₂', hb₃, hJ, hYoff⟩
      := theorem_5_3 (IsGraph.of_le hG hR.le) hR.nodule hg (c := fun a => c (a + 1))
      (fun x y hx hy he => by
        have := hc₁ _ _ (by omega) (by omega) he
        omega) hk₂ hb₂ hno'
    simp only at hb₁ hb₂' hb₃ hJ
    have hsucc : p - 1 + 1 = p := by omega
    rw [hsucc] at hb₁
    have hne : ∀ x y, x ≤ 2 * g → y ≤ 2 * g → x ≠ y → c x ≠ c y := fun x y hx hy h e => h
      (hc₁ x y hx hy e)
    have hadj₀ := hc₂ (p - 1) (by omega)
    rw [hsucc] at hadj₀
    obtain ⟨S', hS', hS₂, hL₃⟩ := exists_more_leaves (t := b) hS hadj₀ (hc₂ p (by omega)) (hc₂
      (p + 1) (by omega)) (hc₂ (p + 2) (by omega)) (hc₃ _ (by omega)) (hc₃ _ (by omega)) (hc₃ _
        (by omega)) (hc₃ _ (by omega)) (hc₃ _ (by omega))
      (hne _ _ (by omega) (by omega) (by omega)) (hne _ _ (by omega) (by omega) (by omega))
        (hne _ _ (by omega) (by omega) (by omega)) hb₁ hb₂' hb₃
    obtain ⟨D', hs'⟩ := hs.step hR.le hR₂.le hR.nodule.free.1 hR₂.nodule.free.1 hR₂.avoid hL₂' hJ
      hYoff hS₂
    refine ⟨G₂, T₂, θ₂, z₂, S', D', hR.trans hN.tangle hR₂, hk₃, hS', hs', ?_⟩
    omega

/-- **(5.4)** (page 341). -/
theorem theorem_5_4 [Fintype ι] (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ :
  ℕ} {z : ι → α} (hN : Nodule G T θ z) {g m k : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m)
    (hcard : Fintype.card ι = (2 * g + 1) * (2 * m - 5) + 2) (hk : Fintype.card ι ≤ 2 * k)
      (hθ : k * 20 ^ (2 * g * (m - 2) + Fintype.card ι) ≤ θ) (hno : ¬ HasGrid G T θ g) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι → α)
      (S : SimpleGraph ι) (D : ι → Set α),
      Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧ S.IsTree ∧ Shadow G G' z z' S D ∧ m ≤
        (leaves S).ncard := by
  obtain ⟨G', T', θ', z', S, D, hR, hb, hS, hs, hL⟩ := exists_shadow hG hN hg hm hcard hk hθ hno
    (m - 2) (by omega)
  rw [show m - (m - 2 + 2) = 0 by omega, Nat.mul_zero, pow_zero, Nat.mul_one] at hb
  exact ⟨G', T', θ', z', S, D, hR, hb, hS, hs, by omega⟩

end GraphMinor.RST94
