/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d

/-!
# Graph Minors IX, Section 3 (Part 1): Path Ends, Interval Calculus, (3.1), and (3.4)

This file establishes:
- uniqueness of endpoints of paths (`IsGraphPathWithEnds.ends_eq`) and characterization of
  `pathEnds` and `pathInternalVerts`,
- interval characterizations of `FirstHitIn`, `IsClockwise4`, `Crosses`, and `IsFence`,
- Graph Minors IX, (3.1) (`theorem_3_1`, page 47): any crooked transaction has at most one overpass,
- Graph Minors IX, (3.4) (`theorem_3_4`, page 48): any crooked transaction of cardinality `≥ p`
  (with `p ≥ 2, p ≠ 3`) contains a crooked transaction of cardinality `p`.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## Uniqueness of endpoints of a path -/

theorem unique_inc_first {G : Graph α β} {a b : α}
    {W : GraphWalk G a b} (hW : W.IsSimple) {e₁ e₂ : β}
    (he₁ : e₁ ∈ W.edges) (he₂ : e₂ ∈ W.edges)
    (hinc₁ : G.Inc e₁ a) (hinc₂ : G.Inc e₂ a) : e₁ = e₂ := by
  cases W with
  | nil _ =>
    simp [GraphWalk.edges] at he₁
  | @cons _ y _ e hxy W' =>
    have hnodup : (a :: W'.support).Nodup := hW
    have hx_not_in : a ∉ W'.support := (List.nodup_cons.mp hnodup).1
    have hnot_tail : ∀ e' ∈ W'.edges, ¬ G.Inc e' a := by
      intro e' he' ⟨w, hlink⟩
      exact hx_not_in (W'.left_mem_support_of_mem_edges he' hlink)
    simp only [GraphWalk.edges, List.mem_cons] at he₁ he₂
    have h₁ : e₁ = e := he₁.resolve_right fun h => (hnot_tail e₁ h hinc₁).elim
    have h₂ : e₂ = e := he₂.resolve_right fun h => (hnot_tail e₂ h hinc₂).elim
    exact h₁.trans h₂.symm

theorem IsGraphPathWithEnds.exists_inc_left_of_ne {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ e ∈ E(P), P.Inc e a := by
  rcases hP with ⟨_, W, _, _, hEP⟩
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons x y z e hxy W' =>
    refine ⟨e, ?_, y, hxy⟩
    rw [hEP, mem_ofPred_eq]
    exact List.mem_cons_self

theorem IsGraphPathWithEnds.left_eq_or_right_eq {G P : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (h₁ : IsGraphPathWithEnds G P a₁ b₁) (h₂ : IsGraphPathWithEnds G P a₂ b₂) :
    a₂ = a₁ ∨ a₂ = b₁ := by
  by_contra! hne
  rcases hne with ⟨hne₁, hne₂⟩
  obtain ⟨Q₁, Q₂, hQ₁P, hQ₂P, hQ₁, hQ₂, _, _, hdisjE⟩ := h₁.exists_split_at h₂.left_mem
  obtain ⟨e₁, he₁, hinc₁⟩ := hQ₁.symm.exists_inc_left_of_ne hne₁
  obtain ⟨e₂, he₂, hinc₂⟩ := hQ₂.exists_inc_left_of_ne hne₂
  have he₁P : e₁ ∈ E(P) := hQ₁P.edgeSet_mono he₁
  have he₂P : e₂ ∈ E(P) := hQ₂P.edgeSet_mono he₂
  have hinc₁P : P.Inc e₁ a₂ := hinc₁.mono hQ₁P
  have hinc₂P : P.Inc e₂ a₂ := hinc₂.mono hQ₂P
  rcases h₂ with ⟨_, W₂, hW₂, _, hEP₂⟩
  rw [hEP₂, mem_ofPred_eq] at he₁P he₂P
  have heq : e₁ = e₂ := unique_inc_first hW₂ he₁P he₂P hinc₁P hinc₂P
  exact disjoint_left.mp hdisjE he₁ (heq ▸ he₂)

theorem IsGraphPathWithEnds.ends_eq {G P : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (h₁ : IsGraphPathWithEnds G P a₁ b₁) (h₂ : IsGraphPathWithEnds G P a₂ b₂) :
    (a₂ = a₁ ∧ b₂ = b₁) ∨ (a₂ = b₁ ∧ b₂ = a₁) := by
  have ha₂ := h₁.left_eq_or_right_eq h₂
  have hb₂ := h₁.left_eq_or_right_eq h₂.symm
  have ha₁ := h₂.left_eq_or_right_eq h₁
  have hb₁ := h₂.left_eq_or_right_eq h₁.symm
  rcases ha₂ with rfl | rfl
  · rcases hb₂ with rfl | rfl
    · rcases hb₁ with h | h
      · exact Or.inl ⟨rfl, h.symm⟩
      · exact Or.inl ⟨rfl, h.symm⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb₂ with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · rcases ha₁ with h | h
      · exact Or.inr ⟨rfl, h.symm⟩
      · exact Or.inr ⟨rfl, h.symm⟩

theorem IsGraphPathWithEnds.pair_ends_eq {G P : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (h₁ : IsGraphPathWithEnds G P a₁ b₁) (h₂ : IsGraphPathWithEnds G P a₂ b₂) :
    ({a₁, b₁} : Set α) = {a₂, b₂} := by
  rcases h₁.ends_eq h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pair_comm _ _

theorem IsGraphPathWithEnds.pathEnds_eq {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : pathEnds G P = {a, b} := by
  ext v
  simp only [pathEnds, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨b', hv⟩
    exact hP.left_eq_or_right_eq hv
  · rintro (rfl | rfl)
    · exact ⟨b, hP⟩
    · exact ⟨a, hP.symm⟩

theorem IsGraphPathWithEnds.pathInternalVerts_eq {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : pathInternalVerts G P = V(P) \ {a, b} := by
  rw [pathInternalVerts, hP.pathEnds_eq]

namespace Society

theorem IsOmegaPathWithEnds.symm (S : Society α β) {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b) : S.IsOmegaPathWithEnds P b a :=
  ⟨hP.1.symm, hP.2.1.symm, hP.2.2.2, hP.2.2.1⟩

theorem IsOmegaPathWithEnds.ends_eq (S : Society α β) {P : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (h₁ : S.IsOmegaPathWithEnds P a₁ b₁) (h₂ : S.IsOmegaPathWithEnds P a₂ b₂) :
    (a₂ = a₁ ∧ b₂ = b₁) ∨ (a₂ = b₁ ∧ b₂ = a₁) :=
  h₁.1.ends_eq h₂.1

theorem IsOmegaPathWithEnds.ends_eq_of_mem_disjoint (S : Society α β)
    {P : Graph α β} {A B : Set α} (hAB : Disjoint A B)
    {a₁ b₁ a₂ b₂ : α} (_ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (ha₂ : a₂ ∈ A)
    (h₁ : S.IsOmegaPathWithEnds P a₁ b₁) (h₂ : S.IsOmegaPathWithEnds P a₂ b₂) :
    a₂ = a₁ ∧ b₂ = b₁ := by
  rcases h₁.ends_eq S h₂ with h | ⟨rfl, _⟩
  · exact h
  · exact (disjoint_left.mp hAB ha₂ hb₁).elim

theorem IsOmegaPathWithEnds.mem_transactionEnds_left (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {a b : α}
    (hP_in : P ∈ P_set) (hP : S.IsOmegaPathWithEnds P a b) :
    a ∈ S.transactionEnds P_set :=
  ⟨P, hP_in, b, hP⟩

theorem IsOmegaPathWithEnds.mem_transactionEnds_right (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {a b : α}
    (hP_in : P ∈ P_set) (hP : S.IsOmegaPathWithEnds P a b) :
    b ∈ S.transactionEnds P_set :=
  ⟨P, hP_in, a, hP.symm S⟩

theorem IsOmegaPathWithEnds.isPeripheralIn_iff (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β} {a b : α}
    (hP_in : P ∈ P_set) (hP : S.IsOmegaPathWithEnds P a b) :
    S.IsPeripheralIn P_set P ↔
      Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) ∨
        Disjoint (S.Ω.interval b a) (S.transactionEnds P_set) := by
  constructor
  · rintro ⟨_, a', b', hP', hdisj⟩
    rcases hP.ends_eq S hP' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj
    · exact hdisj.symm
  · intro hdisj
    exact ⟨hP_in, a, b, hP, hdisj⟩

theorem transactionEnds_subset_bar (S : Society α β) (P_set : Set (Graph α β)) :
    S.transactionEnds P_set ⊆ S.Ω.bar := by
  rintro v ⟨P, _, b, hP⟩
  exact hP.2.2.1

theorem transactionEnds_insert (S : Society α β) (P_set : Set (Graph α β))
    {P : Graph α β} {a b : α} (hP : S.IsOmegaPathWithEnds P a b) :
    S.transactionEnds (P_set ∪ {P}) = S.transactionEnds P_set ∪ {a, b} := by
  ext v
  simp only [transactionEnds, mem_union, mem_singleton_iff, mem_ofPred_eq, mem_insert_iff]
  constructor
  · rintro ⟨Q, hQ | rfl, c, hQc⟩
    · exact Or.inl ⟨Q, hQ, c, hQc⟩
    · exact Or.inr (hP.1.left_eq_or_right_eq hQc.1)
  · rintro (⟨Q, hQ, c, hQc⟩ | rfl | rfl)
    · exact ⟨Q, Or.inl hQ, c, hQc⟩
    · exact ⟨P, Or.inr rfl, b, hP⟩
    · exact ⟨P, Or.inr rfl, a, hP.symm S⟩

theorem transactionEnds_diff_singleton (S : Society α β) {P_set : Set (Graph α β)}
    (hdisj : S.IsDisjointOmegaPathSet P_set) {P : Graph α β} {a b : α}
    (hP_in : P ∈ P_set) (hP : S.IsOmegaPathWithEnds P a b) :
    S.transactionEnds (P_set \ {P}) = S.transactionEnds P_set \ {a, b} := by
  ext v
  simp only [transactionEnds, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, mem_insert_iff, not_or]
  constructor
  · rintro ⟨Q, ⟨hQ_in, hQP⟩, c, hQc⟩
    have hvQ : v ∈ V(Q) := hQc.1.left_mem
    have hdisj_QP : Disjoint V(Q) V(P) := hdisj.2 hQ_in hP_in hQP
    refine ⟨⟨Q, hQ_in, c, hQc⟩, ?_, ?_⟩
    · intro rfl; exact disjoint_left.mp hdisj_QP hvQ hP.1.left_mem
    · intro rfl; exact disjoint_left.mp hdisj_QP hvQ hP.1.right_mem
  · rintro ⟨⟨Q, hQ_in, c, hQc⟩, hva, hvb⟩
    refine ⟨Q, ⟨hQ_in, ?_⟩, c, hQc⟩
    rintro rfl
    rcases hP.1.left_eq_or_right_eq hQc.1 with rfl | rfl
    · exact hva rfl
    · exact hvb rfl

end Society

/-! ## Interval characterizations of `IsClockwise3`, `FirstHitIn`, `IsClockwise4`, `Crosses`, and
`IsFence` -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

theorem isClockwise3_iff_firstHitIn {v₁ v₂ v₃ : α}
    (hv₁ : v₁ ∈ Ω.bar) (hv₂ : v₂ ∈ Ω.bar) (hv₃ : v₃ ∈ Ω.bar)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) :
    Ω.IsClockwise3 v₁ v₂ v₃ ↔ Ω.FirstHitIn {v₁, v₂, v₃} v₁ v₂ := by
  constructor
  · intro h
    exact (Ω.isClockwise3_iff.mp h).2.2.2.2.2.2.1
  · intro hhit
    rcases Ω.isClockwise3_trichotomy hv₁ hv₂ hv₃ h12 h13 h23 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · have hhit' := (Ω.isClockwise3_iff.mp h).2.2.2.2.2.2.1
      have hset : ({v₁, v₃, v₂} : Set α) = {v₁, v₂, v₃} := by ext x; simp [or_comm]
      rw [hset] at hhit'
      exact (h23 (hhit.unique hhit')).elim

theorem mem_interval_iff_firstHitIn {v₁ v₂ v : α}
    (hv₁ : v₁ ∈ Ω.bar) (hv₂ : v₂ ∈ Ω.bar) (hv : v ∈ Ω.bar)
    (h12 : v₁ ≠ v₂) (hv1 : v ≠ v₁) (hv2 : v ≠ v₂) :
    v ∈ Ω.interval v₁ v₂ ↔ Ω.FirstHitIn {v₁, v, v₂} v₁ v := by
  rw [interval, mem_sep_iff, Ω.isClockwise3_iff_firstHitIn hv₁ hv hv₂ hv1.symm h12 hv2]
  exact ⟨fun h => h.2, fun h => ⟨⟨hv, by simp [hv1, hv2]⟩, h⟩⟩

theorem firstHitIn_iff_disjoint_interval {W : Set α} (hW : W ⊆ Ω.bar)
    {x y : α} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) :
    Ω.FirstHitIn W x y ↔ Disjoint (Ω.interval x y) W := by
  have hx_bar : x ∈ Ω.bar := hW hx
  have hy_bar : y ∈ Ω.bar := hW hy
  constructor
  · rintro ⟨k, hk1, rfl, _, hmin⟩
    rw [disjoint_left]
    intro z hz hzW
    have hzx : z ≠ x := fun h => hz.1.2 (by simp [h])
    have hzy : z ≠ (Ω.toFun^[k]) x := fun h => hz.1.2 (by simp [h])
    have hhit_z : Ω.FirstHitIn {x, z, (Ω.toFun^[k]) x} x z :=
      (Ω.mem_interval_iff_firstHitIn hx_bar hy_bar hz.1.1 hxy hzx hzy).mp hz
    rcases hhit_z with ⟨j, hj1, rfl, _, hmin_z⟩
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · exact hmin j hj1 hlt hzW
    · exact hzy rfl
    · exact hmin_z k hk1 hgt (by simp)
  · intro hdisj
    have hne : (Ω.bar ∩ W).Nonempty := ⟨x, hx_bar, hx⟩
    obtain ⟨z, hhit⟩ := Ω.exists_firstHitIn hx_bar hne
    have hzW : z ∈ W := hhit.mem_set
    have hzx : z ≠ x := fun h => Ω.not_firstHitIn_self hx_bar hy_bar hy hxy.symm (h ▸ hhit)
    by_cases hzy : z = y
    · exact hzy ▸ hhit
    · exfalso
      rcases hhit with ⟨j, hj1, rfl, _, hmin⟩
      have hhit3 : Ω.FirstHitIn {x, (Ω.toFun^[j]) x, y} x ((Ω.toFun^[j]) x) := by
        refine ⟨j, hj1, rfl, by simp, fun i hi1 hij hi_in => ?_⟩
        refine hmin i hi1 hij ?_
        simp only [mem_insert_iff, mem_singleton_iff] at hi_in
        rcases hi_in with heq | heq | heq
        · rw [heq]; exact hx
        · rw [heq]; exact hzW
        · rw [heq]; exact hy
      have hz_int : (Ω.toFun^[j]) x ∈ Ω.interval x y :=
        (Ω.mem_interval_iff_firstHitIn hx_bar hy_bar (hW hzW) hxy hzx hzy).mpr hhit3
      exact disjoint_left.mp hdisj hz_int hzW

theorem isClockwise4_iff_interval {v₁ v₂ v₃ v₄ : α} :
    Ω.IsClockwise4 v₁ v₂ v₃ v₄ ↔ v₂ ∈ Ω.interval v₁ v₃ ∧ v₄ ∈ Ω.interval v₃ v₁ := by
  constructor
  · intro h
    obtain ⟨h12, h13, h14, h23, h24, h34, hv₁, hv₂, hv₃, hv₄, hhit0, _, hhit2, _⟩ :=
      Ω.isClockwise4_iff.mp h
    have h2_int : v₂ ∈ Ω.interval v₁ v₃ := by
      rw [Ω.mem_interval_iff_firstHitIn hv₁ hv₃ hv₂ h13 h12.symm h23]
      rcases hhit0 with ⟨k, hk1, rfl, _, hmin⟩
      refine ⟨k, hk1, rfl, by simp, fun j hj1 hjk hj_in => hmin j hj1 hjk ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hj_in ⊢
      rcases hj_in with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    have h4_int : v₄ ∈ Ω.interval v₃ v₁ := by
      rw [Ω.mem_interval_iff_firstHitIn hv₃ hv₁ hv₄ h13.symm h34.symm h14.symm]
      rcases hhit2 with ⟨k, hk1, rfl, _, hmin⟩
      refine ⟨k, hk1, rfl, by simp, fun j hj1 hjk hj_in => hmin j hj1 hjk ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hj_in ⊢
      rcases hj_in with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
    exact ⟨h2_int, h4_int⟩
  · rintro ⟨hv₂_int, hv₄_int⟩
    have hv₁ : v₁ ∈ Ω.bar := (Ω.isClockwise3_iff.mp hv₂_int.2).2.2.2.1
    have hv₂ : v₂ ∈ Ω.bar := hv₂_int.1.1
    have hv₃ : v₃ ∈ Ω.bar := (Ω.isClockwise3_iff.mp hv₂_int.2).2.2.2.2.2.1
    have hv₄ : v₄ ∈ Ω.bar := hv₄_int.1.1
    have h12 : v₁ ≠ v₂ := fun h => hv₂_int.1.2 (by simp [h])
    have h13 : v₁ ≠ v₃ := (Ω.isClockwise3_iff.mp hv₂_int.2).2.1
    have h23 : v₂ ≠ v₃ := fun h => hv₂_int.1.2 (by simp [h])
    have h34 : v₃ ≠ v₄ := fun h => hv₄_int.1.2 (by simp [h])
    have h14 : v₁ ≠ v₄ := fun h => hv₄_int.1.2 (by simp [h])
    have h24 : v₂ ≠ v₄ := fun h =>
      disjoint_left.mp (Ω.disjoint_interval_swap v₁ v₃) hv₂_int (h ▸ hv₄_int)
    have hSub : ({v₁, v₂, v₃, v₄} : Set α) ⊆ Ω.bar := by
      rintro x (rfl | rfl | rfl | rfl) <;> assumption
    have hhit_12_3 : Ω.FirstHitIn {v₁, v₂, v₃} v₁ v₂ :=
      (Ω.isClockwise3_iff.mp hv₂_int.2).2.2.2.2.2.2.1
    have hhit_23_1 : Ω.FirstHitIn {v₂, v₃, v₁} v₂ v₃ := by
      have hset : ({v₂, v₃, v₁} : Set α) = {v₁, v₂, v₃} := by ext x; simp [or_comm, or_left_comm]
      rw [hset]
      exact (Ω.isClockwise3_iff.mp hv₂_int.2).2.2.2.2.2.2.2.1
    have hhit_34_1 : Ω.FirstHitIn {v₃, v₄, v₁} v₃ v₄ :=
      (Ω.isClockwise3_iff.mp hv₄_int.2).2.2.2.2.2.2.1
    have hhit_41_3 : Ω.FirstHitIn {v₄, v₁, v₃} v₄ v₁ := by
      have hset : ({v₄, v₁, v₃} : Set α) = {v₃, v₄, v₁} := by ext x; simp [or_comm, or_left_comm]
      rw [hset]
      exact (Ω.isClockwise3_iff.mp hv₄_int.2).2.2.2.2.2.2.2.1
    -- For any `a, b, c` with `FirstHitIn {a, b, c} a b`, the first hit from `a` in `{a, b, c, d}`
    -- cannot be `c`.
    have hnot_third : ∀ {a b c : α} {S : Set α},
        ({a, b, c} : Set α) ⊆ S → b ≠ c →
        Ω.FirstHitIn {a, b, c} a b → ¬ Ω.FirstHitIn S a c := by
      intro a b c S hsub hbc ⟨k₁, hk₁, heq₁, _, hmin₁⟩ ⟨k₂, hk₂, heq₂, _, hmin₂⟩
      rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
      · exact hmin₂ k₁ hk₁ hlt (hsub (by simp [heq₁]))
      · exact hbc (heq₁.symm.trans heq₂)
      · exact hmin₁ k₂ hk₂ hgt (by simp [heq₂])
    have h1_not_3 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₁ v₃ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h23 hhit_12_3
    have h2_not_1 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₂ v₁ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h13.symm hhit_23_1
    have h3_not_1 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₃ v₁ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h14.symm hhit_34_1
    have h4_not_3 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₄ v₃ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h13 hhit_41_3
    -- Also `v₁ ∈ Ω.interval v₄ v₃`, so `FirstHitIn {v₄, v₁, v₃} v₁ v₃`, meaning `v₁` hits `v₃`
    -- before `v₄`.
    have hhit_13_4 : Ω.FirstHitIn {v₁, v₃, v₄} v₁ v₃ := by
      have hset : ({v₁, v₃, v₄} : Set α) = {v₃, v₄, v₁} := by ext x; simp [or_comm, or_left_comm]
      rw [hset]
      exact (Ω.isClockwise3_iff.mp hv₄_int.2).2.2.2.2.2.2.2.2
    have h1_not_4 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₁ v₄ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h34 hhit_13_4
    have hhit_31_2 : Ω.FirstHitIn {v₃, v₁, v₂} v₃ v₁ := by
      have hset : ({v₃, v₁, v₂} : Set α) = {v₁, v₂, v₃} := by ext x; simp [or_comm, or_left_comm]
      rw [hset]
      exact (Ω.isClockwise3_iff.mp hv₂_int.2).2.2.2.2.2.2.2.2
    have h3_not_2 : ¬ Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₃ v₂ :=
      hnot_third (by intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto)
        h12 hhit_31_2
    have hne4 : (Ω.bar ∩ ({v₁, v₂, v₃, v₄} : Set α)).Nonempty := ⟨v₁, hv₁, by simp⟩
    obtain ⟨y₁, hy₁⟩ := Ω.exists_firstHitIn hv₁ hne4
    obtain ⟨y₂, hy₂⟩ := Ω.exists_firstHitIn hv₂ hne4
    obtain ⟨y₃, hy₃⟩ := Ω.exists_firstHitIn hv₃ hne4
    obtain ⟨y₄, hy₄⟩ := Ω.exists_firstHitIn hv₄ hne4
    have hy₁_ne : y₁ ≠ v₁ := fun h => Ω.not_firstHitIn_self hv₁ hv₂ (by simp) h12.symm (h ▸ hy₁)
    have hy₂_ne : y₂ ≠ v₂ := fun h => Ω.not_firstHitIn_self hv₂ hv₃ (by simp) h23.symm (h ▸ hy₂)
    have hy₃_ne : y₃ ≠ v₃ := fun h => Ω.not_firstHitIn_self hv₃ hv₄ (by simp) h34.symm (h ▸ hy₃)
    have hy₄_ne : y₄ ≠ v₄ := fun h => Ω.not_firstHitIn_self hv₄ hv₁ (by simp) h14 (h ▸ hy₄)
    have hy₁_eq : y₁ = v₂ := by
      rcases hy₁.mem_set with rfl | rfl | rfl | rfl
      · exact (hy₁_ne rfl).elim
      · rfl
      · exact (h1_not_3 hy₁).elim
      · exact (h1_not_4 hy₁).elim
    rw [hy₁_eq] at hy₁
    have hy₃_eq : y₃ = v₄ := by
      rcases hy₃.mem_set with rfl | rfl | rfl | rfl
      · exact (h3_not_1 hy₃).elim
      · exact (h3_not_2 hy₃).elim
      · exact (hy₃_ne rfl).elim
      · rfl
    rw [hy₃_eq] at hy₃
    have hy₂_eq : y₂ = v₃ := by
      rcases hy₂.mem_set with rfl | rfl | rfl | rfl
      · exact (h2_not_1 hy₂).elim
      · exact (hy₂_ne rfl).elim
      · rfl
      · exact (h23 (hy₂.inj_left hv₂ hv₃ (by simp) (by simp) hy₃)).elim
    rw [hy₂_eq] at hy₂
    have hy₄_eq : y₄ = v₁ := by
      rcases hy₄.mem_set with rfl | rfl | rfl | rfl
      · rfl
      · exact (h14 (hy₁.inj_left hv₁ hv₄ (by simp) (by simp) hy₄)).elim
      · exact (h4_not_3 hy₄).elim
      · exact (hy₄_ne rfl).elim
    rw [hy₄_eq] at hy₄
    exact Ω.isClockwise4_iff.mpr
      ⟨h12, h13, h14, h23, h24, h34, hv₁, hv₂, hv₃, hv₄, hy₁, hy₂, hy₃, hy₄⟩

theorem crosses_iff_interval {a₁ b₁ a₂ b₂ : α} :
    Ω.Crosses a₁ b₁ a₂ b₂ ↔
      (a₂ ∈ Ω.interval a₁ b₁ ∧ b₂ ∈ Ω.interval b₁ a₁) ∨
        (b₂ ∈ Ω.interval a₁ b₁ ∧ a₂ ∈ Ω.interval b₁ a₁) := by
  change (Ω.IsClockwise4 a₁ a₂ b₁ b₂ ∨ Ω.IsClockwise4 b₂ b₁ a₂ a₁) ↔ _
  have hrot : Ω.IsClockwise4 b₂ b₁ a₂ a₁ ↔ Ω.IsClockwise4 a₁ b₂ b₁ a₂ :=
    ⟨fun h => Ω.isClockwise4_rotate (Ω.isClockwise4_rotate (Ω.isClockwise4_rotate h)),
      fun h => Ω.isClockwise4_rotate h⟩
  rw [hrot, Ω.isClockwise4_iff_interval, Ω.isClockwise4_iff_interval]

theorem Crosses.symm {a₁ b₁ a₂ b₂ : α} (h : Ω.Crosses a₁ b₁ a₂ b₂) :
    Ω.Crosses a₂ b₂ a₁ b₁ := by
  rcases h with h | h
  · exact Or.inr (Ω.isClockwise4_rotate (Ω.isClockwise4_rotate h))
  · exact Or.inl (Ω.isClockwise4_rotate (Ω.isClockwise4_rotate h))

theorem Crosses.swap_left {a₁ b₁ a₂ b₂ : α} (h : Ω.Crosses a₁ b₁ a₂ b₂) :
    Ω.Crosses b₁ a₁ a₂ b₂ := by
  rw [Ω.crosses_iff_interval] at h ⊢
  exact h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)

theorem Crosses.swap_right {a₁ b₁ a₂ b₂ : α} (h : Ω.Crosses a₁ b₁ a₂ b₂) :
    Ω.Crosses a₁ b₁ b₂ a₂ :=
  (h.symm.swap_left).symm

theorem mem_interval_rotate_left {x y z : α} (h : y ∈ Ω.interval x z) :
    z ∈ Ω.interval y x := by
  refine ⟨⟨(Ω.isClockwise3_iff.mp h.2).2.2.2.2.2.1, ?_⟩, Ω.isClockwise3_rotate h.2⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨(Ω.isClockwise3_iff.mp h.2).2.2.1.symm, (Ω.isClockwise3_iff.mp h.2).2.1.symm⟩

theorem mem_interval_rotate_right {x y z : α} (h : y ∈ Ω.interval x z) :
    x ∈ Ω.interval z y :=
  Ω.mem_interval_rotate_left (Ω.mem_interval_rotate_left h)

theorem interval_subset_interval_left {x y z : α} (hy : y ∈ Ω.interval x z) :
    Ω.interval x y ⊆ Ω.interval x z := by
  intro w hw
  have hz_yx : z ∈ Ω.interval y x := Ω.mem_interval_rotate_left hy
  have hcw4 : Ω.IsClockwise4 x w y z := Ω.isClockwise4_iff_interval.mpr ⟨hw, hz_yx⟩
  have hcw4' : Ω.IsClockwise4 w y z x := Ω.isClockwise4_rotate hcw4
  exact Ω.mem_interval_rotate_left (Ω.isClockwise4_iff_interval.mp hcw4').2

theorem interval_subset_interval_right {x y z : α} (hy : y ∈ Ω.interval x z) :
    Ω.interval y z ⊆ Ω.interval x z := by
  intro w hw
  have hx_zy : x ∈ Ω.interval z y := Ω.mem_interval_rotate_right hy
  have hcw4 : Ω.IsClockwise4 y w z x := Ω.isClockwise4_iff_interval.mpr ⟨hw, hx_zy⟩
  have hcw4' : Ω.IsClockwise4 w z x y := Ω.isClockwise4_rotate hcw4
  exact Ω.mem_interval_rotate_right (Ω.isClockwise4_iff_interval.mp hcw4').1

theorem mem_interval_right_of_mem_interval_left {x y z w : α}
    (hy : y ∈ Ω.interval x z) (hw : w ∈ Ω.interval x y) :
    y ∈ Ω.interval w z := by
  have hz_yx : z ∈ Ω.interval y x := Ω.mem_interval_rotate_left hy
  have hcw4 : Ω.IsClockwise4 x w y z := Ω.isClockwise4_iff_interval.mpr ⟨hw, hz_yx⟩
  exact (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate hcw4)).1

theorem mem_interval_left_of_mem_interval_right {x y z w : α}
    (hy : y ∈ Ω.interval x z) (hw : w ∈ Ω.interval y z) :
    y ∈ Ω.interval x w := by
  have hx_zy : x ∈ Ω.interval z y := Ω.mem_interval_rotate_right hy
  have hcw4 : Ω.IsClockwise4 y w z x := Ω.isClockwise4_iff_interval.mpr ⟨hw, hx_zy⟩
  exact (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate (Ω.isClockwise4_rotate
    (Ω.isClockwise4_rotate hcw4)))).1

theorem interval_eq_union_of_mem {x y z : α} (hy : y ∈ Ω.interval x z) :
    Ω.interval x z = Ω.interval x y ∪ {y} ∪ Ω.interval y z := by
  ext w
  simp only [mem_union, mem_singleton_iff]
  constructor
  · intro hw
    by_cases hwy : w = y
    · exact Or.inl (Or.inr hwy)
    · have hx_bar : x ∈ Ω.bar := (Ω.isClockwise3_iff.mp hy.2).2.2.2.1
      have hy_bar : y ∈ Ω.bar := hy.1.1
      have hxy : x ≠ y := fun h => hy.1.2 (by simp [h])
      have hwx : w ≠ x := fun h => hw.1.2 (by simp [h])
      rcases Ω.mem_interval_or_interval_swap hx_bar hy_bar hw.1.1 hxy hwx hwy with hw_xy | hw_yx
      · exact Or.inl (Or.inl hw_xy)
      · exact Or.inr (Ω.mem_interval_right_of_mem_interval_left hw (Ω.mem_interval_rotate_right
        hw_yx))
  · rintro ((hw | rfl) | hw)
    · exact Ω.interval_subset_interval_left hy hw
    · exact hy
    · exact Ω.interval_subset_interval_right hy hw

theorem disjoint_interval_of_not_mem {x₁ y₁ x₂ y₂ : α}
    (hx₁ : x₁ ∈ Ω.bar) (hx₂ : x₂ ∈ Ω.bar) (hx12 : x₁ ≠ x₂)
    (h₁ : x₁ ∉ Ω.interval x₂ y₂) (h₂ : x₂ ∉ Ω.interval x₁ y₁) :
    Disjoint (Ω.interval x₁ y₁) (Ω.interval x₂ y₂) := by
  rw [disjoint_left]
  intro z hz₁ hz₂
  have hz_bar : z ∈ Ω.bar := hz₁.1.1
  have hzx₁ : z ≠ x₁ := fun h => hz₁.1.2 (by simp [h])
  have hzx₂ : z ≠ x₂ := fun h => hz₂.1.2 (by simp [h])
  have hx₂_not_x₁z : x₂ ∉ Ω.interval x₁ z :=
    fun h => h₂ (Ω.interval_subset_interval_left hz₁ h)
  have hx₂_zx₁ : x₂ ∈ Ω.interval z x₁ :=
    (Ω.mem_interval_or_interval_swap hx₁ hz_bar hx₂ hzx₁.symm hx12.symm hzx₂.symm).resolve_left
      hx₂_not_x₁z
  have hx₁_x₂z : x₁ ∈ Ω.interval x₂ z := Ω.mem_interval_rotate_left hx₂_zx₁
  exact h₁ (Ω.interval_subset_interval_left hz₂ hx₁_x₂z)

theorem isFence_interval_compl {x y : α} (hx : x ∈ Ω.bar) (hy : y ∈ Ω.bar) (hxy : x ≠ y) :
    Ω.IsFence ({x, y} ∪ Ω.interval x y) (Ω.interval y x) := by
  have hsubA : {x, y} ∪ Ω.interval x y ⊆ Ω.bar := by
    rintro z ((rfl | rfl) | hz)
    · exact hx
    · exact hy
    · exact hz.1.1
  have hsubB : Ω.interval y x ⊆ Ω.bar := Ω.interval_subset_bar y x
  have hdisj : Disjoint ({x, y} ∪ Ω.interval x y) (Ω.interval y x) := by
    rw [disjoint_union_left]
    refine ⟨disjoint_left.mpr ?_, Ω.disjoint_interval_swap x y⟩
    rintro z (rfl | rfl) hz
    · exact Ω.not_mem_interval_right y z hz
    · exact Ω.not_mem_interval_left z x hz
  have hunion : ({x, y} ∪ Ω.interval x y) ∪ Ω.interval y x = Ω.bar := by
    rw [union_assoc, Ω.interval_union_interval_swap hx hy hxy, union_sdiff_cancel]
    rintro z (rfl | rfl) <;> assumption
  refine ⟨hsubA, hsubB, hdisj, hunion, fun a₁ ha₁ a₂ ha₂ _ b₁ hb₁ b₂ hb₂ hb12 hcross => ?_⟩
  have hcross' : Ω.Crosses b₁ b₂ a₁ a₂ := hcross.symm
  rw [Ω.crosses_iff_interval] at hcross'
  have hb₁_bar : b₁ ∈ Ω.bar := hb₁.1.1
  have hb₂_bar : b₂ ∈ Ω.bar := hb₂.1.1
  have hby₁ : y ≠ b₁ := fun h => hb₁.1.2 (by simp [h.symm])
  have hby₂ : y ≠ b₂ := fun h => hb₂.1.2 (by simp [h.symm])
  rcases Ω.mem_interval_or_interval_swap hy hb₂_bar hb₁_bar hby₂ hby₁.symm hb12 with hb₁_yb₂ |
    hb₁_b₂y
  · have hb₂_b₁x : b₂ ∈ Ω.interval b₁ x := Ω.mem_interval_right_of_mem_interval_left hb₂ hb₁_yb₂
    have hsub : Ω.interval b₁ b₂ ⊆ Ω.interval y x :=
      (Ω.interval_subset_interval_left hb₂_b₁x).trans (Ω.interval_subset_interval_right hb₁)
    rcases hcross' with ⟨ha₁_in, _⟩ | ⟨ha₂_in, _⟩
    · exact disjoint_left.mp hdisj ha₁ (hsub ha₁_in)
    · exact disjoint_left.mp hdisj ha₂ (hsub ha₂_in)
  · have hb₂_yb₁ : b₂ ∈ Ω.interval y b₁ := Ω.mem_interval_rotate_right hb₁_b₂y
    have hb₁_b₂x : b₁ ∈ Ω.interval b₂ x := Ω.mem_interval_right_of_mem_interval_left hb₁ hb₂_yb₁
    have hsub : Ω.interval b₂ b₁ ⊆ Ω.interval y x :=
      (Ω.interval_subset_interval_left hb₁_b₂x).trans (Ω.interval_subset_interval_right hb₂)
    rcases hcross' with ⟨_, ha₂_in⟩ | ⟨_, ha₁_in⟩
    · exact disjoint_left.mp hdisj ha₂ (hsub ha₂_in)
    · exact disjoint_left.mp hdisj ha₁ (hsub ha₁_in)

theorem IsFence.symm {A B : Set α} (h : Ω.IsFence A B) : Ω.IsFence B A :=
  ⟨h.2.1, h.1, h.2.2.1.symm, union_comm B A ▸ h.2.2.2.1,
    fun b₁ hb₁ b₂ hb₂ hb12 a₁ ha₁ a₂ ha₂ ha12 hc =>
      h.2.2.2.2 a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hc.symm⟩

theorem unique_empty_interval_AB_of_isFence {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a₁ a₂ b₁ b₂ : α} (ha₁ : a₁ ∈ A ∩ W) (hb₁ : b₁ ∈ B ∩ W)
    (ha₂ : a₂ ∈ A ∩ W) (hb₂ : b₂ ∈ B ∩ W)
    (hdisj₁ : Disjoint (Ω.interval a₁ b₁) W)
    (hdisj₂ : Disjoint (Ω.interval a₂ b₂) W) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have ha_eq : a₁ = a₂ := by
    by_contra ha_ne
    have ha₂_not : a₂ ∉ Ω.interval a₁ b₁ := disjoint_right.mp hdisj₁ ha₂.2
    have ha₁_not : a₁ ∉ Ω.interval a₂ b₂ := disjoint_right.mp hdisj₂ ha₁.2
    have hab₁ : a₁ ≠ b₁ := fun h => disjoint_left.mp hfence.2.2.1 ha₁.1 (h ▸ hb₁.1)
    have hab₂ : a₂ ≠ b₂ := fun h => disjoint_left.mp hfence.2.2.1 ha₂.1 (h ▸ hb₂.1)
    have ha₂b₁ : a₂ ≠ b₁ := fun h => disjoint_left.mp hfence.2.2.1 ha₂.1 (h ▸ hb₁.1)
    have ha₁b₂ : a₁ ≠ b₂ := fun h => disjoint_left.mp hfence.2.2.1 ha₁.1 (h ▸ hb₂.1)
    have ha₂_b₁a₁ : a₂ ∈ Ω.interval b₁ a₁ :=
      (Ω.mem_interval_or_interval_swap (hW ha₁.2) (hW hb₁.2) (hW ha₂.2) hab₁
        (Ne.symm ha_ne) ha₂b₁).resolve_left ha₂_not
    have ha₁_b₂a₂ : a₁ ∈ Ω.interval b₂ a₂ :=
      (Ω.mem_interval_or_interval_swap (hW ha₂.2) (hW hb₂.2) (hW ha₁.2) hab₂ ha_ne
        ha₁b₂).resolve_left ha₁_not
    have hb₁_a₁a₂ : b₁ ∈ Ω.interval a₁ a₂ := Ω.mem_interval_rotate_right ha₂_b₁a₁
    have hb₂_a₂a₁ : b₂ ∈ Ω.interval a₂ a₁ := Ω.mem_interval_rotate_right ha₁_b₂a₂
    by_cases hb_eq : b₁ = b₂
    · exact disjoint_left.mp (Ω.disjoint_interval_swap a₁ a₂) hb₁_a₁a₂ (hb_eq ▸ hb₂_a₂a₁)
    · exact hfence.2.2.2.2 a₁ ha₁.1 a₂ ha₂.1 ha_ne b₁ hb₁.1 b₂ hb₂.1 hb_eq
        (Ω.crosses_iff_interval.mpr (Or.inl ⟨hb₁_a₁a₂, hb₂_a₂a₁⟩))
  subst ha_eq
  refine ⟨rfl, ?_⟩
  by_contra hb_ne
  have hab₁ : a₁ ≠ b₁ := fun h => disjoint_left.mp hfence.2.2.1 ha₁.1 (h ▸ hb₁.1)
  have hab₂ : a₁ ≠ b₂ := fun h => disjoint_left.mp hfence.2.2.1 ha₁.1 (h ▸ hb₂.1)
  rcases Ω.mem_interval_or_interval_swap (hW ha₁.2) (hW hb₁.2) (hW hb₂.2) hab₁ hab₂.symm
    (Ne.symm hb_ne) with
    hb₂_in | hb₂_in
  · exact disjoint_left.mp hdisj₁ hb₂_in hb₂.2
  · exact disjoint_left.mp hdisj₂ (Ω.mem_interval_rotate_right hb₂_in) hb₁.2

theorem exists_empty_interval_AB_of_subset_union {A B W : Set α}
    (_hW_bar : W ⊆ Ω.bar) (hW_AB : W ⊆ A ∪ B)
    (ha₀ : (A ∩ W).Nonempty) (hb₀ : (B ∩ W).Nonempty) :
    ∃ a' ∈ A ∩ W, ∃ b ∈ B ∩ W, Disjoint (Ω.interval a' b) W := by
  classical
  have hind : ∀ (n : ℕ) {a' b : α},
      a' ∈ A ∩ W → b ∈ B ∩ W → (Ω.interval a' b).ncard = n →
      ∃ a₁ ∈ A ∩ W, ∃ b₁ ∈ B ∩ W, Disjoint (Ω.interval a₁ b₁) W := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a' b ha' hb hcard
      by_cases hdisj : Disjoint (Ω.interval a' b) W
      · exact ⟨a', ha', b, hb, hdisj⟩
      · rw [not_disjoint_iff] at hdisj
        rcases hdisj with ⟨z, hz_int, hzW⟩
        have hfin : (Ω.interval a' b).Finite := Ω.finite_bar.subset (Ω.interval_subset_bar a' b)
        rcases hW_AB hzW with hzA | hzB
        · have hsub : Ω.interval z b ⊂ Ω.interval a' b :=
            ⟨Ω.interval_subset_interval_right hz_int,
              fun h => Ω.not_mem_interval_left z b (h hz_int)⟩
          have hlt : (Ω.interval z b).ncard < n := hcard ▸ ncard_lt_ncard hsub hfin
          exact ih _ hlt ⟨hzA, hzW⟩ hb rfl
        · have hsub : Ω.interval a' z ⊂ Ω.interval a' b :=
            ⟨Ω.interval_subset_interval_left hz_int,
              fun h => Ω.not_mem_interval_right a' z (h hz_int)⟩
          have hlt : (Ω.interval a' z).ncard < n := hcard ▸ ncard_lt_ncard hsub hfin
          exact ih _ hlt ha' ⟨hzB, hzW⟩ rfl
  rcases ha₀ with ⟨a₀, ha₀⟩
  rcases hb₀ with ⟨b₀, hb₀⟩
  exact hind (Ω.interval a₀ b₀).ncard ha₀ hb₀ rfl

theorem mem_interval_of_mem_A_of_disjoint_AB {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a' b x y : α} (ha' : a' ∈ A ∩ W) (hb : b ∈ B ∩ W)
    (hdisj : Disjoint (Ω.interval a' b) W)
    (hx : x ∈ A ∩ W) (hxa' : x ≠ a') (hy : y ∈ B ∩ W) :
    a' ∈ Ω.interval x y ∧ y ∈ Ω.interval a' x := by
  have hab : a' ≠ b := fun h => disjoint_left.mp hfence.2.2.1 ha'.1 (h ▸ hb.1)
  have hxb : x ≠ b := fun h => disjoint_left.mp hfence.2.2.1 hx.1 (h ▸ hb.1)
  have hx_not : x ∉ Ω.interval a' b := disjoint_right.mp hdisj hx.2
  have hx_ba' : x ∈ Ω.interval b a' :=
    (Ω.mem_interval_or_interval_swap (hW ha'.2) (hW hb.2) (hW hx.2) hab hxa' hxb).resolve_left
      hx_not
  have hb_a'x : b ∈ Ω.interval a' x := Ω.mem_interval_rotate_right hx_ba'
  have hy_a'x : y ∈ Ω.interval a' x := by
    by_cases hyb : y = b
    · exact hyb ▸ hb_a'x
    · have hy_not_xa' : y ∉ Ω.interval x a' := fun hy_xa' =>
        hfence.2.2.2.2 a' ha'.1 x hx.1 hxa'.symm b hb.1 y hy.1 (Ne.symm hyb)
          (Ω.crosses_iff_interval.mpr (Or.inl ⟨hb_a'x, hy_xa'⟩))
      have hya' : y ≠ a' := fun h => disjoint_left.mp hfence.2.2.1 ha'.1 (h ▸ hy.1)
      have hyx : y ≠ x := fun h => disjoint_left.mp hfence.2.2.1 hx.1 (h ▸ hy.1)
      exact (Ω.mem_interval_or_interval_swap (hW ha'.2) (hW hx.2) (hW hy.2) hxa'.symm hya'
        hyx).resolve_right hy_not_xa'
  exact ⟨Ω.mem_interval_rotate_right hy_a'x, hy_a'x⟩

theorem mem_interval_of_mem_B_of_disjoint_AB {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a' b x y : α} (ha' : a' ∈ A ∩ W) (hb : b ∈ B ∩ W)
    (hdisj : Disjoint (Ω.interval a' b) W)
    (hx : x ∈ A ∩ W) (hy : y ∈ B ∩ W) (hyb : y ≠ b) :
    b ∈ Ω.interval x y ∧ x ∈ Ω.interval y b := by
  have hab : a' ≠ b := fun h => disjoint_left.mp hfence.2.2.1 ha'.1 (h ▸ hb.1)
  have hya' : y ≠ a' := fun h => disjoint_left.mp hfence.2.2.1 ha'.1 (h ▸ hy.1)
  have hy_not : y ∉ Ω.interval a' b := disjoint_right.mp hdisj hy.2
  have hy_ba' : y ∈ Ω.interval b a' :=
    (Ω.mem_interval_or_interval_swap (hW ha'.2) (hW hb.2) (hW hy.2) hab hya' hyb).resolve_left
      hy_not
  have ha'_yb : a' ∈ Ω.interval y b := Ω.mem_interval_rotate_left hy_ba'
  have hx_yb : x ∈ Ω.interval y b := by
    by_cases hxa' : x = a'
    · exact hxa' ▸ ha'_yb
    · have hx_not_by : x ∉ Ω.interval b y := fun hx_by =>
        hfence.symm.2.2.2.2 y hy.1 b hb.1 hyb a' ha'.1 x hx.1 (Ne.symm hxa')
          (Ω.crosses_iff_interval.mpr (Or.inl ⟨ha'_yb, hx_by⟩))
      have hxy : x ≠ y := fun h => disjoint_left.mp hfence.2.2.1 hx.1 (h ▸ hy.1)
      have hxb : x ≠ b := fun h => disjoint_left.mp hfence.2.2.1 hx.1 (h ▸ hb.1)
      exact (Ω.mem_interval_or_interval_swap (hW hy.2) (hW hb.2) (hW hx.2) hyb hxy
        hxb).resolve_right hx_not_by
  exact ⟨Ω.mem_interval_rotate_left hx_yb, hx_yb⟩

theorem interval_subset_of_disjoint_AB {A B W : Set α}
    (hfence : Ω.IsFence A B) (hW : W ⊆ Ω.bar)
    {a' b x y : α} (ha' : a' ∈ A ∩ W) (hb : b ∈ B ∩ W)
    (hdisj : Disjoint (Ω.interval a' b) W)
    (hx : x ∈ A ∩ W) (hy : y ∈ B ∩ W) :
    Ω.interval a' b ⊆ Ω.interval x y := by
  have h₁ : Ω.interval a' b ⊆ Ω.interval x b := by
    by_cases hxa' : x = a'
    · exact hxa' ▸ Subset.rfl
    · exact Ω.interval_subset_interval_right
        (Ω.mem_interval_of_mem_A_of_disjoint_AB hfence hW ha' hb hdisj hx hxa' hb).1
  have h₂ : Ω.interval x b ⊆ Ω.interval x y := by
    by_cases hyb : y = b
    · exact hyb ▸ Subset.rfl
    · exact Ω.interval_subset_interval_left
        (Ω.mem_interval_of_mem_B_of_disjoint_AB hfence hW ha' hb hdisj hx hy hyb).1
  exact h₁.trans h₂

end CyclicPerm

/-! ## Proof of (3.1) and (3.4) (pages 47–48) -/

namespace Society

theorem not_omegaPathsCross_of_isPeripheralIn (S : Society α β)
    {P_set : Set (Graph α β)} {P Q : Graph α β}
    (hP : S.IsPeripheralIn P_set P) (hQ : Q ∈ P_set) :
    ¬ S.OmegaPathsCross Q P := by
  rcases hP with ⟨hP_in, a, b, hP_ends, hdisj_int⟩
  rintro ⟨_, s₂, t₂, s₁, t₁, hQ_ends, hP_ends', hcross⟩
  have hs₂_in : s₂ ∈ S.transactionEnds P_set := hQ_ends.mem_transactionEnds_left S hQ
  have ht₂_in : t₂ ∈ S.transactionEnds P_set := hQ_ends.mem_transactionEnds_right S hQ
  have hcross' : S.Ω.Crosses a b s₂ t₂ := by
    rcases hP_ends.ends_eq S hP_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcross.symm
    · exact hcross.symm.swap_left
  rw [S.Ω.crosses_iff_interval] at hcross'
  rcases hdisj_int with hdisj_ab | hdisj_ba
  · rcases hcross' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact disjoint_left.mp hdisj_ab h1 hs₂_in
    · exact disjoint_left.mp hdisj_ab h1 ht₂_in
  · rcases hcross' with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact disjoint_left.mp hdisj_ba h2 ht₂_in
    · exact disjoint_left.mp hdisj_ba h2 hs₂_in

/-- Any member `R ∈ P_set \ {P}` that is peripheral in `P_set \ {P}` (where `P_set` is a crooked
transaction with fence `(A, B)`, `P` has ends `a₁ ∈ A, b₁ ∈ B`, and `R` has ends `x ∈ A, y ∈ B`)
satisfies: if `Disjoint (S.Ω.interval x y) (S.transactionEnds (P_set \ {P}))`, then exactly one of
`a₁, b₁` lies in `S.Ω.interval x y`. -/
theorem mem_interval_of_peripheral_diff_singleton (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B)
    (hcrooked : S.IsCrookedTransaction P_set)
    {P R : Graph α β} {a₁ b₁ x y : α}
    (hP_in : P ∈ P_set) (hR_in : R ∈ P_set \ {P})
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (hP_ends : S.IsOmegaPathWithEnds P a₁ b₁)
    (hx : x ∈ A) (hy : y ∈ B) (hR_ends : S.IsOmegaPathWithEnds R x y)
    (hdisj_xy : Disjoint (S.Ω.interval x y) (S.transactionEnds (P_set \ {P}))) :
    (a₁ ∈ S.Ω.interval x y ∧ b₁ ∉ S.Ω.interval x y) ∨
      (b₁ ∈ S.Ω.interval x y ∧ a₁ ∉ S.Ω.interval x y) := by
  have hnot_periph_R : ¬ S.IsPeripheralIn P_set R := hcrooked.2 R hR_in.1
  have hnot_disj_R : ¬ Disjoint (S.Ω.interval x y) (S.transactionEnds P_set) :=
    fun h => hnot_periph_R ⟨hR_in.1, x, y, hR_ends, Or.inl h⟩
  rw [S.transactionEnds_diff_singleton hfence.1 hP_in hP_ends] at hdisj_xy
  have ha₁_or_hb₁ : a₁ ∈ S.Ω.interval x y ∨ b₁ ∈ S.Ω.interval x y := by
    rw [not_disjoint_iff] at hnot_disj_R
    rcases hnot_disj_R with ⟨z, hz_xy, hz_W⟩
    by_cases hz_ab : z ∈ ({a₁, b₁} : Set α)
    · rcases hz_ab with rfl | rfl
      · exact Or.inl hz_xy
      · exact Or.inr hz_xy
    · exact (disjoint_left.mp hdisj_xy hz_xy ⟨hz_W, hz_ab⟩).elim
  have hnot_both : ¬ (a₁ ∈ S.Ω.interval x y ∧ b₁ ∈ S.Ω.interval x y) := by
    rintro ⟨ha₁_xy, hb₁_xy⟩
    have hdisj_PR : Disjoint V(P) V(R) := hfence.1.2 hP_in hR_in.1 (Ne.symm hR_in.2)
    have hxa₁ : x ≠ a₁ := fun h => disjoint_left.mp hdisj_PR hP_ends.1.left_mem
      (h ▸ hR_ends.1.left_mem)
    have hyb₁ : y ≠ b₁ := fun h => disjoint_left.mp hdisj_PR hP_ends.1.right_mem
      (h ▸ hR_ends.1.right_mem)
    have hy_a₁x : y ∈ S.Ω.interval a₁ x := S.Ω.mem_interval_rotate_left ha₁_xy
    have hb₁_not_xa₁ : b₁ ∉ S.Ω.interval x a₁ := fun hb₁_xa₁ =>
      hfence.2.1.2.2.2.2 x hx a₁ ha₁ hxa₁ b₁ hb₁ y hy hyb₁.symm
        (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hb₁_xa₁, hy_a₁x⟩))
    have hxb₁ : x ≠ b₁ := fun h => disjoint_left.mp hfence.2.1.2.2.1 hx (h ▸ hb₁)
    have ha₁b₁ : a₁ ≠ b₁ := hP_ends.2.1
    have hb₁_a₁x : b₁ ∈ S.Ω.interval a₁ x :=
      (S.Ω.mem_interval_or_interval_swap hR_ends.2.2.1 hP_ends.2.2.1 hP_ends.2.2.2
        hxa₁ hxb₁.symm ha₁b₁.symm).resolve_left hb₁_not_xa₁
    have ha₁_xb₁ : a₁ ∈ S.Ω.interval x b₁ := S.Ω.mem_interval_rotate_right hb₁_a₁x
    have hsub : S.Ω.interval a₁ b₁ ⊆ S.Ω.interval x y :=
      (S.Ω.interval_subset_interval_right ha₁_xb₁).trans (S.Ω.interval_subset_interval_left hb₁_xy)
    have hdisj_a₁b₁ : Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds P_set) := by
      rw [disjoint_left]
      intro z hz hzW
      have hza₁ : z ≠ a₁ := fun h => hz.1.2 (by simp [h])
      have hzb₁ : z ≠ b₁ := fun h => hz.1.2 (by simp [h])
      exact disjoint_left.mp hdisj_xy (hsub hz) ⟨hzW, by simp [hza₁, hzb₁]⟩
    exact hcrooked.2 P hP_in ⟨hP_in, a₁, b₁, hP_ends, Or.inl hdisj_a₁b₁⟩
  rcases ha₁_or_hb₁ with ha₁_in | hb₁_in
  · exact Or.inl ⟨ha₁_in, fun hb₁_in => hnot_both ⟨ha₁_in, hb₁_in⟩⟩
  · exact Or.inr ⟨hb₁_in, fun ha₁_in => hnot_both ⟨ha₁_in, hb₁_in⟩⟩

/-- Every overpass of a crooked transaction `P_set` crosses every other member of `P_set`. -/
theorem omegaPathsCross_of_isOverpass (S : Society α β)
    {P_set : Set (Graph α β)} {P Q : Graph α β}
    (hover : S.IsOverpass P_set P) (hQ : Q ∈ P_set \ {P}) :
    S.OmegaPathsCross P Q := by
  rcases hover with ⟨hcrooked, hP_in, R₁, hR₁_in, R₂, hR₂_in, hR12, hper₁, hper₂⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  obtain ⟨a₁, ha₁, b₁, hb₁, hP_ends⟩ := hfence.2.2 P hP_in
  obtain ⟨a_Q, ha_Q, b_Q, hb_Q, hQ_ends⟩ := hfence.2.2 Q hQ.1
  obtain ⟨x₁, hx₁, y₁, hy₁, hR₁_ends⟩ := hfence.2.2 R₁ hR₁_in.1
  obtain ⟨x₂, hx₂, y₂, hy₂, hR₂_ends⟩ := hfence.2.2 R₂ hR₂_in.1
  let W' := S.transactionEnds (P_set \ {P})
  have hW'_bar : W' ⊆ S.Ω.bar := S.transactionEnds_subset_bar (P_set \ {P})
  have hx₁W' : x₁ ∈ A ∩ W' := ⟨hx₁, hR₁_ends.mem_transactionEnds_left S hR₁_in⟩
  have hy₁W' : y₁ ∈ B ∩ W' := ⟨hy₁, hR₁_ends.mem_transactionEnds_right S hR₁_in⟩
  have hx₂W' : x₂ ∈ A ∩ W' := ⟨hx₂, hR₂_ends.mem_transactionEnds_left S hR₂_in⟩
  have hy₂W' : y₂ ∈ B ∩ W' := ⟨hy₂, hR₂_ends.mem_transactionEnds_right S hR₂_in⟩
  have haQW' : a_Q ∈ A ∩ W' := ⟨ha_Q, hQ_ends.mem_transactionEnds_left S hQ⟩
  have hbQW' : b_Q ∈ B ∩ W' := ⟨hb_Q, hQ_ends.mem_transactionEnds_right S hQ⟩
  have hper₁' := (hR₁_ends.isPeripheralIn_iff S hR₁_in).mp hper₁
  have hper₂' := (hR₂_ends.isPeripheralIn_iff S hR₂_in).mp hper₂
  have hdisj_R12 : Disjoint V(R₁) V(R₂) := hfence.1.2 hR₁_in.1 hR₂_in.1 hR12
  have hx12 : x₁ ≠ x₂ := fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.left_mem
    (h ▸ hR₂_ends.1.left_mem)
  have hy12 : y₁ ≠ y₂ := fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.right_mem
    (h ▸ hR₂_ends.1.right_mem)
  -- `R₁` and `R₂` cannot both have `Disjoint (interval x_i y_i) W'` or both `Disjoint (interval y_i
  -- x_i) W'`.
  have h_one_each :
      (Disjoint (S.Ω.interval x₁ y₁) W' ∧ Disjoint (S.Ω.interval y₂ x₂) W') ∨
      (Disjoint (S.Ω.interval y₁ x₁) W' ∧ Disjoint (S.Ω.interval x₂ y₂) W') := by
    rcases hper₁' with hd₁ | hd₁ <;> rcases hper₂' with hd₂ | hd₂
    · exfalso
      exact hx12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar hx₁W' hy₁W' hx₂W'
        hy₂W' hd₁ hd₂).1
    · exact Or.inl ⟨hd₁, hd₂⟩
    · exact Or.inr ⟨hd₁, hd₂⟩
    · exfalso
      exact hy12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar hy₁W' hx₁W' hy₂W'
        hx₂W' hd₁ hd₂).1
  -- Helper for when `Disjoint (interval u₁ v₁) W'` and `Disjoint (interval v₂ u₂) W'`.
  have hcross_of_pair : ∀ {u₁ v₁ u₂ v₂ : α} {M₁ M₂ : Graph α β},
      M₁ ∈ P_set \ {P} → M₂ ∈ P_set \ {P} → M₁ ≠ M₂ →
      u₁ ∈ A ∩ W' → v₁ ∈ B ∩ W' → S.IsOmegaPathWithEnds M₁ u₁ v₁ →
      u₂ ∈ A ∩ W' → v₂ ∈ B ∩ W' → S.IsOmegaPathWithEnds M₂ u₂ v₂ →
      Disjoint (S.Ω.interval u₁ v₁) W' → Disjoint (S.Ω.interval v₂ u₂) W' →
      S.Ω.Crosses a₁ b₁ a_Q b_Q := by
    intro u₁ v₁ u₂ v₂ M₁ M₂ hM₁ hM₂ hM12 hu₁ hv₁ hM₁_ends hu₂ hv₂ hM₂_ends hd₁ hd₂
    have hsub₁ : S.Ω.interval u₁ v₁ ⊆ S.Ω.interval a_Q b_Q :=
      S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW'_bar hu₁ hv₁ hd₁ haQW' hbQW'
    have hsub₂ : S.Ω.interval v₂ u₂ ⊆ S.Ω.interval b_Q a_Q :=
      S.Ω.interval_subset_of_disjoint_AB hfence.2.1.symm hW'_bar hv₂ hu₂ hd₂ hbQW' haQW'
    have h_ab_1 := S.mem_interval_of_peripheral_diff_singleton hfence hcrooked
      hP_in hM₁ ha₁ hb₁ hP_ends hu₁.1 hv₁.1 hM₁_ends hd₁
    have hfence_BA : S.IsFenceFor P_set B A :=
      ⟨hfence.1, hfence.2.1.symm, fun R hR => by
        obtain ⟨a, ha, b, hb, hR_e⟩ := hfence.2.2 R hR
        exact ⟨b, hb, a, ha, hR_e.symm S⟩⟩
    have h_ab_2 := S.mem_interval_of_peripheral_diff_singleton hfence_BA hcrooked
      hP_in hM₂ hb₁ ha₁ (hP_ends.symm S) hv₂.1 hu₂.1 (hM₂_ends.symm S) hd₂
    have hdisj_int : Disjoint (S.Ω.interval u₁ v₁) (S.Ω.interval v₂ u₂) :=
      (S.Ω.disjoint_interval_swap a_Q b_Q).mono hsub₁ hsub₂
    apply CyclicPerm.Crosses.symm
    rw [S.Ω.crosses_iff_interval]
    rcases h_ab_1 with ⟨ha₁_1, _⟩ | ⟨hb₁_1, _⟩
    · rcases h_ab_2 with ⟨hb₁_2, _⟩ | ⟨ha₁_2, _⟩
      · exact Or.inl ⟨hsub₁ ha₁_1, hsub₂ hb₁_2⟩
      · exact (disjoint_left.mp hdisj_int ha₁_1 ha₁_2).elim
    · rcases h_ab_2 with ⟨hb₁_2, _⟩ | ⟨ha₁_2, _⟩
      · exact (disjoint_left.mp hdisj_int hb₁_1 hb₁_2).elim
      · exact Or.inr ⟨hsub₁ hb₁_1, hsub₂ ha₁_2⟩
  refine ⟨hfence.1.2 hP_in hQ.1 (Ne.symm hQ.2), a₁, b₁, a_Q, b_Q, hP_ends, hQ_ends, ?_⟩
  rcases h_one_each with ⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩
  · exact hcross_of_pair hR₁_in hR₂_in hR12 hx₁W' hy₁W' hR₁_ends hx₂W' hy₂W' hR₂_ends hd₁ hd₂
  · exact hcross_of_pair hR₂_in hR₁_in hR12.symm hx₂W' hy₂W' hR₂_ends hx₁W' hy₁W' hR₁_ends hd₂ hd₁

/-- **Graph Minors IX, (3.1)** (page 47):
"Any crooked transaction has at most one overpass." -/
theorem theorem_3_1_proof (S : Society α β) {P_set : Set (Graph α β)}
    (_hcrooked : S.IsCrookedTransaction P_set)
    {P₁ P₂ : Graph α β} (h₁ : S.IsOverpass P_set P₁) (h₂ : S.IsOverpass P_set P₂) :
    P₁ = P₂ := by
  by_contra hne
  rcases h₁ with ⟨_, _, Q₁, hQ₁_in, Q₂, hQ₂_in, hQ12, hper₁, hper₂⟩
  by_cases hP₂Q₁ : P₂ = Q₁
  · have hP₂Q₂ : P₂ ≠ Q₂ := fun h => hQ12 (hP₂Q₁.symm.trans h)
    have hcross : S.OmegaPathsCross P₂ Q₂ :=
      S.omegaPathsCross_of_isOverpass h₂ ⟨hQ₂_in.1, hP₂Q₂.symm⟩
    exact S.not_omegaPathsCross_of_isPeripheralIn hper₂ ⟨h₂.2.1, Ne.symm hne⟩ hcross
  · have hcross : S.OmegaPathsCross P₂ Q₁ :=
      S.omegaPathsCross_of_isOverpass h₂ ⟨hQ₁_in.1, Ne.symm hP₂Q₁⟩
    exact S.not_omegaPathsCross_of_isPeripheralIn hper₁ ⟨h₂.2.1, Ne.symm hne⟩ hcross

/-- Every crooked transaction is nonempty or has cardinality 0; if nonempty, any crooked transaction
has cardinality `≥ 2`, and contains a 2-element crooked transaction `{P₁, P₂}` (a cross). -/
theorem exists_crooked_pair_of_nonempty (S : Society α β)
    {P_set : Set (Graph α β)} (hcrooked : S.IsCrookedTransaction P_set)
    (hne : P_set.Nonempty) :
    ∃ P₁ ∈ P_set, ∃ P₂ ∈ P_set, P₁ ≠ P₂ ∧ S.IsCrookedTransaction {P₁, P₂} := by
  rcases hne with ⟨P₀, hP₀⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have hW_AB : W ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW_bar
  obtain ⟨a₀, ha₀, b₀, hb₀, hP₀_ends⟩ := hfence.2.2 P₀ hP₀
  have ha_ne : (A ∩ W).Nonempty := ⟨a₀, ha₀, hP₀_ends.mem_transactionEnds_left S hP₀⟩
  have hb_ne : (B ∩ W).Nonempty := ⟨b₀, hb₀, hP₀_ends.mem_transactionEnds_right S hP₀⟩
  obtain ⟨a', ha'W, b, hbW, hdisj_a'b⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_AB ha_ne hb_ne
  obtain ⟨P₁, hP₁_in, c₁, hc₁⟩ := ha'W.2
  obtain ⟨a₁, ha₁, b₁, hb₁, hP₁_ends_raw⟩ := hfence.2.2 P₁ hP₁_in
  have ha₁_eq : a₁ = a' := by
    rcases hP₁_ends_raw.ends_eq S hc₁ with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.symm
    · exact (disjoint_left.mp hfence.2.1.2.2.1 ha'W.1 (h ▸ hb₁)).elim
  have hP₁_ends : S.IsOmegaPathWithEnds P₁ a' b₁ := ha₁_eq ▸ hP₁_ends_raw
  obtain ⟨P₂, hP₂_in, c₂, hc₂⟩ := hbW.2
  obtain ⟨a₂, ha₂, b₂, hb₂, hP₂_ends_raw⟩ := hfence.2.2 P₂ hP₂_in
  have hb₂_eq : b₂ = b := by
    rcases hP₂_ends_raw.ends_eq S hc₂ with ⟨h, _⟩ | ⟨h, _⟩
    · exact (disjoint_left.mp hfence.2.1.2.2.1 (h ▸ ha₂) hbW.1).elim
    · exact h.symm
  have hP₂_ends : S.IsOmegaPathWithEnds P₂ a₂ b := hb₂_eq ▸ hP₂_ends_raw
  have hP12 : P₁ ≠ P₂ := by
    intro hPP
    obtain ⟨heq_a, heq_b⟩ := hP₁_ends.ends_eq_of_mem_disjoint S hfence.2.1.2.2.1 ha'W.1 hb₁ ha₂
      (hPP ▸ hP₂_ends)
    exact hcrooked.2 P₁ hP₁_in ⟨hP₁_in, a', b, heq_b ▸ hP₁_ends, Or.inl hdisj_a'b⟩
  have hdisj_12 : Disjoint V(P₁) V(P₂) := hfence.1.2 hP₁_in hP₂_in hP12
  have ha2a' : a₂ ≠ a' := fun h => disjoint_left.mp hdisj_12 hP₁_ends.1.left_mem
    (h ▸ hP₂_ends.1.left_mem)
  have hb1b : b₁ ≠ b := fun h => disjoint_left.mp hdisj_12 hP₁_ends.1.right_mem
    (h ▸ hP₂_ends.1.right_mem)
  have ha'_a₂b : a' ∈ S.Ω.interval a₂ b :=
    (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar ha'W hbW hdisj_a'b
      ⟨ha₂, hP₂_ends.mem_transactionEnds_left S hP₂_in⟩ ha2a' hbW).1
  have ha'_a₂b₁ : a' ∈ S.Ω.interval a₂ b₁ :=
    (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar ha'W hbW hdisj_a'b
      ⟨ha₂, hP₂_ends.mem_transactionEnds_left S hP₂_in⟩ ha2a'
      ⟨hb₁, hP₁_ends.mem_transactionEnds_right S hP₁_in⟩).1
  have hb_a'b₁ : b ∈ S.Ω.interval a' b₁ :=
    (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar ha'W hbW hdisj_a'b
      ha'W ⟨hb₁, hP₁_ends.mem_transactionEnds_right S hP₁_in⟩ hb1b).1
  have hb₁_ba₂ : b₁ ∈ S.Ω.interval b a₂ :=
    S.Ω.mem_interval_rotate_left (S.Ω.interval_subset_interval_right ha'_a₂b₁ hb_a'b₁)
  have hcross : S.Ω.Crosses a₂ b a' b₁ :=
    S.Ω.crosses_iff_interval.mpr (Or.inl ⟨ha'_a₂b, hb₁_ba₂⟩)
  refine ⟨P₁, hP₁_in, P₂, hP₂_in, hP12, ⟨A, B, ⟨?_, ?_⟩, hfence.2.1, ?_⟩, ?_⟩
  · rintro Q (rfl | rfl)
    · exact hfence.1.1 Q hP₁_in
    · exact hfence.1.1 Q hP₂_in
  · rintro Q₁ (rfl | rfl) Q₂ (rfl | rfl) hne'
    · exact (hne' rfl).elim
    · exact hdisj_12
    · exact hdisj_12.symm
    · exact (hne' rfl).elim
  · rintro Q (rfl | rfl)
    · exact ⟨a', ha'W.1, b₁, hb₁, hP₁_ends⟩
    · exact ⟨a₂, ha₂, b, hbW.1, hP₂_ends⟩
  · rintro Q (rfl | rfl) hper
    · exact S.not_omegaPathsCross_of_isPeripheralIn hper (by simp)
        ⟨hdisj_12.symm, a₂, b, a', b₁, hP₂_ends, hP₁_ends, hcross⟩
    · exact S.not_omegaPathsCross_of_isPeripheralIn hper (by simp)
        ⟨hdisj_12, a', b₁, a₂, b, hP₁_ends, hP₂_ends, hcross.symm⟩

/-- Every crooked transaction of cardinality `≥ 5` contains a crooked transaction of cardinality
`|P_set| - 1`. -/
theorem exists_crooked_diff_singleton_of_ncard_ge_five (S : Society α β)
    {P_set : Set (Graph α β)} (hcrooked : S.IsCrookedTransaction P_set)
    (hcard : 5 ≤ P_set.ncard) :
    ∃ P ∈ P_set, S.IsCrookedTransaction (P_set \ {P}) := by
  classical
  have hfin_P : P_set.Finite := by
    by_contra hinf
    have h0 := Set.Infinite.ncard hinf
    omega
  have hne : P_set.Nonempty := (ncard_pos hfin_P).mp (by omega)
  rcases hne with ⟨P₀, hP₀⟩
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have hW_AB : W ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW_bar
  obtain ⟨a₀, ha₀, b₀, hb₀, hP₀_ends⟩ := hfence.2.2 P₀ hP₀
  have ha_ne : (A ∩ W).Nonempty := ⟨a₀, ha₀, hP₀_ends.mem_transactionEnds_left S hP₀⟩
  have hb_ne : (B ∩ W).Nonempty := ⟨b₀, hb₀, hP₀_ends.mem_transactionEnds_right S hP₀⟩
  obtain ⟨a', ha'W, b, hbW, hdisj_a'b⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_AB ha_ne hb_ne
  obtain ⟨b', hb'W, a, haW, hdisj_b'a⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar (union_comm A B ▸ hW_AB) hb_ne ha_ne
  obtain ⟨P_a', hPa'_in, _, hPa'_c⟩ := ha'W.2
  obtain ⟨P_b, hPb_in, _, hPb_c⟩ := hbW.2
  obtain ⟨P_b', hPb'_in, _, hPb'_c⟩ := hb'W.2
  obtain ⟨P_a, hPa_in, _, hPa_c⟩ := haW.2
  have hcard4 : ({P_a', P_b, P_b', P_a} : Set (Graph α β)).ncard ≤ 4 := by
    calc ({P_a', P_b, P_b', P_a} : Set (Graph α β)).ncard
      _ ≤ ({P_b, P_b', P_a} : Set (Graph α β)).ncard + 1 := ncard_insert_le _ _
      _ ≤ ({P_b', P_a} : Set (Graph α β)).ncard + 1 + 1 := by gcongr; exact ncard_insert_le _ _
      _ ≤ ({P_a} : Set (Graph α β)).ncard + 1 + 1 + 1 := by gcongr; exact ncard_insert_le _ _
      _ = 4 := by simp
  have hnot_sub : ¬ P_set ⊆ {P_a', P_b, P_b', P_a} := by
    intro hsub
    have hle := ncard_le_ncard hsub
    omega
  obtain ⟨P, hP_in, hP_not_in⟩ := not_subset.mp hnot_sub
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hP_not_in
  rcases hP_not_in with ⟨hP_ne_a', hP_ne_b, hP_ne_b', hP_ne_a⟩
  obtain ⟨a_P, ha_P, b_P, hb_P, hP_ends⟩ := hfence.2.2 P hP_in
  have ha'V : a' ∈ V(P_a') := hPa'_c.1.left_mem
  have hbV : b ∈ V(P_b) := hPb_c.1.left_mem
  have hb'V : b' ∈ V(P_b') := hPb'_c.1.left_mem
  have haV : a ∈ V(P_a) := hPa_c.1.left_mem
  have ha'_not_P : a' ∉ ({a_P, b_P} : Set α) := by
    rintro (rfl | rfl)
    · exact disjoint_left.mp (hfence.1.2 hP_in hPa'_in hP_ne_a') hP_ends.1.left_mem ha'V
    · exact disjoint_left.mp (hfence.1.2 hP_in hPa'_in hP_ne_a') hP_ends.1.right_mem ha'V
  have hb_not_P : b ∉ ({a_P, b_P} : Set α) := by
    rintro (rfl | rfl)
    · exact disjoint_left.mp (hfence.1.2 hP_in hPb_in hP_ne_b) hP_ends.1.left_mem hbV
    · exact disjoint_left.mp (hfence.1.2 hP_in hPb_in hP_ne_b) hP_ends.1.right_mem hbV
  have hb'_not_P : b' ∉ ({a_P, b_P} : Set α) := by
    rintro (rfl | rfl)
    · exact disjoint_left.mp (hfence.1.2 hP_in hPb'_in hP_ne_b') hP_ends.1.left_mem hb'V
    · exact disjoint_left.mp (hfence.1.2 hP_in hPb'_in hP_ne_b') hP_ends.1.right_mem hb'V
  have ha_not_P : a ∉ ({a_P, b_P} : Set α) := by
    rintro (rfl | rfl)
    · exact disjoint_left.mp (hfence.1.2 hP_in hPa_in hP_ne_a) hP_ends.1.left_mem haV
    · exact disjoint_left.mp (hfence.1.2 hP_in hPa_in hP_ne_a) hP_ends.1.right_mem haV
  let W' := S.transactionEnds (P_set \ {P})
  have hW'_eq : W' = W \ {a_P, b_P} := S.transactionEnds_diff_singleton hfence.1 hP_in hP_ends
  have ha'W' : a' ∈ W' := hW'_eq ▸ ⟨ha'W.2, ha'_not_P⟩
  have hbW' : b ∈ W' := hW'_eq ▸ ⟨hbW.2, hb_not_P⟩
  have hb'W' : b' ∈ W' := hW'_eq ▸ ⟨hb'W.2, hb'_not_P⟩
  have haW' : a ∈ W' := hW'_eq ▸ ⟨haW.2, ha_not_P⟩
  refine ⟨P, hP_in, ⟨A, B, ⟨fun R hR => hfence.1.1 R hR.1, hfence.1.2.mono sdiff_subset⟩,
    hfence.2.1, fun R hR => hfence.2.2 R hR.1⟩, ?_⟩
  intro R hR hper
  obtain ⟨x, hx, y, hy, hR_ends⟩ := hfence.2.2 R hR.1
  have hxW : x ∈ A ∩ W := ⟨hx, hR_ends.mem_transactionEnds_left S hR.1⟩
  have hyW : y ∈ B ∩ W := ⟨hy, hR_ends.mem_transactionEnds_right S hR.1⟩
  rcases (hR_ends.isPeripheralIn_iff S hR).mp hper with hd_xy | hd_yx
  · by_cases hxa' : x = a'
    · subst hxa'
      have hyb : y ≠ b := fun h => by
        subst h
        exact hcrooked.2 R hR.1 ⟨hR.1, x, y, hR_ends, Or.inl hdisj_a'b⟩
      have hb_xy := (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar ha'W hbW hdisj_a'b
        hxW hyW hyb).1
      exact disjoint_left.mp hd_xy hb_xy hbW'
    · have ha'_xy := (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar ha'W hbW hdisj_a'b
      hxW hxa' hyW).1
      exact disjoint_left.mp hd_xy ha'_xy ha'W'
  · by_cases hyb' : y = b'
    · subst hyb'
      have hxa : x ≠ a := fun h => by
        subst h
        exact hcrooked.2 R hR.1 ⟨hR.1, x, y, hR_ends, Or.inr hdisj_b'a⟩
      have ha_yx := (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1.symm hW_bar hb'W haW
        hdisj_b'a hyW hxW hxa).1
      exact disjoint_left.mp hd_yx ha_yx haW'
    · have hb'_yx := (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1.symm hW_bar hb'W haW
      hdisj_b'a hyW hyb' hxW).1
      exact disjoint_left.mp hd_yx hb'_yx hb'W'

/-- **Graph Minors IX, (3.4)** (page 48):
"Let $p \ge 2$ be an integer, with $p \ne 3$. If $\mathscr{P}$ is a crooked transaction of
cardinality $\ge p$ then some subset of $\mathscr{P}$ is a crooked transaction of cardinality $p$."
-/
theorem theorem_3_4_proof (S : Society α β) {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    {P_set : Set (Graph α β)} (hcrooked : S.IsCrookedTransaction P_set)
    (hcard : p ≤ P_set.ncard) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = p ∧ S.IsCrookedTransaction P_set' := by
  classical
  have hfin_all : P_set.Finite := by
    by_contra hinf
    have h0 := Set.Infinite.ncard hinf
    omega
  rcases eq_or_lt_of_le hp2 with rfl | hp_gt2
  · obtain ⟨P₁, hP₁, P₂, hP₂, h12, hcr12⟩ :=
      S.exists_crooked_pair_of_nonempty hcrooked ((ncard_pos hfin_all).mp (by omega))
    refine ⟨{P₁, P₂}, ?_, ncard_pair h12, hcr12⟩
    rintro Q (rfl | rfl) <;> assumption
  · have hp4 : 4 ≤ p := by omega
    have hind : ∀ (d : ℕ) {T : Set (Graph α β)},
        T ⊆ P_set → S.IsCrookedTransaction T → T.ncard = p + d →
        ∃ P_set' ⊆ P_set, P_set'.ncard = p ∧ S.IsCrookedTransaction P_set' := by
      intro d
      induction d with
      | zero =>
        intro T hT hcrT hcardT
        exact ⟨T, hT, by omega, hcrT⟩
      | succ d ih =>
        intro T hT hcrT hcardT
        have hT_fin : T.Finite := hfin_all.subset hT
        obtain ⟨P, hPT, hcr_diff⟩ :=
          S.exists_crooked_diff_singleton_of_ncard_ge_five hcrT (by omega)
        have hcard_diff : (T \ {P}).ncard = p + d := by
          rw [ncard_sdiff_singleton_of_mem hPT]
          omega
        exact ih (sdiff_subset.trans hT) hcr_diff hcard_diff
    exact hind (P_set.ncard - p) Subset.rfl hcrooked (by omega)

end Society

end GraphMinor.GM09
