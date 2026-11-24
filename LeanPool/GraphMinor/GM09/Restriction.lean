/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section5a

/-!
# Restriction of a cyclic permutation

`Ω | X` keeps the order of `Ω` on `ΩBar ∩ X`. This file proves that first hits, clockwise lists,
crosses and intervals pass to the restriction, and that the restriction exists.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

namespace CyclicPerm

variable {Ω : CyclicPerm α}

theorem IsRestriction.bar_subset {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') : Ω'.bar ⊆ Ω.bar :=
  h.1 ▸ inter_subset_left

/-- Ifevery step of `Ω'` is the first hit in `Ω'.bar` along `Ω`, then any
first hit in `Y ⊆ Ω'.bar` along `Ω'` is also the first hit in `Y` along `Ω`. -/
theorem firstHitIn_of_forall_firstHitIn {Ω' : CyclicPerm α}
    (hhit : ∀ x ∈ Ω'.bar, Ω.FirstHitIn Ω'.bar x (Ω' x))
    {Y : Set α} (hY : Y ⊆ Ω'.bar) {x y : α} (hx : x ∈ Ω'.bar)
    (h : Ω'.FirstHitIn Y x y) : Ω.FirstHitIn Y x y := by
  rcases h with ⟨m, hm1, hm_eq, hyY, hm_min⟩
  have hind : ∀ (n : ℕ) {z : α}, 1 ≤ n → z ∈ Ω'.bar →
      (∀ i, 1 ≤ i → i < n → (Ω'.toFun^[i]) z ∉ Y) →
      ∃ k : ℕ, 1 ≤ k ∧ (Ω.toFun^[k]) z = (Ω'.toFun^[n]) z ∧
        ∀ j, 1 ≤ j → j < k → (Ω.toFun^[j]) z ∉ Y := by
    intro n
    induction n with
    | zero => intro _ hn; omega
    | succ n ih =>
      intro z _ hz hno
      obtain ⟨k₁, hk₁_pos, hk₁_eq, _, hk₁_min⟩ := hhit z hz
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · refine ⟨k₁, hk₁_pos, by simpa using hk₁_eq, fun j hj1 hjlt hjY => ?_⟩
        exact hk₁_min j hj1 hjlt (hY hjY)
      · have hz' : Ω' z ∈ Ω'.bar := Ω'.toFun_mem hz
        have hno' : ∀ i, 1 ≤ i → i < n → (Ω'.toFun^[i]) (Ω' z) ∉ Y := by
          intro i hi1 hilt
          rw [← Function.iterate_succ_apply]
          exact hno (i + 1) (by omega) (by omega)
        obtain ⟨k₂, hk₂_pos, hk₂_eq, hk₂_min⟩ := ih hn_pos hz' hno'
        refine ⟨k₁ + k₂, by omega, ?_, ?_⟩
        · rw [add_comm, Function.iterate_add_apply, hk₁_eq, hk₂_eq,
            ← Function.iterate_succ_apply]
        · intro j hj1 hjlt hjY
          rcases lt_trichotomy j k₁ with hlt | rfl | hgt
          · exact hk₁_min j hj1 hlt (hY hjY)
          · have h1 : (Ω'.toFun^[1]) z ∈ Y := by simpa [hk₁_eq] using hjY
            exact hno 1 le_rfl (by omega) h1
          · have hj_eq : (Ω.toFun^[j]) z = (Ω.toFun^[j - k₁]) (Ω' z) := by
              rw [← hk₁_eq, ← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hgt)]
            rw [hj_eq] at hjY
            exact hk₂_min (j - k₁) (by omega) (by omega) hjY
  obtain ⟨k, hk1, hk_eq, hk_min⟩ := hind m hm1 hx hm_min
  exact ⟨k, hk1, hk_eq.trans hm_eq, hyY, hk_min⟩

theorem IsRestriction.firstHitIn_iff {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {Y : Set α} (hY : Y ⊆ Ω'.bar) {x y : α} (hx : x ∈ Ω'.bar) :
    Ω'.FirstHitIn Y x y ↔ Ω.FirstHitIn Y x y := by
  refine ⟨firstHitIn_of_forall_firstHitIn h.2 hY hx, fun hΩ => ?_⟩
  have hyY : y ∈ Y := hΩ.mem_set
  have hne : (Ω'.bar ∩ Y).Nonempty := ⟨y, hY hyY, hyY⟩
  obtain ⟨y', hy'⟩ := Ω'.exists_firstHitIn hx hne
  have hΩ' : Ω.FirstHitIn Y x y' :=
    firstHitIn_of_forall_firstHitIn h.2 hY hx hy'
  rwa [hΩ.unique hΩ']

theorem IsRestriction.isClockwiseSeq_iff {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {L : List α} :
    Ω'.IsClockwiseSeq L ↔ {v | v ∈ L} ⊆ Ω'.bar ∧ Ω.IsClockwiseSeq L := by
  unfold IsClockwiseSeq
  constructor
  · rintro ⟨hnodup, hsub, hhit⟩
    have hsub' : {v | v ∈ L} ⊆ Ω'.bar := fun v hv => hsub v hv
    refine ⟨hsub', hnodup, fun v hv => h.bar_subset (hsub v hv), fun i hi => ?_⟩
    exact (h.firstHitIn_iff hsub' (hsub _ (List.getElem_mem hi))).mp (hhit i hi)
  · rintro ⟨hsub, hnodup, _, hhit⟩
    refine ⟨hnodup, fun v hv => hsub hv, fun i hi => ?_⟩
    exact (h.firstHitIn_iff hsub (hsub (List.getElem_mem hi))).mpr (hhit i hi)

theorem IsRestriction.isClockwise3_iff {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {x y z : α} :
    Ω'.IsClockwise3 x y z ↔ x ∈ Ω'.bar ∧ y ∈ Ω'.bar ∧ z ∈ Ω'.bar ∧ Ω.IsClockwise3 x y z := by
  unfold IsClockwise3
  rw [h.isClockwiseSeq_iff]
  have hset : {v | v ∈ ([x, y, z] : List α)} ⊆ Ω'.bar ↔ x ∈ Ω'.bar ∧ y ∈ Ω'.bar ∧ z ∈ Ω'.bar := by
    constructor
    · intro hs
      exact ⟨hs (by simp), hs (by simp), hs (by simp)⟩
    · rintro ⟨hx, hy, hz⟩ v hv
      simp only [mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
  rw [hset]
  tauto

theorem IsRestriction.isClockwise4_iff {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {v₁ v₂ v₃ v₄ : α} :
    Ω'.IsClockwise4 v₁ v₂ v₃ v₄ ↔
      v₁ ∈ Ω'.bar ∧ v₂ ∈ Ω'.bar ∧ v₃ ∈ Ω'.bar ∧ v₄ ∈ Ω'.bar ∧ Ω.IsClockwise4 v₁ v₂ v₃ v₄ := by
  unfold IsClockwise4
  rw [h.isClockwiseSeq_iff]
  have hset : {v | v ∈ ([v₁, v₂, v₃, v₄] : List α)} ⊆ Ω'.bar ↔
      v₁ ∈ Ω'.bar ∧ v₂ ∈ Ω'.bar ∧ v₃ ∈ Ω'.bar ∧ v₄ ∈ Ω'.bar := by
    constructor
    · intro hs
      exact ⟨hs (by simp), hs (by simp), hs (by simp), hs (by simp)⟩
    · rintro ⟨h1, h2, h3, h4⟩ v hv
      simp only [mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
  rw [hset]
  tauto

theorem IsRestriction.crosses_iff {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {s₁ t₁ s₂ t₂ : α} :
    Ω'.Crosses s₁ t₁ s₂ t₂ ↔
      s₁ ∈ Ω'.bar ∧ t₁ ∈ Ω'.bar ∧ s₂ ∈ Ω'.bar ∧ t₂ ∈ Ω'.bar ∧ Ω.Crosses s₁ t₁ s₂ t₂ := by
  change (Ω'.IsClockwise4 s₁ s₂ t₁ t₂ ∨ Ω'.IsClockwise4 t₂ t₁ s₂ s₁) ↔
    s₁ ∈ Ω'.bar ∧ t₁ ∈ Ω'.bar ∧ s₂ ∈ Ω'.bar ∧ t₂ ∈ Ω'.bar ∧
      (Ω.IsClockwise4 s₁ s₂ t₁ t₂ ∨ Ω.IsClockwise4 t₂ t₁ s₂ s₁)
  rw [h.isClockwise4_iff, h.isClockwise4_iff]
  tauto

theorem IsRestriction.interval_eq {X : Set α} {Ω' : CyclicPerm α}
    (h : Ω.IsRestriction X Ω') {a b : α} (ha : a ∈ Ω'.bar) (hb : b ∈ Ω'.bar) :
    Ω'.interval a b = Ω.interval a b ∩ Ω'.bar := by
  ext v
  simp only [interval, mem_ofPred_eq, mem_inter_iff, h.isClockwise3_iff]
  constructor
  · rintro ⟨⟨hv, hne⟩, _, _, _, hcw⟩
    exact ⟨⟨⟨h.bar_subset hv, hne⟩, hcw⟩, hv⟩
  · rintro ⟨⟨⟨_, hne⟩, hcw⟩, hv⟩
    exact ⟨⟨hv, hne⟩, ha, hv, hb, hcw⟩

/-- Existence of a restriction `Ω | X` for any cyclic permutation `Ω` and set `X`. -/
theorem exists_isRestriction (Ω : CyclicPerm α) (X : Set α) :
    ∃ Ω' : CyclicPerm α, Ω.IsRestriction X Ω' := by
  classical
  let W := Ω.bar ∩ X
  let nextW (x : α) : α :=
    if hx : x ∈ W then (Ω.exists_firstHitIn hx.1 ⟨x, hx.1, hx⟩).choose else x
  have hnext_spec : ∀ {x : α}, x ∈ W → Ω.FirstHitIn W x (nextW x) := by
    intro x hx
    simp only [nextW, hx, ↓reduceDIte]
    exact (Ω.exists_firstHitIn hx.1 ⟨x, hx.1, hx⟩).choose_spec
  have hnext_mem : ∀ {x : α}, x ∈ W → nextW x ∈ W := fun hx =>
    CyclicPerm.FirstHitIn.mem_set (hnext_spec hx)
  have hiter_mem : ∀ (m : ℕ) {x : α}, x ∈ W → (nextW^[m]) x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; exact hx
    | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hnext_mem (ih hx)
  have hnext_inj : Set.InjOn nextW W := by
    intro x₁ hx₁ x₂ hx₂ heq
    have h₁ := hnext_spec hx₁
    have h₂ := hnext_spec hx₂
    rw [heq] at h₁
    exact CyclicPerm.FirstHitIn.inj_left hx₁.1 hx₂.1 hx₁ hx₂ h₁ h₂
  have hreach_aux : ∀ (K : ℕ) {x z : α}, x ∈ W → z ∈ W → (Ω.toFun^[K]) x = z →
      ∃ m : ℕ, (nextW^[m]) x = z := by
    intro K
    induction K using Nat.strong_induction_on with
    | ind K ih =>
      intro x z hx hz hK
      rcases Nat.eq_zero_or_pos K with rfl | hK_pos
      · exact ⟨0, hK⟩
      · obtain ⟨k₁, hk₁_pos, hk₁_eq, _, hk₁_min⟩ := hnext_spec hx
        have hk₁_le : k₁ ≤ K := by
          by_contra hgt
          exact hk₁_min K hK_pos (by omega) (hK ▸ hz)
        have hrem : (Ω.toFun^[K - k₁]) (nextW x) = z := by
          have hiter : (Ω.toFun^[k₁]) ((Ω.toFun^[K - k₁]) (nextW x)) = (Ω.toFun^[k₁]) z := by
            rw [← hk₁_eq]
            simp only [← Function.iterate_add_apply]
            rw [Nat.sub_add_cancel hk₁_le, Function.iterate_add_apply, hK]
          exact Ω.injOn_iterate k₁ (Ω.iterate_mem (K - k₁) (hnext_mem hx).1) hz.1 hiter
        obtain ⟨m, hm⟩ := ih (K - k₁) (by omega) (hnext_mem hx) hz hrem
        refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply, hm]
  have horb : ∀ x ∈ W, ∀ y ∈ W, ∃ k : ℕ, (nextW^[k]) x = y := by
    intro x hx y hy
    obtain ⟨K, hK⟩ := Ω.single_orbit x hx.1 y hy.1
    exact hreach_aux K hx hy hK
  have hsurj : Set.SurjOn nextW W W := by
    intro y hy
    obtain ⟨k, hk⟩ := horb (nextW y) (hnext_mem hy) y hy
    refine ⟨(nextW^[k]) y, hiter_mem k hy, ?_⟩
    have hstep : nextW ((nextW^[k]) y) = (nextW^[k + 1]) y :=
      (Function.iterate_succ_apply' nextW k y).symm
    rw [hstep, Function.iterate_succ_apply, hk]
  refine ⟨{
    bar := W
    toFun := nextW
    finite_bar := Ω.finite_bar.subset inter_subset_left
    bijOn := ⟨fun _ hx => hnext_mem hx, hnext_inj, hsurj⟩
    single_orbit := horb
  }, rfl, fun x hx => hnext_spec hx⟩

end CyclicPerm

end GraphMinor.GM09
