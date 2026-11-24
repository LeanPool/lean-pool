/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Lawns

/-!
# Points on a circle in a list, and fences

We list a finite set of points of an `O`-arc by their angle, which gives a cyclic permutation that
agrees with the arc. A fence of this permutation with both sides nonempty is cut by two points of
the arc into two arcs, one for each side. This is how we read the fences of the wall, for the park
of Graph Minors IX, page 68.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

theorem circle_exp_ne {s t : ℝ} (h₁ : s < t) (h₂ : t < s + 2 * Real.pi) :
    Circle.exp s ≠ Circle.exp t := by
  intro h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hpi := Real.pi_pos
  have hneg : (m : ℝ) * (2 * Real.pi) < 0 := by linarith
  have hgt : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith
  have h₃ : (m : ℝ) < 0 := by
    by_contra hn
    push Not at hn
    have := mul_nonneg hn (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  have h₄ : (-1 : ℝ) < m := by
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  have h₅ : m < 0 := by exact_mod_cast h₃
  have h₆ : (-1 : ℤ) < m := by exact_mod_cast h₄
  omega

theorem exists_angle_mem_Ico (u : ℝ) (z : Circle) :
    ∃ t ∈ Ico u (u + 2 * Real.pi), Circle.exp t = z := by
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨toIcoMod hp u (Complex.arg z), toIcoMod_mem_Ico hp u _, ?_⟩
  refine (Circle.exp_eq_exp.mpr ⟨-toIcoDiv hp u (Complex.arg z), ?_⟩).trans (Circle.exp_arg z)
  have := self_sub_toIcoDiv_zsmul hp u (Complex.arg z)
  rw [zsmul_eq_mul] at this
  rw [← this]
  push_cast
  ring

/-- Finitely many points of an `O`-arc, listed in the order of their angles. -/
theorem exists_sorted_list {C : Set EuclideanPlane} (φ : Circle ≃ₜ C) {K : Set α} (hK : K.Finite)
    (hne : K.Nonempty) {ν : α → EuclideanPlane} (hinj : InjOn ν K) (hmem : ∀ v ∈ K, ν v ∈ C) :
    ∃ (L : List α) (θ : α → ℝ), L.Nodup ∧ L ≠ [] ∧ {v | v ∈ L} = K ∧ IsValidAngle L θ ∧
      ∀ v ∈ K, (φ (Circle.exp (θ v))).1 = ν v := by
  classical
  let θ : α → ℝ := fun v => if h : ν v ∈ C then Complex.arg (φ.symm ⟨ν v, h⟩ : Circle) else 0
  have hexp : ∀ v ∈ K, (φ (Circle.exp (θ v))).1 = ν v := by
    intro v hv
    simp only [θ, hmem v hv, ↓reduceDIte, Circle.exp_arg, Homeomorph.apply_symm_apply]
  have hrange : ∀ v ∈ K, -Real.pi < θ v ∧ θ v ≤ Real.pi := by
    intro v hv
    simp only [θ, hmem v hv, ↓reduceDIte]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hθinj : InjOn θ K := fun u hu v hv h => hinj hu hv (by rw [← hexp u hu, ← hexp v hv, h])
  let r : α → α → Prop := fun u v => θ u ≤ θ v
  have : DecidableRel r := Classical.decRel _
  have : Std.Total r := ⟨fun u v => le_total _ _⟩
  have : IsTrans α r := ⟨fun _ _ _ => le_trans⟩
  let L₀ := hK.toFinset.toList
  let L := L₀.insertionSort r
  have hmemL : ∀ v, v ∈ L ↔ v ∈ K := by
    intro v
    simp [L, L₀, List.mem_insertionSort]
  have hnd : L.Nodup := (List.perm_insertionSort r L₀).nodup_iff.mpr (Finset.nodup_toList _)
  have hpw : L.Pairwise r := List.pairwise_insertionSort r L₀
  have hL_ne : L ≠ [] := by
    obtain ⟨v, hv⟩ := hne
    intro h
    have := (hmemL v).mpr hv
    simp [h] at this
  refine ⟨L, θ, hnd, hL_ne, by ext v; exact hmemL v, ⟨?_, ?_⟩, hexp⟩
  · intro i j hi hj hij
    have hle : θ (L[i]'hi) ≤ θ (L[j]'hj) := List.pairwise_iff_getElem.mp hpw i j hi hj hij
    refine lt_of_le_of_ne hle fun h => ?_
    have := hθinj ((hmemL _).mp (List.getElem_mem hi)) ((hmemL _).mp (List.getElem_mem hj)) h
    have h₂ := (List.Nodup.getElem_inj_iff hnd).mp this
    omega
  · intro i hi
    have h₁ := hrange _ ((hmemL _).mp (List.getElem_mem hi))
    have h₂ := hrange _ ((hmemL _).mp (List.getElem_mem (Nat.zero_lt_of_lt hi)))
    linarith

theorem exists_min_max_index (L : List α) (S : Set α) (hne : ∃ v ∈ S, v ∈ L) :
    ∃ (i₀ i₁ : ℕ) (h₀ : i₀ < L.length) (h₁ : i₁ < L.length), i₀ ≤ i₁ ∧ L[i₀] ∈ S ∧ L[i₁] ∈ S ∧
      ∀ (i : ℕ) (hi : i < L.length), L[i] ∈ S → i₀ ≤ i ∧ i ≤ i₁ := by
  classical
  let I : Finset ℕ := (Finset.range L.length).filter fun i => ∃ h : i < L.length, L[i] ∈ S
  have hI : I.Nonempty := by
    obtain ⟨v, hv, hvL⟩ := hne
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvL
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hi, hv⟩⟩
  have h₀ := Finset.min'_mem I hI
  have h₁ := Finset.max'_mem I hI
  obtain ⟨-, h₀', h₀S⟩ := Finset.mem_filter.mp h₀
  obtain ⟨-, h₁', h₁S⟩ := Finset.mem_filter.mp h₁
  refine ⟨I.min' hI, I.max' hI, h₀', h₁', Finset.min'_le _ _ h₁, h₀S, h₁S, fun i hi hS => ?_⟩
  have hm : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hi, hS⟩
  exact ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩

/-- Angles for a block of consecutive list entries and for the rest of the list. -/
theorem block_angles {L : List α} {θ : α → ℝ} (hθ : IsValidAngle L θ) {S T : Set α}
    {i₀ i₁ : ℕ} {h₀ : i₀ < L.length} {h₁ : i₁ < L.length} (h01 : i₀ ≤ i₁)
    (hS : ∀ (i : ℕ) (hi : i < L.length), L[i] ∈ S → i₀ ≤ i ∧ i ≤ i₁)
    (hT : ∀ (j : ℕ) (hj : j < L.length), L[j] ∈ T → j < i₀ ∨ i₁ < j)
    (hTne : ∃ v ∈ T, v ∈ L) :
    ∃ u s₁ s₂ v s₃ s₄ : ℝ, u < s₁ ∧ s₁ ≤ s₂ ∧ s₂ < v ∧ v < s₃ ∧ s₃ ≤ s₄ ∧ s₄ < u + 2 * Real.pi ∧
      (∀ a ∈ S, a ∈ L → ∃ t ∈ Icc s₁ s₂, Circle.exp t = Circle.exp (θ a)) ∧
      (∀ b ∈ T, b ∈ L → ∃ t ∈ Icc s₃ s₄, Circle.exp t = Circle.exp (θ b)) := by
  classical
  have hpi := Real.pi_pos
  have hmono : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i ≤ j →
      θ L[i] ≤ θ L[j] := by
    intro i j hi hj hij
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (hθ.1 i j hi hj h).le
  set s₁ := θ (L[i₀]'h₀) with hs₁
  set s₂ := θ (L[i₁]'h₁) with hs₂
  have h12 : s₁ ≤ s₂ := hmono _ _ h₀ h₁ h01
  have hpos : 0 < L.length := Nat.zero_lt_of_lt h₀
  have hrep : ∀ b ∈ T ∩ {v | v ∈ L}, ∃ t, s₂ < t ∧ t < s₁ + 2 * Real.pi ∧
      Circle.exp t = Circle.exp (θ b) := by
    rintro b ⟨hb, hbL⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hbL
    rcases hT j hj hb with h | h
    · refine ⟨θ L[j] + 2 * Real.pi, ?_, ?_, ?_⟩
      · have h₃ := hθ.2 i₁ h₁
        have h₄ := hmono 0 j hpos hj (Nat.zero_le _)
        linarith
      · have := hθ.1 j i₀ hj h₀ h
        linarith
      · exact Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
    · refine ⟨θ L[j], hθ.1 _ _ h₁ hj h, ?_, rfl⟩
      have h₃ := hθ.2 j hj
      have h₄ := hmono 0 i₀ hpos h₀ (Nat.zero_le _)
      linarith
  choose! τ hτ₁ hτ₂ hτ₃ using hrep
  have hfin : (T ∩ {v | v ∈ L}).Finite := (List.finite_toSet L).subset inter_subset_right
  obtain ⟨b₀, hb₀⟩ := hTne
  have hne : (T ∩ {v | v ∈ L}).Nonempty := ⟨b₀, hb₀⟩
  obtain ⟨b₁, hb₁, hmin⟩ := exists_min_image _ τ hfin hne
  obtain ⟨b₂, hb₂, hmax⟩ := exists_max_image _ τ hfin hne
  have hb₁₂ := hmin b₂ hb₂
  have h₅ := hτ₁ b₁ hb₁
  have h₆ := hτ₂ b₂ hb₂
  refine ⟨(τ b₂ - 2 * Real.pi + s₁) / 2, s₁, s₂, (s₂ + τ b₁) / 2, τ b₁, τ b₂, by linarith, h12,
    by linarith, by linarith, hb₁₂, by linarith, ?_, ?_⟩
  · intro a ha haL
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp haL
    obtain ⟨h₇, h₈⟩ := hS i hi ha
    exact ⟨θ L[i], ⟨hmono _ _ h₀ hi h₇, hmono _ _ hi h₁ h₈⟩, rfl⟩
  · intro b hb hbL
    exact ⟨τ b, ⟨hmin b ⟨hb, hbL⟩, hmax b ⟨hb, hbL⟩⟩, hτ₃ b ⟨hb, hbL⟩⟩

/-- A fence of a listed cyclic permutation with both sides nonempty sits in two arcs of angles. -/
theorem exists_fence_angles {L : List α} (hnd : L.Nodup) (hne : L ≠ []) {θ : α → ℝ}
    (hθ : IsValidAngle L θ) {A B : Set α} (hF : (CyclicPerm.ofNodupList L hnd hne).IsFence A B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ u s₁ s₂ v s₃ s₄ : ℝ, u < s₁ ∧ s₁ ≤ s₂ ∧ s₂ < v ∧ v < s₃ ∧ s₃ ≤ s₄ ∧ s₄ < u + 2 * Real.pi ∧
      (∀ a ∈ A, ∃ t ∈ Icc s₁ s₂, Circle.exp t = Circle.exp (θ a)) ∧
      (∀ b ∈ B, ∃ t ∈ Icc s₃ s₄, Circle.exp t = Circle.exp (θ b)) := by
  obtain ⟨hAb, hBb, hd, -, hno⟩ := hF
  have hAL : ∀ a ∈ A, a ∈ L := fun a ha => hAb ha
  have hBL : ∀ b ∈ B, b ∈ L := fun b hb => hBb hb
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  obtain ⟨i₀, i₁, h₀, h₁, h01, hi₀, hi₁, hSA⟩ := exists_min_max_index L A ⟨a₀, ha₀, hAL a₀ ha₀⟩
  have hnotA : ∀ (j : ℕ) (hj : j < L.length), L[j] ∈ B → j ≠ i₀ ∧ j ≠ i₁ := by
    intro j hj hb
    constructor
    · rintro rfl
      exact disjoint_left.mp hd hi₀ hb
    · rintro rfl
      exact disjoint_left.mp hd hi₁ hb
  have hnoc : ∀ (p q r s : ℕ) (h₁ : p < q) (hq : q < L.length) (h₂ : r < s) (hs : s < L.length),
      L[p] ∈ A → L[q] ∈ A → L[r] ∈ B → L[s] ∈ B →
      ¬ ((p < r ∧ r < q ∧ q < s) ∨ (r < p ∧ p < s ∧ s < q)) := by
    intro p q r s hpq hq hrs hs hp hq' hr hs' hc
    have hne₁ : L[p] ≠ L[q] := fun h => by
      have := (List.Nodup.getElem_inj_iff hnd).mp h
      omega
    have hne₂ : L[r] ≠ L[s] := fun h => by
      have := (List.Nodup.getElem_inj_iff hnd).mp h
      omega
    exact hno _ hp _ hq' hne₁ _ hr _ hs' hne₂
      ((CyclicPerm.ofNodupList_crosses_iff L hnd hne hpq hq hrs hs).mpr hc)
  by_cases hin : ∃ (j : ℕ) (hj : j < L.length), L[j] ∈ B ∧ i₀ < j ∧ j < i₁
  · obtain ⟨j, hj, hjB, hj₀, hj₁⟩ := hin
    have hinside : ∀ (j' : ℕ) (hj' : j' < L.length), L[j'] ∈ B → i₀ < j' ∧ j' < i₁ := by
      intro j' hj' hb
      obtain ⟨h₂, h₃⟩ := hnotA j' hj' hb
      by_contra hn
      have hcases : j' < i₀ ∨ i₁ < j' := by omega
      rcases hcases with h | h
      · exact hnoc i₀ i₁ j' j (by omega) h₁ (by omega) hj hi₀ hi₁ hb hjB (Or.inr ⟨h, by omega,
          by omega⟩)
      · exact hnoc i₀ i₁ j j' (by omega) h₁ (by omega) hj' hi₀ hi₁ hjB hb (Or.inl ⟨by omega,
          by omega, h⟩)
    obtain ⟨j₀, j₁, h₂, h₃, h23, hj₀B, hj₁B, hSB⟩ := exists_min_max_index L B ⟨b₀, hb₀, hBL b₀ hb₀⟩
    have hblock : ∀ (i : ℕ) (hi : i < L.length), L[i] ∈ A → i < j₀ ∨ j₁ < i := by
      intro i hi ha
      have hne₁ : i ≠ j₀ := by
        rintro rfl
        exact disjoint_left.mp hd ha hj₀B
      have hne₂ : i ≠ j₁ := by
        rintro rfl
        exact disjoint_left.mp hd ha hj₁B
      by_contra hn
      have h₄ := (hinside j₀ h₂ hj₀B).1
      have h₅ := hSA i hi ha
      exact hnoc i₀ i j₀ j₁ (by omega) hi (by omega) h₃ hi₀ ha hj₀B hj₁B
        (Or.inl ⟨by omega, by omega, by omega⟩)
    obtain ⟨u, s₁, s₂, v, s₃, s₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
      block_angles (S := B) (T := A) hθ (h₀ := h₂) (h₁ := h₃) h23 hSB hblock
        ⟨a₀, ha₀, hAL a₀ ha₀⟩
    refine ⟨v, s₃, s₄, u + 2 * Real.pi, s₁ + 2 * Real.pi, s₂ + 2 * Real.pi, by linarith, h₉, h₁₀,
      by linarith, by linarith, by linarith, fun a ha => h₁₂ a ha (hAL a ha), fun b hb => ?_⟩
    obtain ⟨t, ⟨ht₁, ht₂⟩, ht⟩ := h₁₁ b hb (hBL b hb)
    refine ⟨t + 2 * Real.pi, ⟨by linarith, by linarith⟩, ?_⟩
    rw [← ht]
    exact Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
  · push Not at hin
    have hblock : ∀ (j : ℕ) (hj : j < L.length), L[j] ∈ B → j < i₀ ∨ i₁ < j := by
      intro j hj hb
      obtain ⟨h₂, h₃⟩ := hnotA j hj hb
      by_contra hn
      have h₄ := hin j hj hb (by omega)
      omega
    obtain ⟨u, s₁, s₂, v, s₃, s₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
      block_angles (S := A) (T := B) hθ (h₀ := h₀) (h₁ := h₁) h01 hSA hblock
        ⟨b₀, hb₀, hBL b₀ hb₀⟩
    exact ⟨u, s₁, s₂, v, s₃, s₄, h₅, h₆, h₇, h₈, h₉, h₁₀, fun a ha => h₁₁ a ha (hAL a ha),
      fun b hb => h₁₂ b hb (hBL b hb)⟩

/-- Two arcs of a circle in the plane, given by angles, with two cut points between them. -/
structure IsCircleCut (C X Y : Set EuclideanPlane) (p q : EuclideanPlane) : Prop where
  compact_X : IsCompact X
  compact_Y : IsCompact Y
  conn_X : IsConnected X
  conn_Y : IsConnected Y
  disj : Disjoint X Y
  X_sub : X ⊆ C
  Y_sub : Y ⊆ C
  p_mem : p ∈ C
  q_mem : q ∈ C
  p_X : p ∉ X
  p_Y : p ∉ Y
  q_X : q ∉ X
  q_Y : q ∉ Y
  sep : ∀ J : Set EuclideanPlane, IsPreconnected J → J ⊆ C → p ∉ J → q ∉ J →
    (J ∩ X).Nonempty → (J ∩ Y).Nonempty → False

theorem exists_isCircleCut {C : Set EuclideanPlane} (φ : Circle ≃ₜ C) {u s₁ s₂ v s₃ s₄ : ℝ}
    (h₁ : u < s₁) (h₂ : s₁ ≤ s₂) (h₃ : s₂ < v) (h₄ : v < s₃) (h₅ : s₃ ≤ s₄)
    (h₆ : s₄ < u + 2 * Real.pi) :
    IsCircleCut C ((fun t => (φ (Circle.exp t)).1) '' Icc s₁ s₂)
      ((fun t => (φ (Circle.exp t)).1) '' Icc s₃ s₄)
      (φ (Circle.exp v)).1 (φ (Circle.exp u)).1 := by
  let f : ℝ → EuclideanPlane := fun t => (φ (Circle.exp t)).1
  have hf : Continuous f := continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
  have hinj : ∀ {s t : ℝ}, s < t → t < s + 2 * Real.pi → f s ≠ f t := by
    intro s t hst hts h
    exact circle_exp_ne hst hts (φ.injective (Subtype.ext h))
  have hmem : ∀ t, f t ∈ C := fun t => (φ _).2
  have hper : f (u + 2 * Real.pi) = f u := by
    change (φ _).1 = (φ _).1
    congr 2
    exact Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
  refine ⟨isCompact_Icc.image hf, isCompact_Icc.image hf,
    (isConnected_Icc h₂).image _ hf.continuousOn, (isConnected_Icc h₅).image _ hf.continuousOn,
    ?_, ?_, ?_, hmem _, hmem _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    rintro _ ⟨s, ⟨hs₁, hs₂⟩, rfl⟩ ⟨t, ⟨ht₁, ht₂⟩, ht⟩
    exact hinj (s := s) (t := t) (by linarith) (by linarith) ht.symm
  · rintro _ ⟨t, -, rfl⟩
    exact hmem t
  · rintro _ ⟨t, -, rfl⟩
    exact hmem t
  · rintro ⟨t, ⟨ht₁, ht₂⟩, ht⟩
    exact hinj (s := t) (t := v) (by linarith) (by linarith) ht
  · rintro ⟨t, ⟨ht₁, ht₂⟩, ht⟩
    exact hinj (s := v) (t := t) (by linarith) (by linarith) ht.symm
  · rintro ⟨t, ⟨ht₁, ht₂⟩, ht⟩
    exact hinj (s := u) (t := t) (by linarith) (by linarith) ht.symm
  · rintro ⟨t, ⟨ht₁, ht₂⟩, ht⟩
    have hq : f t = f (u + 2 * Real.pi) := Eq.trans ht hper.symm
    exact hinj (s := t) (t := u + 2 * Real.pi) (by linarith) (by linarith) hq
  · intro J hJ hJC hp hq ⟨x, hxJ, hxX⟩ ⟨y, hyJ, hyY⟩
    have hT₁ : IsClosed (f '' Icc u v) := (isCompact_Icc.image hf).isClosed
    have hT₂ : IsClosed (f '' Icc v (u + 2 * Real.pi)) := (isCompact_Icc.image hf).isClosed
    have hsub : J ⊆ f '' Icc u v ∪ f '' Icc v (u + 2 * Real.pi) := by
      intro w hw
      obtain ⟨t, ⟨ht₁, ht₂⟩, ht⟩ := exists_angle_mem_Ico u (φ.symm ⟨w, hJC hw⟩)
      have hwf : f t = w := by
        change (φ _).1 = w
        rw [ht, Homeomorph.apply_symm_apply]
      rcases le_total t v with h | h
      · exact Or.inl ⟨t, ⟨ht₁, h⟩, hwf⟩
      · exact Or.inr ⟨t, ⟨h, ht₂.le⟩, hwf⟩
    have hx₁ : x ∈ f '' Icc u v := by
      obtain ⟨t, ⟨ht₁, ht₂⟩, ht⟩ := hxX
      exact ⟨t, ⟨by linarith, by linarith⟩, ht⟩
    have hy₂ : y ∈ f '' Icc v (u + 2 * Real.pi) := by
      obtain ⟨t, ⟨ht₁, ht₂⟩, ht⟩ := hyY
      exact ⟨t, ⟨by linarith, by linarith⟩, ht⟩
    obtain ⟨w, hwJ, ⟨s, ⟨hs₁, hs₂⟩, hsw⟩, ⟨t, ⟨ht₁, ht₂⟩, htw⟩⟩ :=
      isPreconnected_closed_iff.mp hJ _ _ hT₁ hT₂ hsub ⟨x, hxJ, hx₁⟩ ⟨y, hyJ, hy₂⟩
    have ht : f t = f s := htw.trans hsw.symm
    have hwJ' : f s ∈ J := hsw ▸ hwJ
    have hsu : s ≠ u := by
      rintro rfl
      exact hq hwJ'
    have hsv : s ≠ v := by
      rintro rfl
      exact hp hwJ'
    have htv : t ≠ v := by
      rintro rfl
      have h' : f t ∈ J := ht.symm ▸ hwJ'
      exact hp h'
    have htu : t ≠ u + 2 * Real.pi := by
      rintro rfl
      have h' : f u ∈ J := (ht.symm.trans hper) ▸ hwJ'
      exact hq h'
    have hs₃ : u < s := lt_of_le_of_ne hs₁ (Ne.symm hsu)
    have hs₄ : s < v := lt_of_le_of_ne hs₂ hsv
    have ht₃ : v < t := lt_of_le_of_ne ht₁ (Ne.symm htv)
    have ht₄ : t < u + 2 * Real.pi := lt_of_le_of_ne ht₂ htu
    exact hinj (s := s) (t := t) (by linarith) (by linarith) ht.symm

/-- The cyclic permutation of a finite set of vertices drawn in an `O`-arc. Its fences with both
sides nonempty are cut by two points of the arc. -/
theorem exists_cyclicPerm_of_oArc {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    {C : Set EuclideanPlane} (φ : Circle ≃ₜ C) {K : Set α} (hK : K ⊆ V(G)) (hfin : K.Finite)
    (hmem : ∀ v ∈ K, vertexPt Γ v ∈ C) :
    ∃ Ω : CyclicPerm α, Ω.bar = K ∧ DrawingAgreesWithOArcHomeo Γ Ω C φ ∧
      ∀ A B : Set α, Ω.IsFence A B → A.Nonempty → B.Nonempty →
        ∃ X Y p q, IsCircleCut C X Y p q ∧ (∀ a ∈ A, vertexPt Γ a ∈ X) ∧
          (∀ b ∈ B, vertexPt Γ b ∈ Y) := by
  classical
  have hsing : ∀ v ∈ K, graphDrawingVertexSet Γ v = {vertexPt Γ v} := fun v hv =>
    vertexSet_eq_vertexPt Γ (hK hv)
  rcases K.eq_empty_or_nonempty with rfl | hne
  · refine ⟨⟨∅, id, finite_empty, ⟨fun _ h => h, injOn_empty _, fun _ h => (h : _).elim⟩,
      fun _ h => h.elim⟩, rfl, ⟨fun v hv => hv.elim, fun v₁ _ _ h => ?_⟩, fun A B hF hA => ?_⟩
    · exact (CyclicPerm.isClockwise3_iff.mp h).2.2.2.1.elim
    · obtain ⟨a, ha⟩ := hA
      exact (hF.1 ha).elim
  obtain ⟨L, θ, hnd, hLne, hset, hθ, hexp⟩ := exists_sorted_list φ hfin hne
    (ν := vertexPt Γ) ((vertexPt_injOn Γ).mono hK) hmem
  have hbar : (CyclicPerm.ofNodupList L hnd hLne).bar = K := hset
  refine ⟨CyclicPerm.ofNodupList L hnd hLne, hbar, ?_, ?_⟩
  · refine drawingAgrees_of_angles (CyclicPerm.isOrbitList_ofNodupList L hnd hLne) hθ φ ?_ ?_
    · intro v hv
      rw [hsing v (hbar ▸ hv), singleton_subset_iff]
      exact hmem v (hbar ▸ hv)
    · intro v hv
      rw [hsing v (hbar ▸ hv), hexp v (hbar ▸ hv)]
      rfl
  · intro A B hF hA hB
    obtain ⟨u, s₁, s₂, v, s₃, s₄, h₁, h₂, h₃, h₄, h₅, h₆, hAt, hBt⟩ :=
      exists_fence_angles hnd hLne hθ hF hA hB
    refine ⟨_, _, _, _, exists_isCircleCut φ h₁ h₂ h₃ h₄ h₅ h₆, fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨t, ht, hte⟩ := hAt a ha
      refine ⟨t, ht, ?_⟩
      change (φ (Circle.exp t)).1 = _
      rw [hte]
      exact hexp a (hbar ▸ hF.1 ha)
    · obtain ⟨t, ht, hte⟩ := hBt b hb
      refine ⟨t, ht, ?_⟩
      change (φ (Circle.exp t)).1 = _
      rw [hte]
      exact hexp b (hbar ▸ hF.2.1 hb)

end GraphMinor.GM09
