/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureCut

/-!
# Arcs around a cuff

Finitely many arcs cover a cuff and meet only at their ends. Lifted to the line, they are intervals
that tile the line, with
period one. Sorting them gives the order of the arcs around the cuff (`exists_tile_order`,
`exists_cuff_order`). Then `cc`
joins a sequence of paths into one path, and `pos` says where each path sits in the join.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

private theorem sorted_fractional_parts_span_lt_one
    {J : Type*}
    (l' : J → ℝ)
    (hl01 : ∀ (s : J), l' s ∈ Ico 0 1)
    (T : Finset ℝ)
    (hk0 : 0 < (T.card))
    (o : Fin T.card ↪o ℝ)
    (sq : ℕ → J)
    (hsq : ∀ (i : ℕ) (h : i < (T.card)), l' (sq i) = o ⟨i, h⟩)
    (i : ℕ)
    (h : i < (T.card)) :
    o ⟨i, h⟩ < o ⟨0, hk0⟩ + 1 := by
  let k := T.card
  have h₁ := (hl01 (sq i)).2
  have h₂ := (hl01 (sq 0)).1
  rw [hsq i h] at h₁
  rw [hsq 0 hk0] at h₂
  linarith

/-- Intervals that tile the line with period one, sorted by their left ends. -/
theorem exists_tile_order {J : Type*} [Finite J] [Nonempty J] (l r : J → ℝ) (hlr : ∀ s, l s < r s)
    (hdisj : ∀ (s s' : J) (n n' : ℤ) (x : ℝ), x ∈ Ioo (l s + n) (r s + n) → x ∈ Ioo (l s' + n')
      (r s' + n') → s = s' ∧ n = n')
    (hcov : ∀ x : ℝ, ∃ (s : J) (n : ℤ), x ∈ Icc (l s + n) (r s + n)) :
    ∃ (k : ℕ) (sq : ℕ → J) (n : ℕ → ℤ), 0 < k ∧ (∀ s, ∃ i < k, sq i = s) ∧ (∀ i < k, ∀ j < k, sq i
      = sq j → i = j) ∧
      (∀ i, i + 1 < k → r (sq i) + n i = l (sq (i + 1)) + n (i + 1)) ∧ r (sq (k - 1)) + n (k - 1)
        = l (sq 0) + n 0 + 1 := by
  classical
  have := Fintype.ofFinite J
  set N : J → ℤ := fun s ↦ -⌊l s⌋ with hN
  set l' : J → ℝ := fun s ↦ l s + N s with hl'
  set r' : J → ℝ := fun s ↦ r s + N s with hr'
  have hl01 : ∀ s, l' s ∈ Ico (0 : ℝ) 1 := fun s ↦ by
    have h₁ := Int.floor_le (l s)
    have h₂ := Int.lt_floor_add_one (l s)
    simp only [hl', hN, Int.cast_neg]
    constructor <;> linarith
  have hinj : Injective l' := fun s s' he ↦ by
    have h₁ := hlr s
    have h₂ := hlr s'
    set p := l' s with hp
    set q := min (r' s) (r' s') with hq
    have hq₁ : p < q := by
      apply lt_min
      · simp only [hp, hl', hr']
        linarith
      · have he' : p = l' s' := he
        rw [he']
        simp only [hl', hr']
        linarith
    have hm₁ : (p + q) / 2 ∈ Ioo (l s + N s) (r s + N s) := by
      constructor
      · simp only [hp, hl'] at hq₁ ⊢
        linarith
      · have : q ≤ r' s := min_le_left _ _
        simp only [hr'] at this
        linarith
    have hm₂ : (p + q) / 2 ∈ Ioo (l s' + N s') (r s' + N s') := ⟨by
      have : p = l s' + N s' := he
      linarith, by
      have : q ≤ r' s' := min_le_right _ _
      simp only [hr'] at this
      linarith⟩
    exact (hdisj s s' _ _ _ hm₁ hm₂).1
  let T : Finset ℝ := Finset.univ.image l'
  have hcard : T.card = Fintype.card J := Finset.card_image_of_injective _ hinj
  set k := T.card with hk
  have hk0 : 0 < k := by
    rw [hcard]
    exact Fintype.card_pos
  let o := T.orderEmbOfFin rfl
  have hoT : ∀ i, ∃ s, l' s = o i := fun i ↦ by
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (T.orderEmbOfFin_mem rfl i)
    exact ⟨s, hs⟩
  have hTo : ∀ s, ∃ i, o i = l' s := fun s ↦ by
    have h₁ : l' s ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ s)
    have h₂ : l' s ∈ Set.range o := by
      rw [Finset.range_orderEmbOfFin]
      exact h₁
    exact h₂
  choose S hS using hoT
  let sq : ℕ → J := fun i ↦ if h : i < k then S ⟨i, h⟩ else Classical.arbitrary J
  let n : ℕ → ℤ := fun i ↦ N (sq i)
  have hsq : ∀ i (h : i < k), l' (sq i) = o ⟨i, h⟩ := fun i h ↦ by
    simp only [sq, h, dite_eq_left]
    exact hS _
  have hx : ∀ i (h : i < k), l (sq i) + n i = o ⟨i, h⟩ := fun i h ↦ hsq i h
  have hsub : ∀ {i j} (hi : i < k) (hj : j < k), i < j → o ⟨i, hi⟩ < o ⟨j, hj⟩
    := fun hi hj h ↦ o.strictMono h
  have hinjS : ∀ i < k, ∀ j < k, sq i = sq j → i = j := fun i hi j hj he ↦ by
    have h₁ := hsq i hi
    rw [he, hsq j hj] at h₁
    exact Fin.mk.inj_iff.mp (o.injective h₁).symm
  have hxlt : ∀ i (h : i < k), l (sq i) + n i < r (sq i) + n i := fun i _ ↦ by linarith [hlr (sq i)]
  have h0 : ∀ i (h : i < k), o ⟨0, hk0⟩ ≤ o ⟨i, h⟩ := fun i h ↦ o.monotone (Fin.mk_le_mk.mpr
    (Nat.zero_le i))
  have hlast : ∀ i (h : i < k), o ⟨i, h⟩ < o ⟨0, hk0⟩ + 1 := fun i h ↦ by
    exact sorted_fractional_parts_span_lt_one (J := J) l' hl01 T hk0 o sq hsq i h
  have hover : ∀ {s s' : J} {m m' : ℤ} {b : ℝ}, s ≠ s' → l s + m < l s' + m' → l s' + m' < r s + m
    → r s' + m' ≤ b → l s' + m' = b → False := by
    intro s s' m m' b _ _ _ h₃ h₄
    linarith [hlr s']
  have hle : ∀ {s s' : J} {m m' : ℤ}, (s, m) ≠ (s', m') → l s + m ≤ l s' + m' → r s + m ≤ l s' + m'
    ∨ l s + m = l s' + m' := by
    intro s s' m m' hne h₁
    by_contra hcon
    push Not at hcon
    obtain ⟨h₂, h₃⟩ := hcon
    have h₄ : l s + m < l s' + m' := lt_of_le_of_ne h₁ h₃
    set q := min (r s + m) (r s' + m') with hq
    have hq₁ : l s' + m' < q := lt_min h₂ (by linarith [hlr s'])
    have hq₂ := min_le_left (r s + m) (r s' + m')
    have hq₃ := min_le_right (r s + m) (r s' + m')
    have hp₁ : (l s' + m' + q) / 2 ∈ Ioo (l s + m) (r s + m) := ⟨by linarith, by linarith⟩
    have hp₂ : (l s' + m' + q) / 2 ∈ Ioo (l s' + (m' : ℤ)) (r s' + m') := ⟨by linarith, by linarith⟩
    obtain ⟨rfl, rfl⟩ := hdisj _ _ _ _ _ hp₁ hp₂
    exact hne rfl
  set xn : ℕ → ℝ := fun i ↦ if h : i + 1 < k then o ⟨i + 1, h⟩ else o ⟨0, hk0⟩ + 1 with hxn
  have hyle : ∀ i (h : i < k), r (sq i) + n i ≤ xn i := fun i h ↦ by
    by_cases h₁ : i + 1 < k
    · simp only [hxn, h₁, dite_eq_left]
      have h₂ := hsub h h₁ (Nat.lt_succ_self i)
      have h₃ : (sq i, n i) ≠ (sq (i + 1), n (i + 1)) := fun he ↦ by
        have := hinjS i h (i + 1) h₁ (Prod.mk.inj he).1
        omega
      rw [← hx i h, ← hx _ h₁] at h₂
      rw [← hx _ h₁]
      exact (hle h₃ h₂.le).resolve_right h₂.ne
    · simp only [hxn, h₁, dite_eq_right, not_false_eq_true]
      have h₂ := hlast i h
      have e₀ := hx 0 hk0
      have h₃ : ((sq i, n i) : J × ℤ) ≠ (sq 0, n 0 + 1) := fun he ↦ by
        have h₄ := (Prod.mk.inj he).2
        have h₅ := (Prod.mk.inj he).1
        have h₆ := hinjS i h 0 hk0 h₅
        subst h₆
        omega
      have e₁ : l (sq i) + n i < l (sq 0) + ((n 0 + 1 : ℤ) : ℝ) := by
        rw [hx i h]
        push_cast
        linarith
      have := (hle h₃ e₁.le).resolve_right e₁.ne
      push_cast at this
      linarith
  have hgap : ∀ i (h : i < k), xn i ≤ r (sq i) + n i := fun i h ↦ by
    by_contra hcon
    push Not at hcon
    set p := (r (sq i) + n i + xn i) / 2 with hp
    have hp₁ : r (sq i) + n i < p := by linarith
    have hp₂ : p < xn i := by linarith
    have hxn0 : ∀ j (hj : j < k), xn j ≤ o ⟨0, hk0⟩ + 1 := fun j hj ↦ by
      by_cases h₁ : j + 1 < k
      · simp only [hxn, h₁, dite_eq_left]
        exact (hlast _ h₁).le
      · simp only [hxn, h₁, dite_eq_right, not_false_eq_true, le_refl]
    have hy0 := fun j hj ↦ (hyle j hj).trans (hxn0 j hj)
    obtain ⟨s, m, hs₁, hs₂⟩ := hcov p
    obtain ⟨t, ht⟩ := hTo s
    have htk : t.1 < k := t.2
    have ht₁ : sq t.1 = s := by
      apply hinj
      rw [hsq t.1 htk]
      exact ht
    have ht₂ : (m : ℝ) = (m - n t.1 : ℤ) + n t.1 := by push_cast; ring
    rw [← ht₁] at hs₁ hs₂
    set M : ℤ := m - N (sq t.1) with hM
    have hs₁' : o t + M ≤ p := by
      have e := hx t.1 htk
      have e₂ : (m : ℝ) = M + n t.1 := by simp only [hM, n]; push_cast; ring
      rw [e₂] at hs₁
      have : o ⟨t.1, htk⟩ = o t := rfl
      linarith
    have hs₂' : p ≤ r (sq t.1) + n t.1 + M := by
      have e₂ : (m : ℝ) = M + n t.1 := by simp only [hM, n]; push_cast; ring
      rw [e₂] at hs₂
      linarith
    have hp₃ : o ⟨0, hk0⟩ < p := by
      have h₁ := h0 i h
      have h₂ := hxlt i h
      rw [hx i h] at h₂
      linarith
    have hp₄ : p < o ⟨0, hk0⟩ + 1 := by linarith [hxn0 i h]
    have hM₀ : M = 0 := by
      have h₁ : M < 1 := by
        by_contra hc
        have h₂ : (1 : ℝ) ≤ M := by exact_mod_cast (not_lt.mp hc)
        have h₃ := h0 t.1 htk
        have : o ⟨t.1, htk⟩ = o t := rfl
        linarith
      have h₂ : -1 < M := by
        by_contra hc
        have h₂ : (M : ℝ) ≤ -1 := by exact_mod_cast (not_lt.mp hc)
        have h₃ := hy0 t.1 htk
        linarith
      omega
    rw [hM₀] at hs₁' hs₂'
    simp only [Int.cast_zero, add_zero] at hs₁' hs₂'
    rcases lt_trichotomy t.1 i with h₁ | h₁ | h₁
    · have h₂ := hyle t.1 htk
      have h₃ : xn t.1 ≤ o ⟨i, h⟩ := by
        have h₄ : t.1 + 1 < k := by omega
        simp only [hxn, h₄, dite_eq_left]
        exact o.monotone (Fin.mk_le_mk.mpr h₁)
      have h₄ := hxlt i h
      rw [hx i h] at h₄
      linarith
    · rw [h₁] at hs₂'
      linarith
    · have h₄ : i + 1 < k := by omega
      have h₂ : xn i ≤ o t := by
        simp only [hxn, h₄, dite_eq_left]
        exact o.monotone (Fin.mk_le_mk.mpr h₁)
      linarith
  have heq : ∀ i (h : i < k), r (sq i) + n i = xn i := fun i h ↦ le_antisymm (hyle i h) (hgap i h)
  refine ⟨k, sq, n, hk0, fun s ↦ ?_, hinjS, fun i hi ↦ ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hTo s
    refine ⟨t.1, t.2, hinj ?_⟩
    rw [hsq t.1 t.2]
    exact ht
  · rw [heq i (by omega), hx _ hi]
    simp only [hxn, hi, dite_eq_left]
  · have hk1 : k - 1 < k := by omega
    rw [heq _ hk1, hx 0 hk0]
    have h₁ : ¬ (k - 1 + 1 < k) := by omega
    simp only [hxn, h₁, dite_eq_right, not_false_eq_true]

/-- Join `k` paths of a sequence, each on `[0, 1]`, into one path. -/
noncomputable def cc {T : Type*} : ℕ → (ℕ → ℝ → T) → ℝ → T
  | 0, M => M 0
  | 1, M => M 0
  | k + 2, M => conc2 (M 0) (cc (k + 1) fun i ↦ M (i + 1))

/-- Where the path `i` sits in the join of `k` paths. -/
noncomputable def pos : ℕ → ℕ → ℝ → ℝ
  | 0, _, u => u
  | 1, _, u => u
  | _ + 2, 0, u => u / 2
  | k + 2, i + 1, u => (1 + pos (k + 1) i u) / 2

theorem pos_mem : ∀ (k i : ℕ) {u : ℝ}, u ∈ Icc (0 : ℝ) 1 → pos k i u ∈ Icc (0 : ℝ) 1
  | 0, _, _, hu => hu
  | 1, _, _, hu => hu
  | _ + 2, 0, _, hu => ⟨by simp only [pos]; linarith [hu.1], by simp only [pos]; linarith [hu.2]⟩
  | k + 2, i + 1, _, hu => by
    have := pos_mem (k + 1) i hu
    exact ⟨by simp only [pos]; linarith [this.1], by simp only [pos]; linarith [this.2]⟩

section cc

variable {T : Type*}

theorem cc_zero : ∀ (k : ℕ) (M : ℕ → ℝ → T), cc k M 0 = M 0 0
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, M => by
    simp only [cc]
    exact conc2_zero

theorem cc_one : ∀ (k : ℕ) (M : ℕ → ℝ → T), (∀ i, i + 1 < k → M i 1 = M (i + 1) 0) → cc k M 1 = M
  (k - 1) 1
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | k + 2, M, h => by
    simp only [cc]
    rw [conc2_one (by rw [cc_zero]; exact h 0 (by omega)), cc_one (k + 1) _ fun i hi ↦ h (i + 1)
      (by omega)]
    rfl

theorem cc_pos : ∀ (k : ℕ) (M : ℕ → ℝ → T), (∀ i, i + 1 < k → M i 1 = M (i + 1) 0)
  → ∀ i < k, ∀ u ∈ Icc (0 : ℝ) 1, cc k M (pos k i u) = M i u
  | 0, _, _, _, hi, _, _ => by omega
  | 1, _, _, 0, _, _, _ => rfl
  | 1, _, _, _ + 1, hi, _, _ => by omega
  | _ + 2, _, _, 0, _, _, hu => by
    simp only [cc, pos]
    exact conc2_left hu
  | k + 2, M, h, i + 1, hi, u, hu => by
    simp only [cc, pos]
    rw [conc2_right (by rw [cc_zero]; exact h 0 (by omega)) (pos_mem (k + 1) i hu), cc_pos
      (k + 1) _ (fun i hi ↦ h (i + 1) (by omega)) i (by omega) u hu]

theorem continuousOn_cc [TopologicalSpace T] : ∀ (k : ℕ) (M : ℕ → ℝ → T), (∀ i, i + 1 < k → M i 1
  = M (i + 1) 0) → (∀ i < k, ContinuousOn (M i) (Icc 0 1)) → 0 < k →
    ContinuousOn (cc k M) (Icc 0 1)
  | 0, _, _, _, h => by omega
  | 1, _, _, h, _ => h 0 (by omega)
  | k + 2, M, h, hc, _ => by
    simp only [cc]
    exact continuousOn_conc2 (hc 0 (by omega)) (continuousOn_cc (k + 1) _ (fun i hi ↦ h (i + 1)
      (by omega)) (fun i hi ↦ hc (i + 1) (by omega)) (by omega))
      (by rw [cc_zero]; exact h 0 (by omega))

theorem strictMonoOn_cc : ∀ (k : ℕ) (M : ℕ → ℝ → ℝ), (∀ i, i + 1 < k → M i 1 = M (i + 1) 0) →
  (∀ i < k, StrictMonoOn (M i) (Icc 0 1)) → 0 < k →
    StrictMonoOn (cc k M) (Icc 0 1)
  | 0, _, _, _, h => by omega
  | 1, _, _, h, _ => h 0 (by omega)
  | k + 2, M, h, hc, _ => by
    simp only [cc]
    exact strictMonoOn_conc2 (hc 0 (by omega)) (strictMonoOn_cc (k + 1) _ (fun i hi ↦ h (i + 1)
      (by omega)) (fun i hi ↦ hc (i + 1) (by omega)) (by omega))
      (by rw [cc_zero]; exact h 0 (by omega))

end cc

theorem ofs_false' : ofs false = fun u : ℝ ↦ 1 - u := funext ofs_false

theorem ofs_true' : ofs true = fun u : ℝ ↦ u := funext ofs_true

/-- **The order of the arcs around a cuff.** -/
theorem exists_cuff_order {Y : Type*} [TopologicalSpace Y] {C : Set Y}
  (φ : Circle ≃ₜ C) {J : Type*} [Finite J] [Nonempty J] {γ : J → ℝ → Y}
    (hc : ∀ s, ContinuousOn (γ s) (Icc 0 1)) (hi : ∀ s, InjOn (γ s) (Icc 0 1)) (hC : ∀ s, ∀ u ∈ Icc
      (0 : ℝ) 1, γ s u ∈ C)
    (hd : ∀ s s', ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, γ s u = γ s' v → s = s' ∧ u = v)
      (hcov : ∀ y ∈ C, ∃ s, ∃ u ∈ Icc (0 : ℝ) 1, γ s u = y) :
    ∃ (k : ℕ) (sq : ℕ → J) (fl : ℕ → Bool) (m : ℕ → ℝ → ℝ), 0 < k ∧ (∀ s, ∃ i < k, sq i = s) ∧
      (∀ i < k, ∀ j < k, sq i = sq j → i = j) ∧
      (∀ i < k, ContinuousOn (m i) (Icc 0 1) ∧ StrictMonoOn (m i) (Icc 0 1) ∧ ∀ u ∈ Icc (0 : ℝ) 1,
        (φ (ee (m i u))).1 = γ (sq i) (ofs (fl i) u)) ∧
      (∀ i, i + 1 < k → m i 1 = m (i + 1) 0) ∧ m (k - 1) 1 = m 0 0 + 1 := by
  have hlift := fun s ↦ exists_lift φ (hc s) (hC s)
  choose m₀ hm₀ hm₁ using hlift
  have hdir : ∀ s, ∃ e : Bool, StrictMonoOn (fun u ↦ m₀ s (ofs e u)) (Icc 0 1) := fun s ↦ by
    have hinj : InjOn (fun u ↦ ee (m₀ s u)) (Icc 0 1) := fun u hu v hv he ↦ by
      apply hi s hu hv
      rw [← hm₁ s u hu, ← hm₁ s v hv]
      simp only at he
      rw [he]
    rcases lift_mono (hm₀ s) hinj with h | h
    · refine ⟨true, fun u hu v hv huv ↦ ?_⟩
      simpa [ofs] using h hu hv huv
    · refine ⟨false, fun u hu v hv huv ↦ ?_⟩
      have h₁ := h (ofs_mem (e := false) hv) (ofs_mem (e := false) hu)
        (by rw [ofs_false, ofs_false]; linarith)
      exact h₁
  choose e he using hdir
  set M : J → ℝ → ℝ := fun s u ↦ m₀ s (ofs (e s) u) with hM
  have hM₁ : ∀ s, ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (M s u))).1 = γ s (ofs (e s) u)
    := fun s u hu ↦ hm₁ s _ (ofs_mem hu)
  have hMc : ∀ s, ContinuousOn (M s) (Icc 0 1) := fun s ↦ by
    have h₁ : Continuous (ofs (e s)) := by
      cases e s
      · simp only [ofs_false']
        fun_prop
      · simp only [ofs_true']
        fun_prop
    exact (hm₀ s).comp h₁.continuousOn fun u hu ↦ ofs_mem hu
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hlr : ∀ s, M s 0 < M s 1 := fun s ↦ he s h01 h11 zero_lt_one
  have hmid : ∀ s (n : ℤ) (x : ℝ), x ∈ Ioo (M s 0 + n) (M s 1 + n) → ∃ u ∈ Ioo (0 : ℝ) 1, M s u + n
    = x := fun s n x hx ↦ by
    have h₁ : x - n ∈ Ioo (M s 0) (M s 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨u, hu, hue⟩ := intermediate_value_Ioo zero_le_one (hMc s) h₁
    exact ⟨u, hu, by linarith⟩
  have hofs : ∀ (e : Bool) {u : ℝ}, u ∈ Ioo (0 : ℝ) 1 → ofs e u ∈ Ioo (0 : ℝ) 1
    := fun e {u} hu ↦ ofs_Ioo e hu
  obtain ⟨k, sq, n, hk, hsur, hinj, hch, hlast⟩ := exists_tile_order (fun s ↦ M s 0)
    (fun s ↦ M s 1) hlr (fun s s' n n' x hx hx' ↦ by
    obtain ⟨u, hu, hue⟩ := hmid s n x hx
    obtain ⟨v, hv, hve⟩ := hmid s' n' x hx'
    have hee : ee (M s u) = ee (M s' v) := by
      rw [← ee_add_int (M s u) n, ← ee_add_int (M s' v) n', hue, hve]
    have h₁ : γ s (ofs (e s) u) = γ s' (ofs (e s') v) := by
      rw [← hM₁ s u ⟨hu.1.le, hu.2.le⟩, ← hM₁ s' v ⟨hv.1.le, hv.2.le⟩, hee]
    obtain ⟨rfl, h₂⟩ := hd s s' _ (hofs _ hu) _ (hofs _ hv) h₁
    have h₃ : u = v := by
      have := congrArg (ofs (e s)) h₂
      rwa [ofs_ofs, ofs_ofs] at this
    subst h₃
    refine ⟨rfl, ?_⟩
    have : (n : ℝ) = n' := by linarith
    exact_mod_cast this) (fun x ↦ by
    obtain ⟨s, v, hv, hve⟩ := hcov _ (φ (ee x)).2
    have h₁ : (φ (ee (M s (ofs (e s) v)))).1 = (φ (ee x)).1 := by
      rw [hM₁ s _ (ofs_mem hv), ofs_ofs, hve]
    obtain ⟨n, hn⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext h₁))
    refine ⟨s, -n, ?_⟩
    have hu := ofs_mem (e := e s) hv
    have h₂ := (he s).monotoneOn h01 hu hu.1
    have h₃ := (he s).monotoneOn hu h11 hu.2
    change M s 0 ≤ M s (ofs (e s) v) at h₂
    change M s (ofs (e s) v) ≤ M s 1 at h₃
    constructor <;> push_cast <;> linarith)
  refine ⟨k, sq, fun i ↦ e (sq i), fun i u ↦ M (sq i) u + n i, hk, hsur, hinj, fun i _ ↦ ⟨(hMc
    _).add continuousOn_const, fun u hu v hv huv ↦ ?_, fun u hu ↦ ?_⟩, fun i hi ↦ ?_, ?_⟩
  · simpa using he _ hu hv huv
  · simp only
    rw [ee_add_int, hM₁ _ u hu]
  · exact hch i hi
  · exact hlast

end GraphMinor.GM19
