/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutConn

/-!
# Arcs around a circle

Let finitely many arcs cover a circle, so that a point inside an arc is on no other arc and is not
an end of an arc. Then the
arcs go around the circle one after the other (`exists_cycle`). We lift the arcs to the real line,
turn them to run forward,
move them to one interval of length one, and sort them by their first ends (`exists_sorted`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

/-- Intervals in `[t, T]`, each one starting outside the others, that cover `[t, T)` follow one
another. -/
theorem exists_sorted {ι : Type*} (a b : ι → ℝ) {t : ℝ} (n : ℕ) : ∀ (F : Finset ι) (T : ℝ), F.card
  = n → F.Nonempty →
    (∀ α ∈ F, a α < b α ∧ t ≤ a α ∧ b α ≤ T) → (∀ α ∈ F, ∀ β ∈ F, a α = a β → α = β) →
    (∀ α ∈ F, ∀ β ∈ F, a β ∉ Ioo (a α) (b α)) → (∀ u ∈ Ico t T, ∃ α ∈ F, u ∈ Icc (a α) (b α)) →
    ∃ L : List ι, L.Nodup ∧ (∀ α, α ∈ L ↔ α ∈ F) ∧ L.IsChain (fun α β => b α = a β) ∧
      (∃ α ∈ L.head?, a α = t) ∧ ∃ α ∈ L.getLast?, b α = T := by
  classical
  induction n with
  | zero =>
    intro F T hc hne
    simp [Finset.card_eq_zero.mp hc] at hne
  | succ n ih =>
    intro F T hc hne hF hinj hnest hcov
    obtain ⟨α, hα, hmax⟩ := F.exists_max_image a hne
    have hb : b α = T := by
      by_contra hne'
      have hlt : b α < T := lt_of_le_of_ne (hF α hα).2.2 hne'
      obtain ⟨β, hβ, h1, h2⟩ := hcov ((b α + T) / 2) ⟨by linarith [(hF α hα).1,
        (hF α hα).2.1], by linarith⟩
      have h3 := hmax β hβ
      have hne2 : β ≠ α := by
        rintro rfl
        linarith
      have h4 : a β < a α := lt_of_le_of_ne h3 fun h => hne2 (hinj β hβ α hα h)
      exact hnest β hβ α hα ⟨h4, by linarith [(hF α hα).1]⟩
    by_cases hemp : F.erase α = ∅
    · have hF1 : F = {α} := by
        have := Finset.insert_erase hα
        rw [hemp] at this
        simpa using this.symm
      subst hF1
      obtain ⟨β, hβ, h1, -⟩ := hcov t ⟨le_rfl, by linarith [(hF α hα).1, (hF α hα).2.1]⟩
      obtain rfl := Finset.mem_singleton.mp hβ
      refine ⟨[β], by simp, by simp, by simp, ⟨β, by simp, le_antisymm h1 (hF β hα).2.1⟩, β,
        by simp, hb⟩
    · have hne' : (F.erase α).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      have hlt : ∀ β ∈ F.erase α, a β < a α := fun β hβ =>
        lt_of_le_of_ne (hmax β (Finset.mem_of_mem_erase hβ)) fun h => (Finset.mem_erase.mp hβ).1
          (hinj β (Finset.mem_of_mem_erase hβ) α hα h)
      have hcard : (F.erase α).card = n := by
        rw [Finset.card_erase_of_mem hα, hc]
        rfl
      obtain ⟨L, h1, h2, h3, h4, γ, h5, h6⟩ := ih (F.erase α) (a α) hcard hne'
        (fun β hβ => ⟨(hF β (Finset.mem_of_mem_erase hβ)).1, (hF β (Finset.mem_of_mem_erase
          hβ)).2.1, by
          by_contra hcon
          exact hnest β (Finset.mem_of_mem_erase hβ) α hα ⟨hlt β hβ, not_le.mp hcon⟩⟩)
        (fun β hβ β' hβ' he => hinj β (Finset.mem_of_mem_erase hβ) β'
          (Finset.mem_of_mem_erase hβ') he)
        (fun β hβ β' hβ' => hnest β (Finset.mem_of_mem_erase hβ) β' (Finset.mem_of_mem_erase hβ'))
        (fun u hu => by
          obtain ⟨β, hβ, h1, h2⟩ := hcov u ⟨hu.1, hu.2.trans_le (by linarith [(hF α hα).1])⟩
          refine ⟨β, Finset.mem_erase.mpr ⟨?_, hβ⟩, h1, h2⟩
          rintro rfl
          linarith [hu.2])
      have hαL : α ∉ L := fun h => (Finset.mem_erase.mp ((h2 α).mp h)).1 rfl
      have hLne : L ≠ [] := by
        rintro rfl
        simp at h5
      refine ⟨L ++ [α], ?_, fun β => ?_, ?_, ?_, α, by simp, hb⟩
      · exact List.Nodup.append h1 (by simp) (by simpa using hαL)
      · simp only [List.mem_append, List.mem_singleton, h2, Finset.mem_erase]
        constructor
        · rintro (h | rfl)
          · exact h.2
          · exact hα
        · intro h
          by_cases he : β = α
          · exact .inr he
          · exact .inl ⟨he, h⟩
      · rw [List.isChain_append]
        refine ⟨h3, by simp, fun x hx y hy => ?_⟩
        have hy' : α = y := by simpa using hy
        rw [← hy', Option.mem_unique hx h5, h6]
      · obtain ⟨β, hβ, he⟩ := h4
        exact ⟨β, by rw [List.head?_append_of_ne_nil _ hLne]; exact hβ, he⟩

/-- A finite family of arcs that covers the boundary. The arcs are paths with `ℓ α 0` and `ℓ α 1` as
ends, which may agree. A point
inside an arc is on no other arc, and it is not an end of any arc. -/
structure IsArcFamily {Z ι : Type*} [TopologicalSpace Z] (ℓ : ι → ℝ → Z) : Prop where
  cont : ∀ α, ContinuousOn (ℓ α) (Icc 0 1)
  inj : ∀ α, InjOn (ℓ α) (Ioo 0 1)
  mem : ∀ α, ∀ u ∈ Icc (0 : ℝ) 1, ℓ α u ∈ bd Z
  disj : ∀ α β, α ≠ β → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, ℓ α u ≠ ℓ β v
  off : ∀ α β, ∀ u ∈ Ioo (0 : ℝ) 1, ℓ α u ≠ ℓ β 0 ∧ ℓ α u ≠ ℓ β 1
  cover : ∀ x ∈ bd Z, ∃ α, ∃ u ∈ Icc (0 : ℝ) 1, x = ℓ α u

theorem ofs_mem_Ioo (σ : Bool) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ofs σ u ∈ Ioo (0 : ℝ) 1 := by
  cases σ
  · rw [ofs_false]
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  · rwa [ofs_true]

section

variable {Z ι : Type*} [TopologicalSpace Z] {ℓ : ι → ℝ → Z}

theorem IsArcFamily.off_ofs (hf : IsArcFamily ℓ) (α β : ι) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
  (σ : Bool) :
    ℓ α u ≠ ℓ β (ofs σ 0) ∧ ℓ α u ≠ ℓ β (ofs σ 1) := by
  have h := hf.off α β u hu
  cases σ <;> simp [ofs_false, ofs_true, h.1, h.2]

theorem IsArcFamily.injOn_Ico (hf : IsArcFamily ℓ) (α : ι) : InjOn (ℓ α) (Ico 0 1) := by
  intro x hx y hy he
  rcases eq_or_lt_of_le hx.1 with rfl | h1
  · rcases eq_or_lt_of_le hy.1 with rfl | h2
    · rfl
    · exact absurd he.symm (hf.off α α y ⟨h2, hy.2⟩).1
  · rcases eq_or_lt_of_le hy.1 with rfl | h2
    · exact absurd he (hf.off α α x ⟨h1, hx.2⟩).1
    · exact hf.inj α ⟨h1, hx.2⟩ ⟨h2, hy.2⟩ he

variable {C : Set Z}

/-- An arc on a circle lifts to a forward path on the real line, of length at most one. -/
theorem exists_dir_lift (hf : IsArcFamily ℓ) (φ : Circle ≃ₜ C) (α : ι) (hC : ∀ u ∈ Icc
  (0 : ℝ) 1, ℓ α u ∈ C) :
    ∃ (σ : Bool) (n : ℝ → ℝ), ContinuousOn n (Icc 0 1) ∧ StrictMonoOn n (Icc 0 1) ∧ (∀ u ∈ Icc
      (0 : ℝ) 1, (φ (ee (n u))).1 = ℓ α (ofs σ u)) ∧
      n 1 ≤ n 0 + 1 := by
  obtain ⟨m, h1, h2⟩ := exists_lift φ (hf.cont α) hC
  have hinj : InjOn (fun u => ee (m u)) (Ico 0 1) := fun x hx y hy he => hf.injOn_Ico α hx hy (by
    rw [← h2 x ⟨hx.1, hx.2.le⟩, ← h2 y ⟨hy.1, hy.2.le⟩]
    simp only at he
    rw [he])
  have h3 : ∃ (σ : Bool) (n : ℝ → ℝ), ContinuousOn n (Icc 0 1) ∧ StrictMonoOn n (Icc 0 1)
    ∧ ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (n u))).1 = ℓ α (ofs σ u) := by
    rcases lift_mono_loop h1 hinj with h | h
    · exact ⟨true, m, h1, h, fun u hu => by rw [ofs_true]; exact h2 u hu⟩
    · refine ⟨false, fun u => m (1 - u), h1.comp (by fun_prop) fun u hu => rev_mem hu,
        fun x hx y hy hxy => h (rev_mem hy) (rev_mem hx) (by linarith),
        fun u hu => by rw [ofs_false]; exact h2 _ (rev_mem hu)⟩
  obtain ⟨σ, n, c, s, v⟩ := h3
  refine ⟨σ, n, c, s, v, ?_⟩
  by_contra hcon
  obtain ⟨u, hu, hu'⟩ := intermediate_value_Ioo zero_le_one c (show n 0 + 1 ∈ Ioo (n 0)
    (n 1) from ⟨by linarith, not_le.mp hcon⟩)
  have h4 : ℓ α (ofs σ u) = ℓ α (ofs σ 0) := by
    rw [← v u ⟨hu.1.le, hu.2.le⟩, ← v 0 (by simp), hu', ee_add_one]
  exact (hf.off_ofs α α (ofs_mem_Ioo σ hu) σ).1 h4

/-- **The arcs go around the circle.** The arcs of `A` lie on the circle `C` and cover it. Then they
can be listed so that each one, run
forward, starts where the one before it ends, and the last one ends where the first one starts, one
turn later. -/
theorem exists_cuff_order (hf : IsArcFamily ℓ) (φ : Circle ≃ₜ C) (A : Finset ι)
  (hsub : ∀ α ∈ A, ∀ u ∈ Icc (0 : ℝ) 1, ℓ α u ∈ C)
    (hcov : ∀ x ∈ C, ∃ α ∈ A, ∃ u ∈ Icc (0 : ℝ) 1, x = ℓ α u) :
    ∃ (L : List ι) (σ : ι → Bool) (n : ι → ℝ → ℝ), L.Nodup ∧ (∀ α, α ∈ L ↔ α ∈ A) ∧
      (∀ α ∈ A, ContinuousOn (n α) (Icc 0 1) ∧ StrictMonoOn (n α) (Icc 0 1) ∧ ∀ u ∈ Icc (0 : ℝ) 1,
        (φ (ee (n α u))).1 = ℓ α (ofs (σ α) u)) ∧
      L.IsChain (fun α β => n α 1 = n β 0) ∧ (∃ α ∈ L.head?, ∃ ω ∈ L.getLast?, n ω 1 = n α 0 + 1) ∧
      (∀ α ∈ A, ∀ β ∈ A, n α 0 = n β 0 → α = β) ∧ (∀ α ∈ A, ∀ β ∈ A, n α 1 = n β 1 → α = β)
        ∧ ∃ t, ∀ α ∈ A, t ≤ n α 0 ∧ n α 1 ≤ t + 1 := by
  classical
  obtain ⟨α₀, hα₀, -⟩ := hcov (φ 1).1 (φ 1).2
  have hch : ∀ α, ∃ (σ : Bool) (n : ℝ → ℝ), α ∈ A → ContinuousOn n (Icc 0 1) ∧ StrictMonoOn n
    (Icc 0 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (n u))).1 = ℓ α (ofs σ u)) ∧ n 1 ≤ n 0 + 1 := fun α => by
    by_cases h : α ∈ A
    · obtain ⟨σ, n, h1⟩ := exists_dir_lift hf φ α (hsub α h)
      exact ⟨σ, n, fun _ => h1⟩
    · exact ⟨true, id, fun h' => absurd h' h⟩
  choose σ n₀ hn₀ using hch
  set t := n₀ α₀ 0 with ht
  set n : ι → ℝ → ℝ := fun α u => n₀ α u + ((-⌊n₀ α 0 - t⌋ : ℤ) : ℝ) with hn
  have hc : ∀ α ∈ A, ContinuousOn (n α) (Icc 0 1) := fun α h => (hn₀ α h).1.add continuousOn_const
  have hs : ∀ α ∈ A, StrictMonoOn (n α) (Icc 0 1) := fun α h x hx y hy hxy => by
    simp only [hn]
    linarith [(hn₀ α h).2.1 hx hy hxy]
  have hv : ∀ α ∈ A, ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (n α u))).1 = ℓ α (ofs (σ α) u) := fun α h u hu
    => by
    simp only [hn]
    rw [ee_add_int]
    exact (hn₀ α h).2.2.1 u hu
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hat : n α₀ 0 = t := by simp [hn, ← ht]
  have ha : ∀ α, t ≤ n α 0 ∧ n α 0 < t + 1 := fun α => by
    have h2 := Int.floor_le (n₀ α 0 - t)
    have h3 := Int.lt_floor_add_one (n₀ α 0 - t)
    simp only [hn, Int.cast_neg]
    constructor <;> linarith
  have hlt : ∀ α ∈ A, n α 0 < n α 1 := fun α h => hs α h h0 h1 zero_lt_one
  have hiv : ∀ α ∈ A, ∀ w ∈ Ioo (n α 0) (n α 1), ∃ u ∈ Ioo (0 : ℝ) 1, (φ (ee w)).1 = ℓ α u
    := fun α h w hw => by
    obtain ⟨u, hu, rfl⟩ := intermediate_value_Ioo zero_le_one (hc α h) hw
    exact ⟨_, ofs_mem_Ioo (σ α) hu, hv α h u ⟨hu.1.le, hu.2.le⟩⟩
  have hend : ∀ α ∈ A, ∀ β ∈ A, n β 0 ∉ Ioo (n α 0) (n α 1) := fun α h β hβ hw => by
    obtain ⟨u, hu, he⟩ := hiv α h _ hw
    exact (hf.off_ofs α β hu (σ β)).1 (by rw [← he, hv β hβ 0 h0])
  have hb : ∀ α ∈ A, n α 1 ≤ t + 1 := fun α h => by
    by_contra hcon
    obtain ⟨u, hu, he⟩ := hiv α h (t + 1) ⟨(ha α).2, not_le.mp hcon⟩
    refine (hf.off_ofs α α₀ hu (σ α₀)).1 ?_
    rw [← he, ee_add_one, ← hv α₀ hα₀ 0 h0, hat]
  have hdisj : ∀ α ∈ A, ∀ β ∈ A, n α 0 = n β 0 → α = β := fun α h β hβ he => by
    by_contra hne
    have h2 := hlt α h
    have h3 := hlt β hβ
    set w := (n α 0 + min (n α 1) (n β 1)) / 2 with hw
    have h4 : n α 0 < min (n α 1) (n β 1) := lt_min h2 (he ▸ h3)
    have h5 := min_le_left (n α 1) (n β 1)
    have h6 := min_le_right (n α 1) (n β 1)
    obtain ⟨u, hu, e1⟩ := hiv α h w ⟨by linarith, by linarith⟩
    obtain ⟨v, hv', e2⟩ := hiv β hβ w ⟨by linarith, by linarith⟩
    exact hf.disj α β hne u hu v hv' (e1.symm.trans e2)
  obtain ⟨L, h2, h3, h4, ⟨α, hα, h5⟩, ω, hω, h6⟩ := exists_sorted (fun α => n α 0) (fun α => n α 1)
    (t := t) _ A (t + 1) rfl ⟨α₀, hα₀⟩
    (fun α h => ⟨hlt α h, (ha α).1, hb α h⟩) hdisj (fun α h β hβ => hend α h β hβ) (fun u hu => by
      obtain ⟨α, h, v, hv', he⟩ := hcov (φ (ee u)).1 (φ (ee u)).2
      have hv1 := ofs_mem (e := σ α) hv'
      have h7 : (φ (ee u)).1 = (φ (ee (n α (ofs (σ α) v)))).1 := by rw [hv α h _ hv1, ofs_ofs, he]
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext h7))
      have h8 := (hs α h).monotoneOn h0 hv1 hv1.1
      have h9 := (hs α h).monotoneOn hv1 h1 hv1.2
      have h10 := hb α h
      have h11 := (ha α).1
      have hk1 : (k : ℝ) < 1 := by linarith [hu.2]
      have hk2 : (-2 : ℝ) < k := by linarith [hu.1]
      have hk3 : k < 1 := by exact_mod_cast hk1
      have hk4 : -2 < k := by exact_mod_cast hk2
      obtain rfl | rfl : k = 0 ∨ k = -1 := by omega
      · refine ⟨α, h, ?_, ?_⟩ <;> simp only [Int.cast_zero, add_zero] at hk <;> rw [hk]
        <;> assumption
      · have hu' : u = t := by
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one] at hk
          linarith [hu.1]
        exact ⟨α₀, hα₀, by simp only [hat, hu']; exact le_rfl, by rw [hu']; rw [← hat]; exact
          (hlt α₀ hα₀).le⟩)
  have hdisj' : ∀ α ∈ A, ∀ β ∈ A, n α 1 = n β 1 → α = β := fun α h β hβ he => by
    by_contra hne
    have h7 := hlt α h
    have h8 := hlt β hβ
    set w := (max (n α 0) (n β 0) + n α 1) / 2 with hw
    have h9 : max (n α 0) (n β 0) < n α 1 := max_lt h7 (he ▸ h8)
    have h10 := le_max_left (n α 0) (n β 0)
    have h11 := le_max_right (n α 0) (n β 0)
    obtain ⟨u, hu, e1⟩ := hiv α h w ⟨by linarith, by linarith⟩
    obtain ⟨v, hv', e2⟩ := hiv β hβ w ⟨by linarith, by linarith⟩
    exact hf.disj α β hne u hu v hv' (e1.symm.trans e2)
  exact ⟨L, σ, n, h2, h3, fun α h => ⟨hc α h, hs α h, hv α h⟩, h4, ⟨α, hα, ω, hω, by rw [h6,
    h5]⟩, hdisj, hdisj', t, fun α h => ⟨(ha α).1, hb α h⟩⟩

end

theorem chain_next {ι : Type*} {R : ι → ι → Prop} {L : List ι} (h : L.IsChain R) : ∀ α ∈ L, α ∈
  L.getLast? ∨ ∃ β ∈ L, R α β := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp
    | cons y L =>
      rw [List.isChain_cons_cons] at h
      intro α hα
      rcases List.mem_cons.mp hα with rfl | h1
      · exact .inr ⟨y, by simp, h.1⟩
      · rcases ih h.2 α h1 with h2 | ⟨β, h3, h4⟩
        · exact .inl (by rw [List.getLast?_cons_cons]; exact h2)
        · exact .inr ⟨β, List.mem_cons_of_mem _ h3, h4⟩

theorem chain_prev {ι : Type*} {R : ι → ι → Prop} {L : List ι} (h : L.IsChain R) : ∀ α ∈ L, α ∈
  L.head? ∨ ∃ β ∈ L, R β α := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp
    | cons y L =>
      rw [List.isChain_cons_cons] at h
      intro α hα
      rcases List.mem_cons.mp hα with rfl | h1
      · exact .inl (by simp)
      · rcases ih h.2 α h1 with h2 | ⟨β, h3, h4⟩
        · refine .inr ⟨x, by simp, ?_⟩
          have : α = y := by simpa using h2.symm
          rw [this]
          exact h.1
        · exact .inr ⟨β, List.mem_cons_of_mem _ h3, h4⟩

section

variable {Z : Type u} [TopologicalSpace Z] {ι : Type*} {ℓ : ι → ℝ → Z}

/-- An arc that meets a cuff lies on it. -/
theorem arc_sub_cuff (hf : IsArcFamily ℓ) {C : Set Z} (hC : C ∈ cuffs Z) {α : ι} {v : ℝ}
  (hv : v ∈ Icc (0 : ℝ) 1) (hv' : ℓ α v ∈ C) :
    ∀ u ∈ Icc (0 : ℝ) 1, ℓ α u ∈ C := by
  obtain ⟨y, -, rfl⟩ := hC
  intro u hu
  have h1 : IsPreconnected (ℓ α '' Icc 0 1) := isPreconnected_Icc.image _ (hf.cont α)
  have hsub : ℓ α '' Icc 0 1 ⊆ bd Z := by
    rintro _ ⟨w, hw, rfl⟩
    exact hf.mem α w hw
  have h2 := h1.subset_connectedComponentIn (mem_image_of_mem _ hv) hsub
  rw [← connectedComponentIn_eq hv'] at h2
  exact h2 (mem_image_of_mem _ hu)

/-- The arcs on a cuff. -/
theorem exists_arcs_on [Finite ι] (hf : IsArcFamily ℓ) {C : Set Z} (hC : C ∈ cuffs Z) :
    ∃ A : Finset ι, (∀ α ∈ A, ∀ u ∈ Icc (0 : ℝ) 1, ℓ α u ∈ C) ∧ (∀ α, ∀ u ∈ Icc
      (0 : ℝ) 1, ℓ α u ∈ C → α ∈ A) ∧
      ∀ x ∈ C, ∃ α ∈ A, ∃ u ∈ Icc (0 : ℝ) 1, x = ℓ α u := by
  classical
  refine ⟨(Set.toFinite {α | ∃ u ∈ Icc (0 : ℝ) 1, ℓ α u ∈ C}).toFinset, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨v, hv, hv'⟩ := (Set.Finite.mem_toFinset _).mp hα
    exact arc_sub_cuff hf hC hv hv'
  · intro α u hu h
    exact (Set.Finite.mem_toFinset _).mpr ⟨u, hu, h⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := id hC
    obtain ⟨α, u, hu, rfl⟩ := hf.cover x (connectedComponentIn_subset _ _ hx)
    exact ⟨α, (Set.Finite.mem_toFinset _).mpr ⟨u, hu, hx⟩, u, hu, rfl⟩

/-- **Two ends at a point.** The ends of the arcs meet in pairs: each end shares its point with
another end, and no three ends share
a point. This is how a circle covered by arcs looks. -/
theorem exists_ends [Finite ι] (hS : IsSurface Z) (hf : IsArcFamily ℓ) (α : ι) (s : Bool) :
    (∃ β s', (β, s') ≠ (α, s) ∧ ℓ β (ofs s' 1) = ℓ α (ofs s 1)) ∧
      ∀ β γ s' s'', ℓ β (ofs s' 1) = ℓ α (ofs s 1) → ℓ γ (ofs s'' 1) = ℓ α (ofs s 1) →
        (β, s') = (α, s) ∨ (γ, s'') = (α, s) ∨ (β, s') = (γ, s'') := by
  classical
  have h01 : ∀ e : Bool, ofs e 1 ∈ Icc (0 : ℝ) 1 := fun e => by cases e
    <;> simp [ofs_true, ofs_false]
  have hyb := hf.mem α _ (h01 s)
  have hC : connectedComponentIn (bd Z) (ℓ α (ofs s 1)) ∈ cuffs Z := ⟨_, hyb, rfl⟩
  have hy := mem_connectedComponentIn hyb
  obtain ⟨φ⟩ := (cuff_statement Z hS).2.2 _ hC
  obtain ⟨A, hsub, hA, hcov⟩ := exists_arcs_on hf hC
  obtain ⟨L, σ, n, h1, h2, h3, h4, ⟨a₀, ha₀, ω, hω, h5⟩, h6, h7, t, h8⟩
    := exists_cuff_order hf φ A hsub hcov
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hhead : ∀ β ∈ A, (φ (ee (n β 1))).1 = ℓ β (ofs (σ β) 1) := fun β h => (h3 β h).2.2 1 h1'
  have htail : ∀ β ∈ A, (φ (ee (n β 0))).1 = ℓ β (ofs (!σ β) 1) := fun β h => by
    rw [(h3 β h).2.2 0 h0]
    cases σ β <;> simp [ofs_true, ofs_false]
  have hlt : ∀ β ∈ A, n β 0 < n β 1 := fun β h => (h3 β h).2.1 h0 h1' zero_lt_one
  have hmemL : ∀ β, β ∈ L → β ∈ A := fun β h => (h2 β).mp h
  have ha₀L : a₀ ∈ L := List.mem_of_mem_head? ha₀
  have hωL : ω ∈ L := List.mem_of_getLast? hω
  have hH : ∀ β ∈ A, ∃ γ ∈ A, ℓ γ (ofs (!σ γ) 1) = ℓ β (ofs (σ β) 1) := fun β hβ => by
    rcases chain_next h4 β ((h2 β).mpr hβ) with h | ⟨γ, h9, h10⟩
    · obtain rfl := Option.mem_unique h hω
      refine ⟨a₀, hmemL _ ha₀L, ?_⟩
      rw [← htail a₀ (hmemL _ ha₀L), ← hhead β hβ, h5, ee_add_one]
    · refine ⟨γ, hmemL _ h9, ?_⟩
      rw [← htail γ (hmemL _ h9), ← hhead β hβ, h10]
  have hT : ∀ β ∈ A, ∃ γ ∈ A, ℓ γ (ofs (σ γ) 1) = ℓ β (ofs (!σ β) 1) := fun β hβ => by
    rcases chain_prev h4 β ((h2 β).mpr hβ) with h | ⟨γ, h9, h10⟩
    · obtain rfl := Option.mem_unique h ha₀
      refine ⟨ω, hmemL _ hωL, ?_⟩
      rw [← htail β hβ, ← hhead ω (hmemL _ hωL), h5, ee_add_one]
    · refine ⟨γ, hmemL _ h9, ?_⟩
      rw [← htail β hβ, ← hhead γ (hmemL _ h9), h10]
  have hαA : α ∈ A := hA α _ (h01 s) hy
  have hmemA : ∀ β s', ℓ β (ofs s' 1) = ℓ α (ofs s 1) → β ∈ A := fun β s' he => hA β _ (h01 s')
    (by rw [he]; exact hy)
  have uT : ∀ β ∈ A, ∀ γ ∈ A, ℓ β (ofs (!σ β) 1) = ℓ γ (ofs (!σ γ) 1) → β = γ := fun β hβ γ hγ he
    => by
    rw [← htail β hβ, ← htail γ hγ] at he
    obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext he))
    have b1 := h8 β hβ
    have b2 := h8 γ hγ
    have b3 := hlt β hβ
    have b4 := hlt γ hγ
    have k1 : (k : ℝ) < 1 := by linarith [b1.1, b2.2]
    have k2 : (-1 : ℝ) < k := by linarith [b1.2, b2.1]
    have k3 : k < 1 := by exact_mod_cast k1
    have k4 : -1 < k := by exact_mod_cast k2
    obtain rfl : k = 0 := by omega
    exact h6 β hβ γ hγ (by simpa using hk)
  have uH : ∀ β ∈ A, ∀ γ ∈ A, ℓ β (ofs (σ β) 1) = ℓ γ (ofs (σ γ) 1) → β = γ := fun β hβ γ hγ he
    => by
    rw [← hhead β hβ, ← hhead γ hγ] at he
    obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext he))
    have b1 := h8 β hβ
    have b2 := h8 γ hγ
    have b3 := hlt β hβ
    have b4 := hlt γ hγ
    have k1 : (k : ℝ) < 1 := by linarith [b1.2, b2.1]
    have k2 : (-1 : ℝ) < k := by linarith [b1.1, b2.2]
    have k3 : k < 1 := by exact_mod_cast k1
    have k4 : -1 < k := by exact_mod_cast k2
    obtain rfl : k = 0 := by omega
    exact h7 β hβ γ hγ (by simpa using hk)
  have hb : ∀ (e : Bool) (β : ι), e = σ β ∨ e = !σ β := fun e β => by cases e <;> cases σ β <;> simp
  constructor
  · rcases hb s α with rfl | rfl
    · obtain ⟨γ, -, h9⟩ := hH α hαA
      refine ⟨γ, !σ γ, ?_, h9⟩
      intro he
      obtain ⟨rfl, h10⟩ := Prod.mk.inj he
      simp at h10
    · obtain ⟨γ, -, h9⟩ := hT α hαA
      refine ⟨γ, σ γ, ?_, h9⟩
      intro he
      obtain ⟨rfl, h10⟩ := Prod.mk.inj he
      simp at h10
  · intro β γ s' s'' he he'
    have hβ := hmemA β s' he
    have hγ := hmemA γ s'' he'
    rcases hb s α with rfl | rfl <;> rcases hb s' β with rfl | rfl <;> rcases hb s'' γ with rfl |
      rfl
    · obtain rfl := uH β hβ α hαA he
      exact .inl rfl
    · obtain rfl := uH β hβ α hαA he
      exact .inl rfl
    · obtain rfl := uH γ hγ α hαA he'
      exact .inr (.inl rfl)
    · obtain rfl := uT β hβ γ hγ (he.trans he'.symm)
      exact .inr (.inr rfl)
    · obtain rfl := uH β hβ γ hγ (he.trans he'.symm)
      exact .inr (.inr rfl)
    · obtain rfl := uT γ hγ α hαA he'
      exact .inr (.inl rfl)
    · obtain rfl := uT β hβ α hαA he
      exact .inl rfl
    · obtain rfl := uT β hβ α hαA he
      exact .inl rfl

end

end GraphMinor.GM07
