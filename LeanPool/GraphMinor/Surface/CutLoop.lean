/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutIArc

/-!
# Lifts of an `O`-arc

An `O`-arc `F` is cut into two lines, and these have lifts as paths. Joining the paths gives two
paths around `F`. Either both
of them are loops, or each one ends where the other starts (`LiftPair.paths`). Lemmas on loops in a
cuff follow: a loop that
lies on a cuff and is one to one goes around the cuff exactly once (`exists_loop_turn`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

theorem half_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x / 2 ∈ Icc (0 : ℝ) 1
  := ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem half_mem' {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : (1 + x) / 2 ∈ Icc (0 : ℝ) 1
  := ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- A point of `[0, 1]` is in the first half or the second half. -/
theorem half_cases {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∃ v ∈ Icc (0 : ℝ) 1, x = v / 2 ∧ x ≤ 1 / 2) ∨ (∃ v ∈ Ioc (0 : ℝ) 1, x = (1 + v) / 2) := by
  by_cases h : x ≤ 1 / 2
  · exact .inl ⟨2 * x, ⟨by linarith [hx.1], by linarith⟩, by ring, h⟩
  · exact .inr ⟨2 * x - 1, ⟨by linarith, by linarith [hx.2]⟩, by ring⟩

section

variable {Y S : Type uu} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] [T2Space S] {ψ : Y
  → S}

omit [T2Space Y] in
/-- Two lifts of two lines that form an `O`-arc are joined to two paths around it. -/
theorem LiftPair.paths {Z₁ Z₂ : Set S} {u c : S} {X₁ Y₁ X₂ Y₂ : Set Y}
  (h : LiftPair ψ Z₁ u c X₁ Y₁) (h' : LiftPair ψ Z₂ c u X₂ Y₂)
    (hi : Z₁ ∩ Z₂ = {u, c}) (_huc : u ≠ c) (hu : (ψ ⁻¹' {u}).encard ≤ 2) (hc : (ψ ⁻¹' {c}).encard
      ≤ 2) (hψ : Continuous ψ) :
    ∃ (a : ℝ → S) (ξ η : ℝ → Y), ContinuousOn ξ (Icc 0 1) ∧ ContinuousOn η (Icc 0 1) ∧ (∀ t ∈ Icc
      (0 : ℝ) 1, ψ (ξ t) = a t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ψ (η t) = a t) ∧ a '' Icc 0 1 = Z₁ ∪ Z₂ ∧
      (∀ y y', ψ y = ψ y' → y ≠ y' → ψ y ∈ Z₁ ∪ Z₂ → ∃ t ∈ Icc (0 : ℝ) 1, (y = ξ t ∧ y' = η t) ∨
        (y' = ξ t ∧ y = η t)) ∧
      InjOn a (Ico 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, ξ t ≠ η t) ∧ ((ξ 1 = ξ 0 ∧ η 1 = η 0) ∨ (ξ 1 = η 0
        ∧ η 1 = ξ 0)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hdis := h
  have hdis' := h'
  obtain ⟨-, -, -, -, -, -, hd₁, -, -, -, -, -, -, -⟩ := hdis
  obtain ⟨-, -, -, -, -, -, hd₂, -, -, -, -, -, -, -⟩ := hdis'
  obtain ⟨a₁, ξ₁, η₁, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, -, -, c11⟩ := exists_arcPart h hψ
  obtain ⟨a₂, ξ₂, η₂, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -, -, d11⟩ := exists_arcPart h' hψ
  have hne₁ : ∀ t ∈ Icc (0 : ℝ) 1, ξ₁ t ≠ η₁ t := fun t ht he =>
    Set.disjoint_left.mp hd₁ (c9 ▸ mem_image_of_mem _ ht) (c10 ▸ he ▸ mem_image_of_mem _ ht)
  have hne₂ : ∀ t ∈ Icc (0 : ℝ) 1, ξ₂ t ≠ η₂ t := fun t ht he =>
    Set.disjoint_left.mp hd₂ (d9 ▸ mem_image_of_mem _ ht) (d10 ▸ he ▸ mem_image_of_mem _ ht)
  /- After swapping the paths over `Z₂`, they continue the paths over `Z₁`. -/
  have key : ∀ ξ' η' : ℝ → Y, ContinuousOn ξ' (Icc 0 1) → ContinuousOn η' (Icc 0 1) → (∀ t ∈ Icc
    (0 : ℝ) 1, ψ (ξ' t) = a₂ t) →
      (∀ t ∈ Icc (0 : ℝ) 1, ψ (η' t) = a₂ t) → (∀ t ∈ Icc (0 : ℝ) 1, ξ' t ≠ η' t) →
      (∀ y y', ψ y = ψ y' → y ≠ y' → ψ y ∈ Z₂ → ∃ t ∈ Icc (0 : ℝ) 1, (y = ξ' t ∧ y' = η' t) ∨ (y'
        = ξ' t ∧ y = η' t)) →
      ξ₁ 1 = ξ' 0 → η₁ 1 = η' 0 → ∃ (a : ℝ → S) (ξ η : ℝ → Y), ContinuousOn ξ (Icc 0 1)
        ∧ ContinuousOn η (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ψ (ξ t) = a t) ∧ (∀ t ∈ Icc (0 : ℝ) 1, ψ (η t) = a t) ∧ a '' Icc 0 1
          = Z₁ ∪ Z₂ ∧
        (∀ y y', ψ y = ψ y' → y ≠ y' → ψ y ∈ Z₁ ∪ Z₂ → ∃ t ∈ Icc (0 : ℝ) 1, (y = ξ t ∧ y' = η t) ∨
          (y' = ξ t ∧ y = η t)) ∧
        InjOn a (Ico 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, ξ t ≠ η t) ∧ ((ξ 1 = ξ 0 ∧ η 1 = η 0) ∨ (ξ 1
          = η 0 ∧ η 1 = ξ 0)) := by
    intro ξ' η' e1 e2 e3 e4 e5 e6 e7 e8
    have hab : a₁ 1 = a₂ 0 := by rw [c8, d7]
    have hval : ∀ {T : Type uu} {f f' : ℝ → T}, f 1 = f' 0 → ∀ x ∈ Icc (0 : ℝ) 1, (conc2 f f' x = f
      (2 * x) ∧ x ≤ 1 / 2) ∨
        (conc2 f f' x = f' (2 * x - 1) ∧ 1 / 2 ≤ x) := by
      intro T f f' hff x hx
      by_cases hx2 : x ≤ 1 / 2
      · exact .inl ⟨ite_eq_left hx2, hx2⟩
      · exact .inr ⟨ite_eq_right hx2, (not_le.mp hx2).le⟩
    have m₁ : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → x ≤ 1 / 2 → 2 * x ∈ Icc (0 : ℝ) 1 := fun hx h2
      => ⟨by linarith [hx.1], by linarith⟩
    have m₂ : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → 1 / 2 ≤ x → 2 * x - 1 ∈ Icc (0 : ℝ) 1 := fun hx h2
      => ⟨by linarith, by linarith [hx.2]⟩
    refine ⟨conc2 a₁ a₂, conc2 ξ₁ ξ', conc2 η₁ η', continuousOn_conc2 c1 e1 e7,
      continuousOn_conc2 c2 e2 e8, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rcases hval e7 t ht with ⟨e, h2⟩ | ⟨e, h2⟩ <;> rcases hval hab t ht with ⟨e', h3⟩ | ⟨e', h3⟩
        <;> rw [e, e']
      · exact c3 _ (m₁ ht h2)
      · have : t = 1 / 2 := le_antisymm h2 h3
        subst this
        norm_num
        rw [c3 1 h1, hab]
      · have : t = 1 / 2 := le_antisymm h3 h2
        subst this
        norm_num
        rw [e3 0 h0, hab]
      · exact e3 _ (m₂ ht h2)
    · intro t ht
      rcases hval e8 t ht with ⟨e, h2⟩ | ⟨e, h2⟩ <;> rcases hval hab t ht with ⟨e', h3⟩ | ⟨e', h3⟩
        <;> rw [e, e']
      · exact c4 _ (m₁ ht h2)
      · have : t = 1 / 2 := le_antisymm h2 h3
        subst this
        norm_num
        rw [c4 1 h1, hab]
      · have : t = 1 / 2 := le_antisymm h3 h2
        subst this
        norm_num
        rw [e4 0 h0, hab]
      · exact e4 _ (m₂ ht h2)
    · apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        rcases hval hab t ht with ⟨e, h2⟩ | ⟨e, h2⟩ <;> rw [e]
        · exact .inl (c5 ▸ mem_image_of_mem _ (m₁ ht h2))
        · exact .inr (d5 ▸ mem_image_of_mem _ (m₂ ht h2))
      · rintro z (hz | hz)
        · obtain ⟨v, hv, rfl⟩ := c5.symm.subset hz
          exact ⟨v / 2, half_mem hv, conc2_left hv⟩
        · obtain ⟨v, hv, rfl⟩ := d5.symm.subset hz
          exact ⟨(1 + v) / 2, half_mem' hv, conc2_right hab hv⟩
    · intro y y' he hne hy
      rcases hy with hy | hy
      · obtain ⟨t, ht, h3⟩ := c6 y y' he hne hy
        refine ⟨t / 2, half_mem ht, ?_⟩
        rw [conc2_left ht, conc2_left ht]
        exact h3
      · obtain ⟨t, ht, h3⟩ := e6 y y' he hne hy
        refine ⟨(1 + t) / 2, half_mem' ht, ?_⟩
        rw [conc2_right e7 ht, conc2_right e8 ht]
        exact h3
    · have cross : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, a₁ x = a₂ y → y = 0 := by
        intro x hx y hy he
        have h3 : a₂ y ∈ Z₁ ∩ Z₂ := ⟨he ▸ c5 ▸ mem_image_of_mem _ hx, d5 ▸ mem_image_of_mem _
          (Ico_subset_Icc_self hy)⟩
        rw [hi] at h3
        rcases h3 with h3 | h3
        · have h4 : a₂ y = a₂ 1 := by rw [h3, d8]
          exact absurd (d11 (Ico_subset_Icc_self hy) h1 h4) hy.2.ne
        · exact d11 (Ico_subset_Icc_self hy) h0 (by rw [h3, d7])
      intro x hx y hy he
      rcases hval hab x (Ico_subset_Icc_self hx) with ⟨e, h2⟩ | ⟨e, h2⟩ <;>
        rcases hval hab y (Ico_subset_Icc_self hy) with ⟨e', h3⟩ | ⟨e', h3⟩ <;> rw [e, e'] at he
      · have := c11 (m₁ (Ico_subset_Icc_self hx) h2) (m₁ (Ico_subset_Icc_self hy) h3) he
        linarith
      · have h4 := cross _ (m₁ (Ico_subset_Icc_self hx) h2) _ ⟨(m₂ (Ico_subset_Icc_self hy) h3).1,
        by linarith [hy.2]⟩ he
        have h5 : y = 1 / 2 := by linarith
        subst h5
        have h6 : a₁ (2 * x) = a₁ 1 := by rw [he, h4, hab]
        have := c11 (m₁ (Ico_subset_Icc_self hx) h2) h1 h6
        linarith
      · have h4 := cross _ (m₁ (Ico_subset_Icc_self hy) h3) _ ⟨(m₂ (Ico_subset_Icc_self hx) h2).1,
        by linarith [hx.2]⟩ he.symm
        have h5 : x = 1 / 2 := by linarith
        subst h5
        have h6 : a₁ (2 * y) = a₁ 1 := by rw [← he, h4, hab]
        have := c11 (m₁ (Ico_subset_Icc_self hy) h3) h1 h6
        linarith
      · have := d11 (m₂ (Ico_subset_Icc_self hx) h2) (m₂ (Ico_subset_Icc_self hy) h3) he
        linarith
    · intro t ht
      by_cases hx2 : t ≤ 1 / 2
      · have e : conc2 ξ₁ ξ' t = ξ₁ (2 * t) := ite_eq_left hx2
        have e' : conc2 η₁ η' t = η₁ (2 * t) := ite_eq_left hx2
        rw [e, e']
        exact hne₁ _ (m₁ ht hx2)
      · have e : conc2 ξ₁ ξ' t = ξ' (2 * t - 1) := ite_eq_right hx2
        have e' : conc2 η₁ η' t = η' (2 * t - 1) := ite_eq_right hx2
        rw [e, e']
        exact e5 _ (m₂ ht (not_le.mp hx2).le)
    · rw [conc2_zero, conc2_zero, conc2_one e7, conc2_one e8]
      have g1 : ψ (ξ' 1) = u := by rw [e3 1 h1, d8]
      have g2 : ψ (η' 1) = u := by rw [e4 1 h1, d8]
      have g3 : ψ (ξ₁ 0) = u := by rw [c3 0 h0, c7]
      have g4 : ψ (η₁ 0) = u := by rw [c4 0 h0, c7]
      rcases eq_or_of_encard_le_two hu g3 g4 (c := ξ' 1) g1 (hne₁ 0 h0) with e | e <;>
        rcases eq_or_of_encard_le_two hu g3 g4 (c := η' 1) g2 (hne₁ 0 h0) with e' | e'
      · exact absurd (e.trans e'.symm) (e5 1 h1)
      · exact .inl ⟨e, e'⟩
      · exact .inr ⟨e, e'⟩
      · exact absurd (e.trans e'.symm) (e5 1 h1)
  have g1 : ψ (ξ₂ 0) = c := by rw [d3 0 h0, d7]
  have g2 : ψ (η₂ 0) = c := by rw [d4 0 h0, d7]
  have g3 : ψ (ξ₁ 1) = c := by rw [c3 1 h1, c8]
  have g4 : ψ (η₁ 1) = c := by rw [c4 1 h1, c8]
  rcases eq_or_of_encard_le_two hc g3 g4 (c := ξ₂ 0) g1 (hne₁ 1 h1) with e | e <;>
    rcases eq_or_of_encard_le_two hc g3 g4 (c := η₂ 0) g2 (hne₁ 1 h1) with e' | e'
  · exact absurd (e.trans e'.symm) (hne₂ 0 h0)
  · exact key ξ₂ η₂ d1 d2 d3 d4 hne₂ d6 e.symm e'.symm
  · refine key η₂ ξ₂ d2 d1 d4 d3 (fun t ht => (hne₂ t ht).symm) (fun y y' he hne hy
    => ?_) e'.symm e.symm
    obtain ⟨t, ht, h3⟩ := d6 y y' he hne hy
    exact ⟨t, ht, h3.elim (fun h4 => .inr h4.symm) fun h4 => .inl h4.symm⟩
  · exact absurd (e.trans e'.symm) (hne₂ 0 h0)

end

/-- A one to one loop on a circle that runs forward goes around once. -/
theorem loop_turn {n : ℝ → ℝ} (c : ContinuousOn n (Icc 0 1)) (s : StrictMonoOn n (Icc 0 1))
  (hi : InjOn (fun u => ee (n u)) (Ico 0 1))
    (he : ee (n 0) = ee (n 1)) : n 1 = n 0 + 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  obtain ⟨m, hm⟩ := ee_eq_iff.mp he
  have h01 := s h0 h1 zero_lt_one
  have hm0 : (m : ℝ) < 0 := by linarith
  have hm1 : m < 0 := by exact_mod_cast hm0
  by_contra hne
  have hm2 : m ≠ -1 := by
    rintro rfl
    apply hne
    push_cast at hm
    linarith
  have hm3 : m ≤ -2 := by omega
  have hm4 : (m : ℝ) ≤ -2 := by exact_mod_cast hm3
  obtain ⟨v, hv, hev⟩ := intermediate_value_Icc zero_le_one c (show n 0 + 1 ∈ Icc (n 0)
    (n 1) from ⟨by linarith, by linarith⟩)
  have hv1 : v ≠ 1 := by
    rintro rfl
    linarith
  have hv0 : v ∈ Ico (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩
  have h2 : ee (n v) = ee (n 0) := by rw [hev, ee_add_one]
  have h3 := hi hv0 ⟨le_rfl, zero_lt_one⟩ h2
  rw [h3] at hev
  linarith

/-- A loop that goes around once meets every point of the circle. -/
theorem loop_fill {n : ℝ → ℝ} (c : ContinuousOn n (Icc 0 1)) (h1 : n 1 = n 0 + 1)
  (x : ℝ) : ∃ v ∈ Icc (0 : ℝ) 1, ee (n v) = ee x := by
  set k := ⌊x - n 0⌋ with hk
  have h2 : (k : ℝ) ≤ x - n 0 := Int.floor_le _
  have h3 : x - n 0 < k + 1 := Int.lt_floor_add_one _
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc zero_le_one c
    (show x - k ∈ Icc (n 0) (n 1) from ⟨by linarith, by rw [h1]; linarith⟩)
  refine ⟨v, hv, ?_⟩
  rw [he, ← ee_add_int (x - k) k]
  congr 1
  ring

theorem ee_negate_inj {x y : ℝ} (h : ee (-x) = ee (-y)) : ee x = ee y := by
  obtain ⟨m, hm⟩ := ee_eq_iff.mp h
  refine ee_eq_iff.mpr ⟨-m, ?_⟩
  push_cast
  linarith

/-- A one to one loop on a cuff goes around once, in one of the two directions. -/
theorem exists_loop_turn {T : Type*} [TopologicalSpace T] {C : Set T} (φ : Circle ≃ₜ C) {ρ : ℝ → T}
  (cρ : ContinuousOn ρ (Icc 0 1))
    (hρ : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ C) (hi : InjOn ρ (Ico 0 1)) (h01 : ρ 0 = ρ 1) :
    ∃ (σ : Bool) (n : ℝ → ℝ), ContinuousOn n (Icc 0 1) ∧ StrictMonoOn n (Icc 0 1) ∧ n 1 = n 0 + 1 ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (n u))).1 = ρ (ofs σ u) := by
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  obtain ⟨n, n1, n2⟩ := exists_lift φ cρ hρ
  have hinj : InjOn (fun u => ee (n u)) (Ico 0 1) := by
    intro x hx y hy he
    refine hi hx hy ?_
    rw [← n2 x (Ico_subset_Icc_self hx), ← n2 y (Ico_subset_Icc_self hy)]
    exact congrArg (fun w => (φ w).1) he
  have he : ee (n 0) = ee (n 1) := by
    apply φ.injective
    apply Subtype.ext
    rw [n2 0 m0, n2 1 m1, h01]
  rcases lift_mono_loop n1 hinj with hs | hs
  · exact ⟨true, n, n1, hs, loop_turn n1 hs hinj he, fun u hu => by rw [ofs_true]; exact n2 u hu⟩
  · have hc' : ContinuousOn (fun u => - n u) (Icc 0 1) := n1.neg
    have hs' : StrictMonoOn (fun u => - n u) (Icc 0 1) := fun x hx y hy hxy => neg_lt_neg
      (hs hx hy hxy)
    have hi' : InjOn (fun u => ee (- n u)) (Ico 0 1) := fun x hx y hy he' => hinj hx hy
      (ee_negate_inj he')
    have he' : ee (- n 0) = ee (- n 1) := by
      obtain ⟨m, hm⟩ := ee_eq_iff.mp he
      refine ee_eq_iff.mpr ⟨-m, ?_⟩
      push_cast
      linarith
    have h3 := loop_turn hc' hs' hi' he'
    refine ⟨false, fun u => n (1 - u), n1.comp (by fun_prop) fun u hu => rev_mem hu,
      fun x hx y hy hxy => hs (rev_mem hy) (rev_mem hx) (by linarith), ?_,
      fun u hu => ?_⟩
    · simp only [sub_self, sub_zero]
      linarith
    · simp only [ofs_false]
      exact n2 _ (rev_mem hu)

/-- A one to one loop on a cuff fills the cuff. -/
theorem loop_image {T : Type*} [TopologicalSpace T] {C : Set T} (φ : Circle ≃ₜ C) {ρ : ℝ → T}
  (cρ : ContinuousOn ρ (Icc 0 1))
    (hρ : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ C) (hi : InjOn ρ (Ico 0 1)) (h01 : ρ 0 = ρ 1) : ρ '' Icc 0 1
      = C := by
  obtain ⟨σ, n, n1, -, n3, n4⟩ := exists_loop_turn φ cρ hρ hi h01
  apply subset_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact hρ u hu
  · intro z hz
    obtain ⟨w, hw⟩ := φ.surjective ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := ee_surjective w
    obtain ⟨v, hv, he⟩ := loop_fill n1 n3 x
    refine ⟨ofs σ v, ofs_mem hv, ?_⟩
    rw [← n4 v hv, he, hw]

/-- An `O`-arc inside an `O`-arc is the whole `O`-arc. -/
theorem oarc_eq {T : Type*} [TopologicalSpace T] {C X : Set T} (φ : Circle ≃ₜ C)
  (hX : IsOArc X) (hs : X ⊆ C) : X = C := by
  obtain ⟨e⟩ := id hX
  obtain ⟨ι, h1, h2, h3, h4, -, h5⟩ := hX.exists_iota (e 1).2
  have h6 : ι '' Icc 0 1 = X := by
    apply subset_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hu.2 with rfl | h7
      · rw [h3]
        exact (e 1).2
      · exact h5 ▸ mem_image_of_mem ι ⟨hu.1, h7⟩
    · rw [← h5]
      exact image_mono Ico_subset_Icc_self
  rw [← h6]
  exact loop_image φ h1.continuousOn (fun u hu => hs (h6 ▸ mem_image_of_mem ι hu)) h4
    (h2.trans h3.symm)

theorem ee_injOn : InjOn ee (Ico 0 1) := by
  intro x hx y hy he
  obtain ⟨m, hm⟩ := ee_eq_iff.mp he
  have h1 : (m : ℝ) < 1 := by linarith [hx.2, hy.1]
  have h2 : (-1 : ℝ) < m := by linarith [hx.1, hy.2]
  have h3 : m < 1 := by exact_mod_cast h1
  have h4 : -1 < m := by exact_mod_cast h2
  have h5 : m = 0 := by omega
  subst h5
  simpa using hm

theorem ee_one : ee 1 = ee 0 := by
  have := ee_add_one 0
  simpa using this

section

variable {Y S : Type uu} [TopologicalSpace Y] [TopologicalSpace S] [T2Space S] {ψ : Y
  → S} {F : Set S}

/-- The other lift of a loop. -/
theorem loop_lift {ξ : ℝ → Y} {X X' : Set Y} (hψ : IsCutting ψ F) (hun : X ∪ X' = ψ ⁻¹' F)
  (b1 : BijOn ψ X F) (b2 : BijOn ψ X' F)
    (hX' : IsCompact X') (cξ : ContinuousOn ξ (Icc 0 1)) (himξ : ξ '' Icc 0 1 = X) :
    ∃ η : ℝ → Y, ArcLift ψ F (fun u => ψ (ξ u)) ξ η ∧ η '' Icc 0 1 = X' ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ξ u = ξ v ↔ η u = η v := by
  obtain ⟨hcψ, -, hinj, -, -⟩ := id hψ
  have hne : Nonempty Y := by
    obtain ⟨z, hz⟩ : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
    exact ⟨ξ z⟩
  obtain ⟨ψ', hψ'c, hψ'⟩ := exists_inv_of_compactOn hX' hcψ.continuousOn b2.injOn
  have him : ψ '' X' = F := b2.image_eq
  have hξX : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ mem_image_of_mem ξ hu
  have hc1 : ContinuousOn (fun u => ψ (ξ u)) (Icc 0 1) := hcψ.comp_continuousOn cξ
  have hc2 : ContinuousOn (fun u => ψ' (ψ (ξ u))) (Icc 0 1) :=
    hψ'c.comp hc1 fun u hu => by
      rw [him]
      exact b1.mapsTo (hξX u hu)
  have hηX : ∀ u ∈ Icc (0 : ℝ) 1, ψ' (ψ (ξ u)) ∈ X' ∧ ψ (ψ' (ψ (ξ u))) = ψ (ξ u) := fun u hu => by
    obtain ⟨y, hy, he⟩ := b2.surjOn (b1.mapsTo (hξX u hu))
    rw [← he, hψ' hy]
    exact ⟨hy, rfl⟩
  refine ⟨fun u => ψ' (ψ (ξ u)), ⟨cξ, hc2, fun u _ => rfl, fun u hu => (hηX u hu).2, ?_, ?_⟩, ?_,
    fun u hu v hv => ⟨fun he => ?_, fun he => ?_⟩⟩
  · rw [← b1.image_eq, ← himξ, image_image]
  · intro y y' he hne'
    by_cases hy : ψ y ∈ F
    · have m1 : y ∈ X ∪ X' := by
        rw [hun]
        exact hy
      have m2 : y' ∈ X ∪ X' := by
        rw [hun]
        change ψ y' ∈ F
        rw [← he]
        exact hy
      have key : ∀ z ∈ X, ∀ z' ∈ X', ψ z = ψ z' → ∃ u ∈ Icc (0 : ℝ) 1, z = ξ u ∧ z' = ψ' (ψ (ξ u))
        := by
        intro z hz z' hz' he'
        obtain ⟨u, hu, rfl⟩ := himξ.symm.subset hz
        exact ⟨u, hu, rfl, by rw [he', hψ' hz']⟩
      rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2
      · exact absurd (b1.injOn m1 m2 he) hne'
      · obtain ⟨u, hu, h11, h12⟩ := key y m1 y' m2 he
        exact ⟨u, hu, .inl ⟨h11, h12⟩⟩
      · obtain ⟨u, hu, h11, h12⟩ := key y' m2 y m1 he.symm
        exact ⟨u, hu, .inr ⟨h11, h12⟩⟩
      · exact absurd (b2.injOn m1 m2 he) hne'
    · exact absurd (hinj hy (show ψ y' ∈ Fᶜ from he ▸ hy) he) hne'
  · ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hηX u hu).1
    · intro hz
      obtain ⟨y, hy, he⟩ := b1.surjOn (b2.mapsTo hz)
      obtain ⟨u, hu, rfl⟩ := himξ.symm.subset hy
      refine ⟨u, hu, ?_⟩
      change ψ' (ψ (ξ u)) = z
      rw [he, hψ' hz]
  · simp only [he]
  · have h11 : ψ (ξ u) = ψ (ξ v) := by
      rw [← (hηX u hu).2, ← (hηX v hv).2]
      exact congrArg ψ he
    exact b1.injOn (hξX u hu) (hξX v hv) h11

end

/-- Counts labels in an explicit word whose tail has known counts. -/
local macro "ct" : tactic =>
  `(tactic| ((try simp only [hB, holB, List.cons_append, List.nil_append, List.append_assoc,
    cnt_append, cnt_cons, cnt_nil, tL, rL, frL, linv, Prod.fst, *]); (try split_ifs) <;> omega))

section

variable {Y S : Type uu} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] {ψ : Y
  → S} {F : Set S}
  {a b c i j : ℕ} {L : List ℕ}

omit [T2Space Y] in
/-- Two cuffs of a connected surface are the lifts of an `O`-arc. -/
theorem loop_two_aux [T2Space S] (hS : IsSurface Y) (hψ : IsCutting ψ F) {C C' : Set Y}
  (hC' : IsCuff C') (hcl : IsClosed C) (hcl' : IsClosed C')
    (hd : Disjoint C C') (hun : C ∪ C' = ψ ⁻¹' F) (b1 : BijOn ψ C F) (b2 : BijOn ψ C' F)
      (φ : Circle ≃ₜ C) (φ' : Circle ≃ₜ C')
    (hij : i ≠ j) (_hi : i < c) (_hj : j < c) (hL : ∀ m ∈ L, m < c ∧ m ≠ i ∧ m ≠ j) {g₀ : ℕ × ℂ → Y}
    (hg : Presents (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀)
    (h1 : SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀ (rL a b i).1 fun u => (φ (ee u)).1)
    (h2 : SideVal (sW (hB a b j ++ (hB a b i ++ rW a b c L))) g₀ (rL a b j).1 fun u => (φ'
      (ee u)).1) :
    ∃ (σ : Bool) (g : ℕ × ℂ → Y), Presents (sW (blkE a b i j σ ++ rW a b c L)) (ψ ∘ g) ∧
      SideVal (sW (blkE a b i j σ ++ rW a b c L)) (ψ ∘ g) (rL a b i).1 fun u => ψ (φ (ee u)).1 := by
  have : CompactSpace Y := hS.1
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have cξ : ContinuousOn (fun u => (φ (ee u)).1) (Icc 0 1) :=
    (continuous_subtype_val.comp (φ.continuous.comp continuous_ee)).continuousOn
  have injξ : InjOn (fun u => (φ (ee u)).1) (Ico 0 1) := fun x hx y hy he =>
    ee_injOn hx hy (φ.injective (Subtype.ext he))
  have h01 : (φ (ee 0)).1 = (φ (ee 1)).1 := by rw [ee_one]
  have himξ := loop_image φ cξ (fun u _ => (φ _).2) injξ h01
  obtain ⟨η, L₀, himη, hiff⟩ := loop_lift hψ hun b1 b2 hcl'.isCompact cξ himξ
  have hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C' := fun u hu => himη ▸ mem_image_of_mem η hu
  have cl : η 0 = η 1 := (hiff 0 m0 1 m1).mp h01
  have injη : InjOn η (Ico 0 1) := fun x hx y hy he =>
    injξ hx hy ((hiff x (Ico_subset_Icc_self hx) y (Ico_subset_Icc_self hy)).mpr he)
  obtain ⟨σ, n', c', s', h3, h4⟩ := exists_loop_turn φ' L₀.cη hη injη cl
  have c1 : cnt (rW a b c L) (2 * a + b + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c2 : cnt (rW a b c L) (2 * a + b + 2 * j + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  obtain ⟨g₁, p1, p2, p3⟩ := exists_pieces1 hS hC' hcl.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd) φ' hg h2 c' s' h3
  have p4 := p3 (rL a b i).1 _ h1 fun u _ h => h (φ _).2
  have e0 : hB a b j ++ (hB a b i ++ rW a b c L) = [tL a b j] ++ ((rL a b j).1, true) :: (linv
    (tL a b j) :: tL a b i :: rL a b i :: linv (tL a b i) :: rW a b c L) := by
    simp [hB, holB, rL]
  rw [e0] at p1 p2 p4
  obtain ⟨h5, h6⟩ := glue_word (p₁ := 4) L₀ hψ.1 hψ.2.1 (A := [tL a b j]) (q := (rL a b j).1) (p :=
    (rL a b i).1) (σ := σ) rfl (by simp)
    (by ct) (by ct) (by simp [rL]; omega) p1 p4 (ζ := fun u => (φ' (ee (n' u))).1) p2
    (fun u hu => by simp only [h4 _ (ofs_mem hu), ofs_ofs])
  exact ⟨σ, g₁, h5, h6⟩

/-- One cuff of a connected surface is the double lift of an `O`-arc. -/
theorem loop_one_aux (hS : IsSurface Y) {a₀ : ℝ → S} {ξ η : ℝ → Y} (L₀ : ArcLift ψ F a₀ ξ η)
  (hψc : Continuous ψ) (hsurj : Surjective ψ) {C : Set Y}
    (hC : IsCuff C) (φ : Circle ≃ₜ C) (hi : i < c) (hL : ∀ m ∈ L, m < c ∧ m ≠ i) {g₀ : ℕ × ℂ → Y}
    (hg : Presents (sW (hB a b i ++ rW a b c L)) g₀)
    (h1 : SideVal (sW (hB a b i ++ rW a b c L)) g₀ (rL a b i).1 fun u => (φ (ee u)).1)
    (hξ : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ C) (hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C) (hinj : InjOn
      (conc2 ξ η) (Ico 0 1)) (e1 : ξ 1 = η 0) (e2 : η 1 = ξ 0) :
    ∃ (g : ℕ × ℂ → Y) (a' : ℝ → S), Presents (sW (blkD a b i ++ rW a b c L)) (ψ ∘ g) ∧
      SideVal (sW (blkD a b i ++ rW a b c L)) (ψ ∘ g) (rL a b i).1 a' ∧ (∀ u ∈ Icc
        (0 : ℝ) 1, a' u ∈ F) ∧ a' 1 = a' 0 ∧
      ContinuousOn a' (Icc 0 1) := by
  have cρ := continuousOn_conc2 L₀.cξ L₀.cη e1
  have hρC : ∀ u ∈ Icc (0 : ℝ) 1, conc2 ξ η u ∈ C := by
    intro u hu
    unfold conc2
    split_ifs with h2
    · exact hξ _ ⟨by linarith [hu.1], by linarith⟩
    · exact hη _ ⟨by linarith [not_le.mp h2], by linarith [hu.2]⟩
  have hcl : conc2 ξ η 0 = conc2 ξ η 1 := by rw [conc2_zero, conc2_one e1, e2]
  obtain ⟨σ, n, n1, n2, n3, n4⟩ := exists_loop_turn φ cρ hρC hinj hcl
  have c1m : ContinuousOn (fun u => n (u / 2)) (Icc 0 1) := n1.comp (by fun_prop) fun u hu
    => half_mem hu
  have c2m : ContinuousOn (fun u => n ((1 + u) / 2)) (Icc 0 1) := n1.comp (by fun_prop) fun u hu
    => half_mem' hu
  have s1m : StrictMonoOn (fun u => n (u / 2)) (Icc 0 1) := fun x hx y hy hxy => n2 (half_mem hx)
    (half_mem hy) (by linarith)
  have s2m : StrictMonoOn (fun u => n ((1 + u) / 2)) (Icc 0 1) := fun x hx y hy hxy => n2
    (half_mem' hx) (half_mem' hy) (by linarith)
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h01 : a₀ 1 = a₀ 0 := by rw [← L₀.hξ 1 m1, e1, L₀.hη 0 m0]
  have hval : ∃ (a' : ℝ → S) (ξ' η' : ℝ → Y), a' 1 = a' 0 ∧ ArcLift ψ F a' ξ' η' ∧ (∀ u ∈ Icc
    (0 : ℝ) 1, (φ (ee (n (u / 2)))).1 = ξ' u) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (n ((1 + u) / 2)))).1 = η' u := by
    cases σ with
    | true =>
      refine ⟨a₀, ξ, η, h01, L₀, fun u hu => ?_, fun u hu => ?_⟩
      · rw [n4 _ (half_mem hu), ofs_true, conc2_left hu]
      · rw [n4 _ (half_mem' hu), ofs_true, conc2_right e1 hu]
    | false =>
      refine ⟨_, _, _, ?_, L₀.rev.swap, fun u hu => ?_, fun u hu => ?_⟩
      · simp only [sub_self, sub_zero]
        exact h01.symm
      · rw [n4 _ (half_mem hu), ofs_false, show 1 - u / 2 = (1 + (1 - u)) / 2 by ring,
          conc2_right e1 (rev_mem hu)]
      · rw [n4 _ (half_mem' hu), ofs_false, show 1 - (1 + u) / 2 = (1 - u) / 2 by ring,
          conc2_left (rev_mem hu)]
  obtain ⟨a', ξ', η', hclosed, L', h2, h3⟩ := hval
  have c1 : cnt (rW a b c L) (2 * a + b + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have c3 : cnt (rW a b c L) (2 * a + b + 2 * c + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL m hm
    omega
  have e0 : hB a b i ++ rW a b c L = [tL a b i] ++ ((rL a b i).1, true) :: (linv
    (tL a b i) :: rW a b c L) := by
    simp [hB, holB, rL]
  rw [e0] at hg h1
  obtain ⟨g₁, p1, p2, p3, -⟩ := exists_pieces2 hS hC isOpen_univ (subset_univ _) φ (q := frL a b c)
    (by simp [rL, frL]; omega)
    (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) hg h1 c1m c2m s1m s2m (by norm_num) (by
      norm_num
      exact n3)
  obtain ⟨h5, h6⟩ := glue_word (p₁ := 1) L' hψc hsurj (A := [tL a b i, rL a b i]) (q := frL a b c)
    (p := (rL a b i).1)
    (B := linv (tL a b i) :: rW a b c L) (σ := true) rfl (by simp) (by ct) (by ct)
      (by simp [rL, frL]; omega) p1 (p2.congr h2) p3
    (fun u hu => by
      rw [ofs_true]
      exact h3 u hu)
  refine ⟨g₁, a', h5, h6, fun u hu => L'.img ▸ mem_image_of_mem a' hu, ?_, ?_⟩
  · exact hclosed
  · exact (hψc.comp_continuousOn L'.cξ).congr fun u hu => (L'.hξ u hu).symm

end

end GraphMinor.Surface
