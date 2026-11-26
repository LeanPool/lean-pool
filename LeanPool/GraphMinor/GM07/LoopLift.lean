/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Whisker
public import LeanPool.GraphMinor.GM07.Taper
public import LeanPool.GraphMinor.Surface.CutLoop
import LeanPool.GraphMinor.Surface.CutArc

/-!
# The two lifts of a loop

Cut a surface along an `O`-arc `F`, with a chosen point `v` of `F`. Going around `F` once from `v`
has two lifts to the cut surface
(`exists_loop_lifts`). The paper uses them in the proof of (7.3), for the two sides of a loop.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

/-- A map of `𝕀 × 𝕀` that agrees at the two ends of the first factor comes from a map of `Circle ×
𝕀`. -/
theorem exists_circle_descent {W : Type*} [TopologicalSpace W] {H : 𝕀 × 𝕀 → W} (hH : Continuous H)
    (he : ∀ p, H (0, p) = H (1, p)) :
    ∃ K : Circle × 𝕀 → W, Continuous K ∧ ∀ t p, K (ee t.1, p) = H (t, p) := by
  classical
  let q : 𝕀 × 𝕀 → Circle × 𝕀 := fun x => (ee x.1.1, x.2)
  have hqc : Continuous q := (continuous_ee.comp (continuous_subtype_val.comp
    continuous_fst)).prodMk continuous_snd
  have hqs : Surjective q := by
    rintro ⟨z, p⟩
    obtain ⟨x, rfl⟩ := ee_surjective z
    refine ⟨(⟨Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, p), ?_⟩
    have h1 : ee (Int.fract x) = ee x := ee_eq_iff.mpr ⟨-⌊x⌋, by
      rw [Int.fract]
      push_cast
      ring⟩
    simp [q, h1]
  have hqq : IsQuotientMap q := (hqc.isClosedMap).isQuotientMap hqc hqs
  have hfib : ∀ x y, q x = q y → H x = H y := by
    rintro ⟨t, p⟩ ⟨t', p'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    obtain rfl : p = p' := h2
    obtain ⟨m, hm⟩ := ee_eq_iff.mp h1
    change (t : ℝ) = t' + m at hm
    have ht := t.2
    have ht' := t'.2
    have hm1 : (m : ℝ) ≤ 1 := by linarith [ht.2, ht'.1]
    have hm2 : (-1 : ℝ) ≤ m := by linarith [ht.1, ht'.2]
    have hm3 : m ≤ 1 := by exact_mod_cast hm1
    have hm4 : -1 ≤ m := by exact_mod_cast hm2
    obtain rfl | rfl | rfl : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    · have h0 : t = 0 := Subtype.ext (by
        change (t : ℝ) = 0
        push_cast at hm
        linarith [ht.1, ht'.2])
      have h1' : t' = 1 := Subtype.ext (by
        change (t' : ℝ) = 1
        push_cast at hm
        linarith [ht.1, ht'.2])
      rw [h0, h1', he]
    · have : t = t' := Subtype.ext (by simpa using hm)
      rw [this]
    · have h0 : t' = 0 := Subtype.ext (by
        change (t' : ℝ) = 0
        push_cast at hm
        linarith [ht.2, ht'.1])
      have h1' : t = 1 := Subtype.ext (by
        change (t : ℝ) = 1
        push_cast at hm
        linarith [ht.2, ht'.1])
      rw [h0, h1', he]
  have hK : Continuous (fun z => H (surjInv hqs z)) := by
    refine hqq.continuous_iff.mpr ?_
    have : (fun z => H (surjInv hqs z)) ∘ q = H := funext fun x => hfib _ _ (surjInv_eq hqs _)
    rw [this]
    exact hH
  exact ⟨_, hK, fun t p => hfib _ _ (surjInv_eq hqs _)⟩

/-- The shift of `[0, 1)` that starts at `s`. -/
noncomputable def rotShift (s t : ℝ) : ℝ := if t < 1 - s then s + t else s + t - 1

theorem rotShift_mem {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico
  (0 : ℝ) 1) : rotShift s t ∈ Ico (0 : ℝ) 1 := by
  unfold rotShift
  split_ifs with h
  · exact ⟨by linarith [hs.1, ht.1], by linarith⟩
  · exact ⟨by linarith, by linarith [hs.2, ht.2]⟩

theorem rotShift_inj {s : ℝ} : InjOn (rotShift s) (Ico 0 1) := by
  intro t ht t' ht' he
  unfold rotShift at he
  split_ifs at he <;> linarith [ht.1, ht.2, ht'.1, ht'.2]

theorem rotShift_surj {s u : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hu : u ∈ Ico (0 : ℝ) 1) : ∃ t ∈ Ico
  (0 : ℝ) 1, rotShift s t = u := by
  by_cases h : s ≤ u
  · refine ⟨u - s, ⟨by linarith, by linarith [hu.2, hs.1]⟩, ?_⟩
    unfold rotShift
    rw [ite_eq_left (by linarith [hu.2])]
    ring
  · push Not at h
    refine ⟨u - s + 1, ⟨by linarith [hu.1, hs.2], by linarith⟩, ?_⟩
    unfold rotShift
    rw [ite_eq_right (by linarith [hu.1])]
    ring

/-- Two paths with `g 1 = g' 0`, cut at `s` and joined up. -/
noncomputable def rotPath {W : Type*} (s : ℝ) (g g' : ℝ → W) (t : ℝ) : W :=
  if t < 1 - s then g (s + t) else g' (s + t - 1)

theorem continuousOn_rotPath {W : Type*} [TopologicalSpace W] {s : ℝ} (hs : s ∈ Ico
  (0 : ℝ) 1) {g g' : ℝ → W}
    (hg : ContinuousOn g (Icc 0 1)) (hg' : ContinuousOn g' (Icc 0 1)) (he : g 1 = g' 0) :
    ContinuousOn (rotPath s g g') (Icc 0 1) := by
  have hcov : Icc (0 : ℝ) 1 = Icc 0 (1 - s) ∪ Icc (1 - s) 1 :=
    (Icc_union_Icc_eq_Icc (by linarith [hs.2]) (by linarith [hs.1])).symm
  rw [hcov]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · refine (hg.comp (by fun_prop) (fun t ht => ?_) : ContinuousOn (fun t => g
      (s + t)) _).congr fun t ht => ?_
    · exact ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
    · unfold rotPath
      split_ifs with h
      · rfl
      · have : t = 1 - s := le_antisymm ht.2 (not_lt.mp h)
        subst this
        simp [he]
  · refine (hg'.comp (by fun_prop) (fun t ht => ?_) : ContinuousOn (fun t => g'
      (s + t - 1)) _).congr fun t ht => ?_
    · exact ⟨by linarith [ht.1], by linarith [ht.2, hs.2]⟩
    · unfold rotPath
      rw [ite_eq_right (not_lt.mpr ht.1)]
      rfl

section

variable {Y S : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] [T2Space S] {ψ : Y
  → S}

omit [T2Space Y] in
/-- Going around an `O`-arc once from a given point has two lifts to the cut surface. -/
theorem exists_loop_lifts {F Z₁ Z₂ : Set S} {u c v : S} {X₁ Y₁ X₂ Y₂ : Set Y}
  (hcut : IsCutting ψ F) (h : LiftPair ψ Z₁ u c X₁ Y₁)
    (h' : LiftPair ψ Z₂ c u X₂ Y₂) (hi : Z₁ ∩ Z₂ = {u, c}) (hun : Z₁ ∪ Z₂ = F) (huc : u ≠ c) (hu :
      (ψ ⁻¹' {u}).encard ≤ 2)
    (hc : (ψ ⁻¹' {c}).encard ≤ 2) (hv : v ∈ F) :
    ∃ (a : 𝕀 → S) (ξ η : 𝕀 → Y), Continuous ξ ∧ Continuous η ∧ (∀ t, ψ (ξ t) = a t) ∧ (∀ t, ψ (η t)
      = a t) ∧ a 0 = v ∧ a 1 = v ∧
      range a = F ∧ InjOn a (Ioo 0 1) ∧ (∀ t ∈ Ioo (0 : 𝕀) 1, a t ≠ v) ∧ (∀ t, ξ t ≠ η t) ∧
      (∀ y, ψ y ∈ F → ∃ t, y = ξ t ∨ y = η t) := by
  classical
  have hψ := hcut.1
  obtain ⟨a, ξ, η, c1, c2, h1, h2, h3, h4, h5, h6, h7⟩ := h.paths h' hi huc hu hc hψ
  rw [hun] at h3 h4
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have ha1 : a 1 = a 0 := by
    rcases h7 with ⟨h8, -⟩ | ⟨h8, -⟩
    · rw [← h1 1 m1, h8, h1 0 m0]
    · rw [← h1 1 m1, h8, h2 0 m0]
  -- A start in `[0, 1)`.
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ Ico (0 : ℝ) 1, a s = v := by
    obtain ⟨s, hs, he⟩ := (h3 ▸ hv : v ∈ a '' Icc 0 1)
    rcases eq_or_lt_of_le hs.2 with rfl | h9
    · exact ⟨0, by simp, by rw [← ha1]; exact he⟩
    · exact ⟨s, ⟨hs.1, h9⟩, he⟩
  obtain ⟨ξ', η', hξ', hη', hpair⟩ : ∃ ξ' η' : ℝ → Y, ContinuousOn ξ' (Icc 0 1) ∧ ContinuousOn η'
    (Icc 0 1) ∧
      ∀ t, (ξ' t = rotPath s ξ ξ t ∧ η' t = rotPath s η η t) ∨ (ξ' t = rotPath s ξ η t ∧ η' t
        = rotPath s η ξ t) := by
    rcases h7 with ⟨h8, h9⟩ | ⟨h8, h9⟩
    · exact ⟨_, _, continuousOn_rotPath hs c1 c1 h8, continuousOn_rotPath hs c2 c2 h9,
        fun t => .inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, continuousOn_rotPath hs c1 c2 h8, continuousOn_rotPath hs c2 c1 h9,
        fun t => .inr ⟨rfl, rfl⟩⟩
  have hshift : ∀ t ∈ Icc (0 : ℝ) 1, rotShift s t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    unfold rotShift
    split_ifs with h9
    · exact ⟨by linarith [hs.1, ht.1], by linarith⟩
    · exact ⟨by linarith, by linarith [hs.2, ht.2]⟩
  have hform : ∀ {g g' : ℝ → Y} (t : ℝ), rotPath s g g' t = g (rotShift s t) ∨ rotPath s g g' t
    = g' (rotShift s t) := by
    intro g g' t
    unfold rotPath rotShift
    split_ifs
    · exact .inl rfl
    · exact .inr rfl
  let a' : ℝ → S := fun t => a (rotShift s t)
  have hvals : ∀ {g g' : ℝ → Y}, (∀ t ∈ Icc (0 : ℝ) 1, ψ (g t) = a t) → (∀ t ∈ Icc (0 : ℝ) 1, ψ
    (g' t) = a t) →
      ∀ t ∈ Icc (0 : ℝ) 1, ψ (rotPath s g g' t) = a' t := by
    intro g g' hg hg' t ht
    rcases hform (g := g) (g' := g') t with h9 | h9
    · rw [h9]; exact hg _ (hshift t ht)
    · rw [h9]; exact hg' _ (hshift t ht)
  have hξa : ∀ t ∈ Icc (0 : ℝ) 1, ψ (ξ' t) = a' t := fun t ht => by
    rcases hpair t with ⟨h9, -⟩ | ⟨h9, -⟩
    · rw [h9]; exact hvals h1 h1 t ht
    · rw [h9]; exact hvals h1 h2 t ht
  have hηa : ∀ t ∈ Icc (0 : ℝ) 1, ψ (η' t) = a' t := fun t ht => by
    rcases hpair t with ⟨-, h9⟩ | ⟨-, h9⟩
    · rw [h9]; exact hvals h2 h2 t ht
    · rw [h9]; exact hvals h2 h1 t ht
  have ha'0 : a' 0 = v := by
    have : rotShift s 0 = s := by
      unfold rotShift
      rw [ite_eq_left (by linarith [hs.2])]
      ring
    simp only [a', this, hsv]
  have ha'1 : a' 1 = v := by
    have : rotShift s 1 = s := by
      unfold rotShift
      rw [ite_eq_right (by linarith [hs.1])]
      ring
    simp only [a', this, hsv]
  have hinj : InjOn a' (Ico 0 1) := fun t ht t' ht' he =>
    rotShift_inj ht ht' (h5 (rotShift_mem hs ht) (rotShift_mem hs ht') he)
  have hIcc : ∀ t : 𝕀, (t : ℝ) ∈ Icc (0 : ℝ) 1 := fun t => t.2
  have hIco : ∀ t ∈ Ioo (0 : 𝕀) 1, (t : ℝ) ∈ Ico (0 : ℝ) 1 := fun t ht => ⟨t.2.1, ht.2⟩
  refine ⟨fun t => a' t, fun t => ξ' t, fun t => η' t, ?_, ?_, fun t => hξa t (hIcc t),
    fun t => hηa t (hIcc t), ha'0, ha'1, ?_, ?_, ?_, ?_, ?_⟩
  · exact hξ'.comp_continuous continuous_subtype_val hIcc
  · exact hη'.comp_continuous continuous_subtype_val hIcc
  · apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      rw [← h3]
      exact mem_image_of_mem a (hshift t (hIcc t))
    · intro x hx
      rw [← h3] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', he⟩ : ∃ w' ∈ Ico (0 : ℝ) 1, a w' = a w := by
        rcases eq_or_lt_of_le hw.2 with rfl | h9
        · exact ⟨0, by simp, ha1.symm⟩
        · exact ⟨w, ⟨hw.1, h9⟩, rfl⟩
      obtain ⟨t, ht, he'⟩ := rotShift_surj hs hw'
      exact ⟨⟨t, ht.1, ht.2.le⟩, by
        change a (rotShift s t) = _
        rw [he', he]⟩
  · exact fun t ht t' ht' he => Subtype.ext (hinj (hIco t ht) (hIco t' ht') he)
  · intro t ht he
    have h9 : a' t = a' 0 := by rw [ha'0]; exact he
    have := hinj (hIco t ht) (by simp) h9
    exact (ne_of_gt ht.1) (Subtype.ext this)
  · intro t he
    change ξ' t = η' t at he
    have hne := h6 (rotShift s t) (hshift t (hIcc t))
    have hsame : ∀ {g₁ g₂ g₃ g₄ : ℝ → Y}, rotPath s g₁ g₂ t.1 = rotPath s g₃ g₄ t.1 → (t.1 < 1 - s
      → g₁ (s + t.1) = g₃ (s + t.1)) ∧ (¬ t.1 < 1 - s → g₂ (s + t.1 - 1) = g₄ (s + t.1 - 1)) := by
      intro g₁ g₂ g₃ g₄ h9
      unfold rotPath at h9
      refine ⟨fun h10 => ?_, fun h10 => ?_⟩
      · rwa [ite_eq_left h10, ite_eq_left h10] at h9
      · rwa [ite_eq_right h10, ite_eq_right h10] at h9
    by_cases h10 : t.1 < 1 - s
    · have h11 : rotShift s t = s + t.1 := by unfold rotShift; rw [ite_eq_left h10]
      rw [h11] at hne
      rcases hpair t with ⟨h8, h9⟩ | ⟨h8, h9⟩ <;> · rw [h8, h9] at he; exact hne ((hsame he).1 h10)
    · have h11 : rotShift s t = s + t.1 - 1 := by unfold rotShift; rw [ite_eq_right h10]
      rw [h11] at hne
      rcases hpair t with ⟨h8, h9⟩ | ⟨h8, h9⟩
      · rw [h8, h9] at he; exact hne ((hsame he).2 h10)
      · rw [h8, h9] at he; exact hne ((hsame he).2 h10).symm
  · intro y hy
    obtain ⟨y', hy', hne⟩ : ∃ y', ψ y' = ψ y ∧ y ≠ y' := by
      have h9 := hcut.2.2.2.1 _ hy
      obtain ⟨p, q, hpq, he⟩ := ncard_eq_two.mp h9
      have hp : p ∈ ψ ⁻¹' {ψ y} := by rw [he]; simp
      have hq : q ∈ ψ ⁻¹' {ψ y} := by rw [he]; simp
      by_cases hyp : y = p
      · exact ⟨q, hq, by rw [hyp]; exact hpq⟩
      · exact ⟨p, hp, hyp⟩
    obtain ⟨u', hu', hcase⟩ := h4 y y' hy'.symm hne hy
    have hy1 : ∃ u'' ∈ Ico (0 : ℝ) 1, y = ξ u'' ∨ y = η u'' := by
      have hyu : y = ξ u' ∨ y = η u' := by
        rcases hcase with h9 | h9
        · exact .inl h9.1
        · exact .inr h9.2
      rcases eq_or_lt_of_le hu'.2 with rfl | h10
      · refine ⟨0, by simp, ?_⟩
        rcases h7 with ⟨h8, h9⟩ | ⟨h8, h9⟩
        · rcases hyu with h11 | h11
          · exact .inl (h11.trans h8)
          · exact .inr (h11.trans h9)
        · rcases hyu with h11 | h11
          · exact .inr (h11.trans h8)
          · exact .inl (h11.trans h9)
      · exact ⟨u', ⟨hu'.1, h10⟩, hyu⟩
    obtain ⟨u'', hu'', hyu⟩ := hy1
    obtain ⟨t, ht, he⟩ := rotShift_surj hs hu''
    refine ⟨⟨t, ht.1, ht.2.le⟩, ?_⟩
    have hval : ∀ {g g' : ℝ → Y}, (t < 1 - s → rotPath s g g' t = g u'') ∧ (¬ t < 1 - s
      → rotPath s g g' t = g' u'') := by
      intro g g'
      unfold rotPath
      unfold rotShift at he
      refine ⟨fun h10 => ?_, fun h10 => ?_⟩
      · rw [ite_eq_left h10] at he ⊢
        rw [he]
      · rw [ite_eq_right h10] at he ⊢
        rw [he]
    change y = ξ' t ∨ y = η' t
    by_cases h10 : t < 1 - s
    · rcases hpair t with ⟨h8, h9⟩ | ⟨h8, h9⟩
      · rw [h8, h9, hval.1 h10, hval.1 h10]; exact hyu
      · rw [h8, h9, hval.1 h10, hval.1 h10]; exact hyu
    · rcases hpair t with ⟨h8, h9⟩ | ⟨h8, h9⟩
      · rw [h8, h9, hval.2 h10, hval.2 h10]; exact hyu
      · rw [h8, h9, hval.2 h10, hval.2 h10]; exact hyu.symm

end

end GraphMinor.GM07
