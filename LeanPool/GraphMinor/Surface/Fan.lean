/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Dissection
public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.Surface.ArcTools
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Isometry

/-!
# Fans in a closed disc

A closed disc with marked points on its boundary is cut into triangles by arcs from one boundary
point to the other marked points (`exists_disc_fan`). We use it to triangulate a surface, which is
what the Euler count of Graph Minors XIX, (6.5) (page 341) needs.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X]

/-- A cutting of the closed disc `Δ` by arcs `𝓛` into discs `𝓒`, each with three points of `Q`. -/
structure IsChordFan (Δ Q : Set X) (𝓛 𝓒 : Set (Set X)) : Prop where
  finL : 𝓛.Finite
  finS : 𝓒.Finite
  disc : ∀ Φ ∈ 𝓒, IsClosedDisc Φ
  sub : ∀ Φ ∈ 𝓒, Φ ⊆ Δ
  bd : ∀ Φ ∈ 𝓒, discBd Φ ⊆ discBd Δ ∪ ⋃₀ 𝓛
  int : ∀ Φ ∈ 𝓒, Disjoint (discInt Φ) (discBd Δ ∪ ⋃₀ 𝓛)
  cover : ⋃₀ 𝓒 = Δ
  disj : ∀ Φ ∈ 𝓒, ∀ Φ' ∈ 𝓒, Φ ≠ Φ' → Disjoint (discInt Φ) Φ'
  three : ∀ Φ ∈ 𝓒, (Φ ∩ Q).ncard = 3
  subL : ∀ L ∈ 𝓛, L ⊆ Δ
  count₁ : ∀ x ∈ discBd Δ, x ∉ Q → {Φ ∈ 𝓒 | x ∈ Φ}.encard ≤ 1
  count₂ : ∀ x, x ∉ Q → {Φ ∈ 𝓒 | x ∈ Φ}.encard ≤ 2

variable [T2Space X]

/-- Two points of the boundary of a closed disc are joined by an arc through the interior. -/
theorem exists_chord {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {Δ : Set Y} (hΔ : IsClosedDisc Δ) {a b : Y} (ha : a ∈ discBd Δ)
    (hb : b ∈ discBd Δ) (hab : a ≠ b) :
    ∃ F, IsLineWithEnds F a b ∧ F ⊆ Δ ∧ F ∩ discBd Δ = {a, b} := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hbdΔ : discBd Δ ⊆ Δ := discBd_subset Δ
  have hsph : ∀ x ∈ discBd Δ, h x ∈ sphere (0 : ℂ) 1 := fun x hx => c.bd ▸ mem_image_of_mem h hx
  set p := h a with hp
  set q := h b with hq
  have hpq : p ≠ q := fun he => hab (by rw [← c.gh (hbdΔ ha), ← c.gh (hbdΔ hb), ← hp, ← hq, he])
  let z : 𝕀 → ℂ := fun t => ((1 - t.1 : ℝ) : ℂ) * p + ((t.1 : ℝ) : ℂ) * q
  have hzc : Continuous z := by
    have h1 : Continuous fun t : 𝕀 => ((t.1 : ℝ) : ℂ) := by fun_prop
    have h2 : Continuous fun t : 𝕀 => ((1 - t.1 : ℝ) : ℂ) := by fun_prop
    exact (h2.mul continuous_const).add (h1.mul continuous_const)
  have hzb : ∀ t, z t ∈ closedBall (0 : ℂ) 1 := fun t => by
    have h1 := (convex_closedBall (0 : ℂ) 1) (sphere_subset_closedBall (hsph a ha))
      (sphere_subset_closedBall (hsph b hb)) (a := 1 - t.1) (b := t.1) (by linarith [t.2.2]) t.2.1
        (by ring)
    simpa [z, Complex.real_smul] using h1
  have hzi : Function.Injective z := fun s t he => by
    have h1 : ((t.1 - s.1 : ℝ) : ℂ) * (q - p) = 0 := by
      simp only [z] at he
      push_cast at he ⊢
      linear_combination -he
    rcases mul_eq_zero.mp h1 with h2 | h2
    · have h3 : t.1 - s.1 = 0 := by exact_mod_cast h2
      exact Subtype.ext (by linarith)
    · exact absurd (sub_eq_zero.mp h2).symm hpq
  have hz0 : z 0 = p := by simp [z]
  have hz1 : z 1 = q := by simp [z]
  have harc : IsArcMap (g ∘ z) := ⟨c.gc.comp_continuous hzc hzb, fun s t he => hzi (by
    have := congrArg h he
    rwa [Function.comp_apply, Function.comp_apply, c.hg (hzb s), c.hg (hzb t)] at this)⟩
  have hl := harc.isLineWithEnds
  have hg0 : (g ∘ z) 0 = a := by rw [Function.comp_apply, hz0, hp, c.gh (hbdΔ ha)]
  have hg1 : (g ∘ z) 1 = b := by rw [Function.comp_apply, hz1, hq, c.gh (hbdΔ hb)]
  rw [hg0, hg1] at hl
  refine ⟨_, hl, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact c.gm (hzb t)
  · ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      have h1 := hsph _ hx
      rw [Function.comp_apply, c.hg (hzb t)] at h1
      by_cases ht0 : t = 0
      · exact .inl (by subst ht0; exact hg0)
      by_cases ht1 : t = 1
      · exact .inr (by subst ht1; exact hg1)
      exfalso
      have ht : t.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne t.2.1 (fun he => ht0 (Subtype.ext he.symm)),
        lt_of_le_of_ne t.2.2 (fun he => ht1 (Subtype.ext he))⟩
      have h2 := (strictConvex_closedBall ℝ (0 : ℂ) 1) (sphere_subset_closedBall (hsph a ha))
        (sphere_subset_closedBall (hsph b hb)) hpq (a := 1 - t.1) (b := t.1)
          (by linarith [ht.2]) ht.1 (by ring)
      rw [interior_closedBall _ one_ne_zero, mem_ball_zero_iff] at h2
      have h3 : ‖z t‖ = 1 := by simpa using h1
      have h4 : ‖z t‖ < 1 := by simpa [z, Complex.real_smul] using h2
      linarith
    · rintro (rfl | rfl)
      · exact ⟨⟨0, hg0⟩, ha⟩
      · exact ⟨⟨1, hg1⟩, hb⟩

omit [T2Space X] in
/-- `{x}` joined to the part of a line off its two ends is preconnected. -/
theorem IsLineWithEnds.isPreconnected_diff_right {L : Set X} {u v : X} (h : IsLineWithEnds L u v) :
    IsPreconnected (L \ {v}) := by
  refine h.isPreconnected_diff.subset_closure (fun x hx => ⟨hx.1,
    fun h' => hx.2 (.inr h')⟩) fun x hx => ?_
  exact h.subset_closure_diff hx.1

omit [T2Space X] in
theorem IsLineWithEnds.isPreconnected_diff_left {L : Set X} {u v : X} (h : IsLineWithEnds L u v) :
    IsPreconnected (L \ {u}) := by
  refine h.isPreconnected_diff.subset_closure (fun x hx => ⟨hx.1,
    fun h' => hx.2 (.inl h')⟩) fun x hx => ?_
  exact h.subset_closure_diff hx.1

omit [T2Space X] in
private theorem inter_eq_singleton_of_boundary_contacts
    {L F K B : Set X} {c p q : X} (hL : IsLineWithEnds L c p) (hcF : c ∈ F)
    (hLK : L ∩ K = {c, p}) (hFK : F ⊆ K)
    (hFB : F ∩ B = {c, q}) (hpB : p ∈ B) (hpq : p ≠ q) : L ∩ F = {c} := by
  ext y
  constructor
  · rintro ⟨hyL, hyF⟩
    rcases hLK.subset ⟨hyL, hFK hyF⟩ with hyc | hyp
    · exact hyc
    · have e : y = p := hyp
      rcases hFB.subset ⟨hyF, e.symm ▸ hpB⟩ with hyc | hyq
      · exact hyc
      · exact (hpq (e.symm.trans hyq)).elim
  · rintro rfl
    exact ⟨hL.left_mem, hcF⟩

omit [T2Space X] in
private theorem attach_chord_to_fan {Δ Δ₁ Δ₂ F X₁ : Set X} {r : 𝕀 → X}
    (S : Finset 𝕀) {s₀ s₁ : 𝕀} {n : ℕ}
    (hcard : S.card = n + 1 + 2) (hr : IsArcMap r)
    (hs₀ : s₀ ∈ S) (hs₁m : s₁ ∈ S.erase s₀) (h1 : (1 : 𝕀) ∉ S)
    (hmin' : ∀ s ∈ S.erase s₀, s₁ ≤ s)
    (hmemr : ∀ {x}, s₀ ≤ x → r x ∈ discBd Δ) (hmin : ∀ s ∈ S, s₀ ≤ s)
    (hΔ₁ : IsClosedDisc Δ₁) (hun : Δ₁ ∪ Δ₂ = Δ) (hint : Δ₁ ∩ Δ₂ = F) :
    let c := r 1
    let u := r s₀
    let q := r s₁
    let X₂ := r '' Icc s₁ 1 \ {q, c}
    (hb₁ : discBd Δ₁ = X₁ ∪ F) → (hb₂ : discBd Δ₂ = X₂ ∪ F) →
    (hF : IsLineWithEnds F c q) → (hFΔ : F ⊆ Δ) → (hFbd : F ∩ discBd Δ = {c, q}) →
    (hX₁sub : X₁ ⊆ discBd Δ \ {c, q}) → (hX₂sub : X₂ ⊆ discBd Δ \ {c, q}) →
    (hu_X₁ : u ∈ X₁) → (∀ {y}, y ∈ X₁ → y ∉ Δ₂) → (∀ {y}, y ∈ X₂ → y ∉ Δ₁) →
    (hbdsplit : ∀ {y}, y ∈ discBd Δ → y ∈ X₁ ∨ y ∈ X₂ ∨ y = c ∨ y = q) →
    ∀ {𝓛 𝓒 : Set (Set X)}, IsChordFan Δ₂ (insert c (r '' (S.erase s₀ : Set 𝕀))) 𝓛 𝓒 →
      𝓛.ncard = n → 𝓒.ncard = n + 1 →
      (∀ L ∈ 𝓛, ∃ s ∈ S.erase s₀, s ≠ s₁ ∧ (∃ t ∈ S.erase s₀, s < t) ∧
        IsLineWithEnds L c (r s) ∧ L ∩ discBd Δ₂ = {c, r s}) →
      (∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c}) →
      (∀ Φ ∈ 𝓒, Φ ∩ insert c (r '' (S : Set 𝕀)) =
        Φ ∩ insert c (r '' (S.erase s₀ : Set 𝕀))) →
      F ∉ 𝓛 → Δ₁ ∉ 𝓒 →
      ∃ 𝓛' 𝓒' : Set (Set X), IsChordFan Δ (insert c (r '' (S : Set 𝕀))) 𝓛' 𝓒' ∧
        𝓛'.ncard = n + 1 ∧ 𝓒'.ncard = n + 1 + 1 ∧
        (∀ L ∈ 𝓛', ∃ s ∈ S, s ≠ s₀ ∧ (∃ t ∈ S, s < t) ∧
          IsLineWithEnds L c (r s) ∧ L ∩ discBd Δ = {c, r s}) ∧
        ∀ L ∈ 𝓛', ∀ L' ∈ 𝓛', L ≠ L' → L ∩ L' = {c} := by
  classical
  intro c u q X₂ hb₁ hb₂ hF hFΔ hFbd hX₁sub hX₂sub hu_X₁ hX₁n hX₂n' hbdsplit
    𝓛 𝓒 hfan hnL hnS hspoke hpair hQ₂ hF𝓛 hΔ₁𝓒
  have hs₁S := Finset.mem_of_mem_erase hs₁m
  have hs₁n := Finset.ne_of_mem_erase hs₁m
  have hcq : c ≠ q := fun h => h1 (hr.2 h ▸ hs₁S)
  have hcu : c ≠ u := fun h => h1 (hr.2 h ▸ hs₀)
  have huq : u ≠ q := fun h => hs₁n (hr.2 h).symm
  have hcbd : c ∈ discBd Δ := hmemr s₀.2.2
  have hcF : c ∈ F := hF.left_mem
  have hqF : q ∈ F := hF.right_mem
  have hFb₁ : F ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hFb₂ : F ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  have hb₁s := discBd_subset Δ₁
  have hΔ₁s : Δ₁ ⊆ Δ := hun ▸ subset_union_left
  have hΔ₂s : Δ₂ ⊆ Δ := hun ▸ subset_union_right
  have hinF : ∀ {y}, y ∈ Δ₁ → y ∈ Δ₂ → y ∈ F := fun {y} h1' h2' => hint ▸ ⟨h1', h2'⟩
  have hFbd' : ∀ {y}, y ∈ F → y ∈ discBd Δ → y = c ∨ y = q := fun {y} h1' h2' => by
    have : y ∈ F ∩ discBd Δ := ⟨h1', h2'⟩
    rwa [hFbd] at this
  have hsubQ : (r '' (S.erase s₀ : Set 𝕀)) ⊆ r '' (S : Set 𝕀) :=
    image_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  refine ⟨insert F 𝓛, insert Δ₁ 𝓒, ⟨hfan.finL.insert _, hfan.finS.insert _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro Φ (rfl | hΦ)
    · exact hΔ₁
    · exact hfan.disc Φ hΦ
  · rintro Φ (rfl | hΦ)
    · exact hΔ₁s
    · exact (hfan.sub Φ hΦ).trans hΔ₂s
  · rintro Φ (rfl | hΦ)
    · rw [hb₁]
      rintro y (h2 | h2)
      · exact .inl (hX₁sub h2).1
      · exact .inr ⟨F, mem_insert _ _, h2⟩
    · refine (hfan.bd Φ hΦ).trans ?_
      rintro y (h2 | ⟨L, hL, h2⟩)
      · rw [hb₂] at h2
        rcases h2 with h2 | h2
        · exact .inl (hX₂sub h2).1
        · exact .inr ⟨F, mem_insert _ _, h2⟩
      · exact .inr ⟨L, mem_insert_of_mem _ hL, h2⟩
  · rintro Φ (rfl | hΦ)
    · refine Set.disjoint_left.mpr ?_
      rintro y hy (h2 | ⟨L, hL, h2⟩)
      · rcases hbdsplit h2 with h3 | h3 | rfl | rfl
        · exact hy.2 (hb₁ ▸ .inl h3)
        · exact hX₂n' h3 hy.1
        · exact hy.2 (hFb₁ hcF)
        · exact hy.2 (hFb₁ hqF)
      · rcases hL with rfl | hL
        · exact hy.2 (hFb₁ h2)
        · exact hy.2 (hFb₁ (hinF hy.1 (hfan.subL L hL h2)))
    · refine Set.disjoint_left.mpr ?_
      have h4 := hfan.int Φ hΦ
      rintro y hy (h2 | ⟨L, hL, h2⟩)
      · have hyΔ₂ := hfan.sub Φ hΦ hy.1
        rcases hbdsplit h2 with h3 | h3 | rfl | rfl
        · exact hX₁n h3 hyΔ₂
        · exact Set.disjoint_left.mp h4 hy (.inl (hb₂ ▸ .inl h3))
        · exact Set.disjoint_left.mp h4 hy (.inl (hFb₂ hcF))
        · exact Set.disjoint_left.mp h4 hy (.inl (hFb₂ hqF))
      · rcases hL with rfl | hL
        · exact Set.disjoint_left.mp h4 hy (.inl (hFb₂ h2))
        · exact Set.disjoint_left.mp h4 hy (.inr ⟨L, hL, h2⟩)
  · rw [sUnion_insert, hfan.cover, hun]
  · rintro Φ (rfl | hΦ) Φ' (rfl | hΦ') hne
    · exact absurd rfl hne
    · refine Set.disjoint_left.mpr fun y hy hy' => hy.2 (hFb₁ (hinF hy.1 (hfan.sub _ hΦ' hy')))
    · refine Set.disjoint_left.mpr fun y hy hy' => ?_
      exact Set.disjoint_left.mp (hfan.int Φ hΦ) hy (.inl (hFb₂ (hinF hy' (hfan.sub _ hΦ hy.1))))
    · exact hfan.disj Φ hΦ Φ' hΦ' hne
  · rintro Φ (rfl | hΦ)
    · have h2 : Φ ∩ insert c (r '' (S : Set 𝕀)) = {c, u, q} := by
        ext y
        constructor
        · rintro ⟨h3, h4⟩
          rcases h4 with rfl | ⟨s, hs, rfl⟩
          · exact .inl rfl
          · by_cases hs0 : s = s₀
            · exact .inr (.inl (congrArg r hs0))
            · have h5 := hmin' s (Finset.mem_erase.mpr ⟨hs0, hs⟩)
              by_cases hs2 : s = s₁
              · exact .inr (.inr (congrArg r hs2))
              · exfalso
                have h6 : r s ∈ X₂ := ⟨⟨s, ⟨h5, s.2.2⟩, rfl⟩, by
                  rintro (h7 | h7)
                  · exact hs2 (hr.2 h7)
                  · exact h1 ((hr.2 h7) ▸ Finset.mem_coe.mp hs)⟩
                exact hX₂n' h6 h3
        · rintro (rfl | rfl | rfl)
          · exact ⟨hb₁s (hFb₁ hcF), .inl rfl⟩
          · exact ⟨hb₁s (hb₁ ▸ .inl hu_X₁), .inr ⟨s₀, hs₀, rfl⟩⟩
          · exact ⟨hb₁s (hFb₁ hqF), .inr ⟨s₁, hs₁S, rfl⟩⟩
      rw [h2]
      exact ncard_eq_three.mpr ⟨_, _, _, hcu, hcq, huq, rfl⟩
    · rw [hQ₂ Φ hΦ]
      exact hfan.three Φ hΦ
  · rintro L (rfl | hL)
    · exact hFΔ
    · exact (hfan.subL L hL).trans hΔ₂s
  · intro y hy hyQ
    have hyQ₂ : y ∉ insert c (r '' ((S.erase s₀ : Finset 𝕀) : Set 𝕀)) := fun h => hyQ (by
      rcases h with h | h
      · exact .inl h
      · exact .inr (hsubQ h))
    by_cases hy1 : y ∈ Δ₁
    · have hy2 : y ∉ Δ₂ := by
        intro hy2
        rcases hFbd' (hinF hy1 hy2) hy with rfl | rfl
        · exact hyQ (.inl rfl)
        · exact hyQ (.inr ⟨s₁, hs₁S, rfl⟩)
      refine (encard_le_encard (t := {Δ₁}) ?_).trans (by simp)
      rintro Φ ⟨rfl | hΦ, h2⟩
      · rfl
      · exact absurd (hfan.sub Φ hΦ h2) hy2
    · have heq : {Φ ∈ insert Δ₁ 𝓒 | y ∈ Φ} ⊆ {Φ ∈ 𝓒 | y ∈ Φ} := by
        rintro Φ ⟨rfl | hΦ, h2⟩
        · exact absurd h2 hy1
        · exact ⟨hΦ, h2⟩
      refine (encard_le_encard heq).trans (hfan.count₁ y ?_ hyQ₂)
      rcases hbdsplit hy with h3 | h3 | rfl | rfl
      · exact absurd (hb₁s (hb₁ ▸ .inl h3)) hy1
      · exact hb₂ ▸ .inl h3
      · exact hFb₂ hcF
      · exact hFb₂ hqF
  · intro y hyQ
    have hyQ₂ : y ∉ insert c (r '' ((S.erase s₀ : Finset 𝕀) : Set 𝕀)) := fun h => hyQ (by
      rcases h with h | h
      · exact .inl h
      · exact .inr (hsubQ h))
    by_cases hy1 : y ∈ Δ₁
    · by_cases hy2 : y ∈ Δ₂
      · have h3 : {Φ ∈ insert Δ₁ 𝓒 | y ∈ Φ} ⊆ insert Δ₁ {Φ ∈ 𝓒 | y ∈ Φ} := by
          rintro Φ ⟨rfl | hΦ, h2⟩
          · exact mem_insert _ _
          · exact mem_insert_of_mem _ ⟨hΦ, h2⟩
        refine (encard_le_encard h3).trans ((encard_insert_le _ _).trans ?_)
        have h4 := hfan.count₁ y (hFb₂ (hinF hy1 hy2)) hyQ₂
        calc _ ≤ (1 : ℕ∞) + 1 := by gcongr
          _ = 2 := by norm_num
      · refine (encard_le_encard (t := {Δ₁}) ?_).trans (by simp)
        rintro Φ ⟨rfl | hΦ, h2⟩
        · rfl
        · exact absurd (hfan.sub Φ hΦ h2) hy2
    · have heq : {Φ ∈ insert Δ₁ 𝓒 | y ∈ Φ} ⊆ {Φ ∈ 𝓒 | y ∈ Φ} := by
        rintro Φ ⟨rfl | hΦ, h2⟩
        · exact absurd h2 hy1
        · exact ⟨hΦ, h2⟩
      exact (encard_le_encard heq).trans (hfan.count₂ y hyQ₂)
  · rw [ncard_insert_of_notMem hF𝓛 hfan.finL, hnL]
  · rw [ncard_insert_of_notMem hΔ₁𝓒 hfan.finS, hnS]
  · rintro L (rfl | hL)
    · refine ⟨s₁, hs₁S, hs₁n, ?_, hF, hFbd⟩
      have hnt : ((S.erase s₀).erase s₁).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hs₁m, Finset.card_erase_of_mem hs₀]
        omega
      obtain ⟨t, ht⟩ := hnt
      have ht1 := Finset.mem_of_mem_erase ht
      exact ⟨t, Finset.mem_of_mem_erase ht1, lt_of_le_of_ne (hmin' t ht1)
        (Finset.ne_of_mem_erase ht).symm⟩
    · obtain ⟨s, hs, hne, ⟨t, ht, hst⟩, hl, h3⟩ := hspoke L hL
      have hsS := Finset.mem_of_mem_erase hs
      refine ⟨s, hsS, Finset.ne_of_mem_erase hs, ⟨t, Finset.mem_of_mem_erase ht, hst⟩, hl, ?_⟩
      ext y
      constructor
      · rintro ⟨h4, h5⟩
        have h6 : y ∈ L ∩ discBd Δ₂ := by
          refine ⟨h4, ?_⟩
          rcases hbdsplit h5 with h7 | h7 | rfl | rfl
          · exact absurd (hfan.subL L hL h4) (hX₁n h7)
          · exact hb₂ ▸ .inl h7
          · exact hFb₂ hcF
          · exact hFb₂ hqF
        rwa [h3] at h6
      · rintro (rfl | rfl)
        · exact ⟨hl.left_mem, hcbd⟩
        · exact ⟨hl.right_mem, hmemr (hmin _ hsS)⟩
  · have hLF : ∀ L ∈ 𝓛, L ∩ F = {c} := by
      intro L hL
      obtain ⟨s, hs, hne, -, hl, hcontact⟩ := hspoke L hL
      exact inter_eq_singleton_of_boundary_contacts hl hcF hcontact hFb₂ hFbd
        (hmemr (hmin _ (Finset.mem_of_mem_erase hs))) (fun h => hne (hr.2 h))
    rintro L (rfl | hL) L' (rfl | hL') hne
    · exact absurd rfl hne
    · rw [inter_comm]
      exact hLF L' hL'
    · exact hLF L hL
    · exact hpair L hL L' hL' hne

omit [T2Space X] in
private theorem fan_of_split_subdisc {Δ F X₁ : Set X} {r : 𝕀 → X}
    (S : Finset 𝕀) {s₀ s₁ : 𝕀} {n : ℕ}
    (hcard : S.card = n + 1 + 2) (hr : IsArcMap r)
    (hs₀ : s₀ ∈ S) (hs₁m : s₁ ∈ S.erase s₀) (h1 : (1 : 𝕀) ∉ S)
    (hmin' : ∀ s ∈ S.erase s₀, s₁ ≤ s)
    (hmemr : ∀ {x}, s₀ ≤ x → r x ∈ discBd Δ) (hmin : ∀ s ∈ S, s₀ ≤ s) :
    let c := r 1
    let u := r s₀
    let q := r s₁
    let L₂ := r '' Icc s₁ 1
    let X₂ := L₂ \ {q, c}
    (hF : IsLineWithEnds F c q) → (hFΔ : F ⊆ Δ) → (hFbd : F ∩ discBd Δ = {c, q}) →
    (hX₁sub : X₁ ⊆ discBd Δ \ {c, q}) → (hX₂sub : X₂ ⊆ discBd Δ \ {c, q}) →
    (hX₁c : IsPreconnected X₁) → (hX₂c : IsPreconnected X₂) → (hu_X₁ : u ∈ X₁) →
    (hcover : discBd Δ \ {c, q} ⊆ X₁ ∪ X₂) →
    (hL₂sub : L₂ ⊆ discBd Δ) → (hl₂ : IsLineWithEnds L₂ q c) →
    (∀ {D : Set X}, IsClosedDisc D → IsLineWithEnds F c q →
      discBd D = L₂ ∪ F → L₂ ∩ F = {q, c} →
      ∃ 𝓛 𝓒 : Set (Set X), IsChordFan D (insert c (r '' (S.erase s₀ : Set 𝕀))) 𝓛 𝓒 ∧
        𝓛.ncard = n ∧ 𝓒.ncard = n + 1 ∧
        (∀ L ∈ 𝓛, ∃ s ∈ S.erase s₀, s ≠ s₁ ∧ (∃ t ∈ S.erase s₀, s < t) ∧
          IsLineWithEnds L c (r s) ∧ L ∩ discBd D = {c, r s}) ∧
        ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c}) →
    ∀ {A₁ A₂ Δ₁ Δ₂ : Set X},
      A₁ ≠ A₂ → componentsIn (discBd Δ \ {c, q}) = {A₁, A₂} →
        IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ∪ Δ₂ = Δ → Δ₁ ∩ Δ₂ = F → discBd Δ₁ = A₁ ∪ F →
        discBd Δ₂ = A₂ ∪ F → (∃ x ∈ X₂, connectedComponentIn (discBd Δ \ {c, q}) x = A₂) →
        ∃ 𝓛 𝓒 : Set (Set X), IsChordFan Δ (insert c (r '' S)) 𝓛 𝓒 ∧ 𝓛.ncard = n + 1 ∧ 𝓒.ncard
          = n + 1 + 1 ∧
      (∀ L ∈ 𝓛, ∃ s ∈ S, s ≠ s₀ ∧ (∃ t ∈ S, s < t) ∧ IsLineWithEnds L c (r s) ∧ L ∩ discBd Δ
        = {c, r s}) ∧
      ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c} := by
  classical
  intro c u q L₂ X₂ hF hFΔ hFbd hX₁sub hX₂sub hX₁c hX₂c hu_X₁ hcover hL₂sub hl₂ ih
  have hs₁S := Finset.mem_of_mem_erase hs₁m
  have hcq : c ≠ q := fun h => h1 (hr.2 h ▸ hs₁S)
  intro A₁ A₂ Δ₁ Δ₂ hA hcomp hΔ₁ hΔ₂ hun hint hb₁ hb₂ ⟨x₂, hx₂, hx₂A⟩
  have hA₂ : X₂ ⊆ A₂ := hx₂A ▸ hX₂c.subset_connectedComponentIn hx₂ hX₂sub
  have hcompu : connectedComponentIn (discBd Δ \ {c, q}) u = A₁ := by
    have h2 : connectedComponentIn (discBd Δ \ {c, q}) u ∈ componentsIn (discBd Δ \ {c, q}) :=
      ⟨u, hX₁sub hu_X₁, rfl⟩
    rw [hcomp] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exfalso
      have hX₁A : X₁ ⊆ A₂ := h2 ▸ hX₁c.subset_connectedComponentIn hu_X₁ hX₁sub
      have h3 : A₁ ∈ componentsIn (discBd Δ \ {c, q}) := hcomp ▸ .inl rfl
      obtain ⟨y, hy, hyA⟩ := h3
      have hyA₂ : y ∈ connectedComponentIn (discBd Δ \ {c, q}) x₂ := by
        rw [hx₂A]
        rcases hcover hy with h4 | h4
        · exact hX₁A h4
        · exact hA₂ h4
      rw [connectedComponentIn_eq hyA₂, hyA] at hx₂A
      exact hA hx₂A
  have hA₁ : X₁ ⊆ A₁ := hcompu ▸ hX₁c.subset_connectedComponentIn hu_X₁ hX₁sub
  have hdA : Disjoint A₁ A₂ := by
    refine Set.disjoint_left.mpr fun y h1' h2' => hA ?_
    rw [← hcompu] at h1' ⊢
    rw [← hx₂A] at h2' ⊢
    rw [connectedComponentIn_eq h1', connectedComponentIn_eq h2']
  have hA₁s : A₁ ⊆ discBd Δ \ {c, q} := hcompu ▸ connectedComponentIn_subset _ _
  have hA₂s : A₂ ⊆ discBd Δ \ {c, q} := hx₂A ▸ connectedComponentIn_subset _ _
  have hA₁e : A₁ = X₁ := Subset.antisymm (fun y hy => (hcover (hA₁s hy)).resolve_right fun h
    => Set.disjoint_left.mp hdA hy (hA₂ h)) hA₁
  have hA₂e : A₂ = X₂ := Subset.antisymm (fun y hy => (hcover (hA₂s hy)).resolve_left fun h
    => Set.disjoint_left.mp hdA (hA₁ h) hy) hA₂
  rw [hA₁e] at hb₁
  rw [hA₂e] at hb₂
  have hcF : c ∈ F := hF.left_mem
  have hqF : q ∈ F := hF.right_mem
  have hFb₁ : F ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hFb₂ : F ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  have hb₁s : discBd Δ₁ ⊆ Δ₁ := discBd_subset _
  have hb₂s : discBd Δ₂ ⊆ Δ₂ := discBd_subset _
  have hΔ₁s : Δ₁ ⊆ Δ := hun ▸ subset_union_left
  have hΔ₂s : Δ₂ ⊆ Δ := hun ▸ subset_union_right
  have hinF : ∀ {y}, y ∈ Δ₁ → y ∈ Δ₂ → y ∈ F := fun {y} h1' h2' => hint ▸ ⟨h1', h2'⟩
  have hFbd' : ∀ {y}, y ∈ F → y ∈ discBd Δ → y = c ∨ y = q := fun {y} h1' h2' => by
    have : y ∈ F ∩ discBd Δ := ⟨h1', h2'⟩
    rwa [hFbd] at this
  have hX₁n : ∀ {y}, y ∈ X₁ → y ∉ Δ₂ := fun {y} hy hy2 => by
    have h3 := hX₁sub hy
    have h4 : y ∈ F := hinF (hb₁s (hb₁ ▸ .inl hy)) hy2
    exact h3.2 (hFbd' h4 h3.1)
  have hX₂n' : ∀ {y}, y ∈ X₂ → y ∉ Δ₁ := fun {y} hy hy1 => by
    have h3 := hX₂sub hy
    have h4 : y ∈ F := hinF hy1 (hb₂s (hb₂ ▸ .inl hy))
    exact h3.2 (hFbd' h4 h3.1)
  have hbdsplit : ∀ {y}, y ∈ discBd Δ → y ∈ X₁ ∨ y ∈ X₂ ∨ y = c ∨ y = q := fun {y} hy => by
    by_cases h3 : y = c ∨ y = q
    · exact .inr (.inr h3)
    · rcases hcover ⟨hy, h3⟩ with h4 | h4
      · exact .inl h4
      · exact .inr (.inl h4)
  have hb₂e : discBd Δ₂ = r '' Icc s₁ 1 ∪ F := by
    rw [hb₂]
    ext y
    constructor
    · rintro (h2 | h2)
      · exact .inl h2.1
      · exact .inr h2
    · rintro (h2 | h2)
      · by_cases h3 : y ∈ F
        · exact .inr h3
        · exact .inl ⟨h2, by rintro (rfl | rfl); exacts [h3 hqF, h3 hcF]⟩
      · exact .inr h2
  have hmeet₂ : r '' Icc s₁ 1 ∩ F = {q, c} := by
    ext y
    constructor
    · rintro ⟨h2, h3⟩
      rcases hFbd' h3 (hL₂sub h2) with h4 | h4
      · exact .inr h4
      · exact .inl h4
    · rintro (rfl | rfl)
      · exact ⟨hl₂.left_mem, hqF⟩
      · exact ⟨hl₂.right_mem, hcF⟩
  obtain ⟨𝓛, 𝓒, hfan, hnL, hnS, hspoke, hpair⟩ := ih hΔ₂ hF hb₂e hmeet₂
  have hsubQ : (r '' ((S.erase s₀ : Finset 𝕀) : Set 𝕀)) ⊆ r '' (S : Set 𝕀) :=
    image_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  have hu_notΔ₂ : u ∉ Δ₂ := hX₁n hu_X₁
  have hQ₂ : ∀ Φ ∈ 𝓒, Φ ∩ insert c (r '' (S : Set 𝕀)) = Φ ∩ insert c (r ''
    ((S.erase s₀ : Finset 𝕀) : Set 𝕀)) := by
    intro Φ hΦ
    ext y
    constructor
    · rintro ⟨h2, h3 | ⟨s, hs, rfl⟩⟩
      · exact ⟨h2, .inl h3⟩
      · by_cases hs0 : s = s₀
        · subst hs0
          exact absurd (hfan.sub Φ hΦ h2) hu_notΔ₂
        · exact ⟨h2, .inr ⟨s, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hs0, hs⟩), rfl⟩⟩
    · rintro ⟨h2, h3 | h3⟩
      · exact ⟨h2, .inl h3⟩
      · exact ⟨h2, .inr (hsubQ h3)⟩
  have hF𝓛 : F ∉ 𝓛 := fun hin => by
    obtain ⟨s, hs, hne, -, -, h3⟩ := hspoke F hin
    have h4 : q ∈ F ∩ discBd Δ₂ := ⟨hqF, hFb₂ hqF⟩
    rw [h3] at h4
    rcases h4 with h4 | h4
    · exact hcq h4.symm
    · exact hne (hr.2 h4).symm
  have hΔ₁𝓒 : Δ₁ ∉ 𝓒 := fun hin => hu_notΔ₂ (hfan.sub _ hin (hb₁s (hb₁ ▸ .inl hu_X₁)))
  exact attach_chord_to_fan S hcard hr hs₀ hs₁m h1 hmin' hmemr hmin hΔ₁ hun hint
    hb₁ hb₂ hF hFΔ hFbd hX₁sub hX₂sub hu_X₁ hX₁n hX₂n' hbdsplit hfan hnL hnS hspoke hpair
    hQ₂ hF𝓛 hΔ₁𝓒

/-- The fan on the boundary points `r(s)`, `s ∈ S`, from the point `r(1)`. The boundary consists of
the part of `r` after the first point of `S` and a line `B`. -/
theorem exists_disc_fan (n : ℕ) : ∀ {Δ B : Set X} {r : 𝕀 → X} (S : Finset 𝕀) (s₀ : 𝕀), S.card
  = n + 2 →
    IsClosedDisc Δ → IsArcMap r → s₀ ∈ S → (∀ s ∈ S, s₀ ≤ s) → (1 : 𝕀) ∉ S →
    IsLineWithEnds B (r 1) (r s₀) → discBd Δ = r '' Icc s₀ 1 ∪ B → r '' Icc s₀ 1 ∩ B = {r s₀, r 1} →
    ∃ 𝓛 𝓒 : Set (Set X), IsChordFan Δ (insert (r 1) (r '' S)) 𝓛 𝓒 ∧ 𝓛.ncard = n ∧ 𝓒.ncard = n + 1 ∧
      (∀ L ∈ 𝓛, ∃ s ∈ S, s ≠ s₀ ∧ (∃ t ∈ S, s < t) ∧ IsLineWithEnds L (r 1) (r s) ∧ L ∩ discBd Δ
        = {r 1, r s}) ∧
      ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {r 1} := by
  induction n with
  | zero =>
    intro Δ B r S s₀ hcard hΔ hr hs₀ hmin h1 hB hbd hmeet
    obtain ⟨s, hs⟩ : ∃ s ∈ S, s ≠ s₀ := by
      by_contra hc
      push Not at hc
      have : S ⊆ {s₀} := fun x hx => Finset.mem_singleton.mpr (hc x hx)
      have := Finset.card_le_card this
      simp at this
      omega
    have hS : S = {s₀, s} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hs₀
        · exact hs.1
      · rw [hcard, Finset.card_pair hs.2.symm]
    have hs1 : s ≠ 1 := fun h => h1 (h ▸ hs.1)
    have hs01 : s₀ ≠ 1 := fun h => h1 (h ▸ hs₀)
    have hQ : (r '' (S : Set 𝕀)) ⊆ discBd Δ := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hbd]
      exact .inl ⟨x, ⟨hmin x hx, x.2.2⟩, rfl⟩
    have hc : r 1 ∈ discBd Δ := by
      rw [hbd]
      exact .inl ⟨1, ⟨s₀.2.2, le_rfl⟩, rfl⟩
    refine ⟨∅, {Δ}, ⟨finite_empty, finite_singleton _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by simp, by simp, by simp, by simp⟩
    · rintro _ rfl
      exact hΔ
    · rintro _ rfl
      exact Subset.rfl
    · rintro _ rfl
      exact subset_union_left
    · rintro _ rfl
      simp only [sUnion_empty, union_empty]
      exact Set.disjoint_left.mpr fun x hx h => hx.2 h
    · simp
    · rintro _ rfl _ rfl h
      exact absurd rfl h
    · intro Φ hΦ
      obtain rfl : Φ = Δ := hΦ
      have hsub : insert (r 1) (r '' (S : Set 𝕀)) ⊆ Φ := insert_subset (discBd_subset _ hc)
        (hQ.trans (discBd_subset _))
      rw [inter_eq_right.mpr hsub, hS]
      have : insert (r 1) (r '' (({s₀, s} : Finset 𝕀) : Set 𝕀)) = {r 1, r s₀, r s} := by
        simp
      rw [this]
      have hn1 : r 1 ≠ r s₀ := fun h => hs01 (hr.2 h).symm
      have hn2 : r 1 ≠ r s := fun h => hs1 (hr.2 h).symm
      have hn3 : r s₀ ≠ r s := fun h => hs.2 (hr.2 h).symm
      exact ncard_eq_three.mpr ⟨_, _, _, hn1, hn2, hn3, rfl⟩
    · simp
    · intro x _ _
      rw [show {Φ ∈ ({Δ} : Set (Set X)) | x ∈ Φ} = {Φ ∈ ({Δ} : Set (Set X)) | x ∈ Φ} from rfl]
      refine (encard_le_encard (sep_subset _ _)).trans (by simp)
    · intro x _
      refine (encard_le_encard (sep_subset _ _)).trans (by simp)
  | succ n ih =>
    intro Δ B r S s₀ hcard hΔ hr hs₀ hmin h1 hB hbd hmeet
    classical
    have hS' : (S.erase s₀).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hs₀]
      omega
    set s₁ := (S.erase s₀).min' hS' with hs₁
    have hs₁m : s₁ ∈ S.erase s₀ := Finset.min'_mem _ hS'
    have hs₁S : s₁ ∈ S := Finset.mem_of_mem_erase hs₁m
    have hs₁n : s₁ ≠ s₀ := Finset.ne_of_mem_erase hs₁m
    have h01 : s₀ < s₁ := lt_of_le_of_ne (hmin _ hs₁S) hs₁n.symm
    have hmin' : ∀ s ∈ S.erase s₀, s₁ ≤ s := fun s hs => Finset.min'_le _ _ hs
    have hs₁1 : s₁ ≠ 1 := fun h => h1 (h ▸ hs₁S)
    have hs₁lt : s₁ < 1 := lt_of_le_of_ne s₁.2.2 hs₁1
    have hs₀lt : s₀ < 1 := h01.trans hs₁lt
    set c := r 1 with hc
    set u := r s₀ with hu
    set q := r s₁ with hq
    have hcq : c ≠ q := fun h => hs₁1 (hr.2 h).symm
    have huq : u ≠ q := fun h => hs₁n (hr.2 h).symm
    have hcu : c ≠ u := fun h => hs₀lt.ne (hr.2 h).symm
    have hmemr : ∀ {x}, s₀ ≤ x → r x ∈ discBd Δ := fun {x} hx => by
      rw [hbd]
      exact .inl ⟨x, ⟨hx, x.2.2⟩, rfl⟩
    have hcbd : c ∈ discBd Δ := hmemr s₀.2.2
    have hqbd : q ∈ discBd Δ := hmemr h01.le
    obtain ⟨F, hF, hFΔ, hFbd⟩ := exists_chord hΔ hcbd hqbd hcq
    obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hcomp, hΔ₁, hΔ₂, hun, hint, hb₁, hb₂, -⟩
      := disc_iArc.{0} Δ F c q hΔ hFΔ hcq hF hFbd
    -- the two sides of the boundary
    let L₁ : Set X := r '' Icc s₀ s₁
    let L₂ : Set X := r '' Icc s₁ 1
    have hl₁ : IsLineWithEnds L₁ u q := by
      have h2 := (hr.sub (s := s₀) (t := s₁) hs₁n.symm).isLineWithEnds
      rwa [range_subArc r h01.le, subArc_zero, subArc_one] at h2
    have hl₂ : IsLineWithEnds L₂ q c := by
      have h2 := (hr.sub (s := s₁) (t := 1) hs₁1).isLineWithEnds
      rwa [range_subArc r hs₁lt.le, subArc_zero, subArc_one] at h2
    have hL₁sub : L₁ ⊆ discBd Δ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmemr hx.1
    have hL₂sub : L₂ ⊆ discBd Δ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmemr (h01.le.trans hx.1)
    have hBsub : B ⊆ discBd Δ := fun x hx => hbd ▸ .inr hx
    have hsplit : r '' Icc s₀ 1 = L₁ ∪ L₂ := by
      rw [← image_union, Icc_union_Icc_eq_Icc h01.le hs₁lt.le]
    let X₁ : Set X := (L₁ \ {q}) ∪ (B \ {c})
    let X₂ : Set X := L₂ \ {q, c}
    have hX₁c : IsPreconnected X₁ := hl₁.isPreconnected_diff_right.union u ⟨hl₁.left_mem, huq⟩
      ⟨hB.right_mem, fun h => hcu h.symm⟩ hB.isPreconnected_diff_left
    have hX₂c : IsPreconnected X₂ := hl₂.isPreconnected_diff
    have hX₂n : X₂.Nonempty := by
      by_contra hc'
      rw [not_nonempty_iff_eq_empty] at hc'
      have h2 := hl₂.subset_closure_diff
      change L₂ ⊆ closure X₂ at h2
      rw [hc', closure_empty] at h2
      exact h2 hl₂.left_mem
    have hu_X₁ : u ∈ X₁ := .inl ⟨hl₁.left_mem, huq⟩
    have hL₁c : c ∉ L₁ := by
      rintro ⟨x, hx, he⟩
      exact (lt_of_le_of_lt hx.2 hs₁lt).ne (hr.2 he)
    have hX₁sub : X₁ ⊆ discBd Δ \ {c, q} := by
      rintro x (⟨h2, h3⟩ | ⟨h2, h3⟩)
      · refine ⟨hL₁sub h2, ?_⟩
        rintro (rfl | h4)
        · exact hL₁c h2
        · exact h3 h4
      · refine ⟨hBsub h2, ?_⟩
        rintro (rfl | rfl)
        · exact h3 rfl
        · have h4 : q ∈ r '' Icc s₀ 1 ∩ B := ⟨⟨s₁, ⟨h01.le, s₁.2.2⟩, rfl⟩, h2⟩
          rw [hmeet] at h4
          rcases h4 with h4 | h4
          · exact huq h4.symm
          · exact hcq h4.symm
    have hX₂sub : X₂ ⊆ discBd Δ \ {c, q} := fun x hx => ⟨hL₂sub hx.1, fun h2 => hx.2 (by
      rcases h2 with h2 | h2
      · exact .inr h2
      · exact .inl h2)⟩
    have hcover : discBd Δ \ {c, q} ⊆ X₁ ∪ X₂ := by
      rintro x ⟨h2, h3⟩
      have hxc : x ≠ c := fun h => h3 (.inl h)
      have hxq : x ≠ q := fun h => h3 (.inr h)
      rw [hbd, hsplit] at h2
      rcases h2 with (h2 | h2) | h2
      · exact .inl (.inl ⟨h2, hxq⟩)
      · exact .inr ⟨h2, by rintro (h | h); exacts [hxq h, hxc h]⟩
      · exact .inl (.inr ⟨h2, hxc⟩)
    have hdisj : Disjoint X₁ X₂ := by
      refine Set.disjoint_left.mpr ?_
      rintro x (⟨⟨a, ha, rfl⟩, h3⟩ | ⟨h2, h3⟩) ⟨⟨b, hb, he⟩, h4⟩
      · have hab : b = a := hr.2 he
        subst hab
        have : b = s₁ := le_antisymm ha.2 hb.1
        exact h3 (by rw [this]; rfl)
      · have h5 : r b ∈ r '' Icc s₀ 1 ∩ B := ⟨⟨b, ⟨h01.le.trans hb.1, b.2.2⟩, rfl⟩, he ▸ h2⟩
        rw [hmeet] at h5
        rcases h5 with h5 | h5
        · have h6 : b = s₀ := hr.2 h5
          exact absurd hb.1 (not_le.mpr (h6 ▸ h01))
        · exact h4 (.inr (he ▸ h5))
    let main := fun {A₁ A₂ Δ₁ Δ₂ : Set X} =>
      fan_of_split_subdisc S hcard hr hs₀ hs₁m h1 hmin' hmemr hmin hF hFΔ hFbd
        hX₁sub hX₂sub hX₁c hX₂c hu_X₁ hcover hL₂sub hl₂
        (fun hD hline hbd hmeet =>
          ih (S.erase s₀) s₁ (by rw [Finset.card_erase_of_mem hs₀, hcard]; rfl)
            hD hr hs₁m hmin' (fun h => h1 (Finset.mem_of_mem_erase h)) hline hbd hmeet)
        (A₁ := A₁) (A₂ := A₂) (Δ₁ := Δ₁) (Δ₂ := Δ₂)
    -- choose the labelling of the two sides
    obtain ⟨x₂, hx₂⟩ := hX₂n
    have hcm : connectedComponentIn (discBd Δ \ {c, q}) x₂ ∈ componentsIn (discBd Δ \ {c, q})
      := ⟨x₂, hX₂sub hx₂, rfl⟩
    rw [hcomp] at hcm
    rcases hcm with h2 | h2
    · exact main hA.symm (by rw [hcomp, pair_comm]) hΔ₂ hΔ₁ (by rw [union_comm,
        hun]) (by rw [inter_comm, hint]) hb₂ hb₁ ⟨x₂, hx₂, h2⟩
    · exact main hA hcomp hΔ₁ hΔ₂ hun hint hb₁ hb₂ ⟨x₂, hx₂, h2⟩

/-- The fan on one side of a chord, whose boundary is a line `L` with the points `P` and two lines
`F₁, F₂` from `c` to the ends of `L`. -/
theorem fan_side {Δ L F₁ F₂ P : Set X} {a b c : X} (hΔ : IsClosedDisc Δ) (hL : IsLineWithEnds L a b)
    (h₁ : IsLineWithEnds F₁ c a) (h₂ : IsLineWithEnds F₂ c b) (hbd : discBd Δ = L ∪ F₁ ∪ F₂)
    (hm₁ : L ∩ F₁ = {a}) (hm₂ : L ∩ F₂ = {b}) (hm : F₁ ∩ F₂ = {c}) (hP : P.Finite) (hPL : P ⊆ L)
      (ha : a ∈ P)
    (hb : b ∈ P) (hab : a ≠ b) :
    ∃ (n : ℕ) (𝓛 𝓒 : Set (Set X)), IsChordFan Δ (insert c P) 𝓛 𝓒 ∧ P.ncard = n + 2 ∧ 𝓛.ncard = n
      ∧ 𝓒.ncard = n + 1 ∧
      (∀ L' ∈ 𝓛, ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ IsLineWithEnds L' c p ∧ L' ∩ discBd Δ = {c, p}) ∧
      ∀ L' ∈ 𝓛, ∀ L'' ∈ 𝓛, L' ≠ L'' → L' ∩ L'' = {c} := by
  classical
  have hcL : c ∉ L := fun hc => by
    have h3 : c ∈ L ∩ F₁ := ⟨hc, h₁.left_mem⟩
    rw [hm₁] at h3
    have h4 : c = a := h3
    have h5 : a ∈ L ∩ F₂ := ⟨hL.left_mem, h4 ▸ h₂.left_mem⟩
    rw [hm₂] at h5
    exact hab h5
  have hR : IsLineWithEnds (L ∪ F₂) a c := IsLineWithEnds.union hL h₂.symm hm₂
  obtain ⟨r, hr, hrr, hr0, hr1⟩ := hR.exists_arc
  have hrinj : InjOn r (r ⁻¹' P) := hr.2.injOn
  have hSf : (r ⁻¹' P).Finite := hP.preimage hrinj
  let S : Finset 𝕀 := hSf.toFinset
  have hSm : ∀ {s}, s ∈ S ↔ r s ∈ P := fun {s} => by simp [S]
  have hrS : r '' (S : Set 𝕀) = P := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hSm.mp hs
    · intro hx
      have h3 : x ∈ range r := hrr ▸ .inl (hPL hx)
      obtain ⟨s, rfl⟩ := h3
      exact ⟨s, hSm.mpr hx, rfl⟩
  have h0S : (0 : 𝕀) ∈ S := hSm.mpr (hr0 ▸ ha)
  have h1S : (1 : 𝕀) ∉ S := fun h => hcL (hPL (hr1 ▸ hSm.mp h))
  have hbr : b ∈ range r := hrr ▸ .inl hL.right_mem
  obtain ⟨tb, htb⟩ := hbr
  have hcard2 : 2 ≤ S.card := by
    have h3 : ({0, tb} : Finset 𝕀) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0S
      · exact hSm.mpr (htb ▸ hb)
    have h4 : (0 : 𝕀) ≠ tb := fun h => hab (by rw [← hr0, h, htb])
    have := Finset.card_le_card h3
    rwa [Finset.card_pair h4] at this
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 2 := ⟨S.card - 2, by omega⟩
  have hI : (Icc (0 : 𝕀) 1) = univ := by
    ext x
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨x.2.1, x.2.2⟩
  have hBd : discBd Δ = r '' Icc 0 1 ∪ F₁ := by
    rw [hI, image_univ, hrr, hbd, union_right_comm]
  have hmt : r '' Icc 0 1 ∩ F₁ = {r 0, r 1} := by
    rw [hI, image_univ, hrr, hr0, hr1, union_inter_distrib_right, hm₁, inter_comm F₂, hm]
    rfl
  obtain ⟨𝓛, 𝓒, hf, h3, h4, h5, h6⟩ := exists_disc_fan n S 0 hn hΔ hr h0S (fun s _ => s.2.1) h1S
    (by rwa [hr0, hr1]) hBd hmt
  rw [hrS, hr1] at hf
  rw [hr1] at h6
  refine ⟨n, 𝓛, 𝓒, hf, ?_, h3, h4, ?_, h6⟩
  · rw [← hrS, ncard_image_of_injective _ hr.2, ncard_coe_finset]
    exact hn
  · intro L' hL'
    obtain ⟨s, hs, hs0, ⟨t, ht, hst⟩, h7, h8⟩ := h5 L' hL'
    rw [hr1] at h7 h8
    refine ⟨r s, hSm.mp hs, fun he => hs0 (hr.2 (he.trans hr0.symm)), ?_, h7, h8⟩
    intro he
    -- the part of `r` after `b` lies in `F₂`
    have hstb : s = tb := hr.2 (he.trans htb.symm)
    subst hstb
    have hpre : IsPreconnected (r ⁻¹' F₂) := by
      have hhe : Topology.IsEmbedding r := (hr.1.isClosedEmbedding hr.2).isEmbedding
      have hrg : r '' (r ⁻¹' F₂) = F₂ := image_preimage_eq_of_subset (hrr ▸ subset_union_right)
      refine hhe.isInducing.isPreconnected_image.mp ?_
      rw [hrg]
      obtain ⟨e, he', her, -, -⟩ := h₂.exists_arc
      rw [← her]
      exact isPreconnected_range he'.1
    have htbF : s ∈ r ⁻¹' F₂ := by
      change r s ∈ F₂
      rw [htb]
      exact h₂.right_mem
    have h1F : (1 : 𝕀) ∈ r ⁻¹' F₂ := by
      change r 1 ∈ F₂
      rw [hr1]
      exact h₂.left_mem
    have htF : t ∈ r ⁻¹' F₂ := hpre.Icc_subset htbF h1F ⟨hst.le, t.2.2⟩
    have h9 : r t ∈ L ∩ F₂ := ⟨hPL (hSm.mp ht), htF⟩
    rw [hm₂] at h9
    exact hst.ne (hr.2 (htb.trans h9.symm))

omit [T2Space X] in
/-- The facts on one side of a chord that are needed to merge two fans. -/
theorem IsChordFan.side {Δ Δ₁ Δ₂ F Q₁ : Set X} {𝓛₁ 𝓒₁ 𝓛₂ : Set (Set X)} (h : IsChordFan Δ₁ Q₁ 𝓛₁ 𝓒₁)
    (hF : F ⊆ discBd Δ₁) (hint : Δ₁ ∩ Δ₂ = F) (hin : ∀ y ∈ discBd Δ, y ∈ Δ₁ → y ∈ discBd Δ₁)
    (hbd₁ : discBd Δ₁ ⊆ discBd Δ ∪ F) (hL₂ : ∀ L ∈ 𝓛₂, L ⊆ Δ₂) {Φ : Set X} (hΦ : Φ ∈ 𝓒₁) :
    discBd Φ ⊆ discBd Δ ∪ F ∪ ⋃₀ 𝓛₁ ∧ Disjoint (discInt Φ) (discBd Δ ∪ F ∪ ⋃₀ (𝓛₁ ∪ 𝓛₂)) := by
  constructor
  · refine (h.bd Φ hΦ).trans ?_
    rintro y (h1 | h1)
    · exact .inl (hbd₁ h1)
    · exact .inr h1
  · have hd := h.int Φ hΦ
    refine Set.disjoint_left.mpr ?_
    rintro y hy ((h1 | h1) | ⟨L, hL | hL, h1⟩)
    · exact Set.disjoint_left.mp hd hy (.inl (hin y h1 (h.sub Φ hΦ hy.1)))
    · exact Set.disjoint_left.mp hd hy (.inl (hF h1))
    · exact Set.disjoint_left.mp hd hy (.inr ⟨L, hL, h1⟩)
    · have h2 : y ∈ F := hint ▸ ⟨h.sub Φ hΦ hy.1, hL₂ L hL h1⟩
      exact Set.disjoint_left.mp hd hy (.inl (hF h2))

omit [T2Space X] in
theorem comps_two {Y X₁ X₂ A₁ A₂ : Set X} (hA : A₁ ≠ A₂) (hc : componentsIn Y = {A₁, A₂}) (hY : Y
  = X₁ ∪ X₂)
    (_hd : Disjoint X₁ X₂) (h₁ : IsPreconnected X₁) (h₂ : IsPreconnected X₂) (n₁ : X₁.Nonempty)
      (n₂ : X₂.Nonempty) :
    (A₁ = X₁ ∧ A₂ = X₂) ∨ (A₁ = X₂ ∧ A₂ = X₁) := by
  obtain ⟨x₁, hx₁⟩ := n₁
  obtain ⟨x₂, hx₂⟩ := n₂
  have hs₁ : X₁ ⊆ Y := hY ▸ subset_union_left
  have hs₂ : X₂ ⊆ Y := hY ▸ subset_union_right
  have h3 : X₁ ⊆ connectedComponentIn Y x₁ := h₁.subset_connectedComponentIn hx₁ hs₁
  have h4 : X₂ ⊆ connectedComponentIn Y x₂ := h₂.subset_connectedComponentIn hx₂ hs₂
  have hne : connectedComponentIn Y x₁ ≠ connectedComponentIn Y x₂ := fun he => by
    have hall : ∀ y ∈ Y, connectedComponentIn Y y = connectedComponentIn Y x₁ := fun y hy => by
      rcases (hY ▸ hy : y ∈ X₁ ∪ X₂) with h5 | h5
      · exact (connectedComponentIn_eq (h3 h5)).symm
      · rw [he]
        exact (connectedComponentIn_eq (h4 h5)).symm
    have h5 : A₁ ∈ componentsIn Y := hc ▸ .inl rfl
    have h6 : A₂ ∈ componentsIn Y := hc ▸ .inr rfl
    obtain ⟨y, hy, rfl⟩ := h5
    obtain ⟨z, hz, rfl⟩ := h6
    exact hA ((hall y hy).trans (hall z hz).symm)
  have hd' : Disjoint (connectedComponentIn Y x₁) (connectedComponentIn Y x₂) :=
    Set.disjoint_left.mpr fun y hy hy' => hne ((connectedComponentIn_eq hy).trans
      (connectedComponentIn_eq hy').symm)
  have e₁ : connectedComponentIn Y x₁ = X₁ := Subset.antisymm (fun y hy => by
    rcases (hY ▸ connectedComponentIn_subset Y x₁ hy : y ∈ X₁ ∪ X₂) with h5 | h5
    · exact h5
    · exact absurd (h4 h5) (Set.disjoint_left.mp hd' hy)) h3
  have e₂ : connectedComponentIn Y x₂ = X₂ := Subset.antisymm (fun y hy => by
    rcases (hY ▸ connectedComponentIn_subset Y x₂ hy : y ∈ X₁ ∪ X₂) with h5 | h5
    · exact absurd hy (Set.disjoint_left.mp hd' (h3 h5))
    · exact h5) h4
  have m₁ : X₁ ∈ componentsIn Y := ⟨x₁, hs₁ hx₁, e₁⟩
  have m₂ : X₂ ∈ componentsIn Y := ⟨x₂, hs₂ hx₂, e₂⟩
  rw [hc] at m₁ m₂
  have hX : X₁ ≠ X₂ := fun h => hne (e₁.trans (h.trans e₂.symm))
  rcases m₁ with m₁ | m₁ <;> rcases m₂ with m₂ | m₂
  · exact absurd (m₁.trans m₂.symm) hX
  · exact .inl ⟨m₁.symm, m₂.symm⟩
  · exact .inr ⟨m₂.symm, m₁.symm⟩
  · exact absurd (m₁.trans m₂.symm) hX

omit [T2Space X] in
private theorem merge_cone_fans
    {Δ Δ₁ Δ₂ F F₁ F₂ P X₁ X₂ U₁ U₂ : Set X} {a b c : X}
    {𝓛₁ 𝓛₂ 𝓒₁ 𝓒₂ : Set (Set X)} {n₁ n₂ : ℕ}
    (hf₁ : IsChordFan Δ₁ (insert c (P ∩ U₁)) 𝓛₁ 𝓒₁)
    (hf₂ : IsChordFan Δ₂ (insert c (P ∩ U₂)) 𝓛₂ 𝓒₂)
    (hPb : P ⊆ discBd Δ) (ha : a ∈ P) (hb : b ∈ P) (hcF : c ∈ F) (hcbd : c ∉ discBd Δ)
    (hFΔ : F ⊆ Δ) (hFu : F = F₁ ∪ F₂) (h₁ : IsLineWithEnds F₁ c a) (h₂ : IsLineWithEnds F₂ c b)
    (haF₂ : a ∉ F₂) (hbF₁ : b ∉ F₁)
    (hLF : ∀ {L : Set X}, L ⊆ discBd Δ → ∀ {y}, y ∈ L → y ∈ F → y = a ∨ y = b)
    (hun : Δ₁ ∪ Δ₂ = Δ) (hint : Δ₁ ∩ Δ₂ = F)
    (hb₁ : discBd Δ₁ = X₁ ∪ F) (hb₂ : discBd Δ₂ = X₂ ∪ F)
    (hX₁n : ∀ {y}, y ∈ X₁ → y ∉ Δ₂) (hX₂n : ∀ {y}, y ∈ X₂ → y ∉ Δ₁)
    (hsplit' : ∀ {y}, y ∈ discBd Δ → y ∈ X₁ ∨ y ∈ X₂ ∨ y ∈ F)
    (hin₁ : ∀ y ∈ discBd Δ, y ∈ Δ₁ → y ∈ discBd Δ₁)
    (hin₂ : ∀ y ∈ discBd Δ, y ∈ Δ₂ → y ∈ discBd Δ₂)
    (hbd₁ : discBd Δ₁ ⊆ discBd Δ ∪ F) (hbd₂ : discBd Δ₂ ⊆ discBd Δ ∪ F)
    (hQ₁ : ∀ Φ, Φ ⊆ Δ₁ → Φ ∩ insert c P = Φ ∩ insert c (P ∩ U₁))
    (hQ₂ : ∀ Φ, Φ ⊆ Δ₂ → Φ ∩ insert c P = Φ ∩ insert c (P ∩ U₂))
    (hsp₁' : ∀ L ∈ 𝓛₁, ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ p ∈ U₁ ∧
      IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p} ∧ L ∩ F = {c})
    (hsp₂' : ∀ L ∈ 𝓛₂, ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ p ∈ U₂ ∧
      IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p} ∧ L ∩ F = {c})
    (hsp : ∀ L ∈ 𝓛₁ ∪ 𝓛₂, ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ IsLineWithEnds L c p ∧
      L ∩ discBd Δ = {p} ∧ L ∩ F = {c})
    (hF₁L : F₁ ∉ 𝓛₁ ∪ 𝓛₂) (hF₂L : F₂ ∉ 𝓛₁ ∪ 𝓛₂)
    (hF₁₂ : F₁ ≠ F₂) (hF₁F₂ : F₁ ∩ F₂ = {c})
    (hdL : Disjoint 𝓛₁ 𝓛₂) (hd𝓒 : Disjoint 𝓒₁ 𝓒₂)
    (hnL₁ : 𝓛₁.ncard = n₁) (hnL₂ : 𝓛₂.ncard = n₂) (hnS₁ : 𝓒₁.ncard = n₁ + 1)
    (hnS₂ : 𝓒₂.ncard = n₂ + 1) (hPcount : P.ncard = n₁ + n₂ + 2)
    (hpr₁ : ∀ L ∈ 𝓛₁, ∀ L' ∈ 𝓛₁, L ≠ L' → L ∩ L' = {c})
    (hpr₂ : ∀ L ∈ 𝓛₂, ∀ L' ∈ 𝓛₂, L ≠ L' → L ∩ L' = {c}) :
    ∃ (c : X) (𝓛 𝓒 : Set (Set X)), c ∈ discInt Δ ∧ IsChordFan Δ (insert c P) 𝓛 𝓒 ∧
      𝓛.ncard = P.ncard ∧ 𝓒.ncard = P.ncard ∧
      (∀ L ∈ 𝓛, ∃ p ∈ P, IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p}) ∧
      ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c} := by
  classical
  have hΔ₁s : Δ₁ ⊆ Δ := hun ▸ subset_union_left
  have hΔ₂s : Δ₂ ⊆ Δ := hun ▸ subset_union_right
  have hFb₁ : F ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hFb₂ : F ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  have hinF : ∀ {y}, y ∈ Δ₁ → y ∈ Δ₂ → y ∈ F := fun {y} hy hz => hint ▸ (⟨hy, hz⟩ : y ∈ Δ₁ ∩ Δ₂)
  have hint' : Δ₂ ∩ Δ₁ = F := by rw [inter_comm, hint]
  let 𝓛 : Set (Set X) := insert F₁ (insert F₂ (𝓛₁ ∪ 𝓛₂))
  have hU : ⋃₀ 𝓛 = F ∪ ⋃₀ (𝓛₁ ∪ 𝓛₂) := by
    simp only [𝓛, sUnion_insert, hFu, union_assoc]
  have hnQ₁ : ∀ {y}, y ∉ insert c P → y ∉ insert c (P ∩ U₁) :=
    fun h => fun hy => h (insert_subset_insert inter_subset_left hy)
  have hnQ₂ : ∀ {y}, y ∉ insert c P → y ∉ insert c (P ∩ U₂) :=
    fun h => fun hy => h (insert_subset_insert inter_subset_left hy)
  have hside₁ := fun {Φ} (hΦ : Φ ∈ 𝓒₁) => hf₁.side (Δ := Δ) hFb₁ hint hin₁ hbd₁ hf₂.subL hΦ
  have hside₂ := fun {Φ} (hΦ : Φ ∈ 𝓒₂) => hf₂.side (Δ := Δ) hFb₂ hint' hin₂ hbd₂ hf₁.subL hΦ
  refine ⟨c, 𝓛, 𝓒₁ ∪ 𝓒₂, ⟨hFΔ hcF, hcbd⟩, ⟨?_, hf₁.finS.union hf₂.finS,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact ((hf₁.finL.union hf₂.finL).insert _).insert _
  · rintro Φ (hΦ | hΦ)
    · exact hf₁.disc Φ hΦ
    · exact hf₂.disc Φ hΦ
  · rintro Φ (hΦ | hΦ)
    · exact (hf₁.sub Φ hΦ).trans hΔ₁s
    · exact (hf₂.sub Φ hΦ).trans hΔ₂s
  · rw [hU]
    rintro Φ (hΦ | hΦ) y hy
    · rcases (hside₁ hΦ).1 hy with (h2 | h2) | ⟨L, hL, h2⟩
      · exact .inl h2
      · exact .inr (.inl h2)
      · exact .inr (.inr ⟨L, .inl hL, h2⟩)
    · rcases (hside₂ hΦ).1 hy with (h2 | h2) | ⟨L, hL, h2⟩
      · exact .inl h2
      · exact .inr (.inl h2)
      · exact .inr (.inr ⟨L, .inr hL, h2⟩)
  · rw [hU, ← union_assoc]
    rintro Φ (hΦ | hΦ)
    · exact (hside₁ hΦ).2
    · rw [union_comm 𝓛₁]
      exact (hside₂ hΦ).2
  · rw [sUnion_union, hf₁.cover, hf₂.cover, hun]
  · rintro Φ (hΦ | hΦ) Φ' (hΦ' | hΦ') hne
    · exact hf₁.disj Φ hΦ Φ' hΦ' hne
    · exact Set.disjoint_left.mpr fun y hy hy' => Set.disjoint_left.mp (hf₁.int Φ hΦ) hy
        (.inl (hFb₁ (hinF (hf₁.sub Φ hΦ hy.1) (hf₂.sub Φ' hΦ' hy'))))
    · exact Set.disjoint_left.mpr fun y hy hy' => Set.disjoint_left.mp (hf₂.int Φ hΦ) hy
        (.inl (hFb₂ (hinF (hf₁.sub Φ' hΦ' hy') (hf₂.sub Φ hΦ hy.1))))
    · exact hf₂.disj Φ hΦ Φ' hΦ' hne
  · rintro Φ (hΦ | hΦ)
    · rw [hQ₁ Φ (hf₁.sub Φ hΦ)]
      exact hf₁.three Φ hΦ
    · rw [hQ₂ Φ (hf₂.sub Φ hΦ)]
      exact hf₂.three Φ hΦ
  · rintro L (rfl | rfl | hL | hL)
    · exact fun y hy => hFΔ (hFu ▸ .inl hy)
    · exact fun y hy => hFΔ (hFu ▸ .inr hy)
    · exact (hf₁.subL L hL).trans hΔ₁s
    · exact (hf₂.subL L hL).trans hΔ₂s
  · intro y hy hyQ
    have hyF : y ∉ F := fun h => by
      rcases hLF (fun _ h => h) hy h with rfl | rfl
      · exact hyQ (.inr ha)
      · exact hyQ (.inr hb)
    rcases hsplit' hy with h3 | h3 | h3
    · have h4 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} ⊆ {Φ ∈ 𝓒₁ | y ∈ Φ} := by
        rintro Φ ⟨hΦ | hΦ, h5⟩
        · exact ⟨hΦ, h5⟩
        · exact absurd (hf₂.sub Φ hΦ h5) (hX₁n h3)
      exact (encard_le_encard h4).trans (hf₁.count₁ y (hb₁ ▸ .inl h3) (hnQ₁ hyQ))
    · have h4 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} ⊆ {Φ ∈ 𝓒₂ | y ∈ Φ} := by
        rintro Φ ⟨hΦ | hΦ, h5⟩
        · exact absurd (hf₁.sub Φ hΦ h5) (hX₂n h3)
        · exact ⟨hΦ, h5⟩
      exact (encard_le_encard h4).trans (hf₂.count₁ y (hb₂ ▸ .inl h3) (hnQ₂ hyQ))
    · exact absurd h3 hyF
  · intro y hyQ
    by_cases hy1 : y ∈ Δ₁ <;> by_cases hy2 : y ∈ Δ₂
    · have hyF : y ∈ F := hinF hy1 hy2
      have h3 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} ⊆ {Φ ∈ 𝓒₁ | y ∈ Φ} ∪ {Φ ∈ 𝓒₂ | y ∈ Φ} := by
        rintro Φ ⟨hΦ | hΦ, h5⟩
        · exact .inl ⟨hΦ, h5⟩
        · exact .inr ⟨hΦ, h5⟩
      refine (encard_le_encard h3).trans ((encard_union_le _ _).trans ?_)
      have h4 := hf₁.count₁ y (hFb₁ hyF) (hnQ₁ hyQ)
      have h5 := hf₂.count₁ y (hFb₂ hyF) (hnQ₂ hyQ)
      calc _ ≤ (1 : ℕ∞) + 1 := by gcongr
        _ = 2 := by norm_num
    · have h4 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} ⊆ {Φ ∈ 𝓒₁ | y ∈ Φ} := by
        rintro Φ ⟨hΦ | hΦ, h5⟩
        · exact ⟨hΦ, h5⟩
        · exact absurd (hf₂.sub Φ hΦ h5) hy2
      exact (encard_le_encard h4).trans (hf₁.count₂ y (hnQ₁ hyQ))
    · have h4 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} ⊆ {Φ ∈ 𝓒₂ | y ∈ Φ} := by
        rintro Φ ⟨hΦ | hΦ, h5⟩
        · exact absurd (hf₁.sub Φ hΦ h5) hy1
        · exact ⟨hΦ, h5⟩
      exact (encard_le_encard h4).trans (hf₂.count₂ y (hnQ₂ hyQ))
    · have h4 : {Φ ∈ 𝓒₁ ∪ 𝓒₂ | y ∈ Φ} = ∅ := by
        ext Φ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hΦ | hΦ, h5⟩
        · exact hy1 (hf₁.sub Φ hΦ h5)
        · exact hy2 (hf₂.sub Φ hΦ h5)
      rw [h4]
      simp
  · have hfinU := hf₁.finL.union hf₂.finL
    have h3 : F₁ ∉ insert F₂ (𝓛₁ ∪ 𝓛₂) := by
      rintro (h | h)
      · exact hF₁₂ h
      · exact hF₁L h
    rw [ncard_insert_of_notMem h3 (hfinU.insert _), ncard_insert_of_notMem hF₂L hfinU,
      ncard_union_eq hdL hf₁.finL hf₂.finL, hnL₁, hnL₂, hPcount]
  · rw [ncard_union_eq hd𝓒 hf₁.finS hf₂.finS, hnS₁, hnS₂, hPcount]
    omega
  · rintro L (rfl | rfl | hL)
    · refine ⟨a, ha, h₁, ?_⟩
      ext y
      constructor
      · rintro ⟨h2, h3⟩
        rcases hLF (L := discBd Δ) (fun _ h => h) h3 (hFu ▸ .inl h2) with rfl | rfl
        · rfl
        · exact absurd h2 hbF₁
      · rintro rfl
        exact ⟨h₁.right_mem, hPb ha⟩
    · refine ⟨b, hb, h₂, ?_⟩
      ext y
      constructor
      · rintro ⟨h2, h3⟩
        rcases hLF (L := discBd Δ) (fun _ h => h) h3 (hFu ▸ .inr h2) with rfl | rfl
        · exact absurd h2 haF₂
        · rfl
      · rintro rfl
        exact ⟨h₂.right_mem, hPb hb⟩
    · obtain ⟨p, h2, -, -, h3, h4, -⟩ := hsp L hL
      exact ⟨p, h2, h3, h4⟩
  · have hsubF : ∀ L ∈ 𝓛₁ ∪ 𝓛₂, L ∩ F₁ = {c} ∧ L ∩ F₂ = {c} := by
      intro L hL
      obtain ⟨p, -, -, -, hl, -, h3⟩ := hsp L hL
      have hcF₁ : c ∈ F₁ := h₁.left_mem
      have hcF₂ : c ∈ F₂ := h₂.left_mem
      constructor
      · ext y
        constructor
        · rintro ⟨h4, h5⟩
          exact (show y ∈ L ∩ F from ⟨h4, hFu ▸ .inl h5⟩) |> fun h => h3 ▸ h
        · rintro rfl
          exact ⟨hl.left_mem, hcF₁⟩
      · ext y
        constructor
        · rintro ⟨h4, h5⟩
          exact (show y ∈ L ∩ F from ⟨h4, hFu ▸ .inr h5⟩) |> fun h => h3 ▸ h
        · rintro rfl
          exact ⟨hl.left_mem, hcF₂⟩
    rintro L (rfl | rfl | hL) L' (rfl | rfl | hL') hne
    · exact absurd rfl hne
    · exact hF₁F₂
    · rw [inter_comm]
      exact (hsubF L' hL').1
    · rw [inter_comm]
      exact hF₁F₂
    · exact absurd rfl hne
    · rw [inter_comm]
      exact (hsubF L' hL').2
    · exact (hsubF L hL).1
    · exact (hsubF L hL).2
    · rcases hL with hL | hL <;> rcases hL' with hL' | hL'
      · exact hpr₁ L hL L' hL' hne
      · have h3 : L ∩ L' ⊆ F := fun y hy => hinF (hf₁.subL L hL hy.1) (hf₂.subL L' hL' hy.2)
        obtain ⟨p, -, -, -, -, hl, -, h4⟩ := hsp₁' L hL
        obtain ⟨p', -, -, -, -, hl', -, -⟩ := hsp₂' L' hL'
        ext y
        constructor
        · intro hy
          exact (show y ∈ L ∩ F from ⟨hy.1, h3 hy⟩) |> fun h => h4 ▸ h
        · rintro rfl
          exact ⟨hl.left_mem, hl'.left_mem⟩
      · have h3 : L ∩ L' ⊆ F := fun y hy => hinF (hf₁.subL L' hL' hy.2) (hf₂.subL L hL hy.1)
        obtain ⟨p, -, -, -, -, hl, -, h4⟩ := hsp₂' L hL
        obtain ⟨p', -, -, -, -, hl', -, -⟩ := hsp₁' L' hL'
        ext y
        constructor
        · intro hy
          exact (show y ∈ L ∩ F from ⟨hy.1, h3 hy⟩) |> fun h => h4 ▸ h
        · rintro rfl
          exact ⟨hl.left_mem, hl'.left_mem⟩
      · exact hpr₂ L hL L' hL' hne

omit [T2Space X] in
private theorem cone_spoke_on_whole_disc {Δ Δ₀ F P U L : Set X} {a b c : X}
    (hsp : ∃ p ∈ P ∩ U, p ≠ a ∧ p ≠ b ∧ IsLineWithEnds L c p ∧ L ∩ discBd Δ₀ = {c, p})
    (hsubL : L ⊆ Δ₀) (hin : ∀ y ∈ discBd Δ, y ∈ Δ₀ → y ∈ discBd Δ₀)
    (hFb : F ⊆ discBd Δ₀) (hUsub : U ⊆ discBd Δ) (hPb : P ⊆ discBd Δ)
    (hcbd : c ∉ discBd Δ) (hcF : c ∈ F)
    (hLF : ∀ {U : Set X}, U ⊆ discBd Δ → ∀ {y}, y ∈ U → y ∈ F → y = a ∨ y = b) :
    ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ p ∈ U ∧ IsLineWithEnds L c p ∧
      L ∩ discBd Δ = {p} ∧ L ∩ F = {c} := by
  obtain ⟨p, hp, hpa, hpb, hl, h3⟩ := hsp
  refine ⟨p, hp.1, hpa, hpb, hp.2, hl, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨h4, h5⟩
      have h6 : y ∈ L ∩ discBd Δ₀ := ⟨h4, hin y h5 (hsubL h4)⟩
      rw [h3] at h6
      rcases h6 with rfl | h6
      · exact absurd h5 hcbd
      · exact h6
    · rintro rfl
      exact ⟨hl.right_mem, hPb hp.1⟩
  · ext y
    constructor
    · rintro ⟨h4, h5⟩
      have h6 : y ∈ L ∩ discBd Δ₀ := ⟨h4, hFb h5⟩
      rw [h3] at h6
      rcases h6 with h6 | h6
      · exact h6
      · subst h6
        rcases hLF hUsub hp.2 h5 with h7 | h7
        · exact absurd h7 hpa
        · exact absurd h7 hpb
    · rintro rfl
      exact ⟨hl.left_mem, hcF⟩

private theorem cone_of_split_discs {Δ F F₁ F₂ P : Set X} {a b c : X}
    {a₁ a₂ : 𝕀 → X} (hF : IsLineWithEnds F a b) (hFΔ : F ⊆ Δ)
    (hFbd : F ∩ discBd Δ = {a, b}) (hFu : F = F₁ ∪ F₂)
    (h₁ : IsLineWithEnds F₁ c a) (h₂ : IsLineWithEnds F₂ c b) (hF₁F₂ : F₁ ∩ F₂ = {c})
    (hbF₁ : b ∉ F₁) (haF₂ : a ∉ F₂) (hcbd : c ∉ discBd Δ)
    (hP : P.Finite) (hPb : P ⊆ discBd Δ) (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (hl₁ : IsLineWithEnds (range a₁) a b) (hl₂ : IsLineWithEnds (range a₂) a b)
    (hinter : range a₁ ∩ range a₂ = {a, b}) (hu : range a₁ ∪ range a₂ = discBd Δ) :
    let X₁ : Set X := range a₁ \ {a, b}
    let X₂ : Set X := range a₂ \ {a, b}
    ∀ {Δ₁ Δ₂ : Set X}, IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ∪ Δ₂ = Δ →
      Δ₁ ∩ Δ₂ = F → discBd Δ₁ = X₁ ∪ F → discBd Δ₂ = X₂ ∪ F →
      ∃ (c : X) (𝓛 𝓒 : Set (Set X)), c ∈ discInt Δ ∧ IsChordFan Δ (insert c P) 𝓛 𝓒 ∧
        𝓛.ncard = P.ncard ∧ 𝓒.ncard = P.ncard ∧
        (∀ L ∈ 𝓛, ∃ p ∈ P, IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p}) ∧
        ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c} := by
  classical
  intro X₁ X₂
  have hY : discBd Δ \ {a, b} = X₁ ∪ X₂ := by
    rw [← hu, union_sdiff_distrib]
  intro Δ₁ Δ₂ hΔ₁ hΔ₂ hun hint hb₁ hb₂
  have haF : a ∈ F := hF.left_mem
  have hbF : b ∈ F := hF.right_mem
  have hsplit : ∀ {L X' : Set X}, IsLineWithEnds L a b → X' = L \ {a, b} → X' ∪ F = L ∪ F₁ ∪ F₂
    := by
    intro L X' hL hX'
    ext y
    subst hX'
    constructor
    · rintro (h2 | h2)
      · exact .inl (.inl h2.1)
      · rw [hFu] at h2
        rcases h2 with h2 | h2
        · exact .inl (.inr h2)
        · exact .inr h2
    · rintro ((h2 | h2) | h2)
      · by_cases h3 : y ∈ F
        · exact .inr h3
        · exact .inl ⟨h2, by rintro (rfl | rfl); exacts [h3 haF, h3 hbF]⟩
      · exact .inr (hFu ▸ .inl h2)
      · exact .inr (hFu ▸ .inr h2)
  have hLF : ∀ {L : Set X}, L ⊆ discBd Δ → ∀ {y}, y ∈ L → y ∈ F → y = a ∨ y = b
    := fun {L} hL {y} h2 h3 => by
    have : y ∈ F ∩ discBd Δ := ⟨h3, hL h2⟩
    rwa [hFbd] at this
  have hsub₁ : range a₁ ⊆ discBd Δ := hu ▸ subset_union_left
  have hsub₂ : range a₂ ⊆ discBd Δ := hu ▸ subset_union_right
  have hm1' : ∀ {L : Set X}, IsLineWithEnds L a b → L ⊆ discBd Δ → L ∩ F₁ = {a} := fun {L} hL hs
    => by
    ext y
    constructor
    · rintro ⟨h2, h3⟩
      rcases hLF hs h2 (hFu ▸ .inl h3) with rfl | rfl
      · rfl
      · exact absurd h3 hbF₁
    · rintro rfl
      exact ⟨hL.left_mem, h₁.right_mem⟩
  have hm2' : ∀ {L : Set X}, IsLineWithEnds L a b → L ⊆ discBd Δ → L ∩ F₂ = {b} := fun {L} hL hs
    => by
    ext y
    constructor
    · rintro ⟨h2, h3⟩
      rcases hLF hs h2 (hFu ▸ .inr h3) with rfl | rfl
      · exact absurd h3 haF₂
      · rfl
    · rintro rfl
      exact ⟨hL.right_mem, h₂.right_mem⟩
  have hPf : ∀ L : Set X, (P ∩ L).Finite := fun L => hP.subset inter_subset_left
  obtain ⟨n₁, 𝓛₁, 𝓒₁, hf₁, hc₁, hnL₁, hnS₁, hsp₁, hpr₁⟩ := fan_side hΔ₁ hl₁ h₁ h₂ (hb₁.trans
    (hsplit hl₁ rfl))
    (hm1' hl₁ hsub₁) (hm2' hl₁ hsub₁) hF₁F₂ (hPf _) inter_subset_right ⟨ha, hl₁.left_mem⟩ ⟨hb,
      hl₁.right_mem⟩ hab
  obtain ⟨n₂, 𝓛₂, 𝓒₂, hf₂, hc₂, hnL₂, hnS₂, hsp₂, hpr₂⟩ := fan_side hΔ₂ hl₂ h₁ h₂ (hb₂.trans
    (hsplit hl₂ rfl))
    (hm1' hl₂ hsub₂) (hm2' hl₂ hsub₂) hF₁F₂ (hPf _) inter_subset_right ⟨ha, hl₂.left_mem⟩ ⟨hb,
      hl₂.right_mem⟩ hab
  have hFb₁ : F ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hFb₂ : F ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  have hb₁s := discBd_subset Δ₁
  have hb₂s := discBd_subset Δ₂
  have hΔ₁s : Δ₁ ⊆ Δ := hun ▸ subset_union_left
  have hΔ₂s : Δ₂ ⊆ Δ := hun ▸ subset_union_right
  have hinF : ∀ {y}, y ∈ Δ₁ → y ∈ Δ₂ → y ∈ F := fun {y} h1' h2' => hint ▸ ⟨h1', h2'⟩
  have hX₁n : ∀ {y}, y ∈ X₁ → y ∉ Δ₂ := fun {y} hy h2 => by
    rcases hLF hsub₁ hy.1 (hinF (hb₁s (hb₁ ▸ .inl hy)) h2) with h3 | h3
    · exact hy.2 (.inl h3)
    · exact hy.2 (.inr h3)
  have hX₂n : ∀ {y}, y ∈ X₂ → y ∉ Δ₁ := fun {y} hy h2 => by
    rcases hLF hsub₂ hy.1 (hinF h2 (hb₂s (hb₂ ▸ .inl hy))) with h3 | h3
    · exact hy.2 (.inl h3)
    · exact hy.2 (.inr h3)
  have hsplit' : ∀ {y}, y ∈ discBd Δ → y ∈ X₁ ∨ y ∈ X₂ ∨ y ∈ F := fun {y} hy => by
    by_cases h3 : y = a ∨ y = b
    · rcases h3 with rfl | rfl
      · exact .inr (.inr haF)
      · exact .inr (.inr hbF)
    · have h4 : y ∈ discBd Δ \ {a, b} := ⟨hy, h3⟩
      rw [hY] at h4
      rcases h4 with h4 | h4
      · exact .inl h4
      · exact .inr (.inl h4)
  have hin₁ : ∀ y ∈ discBd Δ, y ∈ Δ₁ → y ∈ discBd Δ₁ := fun y hy h2 => by
    rcases hsplit' hy with h3 | h3 | h3
    · exact hb₁ ▸ .inl h3
    · exact absurd h2 (hX₂n h3)
    · exact hFb₁ h3
  have hin₂ : ∀ y ∈ discBd Δ, y ∈ Δ₂ → y ∈ discBd Δ₂ := fun y hy h2 => by
    rcases hsplit' hy with h3 | h3 | h3
    · exact absurd h2 (hX₁n h3)
    · exact hb₂ ▸ .inl h3
    · exact hFb₂ h3
  have hbd₁ : discBd Δ₁ ⊆ discBd Δ ∪ F := fun y hy => by
    rw [hb₁] at hy
    rcases hy with hy | hy
    · exact .inl (hsub₁ hy.1)
    · exact .inr hy
  have hbd₂ : discBd Δ₂ ⊆ discBd Δ ∪ F := fun y hy => by
    rw [hb₂] at hy
    rcases hy with hy | hy
    · exact .inl (hsub₂ hy.1)
    · exact .inr hy
  have hQ₁ : ∀ Φ, Φ ⊆ Δ₁ → Φ ∩ insert c P = Φ ∩ insert c (P ∩ range a₁) := fun Φ hΦ => by
    ext y
    constructor
    · rintro ⟨h2, h3 | h3⟩
      · exact ⟨h2, .inl h3⟩
      · refine ⟨h2, .inr ⟨h3, ?_⟩⟩
        rcases hsplit' (hPb h3) with h4 | h4 | h4
        · exact h4.1
        · exact absurd (hΦ h2) (hX₂n h4)
        · rcases hFbd.subset ⟨h4, hPb h3⟩ with rfl | rfl
          · exact hl₁.left_mem
          · exact hl₁.right_mem
    · rintro ⟨h2, h3 | h3⟩
      · exact ⟨h2, .inl h3⟩
      · exact ⟨h2, .inr h3.1⟩
  have hQ₂ : ∀ Φ, Φ ⊆ Δ₂ → Φ ∩ insert c P = Φ ∩ insert c (P ∩ range a₂) := fun Φ hΦ => by
    ext y
    constructor
    · rintro ⟨h2, h3 | h3⟩
      · exact ⟨h2, .inl h3⟩
      · refine ⟨h2, .inr ⟨h3, ?_⟩⟩
        rcases hsplit' (hPb h3) with h4 | h4 | h4
        · exact absurd (hΦ h2) (hX₁n h4)
        · exact h4.1
        · rcases hFbd.subset ⟨h4, hPb h3⟩ with rfl | rfl
          · exact hl₂.left_mem
          · exact hl₂.right_mem
    · rintro ⟨h2, h3 | h3⟩
      · exact ⟨h2, .inl h3⟩
      · exact ⟨h2, .inr h3.1⟩
  have hd𝓒 : Disjoint 𝓒₁ 𝓒₂ := Set.disjoint_left.mpr fun Φ h1' h2' => by
    have hdisc := hf₁.disc Φ h1'
    obtain ⟨h', g', c'⟩ := hdisc.exists_isChart
    have hg0 : g' 0 ∈ Φ := c'.gm (by simp)
    have h3 := hdisc.subset_closure_discInt hg0
    obtain ⟨y, hy⟩ : (discInt Φ).Nonempty := by
      by_contra hc'
      rw [not_nonempty_iff_eq_empty] at hc'
      rw [hc', closure_empty] at h3
      exact h3
    have h4 : y ∈ F := hinF (hf₁.sub Φ h1' hy.1) (hf₂.sub Φ h2' hy.1)
    exact Set.disjoint_left.mp (hf₁.int Φ h1') hy (.inl (hFb₁ h4))
  have hcF : c ∈ F := hFu ▸ Or.inl h₁.left_mem
  have hsp₁' := fun L hL =>
    cone_spoke_on_whole_disc (hsp₁ L hL) (hf₁.subL L hL) hin₁ hFb₁ hsub₁ hPb hcbd hcF hLF
  have hsp₂' := fun L hL =>
    cone_spoke_on_whole_disc (hsp₂ L hL) (hf₂.subL L hL) hin₂ hFb₂ hsub₂ hPb hcbd hcF hLF
  have hsp : ∀ L ∈ 𝓛₁ ∪ 𝓛₂, ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p}
    ∧ L ∩ F = {c} := by
    rintro L (hL | hL)
    · obtain ⟨p, h2, h3, h4, -, h5⟩ := hsp₁' L hL
      exact ⟨p, h2, h3, h4, h5⟩
    · obtain ⟨p, h2, h3, h4, -, h5⟩ := hsp₂' L hL
      exact ⟨p, h2, h3, h4, h5⟩
  have hF₁L : F₁ ∉ 𝓛₁ ∪ 𝓛₂ := fun h => by
    obtain ⟨p, -, hpa, -, -, h3, -⟩ := hsp _ h
    have h4 : a ∈ F₁ ∩ discBd Δ := ⟨h₁.right_mem, hPb ha⟩
    rw [h3] at h4
    exact hpa h4.symm
  have hF₂L : F₂ ∉ 𝓛₁ ∪ 𝓛₂ := fun h => by
    obtain ⟨p, -, -, hpb, -, h3, -⟩ := hsp _ h
    have h4 : b ∈ F₂ ∩ discBd Δ := ⟨h₂.right_mem, hPb hb⟩
    rw [h3] at h4
    exact hpb h4.symm
  have hF₁₂ : F₁ ≠ F₂ := fun h => haF₂ (h ▸ h₁.right_mem)
  have hdL : Disjoint 𝓛₁ 𝓛₂ := Set.disjoint_left.mpr fun L h1' h2' => by
    obtain ⟨p, -, hpa, hpb, hpr, hl, -, -⟩ := hsp₁' L h1'
    have h3 : p ∈ F := hinF (hf₁.subL L h1' hl.right_mem) (hf₂.subL L h2' hl.right_mem)
    rcases hLF hsub₁ hpr h3 with h4 | h4
    · exact hpa h4
    · exact hpb h4
  have hPcount : P.ncard = n₁ + n₂ + 2 := by
    have h3 : (P ∩ range a₁) ∪ (P ∩ range a₂) = P := by
      rw [← inter_union_distrib_left, hu]
      exact inter_eq_left.mpr hPb
    have h4 : (P ∩ range a₁) ∩ (P ∩ range a₂) = {a, b} := by
      rw [← inter_inter_distrib_left, hinter]
      exact inter_eq_right.mpr (insert_subset ha (singleton_subset_iff.mpr hb))
    have h5 := ncard_union_add_ncard_inter (P ∩ range a₁) (P ∩ range a₂) (hPf _) (hPf _)
    rw [h3, h4, ncard_pair hab, hc₁, hc₂] at h5
    omega
  exact merge_cone_fans hf₁ hf₂ hPb ha hb (hFu ▸ Or.inl h₁.left_mem) hcbd hFΔ hFu h₁ h₂ haF₂ hbF₁
    hLF
    hun hint hb₁ hb₂ hX₁n hX₂n hsplit' hin₁ hin₂ hbd₁ hbd₂ hQ₁ hQ₂ hsp₁' hsp₂' hsp
    hF₁L hF₂L hF₁₂ hF₁F₂ hdL hd𝓒 hnL₁ hnL₂ hnS₁ hnS₂ hPcount hpr₁ hpr₂

/-- **The cone on a closed disc.** A closed disc with at least two marked boundary points is cut
into triangles by arcs from an interior point `c` to the marked points. -/
theorem exists_cone {Δ P : Set X} (hΔ : IsClosedDisc Δ) (hP : P.Finite)
  (hPb : P ⊆ discBd Δ) {a b : X} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    ∃ (c : X) (𝓛 𝓒 : Set (Set X)), c ∈ discInt Δ ∧ IsChordFan Δ (insert c P) 𝓛 𝓒 ∧ 𝓛.ncard
      = P.ncard ∧ 𝓒.ncard = P.ncard ∧
      (∀ L ∈ 𝓛, ∃ p ∈ P, IsLineWithEnds L c p ∧ L ∩ discBd Δ = {p}) ∧
      ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c} := by
  classical
  obtain ⟨F, hF, hFΔ, hFbd⟩ := exists_chord hΔ (hPb ha) (hPb hb) hab
  obtain ⟨f, hf, hfr, hf0, hf1⟩ := hF.exists_arc
  let m : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hm0 : (0 : 𝕀) < m := by
    change (0 : ℝ) < 1 / 2
    norm_num
  have hm1 : m < 1 := by
    change (1 / 2 : ℝ) < 1
    norm_num
  set c := f m with hc
  let F₁ : Set X := f '' Icc 0 m
  let F₂ : Set X := f '' Icc m 1
  have h₁ : IsLineWithEnds F₁ c a := by
    have h2 := (hf.sub (s := 0) (t := m) hm0.ne).isLineWithEnds
    rw [range_subArc f hm0.le, subArc_zero, subArc_one, hf0] at h2
    exact h2.symm
  have h₂ : IsLineWithEnds F₂ c b := by
    have h2 := (hf.sub (s := m) (t := 1) hm1.ne).isLineWithEnds
    rwa [range_subArc f hm1.le, subArc_zero, subArc_one, hf1] at h2
  have hFu : F = F₁ ∪ F₂ := by
    rw [← image_union, Icc_union_Icc_eq_Icc hm0.le hm1.le, ← hfr]
    ext x
    simp only [mem_range, mem_image, mem_Icc]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ⟨t.2.1, t.2.2⟩, ht⟩, fun ⟨t, _, ht⟩ => ⟨t, ht⟩⟩
  have hF₁F₂ : F₁ ∩ F₂ = {c} := by
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, he⟩⟩
      have h3 : t = s := hf.2 he
      subst h3
      have : t = m := le_antisymm hs.2 ht.1
      rw [this]
      rfl
    · rintro rfl
      exact ⟨⟨m, ⟨hm0.le, le_rfl⟩, rfl⟩, ⟨m, ⟨le_rfl, hm1.le⟩, rfl⟩⟩
  have hcbd : c ∉ discBd Δ := fun h => by
    have h3 : c ∈ F ∩ discBd Δ := ⟨hfr ▸ mem_range_self m, h⟩
    rw [hFbd] at h3
    rcases h3 with h3 | h3
    · exact hm0.ne (hf.2 (hf0.trans h3.symm))
    · exact hm1.ne' (hf.2 (hf1.trans h3.symm))
  have hbF₁ : b ∉ F₁ := by
    rintro ⟨t, ht, he⟩
    have h3 : t = 1 := hf.2 (he.trans hf1.symm)
    exact absurd (ht.2.trans_lt hm1) (by rw [h3]; exact lt_irrefl _)
  have haF₂ : a ∉ F₂ := by
    rintro ⟨t, ht, he⟩
    have h3 : t = 0 := hf.2 (he.trans hf0.symm)
    exact absurd (hm0.trans_le ht.1) (by rw [h3]; exact lt_irrefl _)
  obtain ⟨a₁, a₂, hTwo, h0, h1, hu⟩ := hΔ.isOArc_discBd.exists_arcs (hPb ha) (hPb hb) hab
  have hl₁ : IsLineWithEnds (range a₁) a b := by
    have := hTwo.arc_left.isLineWithEnds
    rwa [h0, h1] at this
  have hl₂ : IsLineWithEnds (range a₂) a b := by
    have := hTwo.arc_right.isLineWithEnds
    rwa [hTwo.zero, hTwo.one, h0, h1] at this
  have hinter : range a₁ ∩ range a₂ = {a, b} := by
    rw [hTwo.inter, h0, h1]
  let X₁ : Set X := range a₁ \ {a, b}
  let X₂ : Set X := range a₂ \ {a, b}
  have hY : discBd Δ \ {a, b} = X₁ ∪ X₂ := by
    rw [← hu, union_sdiff_distrib]
  have hdX : Disjoint X₁ X₂ := Set.disjoint_left.mpr fun y hy hy' => hy.2 (hinter ▸ ⟨hy.1, hy'.1⟩)
  have nX : ∀ {L : Set X}, IsLineWithEnds L a b → (L \ {a, b}).Nonempty := fun {L} hL => by
    by_contra hc'
    rw [not_nonempty_iff_eq_empty] at hc'
    have h2 := hL.subset_closure_diff
    rw [hc', closure_empty] at h2
    exact h2 hL.left_mem
  let main := fun {Δ₁ Δ₂ : Set X} =>
    cone_of_split_discs hF hFΔ hFbd hFu h₁ h₂ hF₁F₂ hbF₁ haF₂ hcbd hP hPb ha hb hab
      hl₁ hl₂ hinter hu (Δ₁ := Δ₁) (Δ₂ := Δ₂)
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hcomp, hΔ₁, hΔ₂, hun, hint, hb₁, hb₂, -⟩
    := disc_iArc.{0} Δ F a b hΔ hFΔ hab hF hFbd
  rcases comps_two hA hcomp hY hdX hl₁.isPreconnected_diff hl₂.isPreconnected_diff (nX hl₁)
    (nX hl₂) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact main hΔ₁ hΔ₂ hun hint hb₁ hb₂
  · exact main hΔ₂ hΔ₁ (by rw [union_comm, hun]) (by rw [inter_comm, hint]) hb₂ hb₁

end GraphMinor.Surface
