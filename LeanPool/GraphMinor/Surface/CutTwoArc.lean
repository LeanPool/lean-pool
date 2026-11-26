/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutTwoWords

/-!
# Arcs with lifts in two components

If the two lifts of an arc lie in different components of the cut surface, then each component has a
word with the lift as a
side, and pasting these sides gives a family of two words for the surface before cutting
(`arc_two_comps`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

theorem rW_labels_lt {a b c : ℕ} {L : List ℕ} (hL : ∀ m ∈ L, m < c) : ∀ l ∈ rW a b c L, l.1 < frL a
  b c := by
  intro l hl
  simp only [rW, frL, List.mem_append] at hl ⊢
  rcases hl with ((hl | hl) | hl) | hl
  · have := (hW_labels _ _ l hl).2
    omega
  · have := (cW_labels _ _ l hl).2
    omega
  · obtain ⟨m, h1, h2⟩ := hlW_labels l hl
    have := hL m h1
    omega
  · simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp

theorem erase_facts (c i : ℕ) : ((List.range' 0 c).erase i).Nodup ∧ ∀ m ∈
  (List.range' 0 c).erase i, m < c ∧ m ≠ i := by
  have h := List.nodup_range' (s := 0) (n := c)
  refine ⟨h.erase _, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := (h.mem_erase_iff).mp hm
  have h3 := List.mem_range'_1.mp h2
  exact ⟨by omega, h1⟩

theorem length_erase_range {c i : ℕ} (h : i < c) : ((List.range' 0 c).erase i).length = c - 1 := by
  rw [List.length_erase_of_mem (List.mem_range'_1.mpr (by omega))]
  simp

/-- The set `C`, as a subset of the big space. -/
noncomputable def hatC {Y : Type*} [TopologicalSpace Y] {W : Set Y} {C : Set W} (φ : Circle ≃ₜ C) :
    Circle ≃ₜ (Subtype.val '' C : Set Y) :=
  φ.trans (IsEmbedding.subtypeVal.homeomorphImage C)

theorem hatC_val {Y : Type*} [TopologicalSpace Y] {W : Set Y} {C : Set W} (φ : Circle ≃ₜ C)
  (x : Circle) :
    (hatC φ x).1 = (φ x).1.1 := rfl

/-- A connected part of the boundary inside an open part lies in one cuff of this part. -/
theorem exists_cuff_sub {Y : Type*} [TopologicalSpace Y] {W K : Set Y} (hW : IsOpen W)
  (hK : IsPreconnected K) (hne : K.Nonempty)
    (hsub : K ⊆ W) (hb : K ⊆ bd Y) : ∃ C ∈ cuffs W, K ⊆ Subtype.val '' C := by
  obtain ⟨x, hx⟩ := hne
  have h1 : (Subtype.val ⁻¹' K : Set W) ⊆ bd W := fun z hz => (mem_bd_sub hW).mpr (hb hz)
  have h2 : IsPreconnected (Subtype.val ⁻¹' K : Set W) := by
    refine (IsInducing.subtypeVal.isPreconnected_image).mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
    exact hK
  have hx' : (⟨x, hsub hx⟩ : W) ∈ (Subtype.val ⁻¹' K : Set W) := hx
  refine ⟨_, ⟨_, h1 hx', rfl⟩, fun z hz => ?_⟩
  exact ⟨⟨z, hsub hz⟩, h2.subset_connectedComponentIn hx' h1 hz, rfl⟩

section

variable {Y S : Type*} [TopologicalSpace Y] [TopologicalSpace S] {ψ : Y → S} {F : Set S} {a₀ : ℝ
  → S} {ξ η : ℝ → Y}

/-- Two pieces of the family, pasted. -/
theorem two_gl (L₀ : ArcLift ψ F a₀ ξ η) (hψc : Continuous ψ) (hsurj : Surjective ψ) {W₁ W₂ : Set
  Y} (hd : Disjoint W₁ W₂)
    (hU : W₁ ∪ W₂ = univ) {u A B : List Letter} {p q p₁ : ℕ} {σ : Bool} (hp1 : u[p₁]? = some
      (p, true)) (hc1 : cnt u p = 1)
    (hc2 : cnt (A ++ (q, true) :: B) q = 1) (hdis : DisjL u (A ++ (q, true) :: B)) {g₁ : ℕ × ℂ
      → W₁} {g₂ : ℕ × ℂ → W₂}
    (h₁ : Presents (sW u) g₁) (h₂ : Presents (sW (A ++ (q, true) :: B)) g₂) {ρ₁ : ℝ → W₁} {ρ₂ : ℝ
      → W₂}
    (hs₁ : SideVal (sW u) g₁ p ρ₁) (hs₂ : SideVal (sW (A ++ (q, true) :: B)) g₂ q ρ₂)
      (he₁ : ∀ t ∈ Icc (0 : ℝ) 1, (ρ₁ t).1 = ξ t)
    (he₂ : ∀ t ∈ Icc (0 : ℝ) 1, (ρ₂ (ofs σ t)).1 = η t) :
    Presents (dW u (A ++ (p, σ) :: B)) (ψ ∘ glW g₁ g₂) ∧ SideVal (dW u (A ++ (p, σ) :: B))
      (ψ ∘ glW g₁ g₂) p a₀ := by
  have hne : u ≠ [] := by
    rintro rfl
    simp at hp1
  have hq : (A ++ (q, true) :: B)[A.length]? = some (q, true) := by simp
  refine glue_two L₀ hψc hsurj (ζ := fun t => (ρ₂ t).1) hp1 hc1 hc2 hdis (presents_dW hne
    (by simp) hdis hd hU h₁ h₂) rfl
    (fun t ht => ?_) (fun t ht => ?_) he₂
  · simp only [glW, ite_true]
    rw [hs₁.at_word hp1 hc1 t ht, he₁ t ht]
  · simp only [glW, one_ne_zero, ite_false]
    rw [hs₂.at_word hq hc2 t ht]

end

/-- Counts labels in an explicit word whose tail has known counts. -/
local macro "ct" : tactic =>
  `(tactic| ((try simp only [hB, holB, List.cons_append, List.nil_append, List.append_assoc,
    cnt_append, cnt_cons, cnt_nil, tL, rL, frL, linv, Prod.fst, *]); (try split_ifs) <;> omega))

section

variable {Y S : Type uu} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] {ψ : Y
  → S} {F : Set S} {a₀ : ℝ → S} {ξ η : ℝ → Y}
  {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ}

/-- Each component has the lift as a side. -/
theorem arc_comps_aux (hS : IsSurface Y) (L₀ : ArcLift ψ F a₀ ξ η) (hψc : Continuous ψ)
  (hsurj : Surjective ψ) {W₁ W₂ : Set Y}
    (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂) (hd : Disjoint W₁ W₂) (hU : W₁ ∪ W₂ = univ)
      (e₁ : W₁ ≃ₜ SurfaceModel a₁ b₁ c₁)
    (e₂ : W₂ ≃ₜ SurfaceModel a₂ b₂ c₂) (hξ1 : ξ '' Icc 0 1 ⊆ W₁) (hη1 : η '' Icc 0 1 ⊆ W₂)
      (hξ2 : ξ '' Icc 0 1 ⊆ bd Y)
    (hη2 : η '' Icc 0 1 ⊆ bd Y) (hiξ : InjOn ξ (Icc 0 1)) (hiη : InjOn η (Icc 0 1)) :
    ∃ (i j : ℕ) (σ : Bool) (a' : ℝ → S) (f : ℕ × ℂ → S), i < c₁ ∧ j < c₂ ∧ a' '' Icc 0 1 = F ∧
      ((a' 0 = a₀ 0 ∧ a' 1 = a₀ 1) ∨ (a' 0 = a₀ 1 ∧ a' 1 = a₀ 0)) ∧
      Presents (dW (wArc₁ a₁ b₁ c₁ i ((List.range' 0 c₁).erase i))
        (wArc₂ a₂ b₂ c₂ j ((List.range' 0 c₂).erase j) (frL a₁ b₁ c₁ + 1) ((rL a₁ b₁ i).1, σ))) f ∧
      SideVal (dW (wArc₁ a₁ b₁ c₁ i ((List.range' 0 c₁).erase i))
        (wArc₂ a₂ b₂ c₂ j ((List.range' 0 c₂).erase j) (frL a₁ b₁ c₁ + 1) ((rL a₁ b₁ i).1, σ))) f
          (rL a₁ b₁ i).1 a' := by
  have hS₁ := isSurface_sub hS hW₁
  have hS₂ := isSurface_sub hS hW₂
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨C₁, hC₁, hsC₁⟩ := exists_cuff_sub hW₁.2 (isPreconnected_Icc.image _ L₀.cξ)
    (hne.image _) hξ1 hξ2
  obtain ⟨C₂, hC₂, hsC₂⟩ := exists_cuff_sub hW₂.2 (isPreconnected_Icc.image _ L₀.cη)
    (hne.image _) hη1 hη2
  obtain ⟨i, hi, φ₁, g₁, hg₁, hs₁⟩ := exists_one_hole e₁ hC₁
  obtain ⟨j, hj, φ₂, g₂, hg₂, hs₂⟩ := exists_one_hole e₂ hC₂
  have hRange₁ : range (hatC φ₁) = univ := (hatC φ₁).surjective.range_eq
  have hRange₂ : range (hatC φ₂) = univ := (hatC φ₂).surjective.range_eq
  obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L₀ (hatC φ₁)
    (fun u hu => hsC₁ ⟨u, hu, rfl⟩) hiξ hiη
  have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ (Subtype.val '' C₂ : Set Y) := fun u hu => hsC₂
    (heim ▸ ⟨u, hu, rfl⟩)
  obtain ⟨n, n1, n2⟩ := exists_lift (hatC φ₂) L'.cη hη'
  obtain ⟨σ, n', c', s', h3, h4⟩ := exists_dir n1 (lift_mono n1 (inj_of_lift n2 hie))
    (inj_of_lift n2 hie)
  have hlt := lift_lt_add_one hmc (inj_of_lift hmξ hix)
  have hlt' := lift_lt_add_one c' h4
  obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
  obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
  set L₁ := (List.range' 0 c₁).erase i
  set L₂ := (List.range' 0 c₂).erase j
  have c1 : cnt (rW a₁ b₁ c₁ L₁) (2 * a₁ + b₁ + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega
  have c3 : cnt (rW a₁ b₁ c₁ L₁) (2 * a₁ + b₁ + 2 * c₁ + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega
  have c1' : cnt (rW a₂ b₂ c₂ L₂) (2 * a₂ + b₂ + 2 * j + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₂ m hm
    omega
  have c3' : cnt (rW a₂ b₂ c₂ L₂) (2 * a₂ + b₂ + 2 * c₂ + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₂ m hm
    omega
  have hl₁ : ∀ l ∈ wArc₁ a₁ b₁ c₁ i L₁, l.1 < frL a₁ b₁ c₁ + 1 := by
    intro l hl
    simp only [wArc₁, List.cons_append, List.nil_append, List.mem_cons, tL, rL, linv, frL] at hl
    rcases hl with rfl | rfl | rfl | rfl | hl
    · simp only [frL]; omega
    · simp only [frL]; omega
    · simp only [frL]; omega
    · simp only [frL]; omega
    · have := rW_labels_lt (fun m hm => (hL₁ m hm).1) l hl
      omega
  have e0 : ∀ a b c i' (L : List ℕ), hB a b i' ++ rW a b c L = [tL a b i'] ++
    ((rL a b i').1, true) :: (linv (tL a b i') :: rW a b c L) := by
    intro a b c i' L
    simp [hB, holB, rL]
  rw [e0] at hg₁ hs₁ hg₂ hs₂
  obtain ⟨g₁', p1, p2, -, -⟩ := exists_pieces2 hS₁ hC₁ isOpen_univ (subset_univ _) φ₁ (q
    := frL a₁ b₁ c₁)
    (by simp [rL, frL]; omega) (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) hg₁ hs₁ hmc
      (continuousOn_lin _ _) hmm (strictMonoOn_lin hlt)
    (lin_zero _ _).symm (lin_one _ _)
  obtain ⟨g₂', p3, p4, -, -⟩ := exists_pieces2 hS₂ hC₂ isOpen_univ (subset_univ _) φ₂ (q
    := frL a₂ b₂ c₂)
    (by simp [rL, frL]; omega) (noLab_iff_cnt.mpr (by ct)) (noLab_iff_cnt.mpr (by ct)) hg₂ hs₂ c'
      (continuousOn_lin _ _) s' (strictMonoOn_lin hlt')
    (lin_zero _ _).symm (lin_one _ _)
  set M := frL a₁ b₁ c₁ + 1
  have p5 := presents_shW M p3
  have p6 := p4.shW M
  have e1 : shW M ([tL a₂ b₂ j] ++ ((rL a₂ b₂ j).1, true) :: (frL a₂ b₂ c₂, true) :: linv
    (tL a₂ b₂ j) :: rW a₂ b₂ c₂ L₂) =
      [((tL a₂ b₂ j).1 + M, true)] ++ ((rL a₂ b₂ j).1 + M, true) ::
        ((frL a₂ b₂ c₂ + M, true) :: ((tL a₂ b₂ j).1 + M, false) :: shW M (rW a₂ b₂ c₂ L₂)) := by
    simp [shW, tL, linv]
  rw [e1] at p5 p6
  have c5 : cnt (shW M (rW a₂ b₂ c₂ L₂)) (2 * a₂ + b₂ + 2 * j + 1 + M) = 0 :=
    noLab_iff_cnt.mp (noLab_shW_of fun k' he => by
      have : k' = 2 * a₂ + b₂ + 2 * j + 1 := by omega
      subst this
      exact noLab_iff_cnt.mpr c1')
  have hcq : cnt ([((tL a₂ b₂ j).1 + M, true)] ++ ((rL a₂ b₂ j).1 + M, true) ::
        ((frL a₂ b₂ c₂ + M, true) :: ((tL a₂ b₂ j).1 + M, false) :: shW M (rW a₂ b₂ c₂ L₂)))
          ((rL a₂ b₂ j).1 + M) = 1 := by
    simp only [List.cons_append, List.nil_append, cnt_cons, tL, rL, frL, c5]
    split_ifs <;> omega
  obtain ⟨p7, p8⟩ := two_gl L' hψc hsurj hd hU (p₁ := 1) (u := wArc₁ a₁ b₁ c₁ i L₁) (p :=
    (rL a₁ b₁ i).1) (σ := σ) rfl
    (by simp only [wArc₁]; ct) hcq (by
      rw [← e1]
      intro l hl
      have := hl₁ l hl
      exact noLab_shW_of fun k' he => by omega) p1 p5 p2 p6 (fun t ht => hmξ t ht) (fun t ht => by
        simp only [h3 t ht]
        exact n2 t ht)
  exact ⟨i, j, σ, a', _, hi, hj, L'.img, ha', p7, p8⟩

end

end GraphMinor.Surface
