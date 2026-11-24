/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutCyl

/-!
# Cutting along an `O`-arc

We prove `CutOArcStatement` (`cutOArc`). As for `I`-arcs, the cut surface comes from
`exists_cut_loop`, each component has a
word from `classification`, and the word of the surface before cutting has a normal form that shows
which surface it is.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u uu

section

variable {Y S : Type uu} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] {ψ : Y
  → S} {F : Set S}
  {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ}

omit [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] in
/-- Two paths that continue each other around a loop form a one to one loop. -/
theorem conc_inj {ξ η : ℝ → Y} {a : ℝ → S} (hξ : ∀ t ∈ Icc (0 : ℝ) 1, ψ (ξ t) = a t)
  (hη : ∀ t ∈ Icc (0 : ℝ) 1, ψ (η t) = a t)
    (c7 : InjOn a (Ico 0 1)) (c8 : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ≠ η t) (e1 : ξ 1 = η 0) (e2 : η 1
      = ξ 0) : InjOn (conc2 ξ η) (Ico 0 1) := by
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h10 : a 1 = a 0 := by rw [← hξ 1 m1, e1, hη 0 m0]
  have one : ∀ v ∈ Icc (0 : ℝ) 1, a v = a 0 → v = 0 ∨ v = 1 := by
    intro v hv he
    rcases eq_or_lt_of_le hv.2 with rfl | h
    · exact .inr rfl
    · exact .inl (c7 ⟨hv.1, h⟩ ⟨le_rfl, zero_lt_one⟩ he)
  have injξ : InjOn ξ (Icc 0 1) := by
    intro x hx y hy he
    have ha : a x = a y := by rw [← hξ x hx, ← hξ y hy, he]
    rcases eq_or_lt_of_le hx.2 with rfl | h
    · rcases eq_or_lt_of_le hy.2 with rfl | h'
      · rfl
      · rw [h10] at ha
        rcases one y hy ha.symm with rfl | h4
        · exact absurd (he.symm.trans e1) (c8 0 m0)
        · exact h4.symm
    · rcases eq_or_lt_of_le hy.2 with rfl | h'
      · rw [h10] at ha
        rcases one x hx ha with rfl | h4
        · exact absurd (he.trans e1) (c8 0 m0)
        · exact h4
      · exact c7 ⟨hx.1, h⟩ ⟨hy.1, h'⟩ ha
  have injη : InjOn η (Icc 0 1) := by
    intro x hx y hy he
    have ha : a x = a y := by rw [← hη x hx, ← hη y hy, he]
    rcases eq_or_lt_of_le hx.2 with rfl | h
    · rcases eq_or_lt_of_le hy.2 with rfl | h'
      · rfl
      · rw [h10] at ha
        rcases one y hy ha.symm with rfl | h4
        · exact absurd (e2.symm.trans (he)) (c8 0 m0)
        · exact h4.symm
    · rcases eq_or_lt_of_le hy.2 with rfl | h'
      · rw [h10] at ha
        rcases one x hx ha with rfl | h4
        · exact absurd (e2.symm.trans he.symm) (c8 0 m0)
        · exact h4
      · exact c7 ⟨hx.1, h⟩ ⟨hy.1, h'⟩ ha
  have cross : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1, ξ v ≠ η w := by
    intro v hv w hw he
    have ha : a v = a w := by rw [← hξ v hv, he, hη w (Ioo_subset_Icc_self hw)]
    rcases eq_or_lt_of_le hv.2 with rfl | h
    · rw [h10] at ha
      exact hw.1.ne (c7 ⟨le_rfl, zero_lt_one⟩ (Ioo_subset_Ico_self hw) ha)
    · have := c7 ⟨hv.1, h⟩ (Ioo_subset_Ico_self hw) ha
      subst this
      exact c8 v hv he
  intro x hx y hy he
  unfold conc2 at he
  have mem1 : ∀ {z : ℝ}, z ∈ Ico (0 : ℝ) 1 → z ≤ 1 / 2 → 2 * z ∈ Icc (0 : ℝ) 1 := fun hz h
    => ⟨by linarith [hz.1], by linarith⟩
  have mem2 : ∀ {z : ℝ}, z ∈ Ico (0 : ℝ) 1 → ¬ z ≤ 1 / 2 → 2 * z - 1 ∈ Ioo (0 : ℝ) 1 := fun hz h
    => by
    have := not_le.mp h
    exact ⟨by linarith, by linarith [hz.2]⟩
  by_cases hx2 : x ≤ 1 / 2 <;> by_cases hy2 : y ≤ 1 / 2
  · rw [ite_eq_left hx2, ite_eq_left hy2] at he
    have := injξ (mem1 hx hx2) (mem1 hy hy2) he
    linarith
  · rw [ite_eq_left hx2, ite_eq_right hy2] at he
    exact absurd he (cross _ (mem1 hx hx2) _ (mem2 hy hy2))
  · rw [ite_eq_right hx2, ite_eq_left hy2] at he
    exact absurd he.symm (cross _ (mem1 hy hy2) _ (mem2 hx hx2))
  · rw [ite_eq_right hx2, ite_eq_right hy2] at he
    have := injη (Ioo_subset_Icc_self (mem2 hx hx2)) (Ioo_subset_Icc_self (mem2 hy hy2)) he
    linarith

/-- Counts labels in an explicit word whose tail has known counts. -/
local macro "ct" : tactic =>
  `(tactic| ((try simp only [hB, holB, List.cons_append, List.nil_append, List.append_assoc,
    cnt_append, cnt_cons, cnt_nil, tL, rL, frL, linv, Prod.fst, *]); (try split_ifs) <;> omega))

/-- Each component has a whole cuff as a lift. -/
theorem loop_comps_aux [T2Space S] (hS : IsSurface Y) (hψ : IsCutting ψ F) {X X' : Set Y}
  (hun : X ∪ X' = ψ ⁻¹' F) (b1 : BijOn ψ X F)
    (b2 : BijOn ψ X' F) (hOX : IsOArc X) (hOX' : IsOArc X') {W₁ W₂ : Set Y} (hW₁ : IsClopen W₁)
      (hW₂ : IsClopen W₂) (hd : Disjoint W₁ W₂)
    (hU : W₁ ∪ W₂ = univ) (e₁ : W₁ ≃ₜ SurfaceModel a₁ b₁ c₁) (e₂ : W₂ ≃ₜ SurfaceModel a₂ b₂ c₂)
      (s₁ : X ⊆ W₁) (s₂ : X' ⊆ W₂)
    (t₁ : X ⊆ bd Y) (t₂ : X' ⊆ bd Y) :
    ∃ (i j : ℕ) (σ : Bool) (f : ℕ × ℂ → S) (ρ : ℝ → Y) (q : ℕ), i < c₁ ∧ j < c₂ ∧
      Presents (dW (wLoop₁ a₁ b₁ c₁ i ((List.range' 0 c₁).erase i))
        (wLoop₂ a₂ b₂ c₂ j ((List.range' 0 c₂).erase j) (frL a₁ b₁ c₁ + 1) ((rL a₁ b₁ i).1, σ))) f ∧
      (wLoop₁ a₁ b₁ c₁ i ((List.range' 0 c₁).erase i))[q]? = some ((rL a₁ b₁ i).1, true) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, f (0, per (wLoop₁ a₁ b₁ c₁ i ((List.range' 0 c₁).erase i)).length
        (q + u)) = ψ (ρ u)) ∧
      ContinuousOn ρ (Icc 0 1) ∧ ρ 1 = ρ 0 ∧ ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ X := by
  have hS₁ := isSurface_sub hS hW₁
  have hS₂ := isSurface_sub hS hW₂
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have ne₁ : X.Nonempty := by
    obtain ⟨e⟩ := id hOX
    exact ⟨_, (e 1).2⟩
  have ne₂ : X'.Nonempty := by
    obtain ⟨e⟩ := id hOX'
    exact ⟨_, (e 1).2⟩
  obtain ⟨C₁, hC₁, hsC₁⟩ := exists_cuff_sub hW₁.2 hOX.isPreconnected ne₁ s₁ t₁
  obtain ⟨C₂, hC₂, hsC₂⟩ := exists_cuff_sub hW₂.2 hOX'.isPreconnected ne₂ s₂ t₂
  obtain ⟨i, hi, φ₁, g₁, hg₁, hs₁⟩ := exists_one_hole e₁ hC₁
  obtain ⟨j, hj, φ₂, g₂, hg₂, hs₂⟩ := exists_one_hole e₂ hC₂
  have eX := oarc_eq (hatC φ₁) hOX hsC₁
  have eX' := oarc_eq (hatC φ₂) hOX' hsC₂
  have : CompactSpace Y := hS.1
  have hcX' : IsCompact X' := hOX'.isCompact
  have cξ : ContinuousOn (fun u => (hatC φ₁ (ee u)).1) (Icc 0 1) :=
    (continuous_subtype_val.comp ((hatC φ₁).continuous.comp continuous_ee)).continuousOn
  have injξ : InjOn (fun u => (hatC φ₁ (ee u)).1) (Ico 0 1) := fun x hx y hy he =>
    ee_injOn hx hy ((hatC φ₁).injective (Subtype.ext he))
  have h01 : (hatC φ₁ (ee 0)).1 = (hatC φ₁ (ee 1)).1 := by rw [ee_one]
  have himξ : (fun u => (hatC φ₁ (ee u)).1) '' Icc 0 1 = X := by
    rw [eX]
    exact loop_image (hatC φ₁) cξ (fun u _ => (hatC φ₁ _).2) injξ h01
  obtain ⟨η, L₀, himη, hiff⟩ := loop_lift hψ hun b1 b2 hcX' cξ himξ
  have hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ (Subtype.val '' C₂ : Set Y) := fun u hu
    => eX' ▸ himη ▸ mem_image_of_mem η hu
  have cl : η 0 = η 1 := (hiff 0 m0 1 m1).mp h01
  have injη : InjOn η (Ico 0 1) := fun x hx y hy he =>
    injξ hx hy ((hiff x (Ico_subset_Icc_self hx) y (Ico_subset_Icc_self hy)).mpr he)
  obtain ⟨σ, n', c', s', h3, h4⟩ := exists_loop_turn (hatC φ₂) L₀.cη hη injη cl
  obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
  obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
  set L₁ := (List.range' 0 c₁).erase i
  set L₂ := (List.range' 0 c₂).erase j
  have c1 : cnt (rW a₁ b₁ c₁ L₁) (2 * a₁ + b₁ + 2 * i + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega
  have c1' : cnt (rW a₂ b₂ c₂ L₂) (2 * a₂ + b₂ + 2 * j + 1) = 0 := cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₂ m hm
    omega
  have hl₁ : ∀ l ∈ wLoop₁ a₁ b₁ c₁ i L₁, l.1 < frL a₁ b₁ c₁ + 1 := by
    intro l hl
    simp only [wLoop₁, hB, holB, List.cons_append, List.nil_append, List.mem_cons, tL, rL, linv]
      at hl
    rcases hl with rfl | rfl | rfl | hl
    · simp only [frL]; omega
    · simp only [frL]; omega
    · simp only [frL]; omega
    · have := rW_labels_lt (fun m hm => (hL₁ m hm).1) l hl
      omega
  obtain ⟨g₂', p1, p2, -⟩ := exists_pieces1 hS₂ hC₂ isOpen_univ (subset_univ _) φ₂ hg₂ hs₂ c' s' h3
  set M := frL a₁ b₁ c₁ + 1
  have p5 := presents_shW M p1
  have p6 := p2.shW M
  have e1 : shW M (hB a₂ b₂ j ++ rW a₂ b₂ c₂ L₂) =
      [((tL a₂ b₂ j).1 + M, true)] ++ ((rL a₂ b₂ j).1 + M, true) :: (((tL a₂ b₂ j).1 + M, false) ::
        shW M (rW a₂ b₂ c₂ L₂)) := by
    simp [shW, hB, holB, tL, rL, linv]
  rw [e1] at p5 p6
  have c5 : cnt (shW M (rW a₂ b₂ c₂ L₂)) (2 * a₂ + b₂ + 2 * j + 1 + M) = 0 :=
    noLab_iff_cnt.mp (noLab_shW_of fun k' he => by
      have : k' = 2 * a₂ + b₂ + 2 * j + 1 := by omega
      subst this
      exact noLab_iff_cnt.mpr c1')
  have hcq : cnt ([((tL a₂ b₂ j).1 + M, true)] ++ ((rL a₂ b₂ j).1 + M, true) ::
        (((tL a₂ b₂ j).1 + M, false) :: shW M (rW a₂ b₂ c₂ L₂))) ((rL a₂ b₂ j).1 + M) = 1 := by
    simp only [List.cons_append, List.nil_append, cnt_cons, tL, rL, c5]
    split_ifs <;> omega
  obtain ⟨p7, -⟩ := two_gl L₀ hψ.1 hψ.2.1 hd hU (p₁ := 1) (u := wLoop₁ a₁ b₁ c₁ i L₁) (p :=
    (rL a₁ b₁ i).1) (σ := σ) rfl
    (by simp only [wLoop₁]; ct) hcq (by
      rw [← e1]
      intro l hl
      have := hl₁ l hl
      exact noLab_shW_of fun k' he => by omega) hg₁ p5 hs₁ p6 (fun t _ => rfl) (fun t ht => by
        have h5 := h4 _ (ofs_mem (e := σ) ht)
        rw [ofs_ofs] at h5
        exact h5)
  obtain ⟨d, q, hq1, hq2⟩ := hs₁
  obtain ⟨rfl, hq3⟩ := sW_get hq1
  rw [sW_zero] at hq2
  refine ⟨i, j, σ, _, _, q, hi, hj, p7, hq3, fun u hu => ?_, cξ, ?_,
    fun u hu => himξ ▸ mem_image_of_mem _ hu⟩
  · have e6 : per (wLoop₁ a₁ b₁ c₁ i L₁).length (q + u) = sdPt (hB a₁ b₁ i ++ rW a₁ b₁ c₁
      L₁).length q true u := by
      simp only [sdPt, ite_true, wLoop₁]
    simp only [Function.comp, glW, ite_true]
    rw [e6, hq2 u hu]
    rfl
  · exact h01.symm

end

/-- **Cutting along an `O`-arc.** The classical cut and paste proof: Massey, *Algebraic Topology: an
Introduction*, Chapter 1,
Section 7. -/
theorem cutOArc : CutOArcStatement.{u} := by
  intro S _ F hS hconn hO hd
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hcase, Z₁, Z₂, u, c, X₁, Y₁, X₂, Y₂, h7, h8, hi, hun, huc, hfu,
    hfc⟩ := exists_cut_loop hS hO hd
  have hcY : CompactSpace Y := hY.1
  refine ⟨Y, tY, ψ, hY, hψ, ?_, hcase⟩
  have hdcuff := cuff_statement.{u} Y hY
  obtain ⟨s⟩ : Nonempty S := inferInstance
  have hne : Nonempty S := ⟨s⟩
  rcases hcase with ⟨X, X', hdX, hunX, hOX, hOX', b1, b2⟩ | hQ
  · have ne₁ : X.Nonempty := by
      obtain ⟨e⟩ := id hOX
      exact ⟨_, (e 1).2⟩
    have ne₂ : X'.Nonempty := by
      obtain ⟨e⟩ := id hOX'
      exact ⟨_, (e 1).2⟩
    obtain ⟨x, hx⟩ := ne₁
    obtain ⟨y, hy⟩ := ne₂
    have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hunX ▸ Or.inl hz)
    have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hunX ▸ Or.inr hz)
    rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hunX hx hy with hYc | ⟨W₁, W₂,
      hne', hsc, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
    · obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{u} Y hY hYc
      have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
      have hC' : connectedComponentIn (bd Y) y ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
      obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
      obtain ⟨φ₀'⟩ := hdcuff.2.2 _ hC'
      have eX := oarc_eq φ₀ hOX (hOX.isPreconnected.subset_connectedComponentIn hx hXb)
      have eX' := oarc_eq φ₀' hOX' (hOX'.isPreconnected.subset_connectedComponentIn hy hXb')
      have hCC : connectedComponentIn (bd Y) x ≠ connectedComponentIn (bd Y) y := by
        intro he
        rw [← eX, ← eX'] at he
        exact Set.disjoint_left.mp hdX hx (he ▸ hx)
      obtain ⟨i, hi', j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      rw [eX, eX'] at hunX
      rw [eX] at b1
      rw [eX'] at b2
      have hdis := cuffs_disjoint hC hC' hCC
      obtain ⟨σ, g', hp⟩ := loop_two_aux hY hψ hC' (hdcuff.2.2 _ hC).isCompact.isClosed
        (hdcuff.2.2 _ hC').isCompact.isClosed hdis hunX b1 b2 φ φ'
        hij hi' hj hLf hg hs hs'
      replace hp := hp.1
      have hn := nf_blkE (a := a) (b := b) (c := c) hij hi' hj hN hLf σ
      have hlen := length_erase_erase hij hi' hj
      left
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        exact cutIsSimpler_of_connected e e' (by omega) (by omega) (by omega)
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at e'
        exact cutIsSimpler_of_connected e e' (by omega) (by omega) (by omega)
    · obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{u} W₁ (isSurface_sub hY hW₁) hc₁
      obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification.{u} W₂ (isSurface_sub hY hW₂) hc₂
      obtain ⟨i, j, σ, f, -, -, hi', hj, hf, -⟩ := loop_comps_aux hY hψ hunX b1 b2 hOX hOX' hW₁ hW₂
        hdW hU e₁ e₂ hX₁ hX₂ hXb hXb'
      obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
      obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
      obtain ⟨e'⟩ := homeo_of_two_loop hi' hj hN₁ hN₂ hL₁ hL₂ hf
      rw [length_erase_range hi', length_erase_range hj] at e'
      obtain ⟨d⟩ := nonempty_disc_homeo
      obtain ⟨d'⟩ := nonempty_cyl_homeo
      by_cases h2 : a₂ = 0 ∧ b₂ = 0 ∧ c₂ = 1
      · obtain ⟨rfl, rfl, rfl⟩ := h2
        exact .inr (.inr ⟨W₂, W₁, hne'.symm, by rw [hsc, pair_comm], ⟨(e₂.trans d).symm⟩⟩)
      by_cases h1 : a₁ = 0 ∧ b₁ = 0 ∧ c₁ = 1
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        exact .inr (.inr ⟨W₁, W₂, hne', hsc, ⟨(e₁.trans d).symm⟩⟩)
      by_cases h4 : a₂ = 0 ∧ b₂ = 0 ∧ c₂ = 2
      · obtain ⟨rfl, rfl, rfl⟩ := h4
        rw [show 0 + a₁ = a₁ by omega, show 0 + b₁ = b₁ by omega,
          show 2 - 1 + (c₁ - 1) = c₁ by omega] at e'
        exact .inr (.inl ⟨W₂, W₁, hne'.symm, by rw [hsc, pair_comm], ⟨e₂.trans d'⟩,
          ⟨e₁.trans e'.symm⟩⟩)
      by_cases h3 : a₁ = 0 ∧ b₁ = 0 ∧ c₁ = 2
      · obtain ⟨rfl, rfl, rfl⟩ := h3
        rw [show a₂ + 0 = a₂ by omega, show b₂ + 0 = b₂ by omega,
          show c₂ - 1 + (2 - 1) = c₂ by omega] at e'
        exact .inr (.inl ⟨W₁, W₂, hne', hsc, ⟨e₁.trans d'⟩, ⟨e₂.trans e'.symm⟩⟩)
      refine .inl (cutIsSimpler_of_two hsc e₁ e₂ e' (by omega) (by omega) ?_ (by omega)
        (by omega) ?_)
      · omega
      · omega
  · have ne₀ : (ψ ⁻¹' F).Nonempty := by
      obtain ⟨e⟩ := id hQ
      exact ⟨_, (e 1).2⟩
    have hYc := connected_of_cut hψ hY hQ.isPreconnected rfl ne₀
    obtain ⟨a, b, c', ⟨e⟩⟩ := classification.{u} Y hY hYc
    obtain ⟨x, hx⟩ := ne₀
    have hQb := hψ.2.2.2.2
    have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_, hQb hx, rfl⟩
    obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
    have eQ := oarc_eq φ₀ hQ (hQ.isPreconnected.subset_connectedComponentIn hx hQb)
    obtain ⟨i, hi', φ, g, hg, hs⟩ := exists_one_hole e hC
    obtain ⟨hN, hLf⟩ := erase_facts c' i
    obtain ⟨a₀, ξ, η, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h7.paths h8 hi huc hfu hfc hψ.1
    rw [hun] at c5 c6
    have L : ArcLift ψ F a₀ ξ η := ⟨c1, c2, c3, c4, c5, fun y y' he hne' => by
      by_cases hy : ψ y ∈ F
      · exact c6 y y' he hne' hy
      · exact absurd (hψ.2.2.1 hy (show ψ y' ∈ Fᶜ from he ▸ hy) he) hne'⟩
    have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hξ : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      change ψ (ξ t) ∈ F
      rw [c3 t ht, ← c5]
      exact mem_image_of_mem _ ht
    have hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      change ψ (η t) ∈ F
      rw [c4 t ht, ← c5]
      exact mem_image_of_mem _ ht
    rcases c9 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exfalso
      have injξ : InjOn ξ (Ico 0 1) := fun p hp q hq he => c7 hp hq (by
        rw [← c3 p (Ico_subset_Icc_self hp), ← c3 q (Ico_subset_Icc_self hq), he])
      have him := loop_image φ c1 hξ injξ e1.symm
      obtain ⟨v, hv, hve⟩ := him.symm.subset (hη 0 m0)
      have ha : a₀ v = a₀ 0 := by rw [← c3 v hv, hve, c4 0 m0]
      rcases eq_or_lt_of_le hv.2 with rfl | hv1
      · exact c8 0 m0 (e1.symm.trans hve)
      · have := c7 ⟨hv.1, hv1⟩ ⟨le_rfl, zero_lt_one⟩ ha
        subst this
        exact c8 0 m0 hve
    · obtain ⟨g', -, hp, -⟩ := loop_one_aux hY L hψ.1 hψ.2.1 hC φ hi' hLf hg hs hξ hη
        (conc_inj c3 c4 c7 c8 e1 e2) e1 e2
      obtain ⟨w, h5, h6⟩ := nf_blkD (a := a) (b := b) (c := c') hi' hN hLf
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [length_erase_range hi'] at e'
      exact .inl (cutIsSimpler_of_connected e e' (by omega) (by omega) (by omega))

end GraphMinor.Surface
