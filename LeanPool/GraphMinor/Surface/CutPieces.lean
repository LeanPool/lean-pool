/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.HoleLoop

/-!
# Placing the sides of a word on a cuff

A word has a free side that goes once around a cuff. We move the cuff by `exists_move_loop` and cut
the side into one, two
or four sides, so that the new sides have any given monotone lifts as parameters (`exists_pieces1`,
`exists_pieces2`,
`exists_pieces4`). The lemma `presents_glue` passes from a presentation of a surface that has been
cut to a presentation
of the surface before cutting: two free sides of the word get the same label.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-- Two maps of `[0, 1]` one after the other. -/
noncomputable def conc2 {T : Type*} (m m' : ℝ → T) (x : ℝ) : T := if x ≤ 1 / 2 then m
  (2 * x) else m' (2 * x - 1)

theorem conc2_left {T : Type*} {m m' : ℝ → T} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : conc2 m m' (x / 2)
  = m x := by
  unfold conc2
  rw [ite_eq_left (by linarith [hx.2])]
  congr 1
  ring

theorem conc2_right {T : Type*} {m m' : ℝ → T} (h : m 1 = m' 0) {x : ℝ} (hx : x ∈ Icc
  (0 : ℝ) 1) : conc2 m m' ((1 + x) / 2) = m' x := by
  unfold conc2
  by_cases h1 : (1 + x) / 2 ≤ 1 / 2
  · have hx0 : x = 0 := le_antisymm (by linarith) hx.1
    subst hx0
    rw [ite_eq_left h1]
    norm_num
    exact h
  · rw [ite_eq_right h1]
    congr 1
    ring

theorem conc2_zero {T : Type*} {m m' : ℝ → T} : conc2 m m' 0 = m 0 := by
  have := conc2_left (m := m) (m' := m') (x := 0) (by simp)
  simpa using this

theorem conc2_one {T : Type*} {m m' : ℝ → T} (h : m 1 = m' 0) : conc2 m m' 1 = m' 1 := by
  have := conc2_right h (x := 1) (by simp)
  simpa using this

theorem continuousOn_conc2 {T : Type*} [TopologicalSpace T] {m m' : ℝ → T} (hm : ContinuousOn m
  (Icc 0 1)) (hm' : ContinuousOn m' (Icc 0 1)) (h : m 1 = m' 0) :
    ContinuousOn (conc2 m m') (Icc 0 1) := by
  have e : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 := (Icc_union_Icc_eq_Icc (by norm_num)
    (by norm_num)).symm
  rw [e]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · refine (hm.comp (by fun_prop) fun x hx => ⟨by linarith [hx.1],
      by linarith [hx.2]⟩ : ContinuousOn (fun x => m (2 * x)) _).congr fun x hx => ?_
    exact ite_eq_left hx.2
  · refine (hm'.comp (by fun_prop) fun x hx => ⟨by linarith [hx.1],
      by linarith [hx.2]⟩ : ContinuousOn (fun x => m' (2 * x - 1)) _).congr fun x hx => ?_
    unfold conc2
    split_ifs with h1
    · have hx0 : x = 1 / 2 := le_antisymm h1 hx.1
      subst hx0
      norm_num
      exact h
    · rfl

theorem strictMonoOn_conc2 {m m' : ℝ → ℝ} (hm : StrictMonoOn m (Icc 0 1)) (hm' : StrictMonoOn m'
  (Icc 0 1)) (h : m 1 = m' 0) :
    StrictMonoOn (conc2 m m') (Icc 0 1) := by
  intro x hx y hy hxy
  unfold conc2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  by_cases hx2 : x ≤ 1 / 2
  · by_cases hy2 : y ≤ 1 / 2
    · rw [ite_eq_left hx2, ite_eq_left hy2]
      exact hm ⟨by linarith [hx.1], by linarith⟩ ⟨by linarith [hy.1], by linarith⟩ (by linarith)
    · rw [ite_eq_left hx2, ite_eq_right hy2]
      push Not at hy2
      have h3 : m (2 * x) ≤ m 1 := hm.monotoneOn ⟨by linarith [hx.1], by linarith⟩ h1 (by linarith)
      have h4 : m' 0 < m' (2 * y - 1) := hm' h0 ⟨by linarith, by linarith [hy.2]⟩ (by linarith)
      linarith
  · have hy2 : ¬ y ≤ 1 / 2 := fun h2 => hx2 (by linarith)
    rw [ite_eq_right hx2, ite_eq_right hy2]
    push Not at hx2 hy2
    exact hm' ⟨by linarith, by linarith [hx.2]⟩ ⟨by linarith, by linarith [hy.2]⟩ (by linarith)

theorem SideVal.congr {T : Type*} {W : ℕ → List Letter} {f : ℕ × ℂ → T} {k : ℕ} {ρ ρ' : ℝ → T}
  (h : SideVal W f k ρ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, ρ u = ρ' u) : SideVal W f k ρ' := by
  obtain ⟨i, p, h1, h2⟩ := h
  exact ⟨i, p, h1, fun u hu => (h2 u hu).trans (he u hu)⟩

theorem presents_homeo_comp {W : ℕ → List Letter} {T : Type*} [TopologicalSpace T] {g : ℕ × ℂ → T}
  (hg : Presents W g)
    (α : T ≃ₜ T) : Presents W (α ∘ g) := presents_comp hg α

theorem SideVal.comp {T T' : Type*} {W : ℕ → List Letter} {f : ℕ × ℂ → T} {k : ℕ} {ρ : ℝ → T}
  (h : SideVal W f k ρ)
    (α : T → T') : SideVal W (α ∘ f) k (α ∘ ρ) := by
  obtain ⟨i, p, h1, h2⟩ := h
  exact ⟨i, p, h1, fun u hu => congrArg α (h2 u hu)⟩

section pieces

variable {S : Type uu} [TopologicalSpace S]

/-- A cuff moves, and a side that goes around it gets a new parameter. -/
theorem exists_pieces1 (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (hU : IsOpen U)
  (hCU : C ⊆ U) (φ : Circle ≃ₜ C)
    {W : ℕ → List Letter} {g : ℕ × ℂ → S} (hg : Presents W g) {p : ℕ} (hρ : SideVal W g p fun u =>
      (φ (ee u)).1)
    {τ : ℝ → ℝ} (hc : ContinuousOn τ (Icc 0 1)) (hm : StrictMonoOn τ (Icc 0 1)) (h1 : τ 1
      = τ 0 + 1) :
    ∃ g', Presents W g' ∧ SideVal W g' p (fun u => (φ (ee (τ u))).1) ∧
      ∀ k ρ', SideVal W g k ρ' → (∀ u ∈ Icc (0 : ℝ) 1, ρ' u ∉ U) → SideVal W g' k ρ' := by
  obtain ⟨α, h2, h3⟩ := exists_move_loop hS hC hU hCU φ hc hm h1
  refine ⟨α ∘ g, presents_comp hg α, (hρ.comp α).congr fun u hu => h2 u hu, fun k ρ' h4 h5 => ?_⟩
  exact (h4.comp α).congr fun u hu => h3 _ (h5 u hu)

variable [T2Space S]

/-- A side that goes around a cuff is replaced by two sides. -/
theorem exists_pieces2 (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (hU : IsOpen U)
  (hCU : C ⊆ U) (φ : Circle ≃ₜ C)
    {A B : List Letter} {p q : ℕ} (hpq : p ≠ q) (hp : NoLab (B ++ A) p) (hq : NoLab
      (B ++ A) q) {g : ℕ × ℂ → S}
    (hg : Presents (sW (A ++ (p, true) :: B)) g) (hρ : SideVal (sW (A ++ (p, true) :: B)) g p fun u
      => (φ (ee u)).1)
    {m m' : ℝ → ℝ} (hc : ContinuousOn m (Icc 0 1)) (hc' : ContinuousOn m' (Icc 0 1))
      (hm : StrictMonoOn m (Icc 0 1))
    (hm' : StrictMonoOn m' (Icc 0 1)) (h1 : m 1 = m' 0) (h2 : m' 1 = m 0 + 1) :
    ∃ g', Presents (sW (A ++ (p, true) :: (q, true) :: B)) g' ∧
      SideVal (sW (A ++ (p, true) :: (q, true) :: B)) g' p (fun u => (φ (ee (m u))).1) ∧
      SideVal (sW (A ++ (p, true) :: (q, true) :: B)) g' q (fun u => (φ (ee (m' u))).1) ∧
      ∀ k, k ≠ p → k ≠ q → ∀ ρ', SideVal (sW (A ++ (p, true) :: B)) g k ρ' → (∀ u ∈ Icc
        (0 : ℝ) 1, ρ' u ∉ U) →
        SideVal (sW (A ++ (p, true) :: (q, true) :: B)) g' k ρ' := by
  obtain ⟨g₁, h3, h4, h5⟩ := exists_pieces1 hS hC hU hCU φ hg hρ (continuousOn_conc2 hc hc' h1)
    (strictMonoOn_conc2 hm hm' h1)
    (by rw [conc2_zero, conc2_one h1, h2])
  obtain ⟨g₂, h6, h7, h8, h9⟩ := exists_split hpq hp hq h3 h4
  refine ⟨g₂, h6, h7.congr fun u hu => ?_, h8.congr fun u hu => ?_,
    fun k hk hk' ρ' h10 h11 => h9 k hk hk' ρ' (h5 k ρ' h10 h11)⟩
  · simp only [conc2_left hu]
  · simp only [conc2_right h1 hu]

/-- A side that goes around a cuff is replaced by four sides. -/
theorem exists_pieces4 (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (hU : IsOpen U)
  (hCU : C ⊆ U) (φ : Circle ≃ₜ C)
    {A B : List Letter} {p q₁ q₂ q₃ : ℕ} (h12 : p ≠ q₁) (h13 : p ≠ q₂) (h14 : p ≠ q₃)
      (h23 : q₁ ≠ q₂) (h24 : q₁ ≠ q₃) (h34 : q₂ ≠ q₃)
    (hp : NoLab (B ++ A) p) (hq₁ : NoLab (B ++ A) q₁) (hq₂ : NoLab (B ++ A) q₂) (hq₃ : NoLab
      (B ++ A) q₃) {g : ℕ × ℂ → S}
    (hg : Presents (sW (A ++ (p, true) :: B)) g) (hρ : SideVal (sW (A ++ (p, true) :: B)) g p fun u
      => (φ (ee u)).1)
    {m₀ m₁ m₂ m₃ : ℝ → ℝ} (c0 : ContinuousOn m₀ (Icc 0 1)) (c1 : ContinuousOn m₁ (Icc 0 1))
      (c2 : ContinuousOn m₂ (Icc 0 1))
    (c3 : ContinuousOn m₃ (Icc 0 1)) (s0 : StrictMonoOn m₀ (Icc 0 1)) (s1 : StrictMonoOn m₁
      (Icc 0 1))
    (s2 : StrictMonoOn m₂ (Icc 0 1)) (s3 : StrictMonoOn m₃ (Icc 0 1)) (e1 : m₀ 1 = m₁ 0) (e2 : m₁ 1
      = m₂ 0) (e3 : m₂ 1 = m₃ 0)
    (e4 : m₃ 1 = m₀ 0 + 1) :
    ∃ g', Presents (sW (A ++ (p, true) :: (q₁, true) :: (q₂, true) :: (q₃, true) :: B)) g' ∧
      SideVal (sW (A ++ (p, true) :: (q₁, true) :: (q₂, true) :: (q₃, true) :: B)) g' p (fun u =>
        (φ (ee (m₀ u))).1) ∧
      SideVal (sW (A ++ (p, true) :: (q₁, true) :: (q₂, true) :: (q₃, true) :: B)) g' q₁ (fun u =>
        (φ (ee (m₁ u))).1) ∧
      SideVal (sW (A ++ (p, true) :: (q₁, true) :: (q₂, true) :: (q₃, true) :: B)) g' q₂ (fun u =>
        (φ (ee (m₂ u))).1) ∧
      SideVal (sW (A ++ (p, true) :: (q₁, true) :: (q₂, true) :: (q₃, true) :: B)) g' q₃ (fun u =>
        (φ (ee (m₃ u))).1) := by
  have hl : conc2 m₀ m₁ 1 = conc2 m₂ m₃ 0 := by rw [conc2_zero, conc2_one e1, e2]
  obtain ⟨g₁, h3, h4, -⟩ := exists_pieces1 hS hC hU hCU φ hg hρ
    (continuousOn_conc2 (continuousOn_conc2 c0 c1 e1) (continuousOn_conc2 c2 c3 e3) hl)
    (strictMonoOn_conc2 (strictMonoOn_conc2 s0 s1 e1) (strictMonoOn_conc2 s2 s3 e3) hl)
    (by rw [conc2_zero, conc2_zero, conc2_one hl, conc2_one e3, e4])
  obtain ⟨g₂, h6, h7, h8, -⟩ := exists_split (q := q₂) h13 hp hq₂ h3 h4
  have n1 : NoLab (((q₂, true) :: B) ++ A) p := noLab_append.mpr ⟨noLab_cons.mpr ⟨h13.symm,
    (noLab_append.mp hp).1⟩, (noLab_append.mp hp).2⟩
  have n2 : NoLab (((q₂, true) :: B) ++ A) q₁ := noLab_append.mpr ⟨noLab_cons.mpr ⟨h23.symm,
    (noLab_append.mp hq₁).1⟩, (noLab_append.mp hq₁).2⟩
  obtain ⟨g₃, h9, h10, h11, h12'⟩ := exists_split (A := A) (B := (q₂, true) :: B) (q
    := q₁) h12 n1 n2 h6 h7
  have h8' := h12' q₂ (Ne.symm h13) (Ne.symm h23) _ h8
  have e5 : A ++ (p, true) :: (q₁, true) :: (q₂, true) :: B = (A ++ [(p, true), (q₁, true)]) ++
    (q₂, true) :: B := by simp
  rw [e5] at h9 h8'
  have n3 : NoLab (B ++ (A ++ [(p, true), (q₁, true)])) q₂ := noLab_append.mpr ⟨(noLab_append.mp
    hq₂).1,
    noLab_append.mpr ⟨(noLab_append.mp hq₂).2, noLab_cons.mpr ⟨h13, noLab_cons.mpr ⟨h23,
      noLab_nil⟩⟩⟩⟩
  have n4 : NoLab (B ++ (A ++ [(p, true), (q₁, true)])) q₃ := noLab_append.mpr ⟨(noLab_append.mp
    hq₃).1,
    noLab_append.mpr ⟨(noLab_append.mp hq₃).2, noLab_cons.mpr ⟨h14, noLab_cons.mpr ⟨h24,
      noLab_nil⟩⟩⟩⟩
  rw [e5] at h10 h11
  obtain ⟨g₄, h13', h14', h15, h16⟩ := exists_split h34 n3 n4 h9 h8'
  have e6 : (A ++ [(p, true), (q₁, true)]) ++ (q₂, true) :: (q₃, true) :: B = A ++ (p, true) ::
    (q₁, true) :: (q₂, true) :: (q₃, true) :: B := by simp
  rw [e6] at h13' h14' h15 h16
  refine ⟨g₄, h13', (h16 p h13 h14 _ h10).congr fun u hu => ?_, (h16 q₁ h23 h24 _ h11).congr fun u
    hu => ?_,
    h14'.congr fun u hu => ?_, h15.congr fun u hu => ?_⟩
  · have h0 : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [conc2_left h0, conc2_left hu]
  · have h0 : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [conc2_left h0, conc2_right e1 hu]
  · have h0 : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [conc2_right hl h0, conc2_left hu]
  · have h0 : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [conc2_right hl h0, conc2_right e3 hu]

end pieces

/-- Identifying a free side with another free side of a family, by a map that glues them. -/
theorem presents_glue {Y S : Type*} [TopologicalSpace Y] [TopologicalSpace S] {W W₁ : ℕ
  → List Letter} {g : ℕ × ℂ → Y} {ψ : Y → S}
    (hg : Presents W g) (hψ : Continuous ψ) (hsurj : Surjective ψ) {i₀ q₀ i₁ p₁ p q : ℕ} {σ ε₀ ε₁ :
      Bool}
    (hW : ∀ i n, (i, n) ≠ (i₀, q₀) → (W₁ i)[n]? = (W i)[n]?) (hq0 : (W i₀)[q₀]? = some (q, ε₀))
    (hq1 : (W₁ i₀)[q₀]? = some (p, σ)) (hp1 : (W i₁)[p₁]? = some (p, ε₁)) (hne : (i₁, p₁) ≠
      (i₀, q₀))
    (hlen : ∀ i, (W₁ i).length = (W i).length)
    (hfq : ∀ j m e, (W j)[m]? = some (q, e) → (j, m) = (i₀, q₀)) (hfp : ∀ j m e, (W j)[m]? = some
      (p, e) → (j, m) = (i₁, p₁))
    (hmatch : ∀ t ∈ Icc (0 : ℝ) 1, ψ (g (i₁, sdPt (W i₁).length p₁ ε₁ t)) = ψ (g (i₀, sdPt
      (W i₀).length q₀ σ t)))
    (hfib : ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, ψ (g a) = ψ (g b) → g a ≠ g b → ∃ t ∈ Icc (0 : ℝ) 1,
      (g a = g (i₁, sdPt (W i₁).length p₁ ε₁ t) ∧ g b = g (i₀, sdPt (W i₀).length q₀ σ t)) ∨
      (g b = g (i₁, sdPt (W i₁).length p₁ ε₁ t) ∧ g a = g (i₀, sdPt (W i₀).length q₀ σ t))) :
    Presents W₁ (ψ ∘ g) := by
  classical
  have hDs : Dsk W₁ = Dsk W := by
    ext a
    simp only [Dsk, mem_ofPred_eq, ne_eq, ← List.length_eq_zero_iff, hlen]
  have hSt : ∀ a b, Stp W a b → Stp W₁ a b := by
    rintro _ _ ⟨i, j, n, m, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    have hk : k ≠ q := by
      rintro rfl
      exact h3 ((hfq i n ε h1).trans (hfq j m ε' h2).symm)
    have h4 : (i, n) ≠ (i₀, q₀) := fun he => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [hq0] at h1
      exact hk (Prod.mk.inj (Option.some.inj h1)).1.symm
    have h5 : (j, m) ≠ (i₀, q₀) := fun he => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [hq0] at h2
      exact hk (Prod.mk.inj (Option.some.inj h2)).1.symm
    exact ⟨i, j, n, m, k, ε, ε', t, by rw [hW i n h4]; exact h1, by rw [hW j m h5]; exact h2, h3,
      ht, by rw [hlen], by rw [hlen]⟩
  have hmem : ∀ {i n k ε} (t : ℝ), (W i)[n]? = some (k, ε) → (i, sdPt (W i).length n ε t) ∈ Dsk W
    := fun t h =>
    ⟨fun he => by simp [he] at h, (norm_per _ _).le⟩
  have hSt' : ∀ a b, Stp W₁ a b → ψ (g a) = ψ (g b) := by
    rintro _ _ ⟨i, j, n, m, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    rw [hlen, hlen]
    by_cases h4 : (i, n) = (i₀, q₀)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
      rw [hq1] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
      have h5 : (j, m) ≠ (i, n) := fun he => h3 he.symm
      rw [hW j m h5] at h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hfp j m ε' h2)
      rw [hp1] at h2
      obtain rfl : ε₁ = ε' := (Prod.mk.inj (Option.some.inj h2)).2
      exact (hmatch t ht).symm
    by_cases h5 : (j, m) = (i₀, q₀)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      rw [hq1] at h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
      rw [hW i n h4] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hfp i n ε h1)
      rw [hp1] at h1
      obtain rfl : ε₁ = ε := (Prod.mk.inj (Option.some.inj h1)).2
      exact hmatch t ht
    · rw [hW i n h4] at h1
      rw [hW j m h5] at h2
      have h6 := (hg.2.2 _ (hmem t h1) _ (hmem t h2)).mpr (.rel _ _ ⟨i, j, n, m, k, ε, ε', t, h1,
        h2, h3, ht, rfl, rfl⟩)
      rw [h6]
  have hPR : ∀ a b, PRel W a b → PRel W₁ a b := by
    intro a b h
    induction h with
    | rel x y hs => exact .rel _ _ (hSt _ _ hs)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
  have hPR' : ∀ a b, PRel W₁ a b → ψ (g a) = ψ (g b) := by
    intro a b h
    induction h with
    | rel x y hs => exact hSt' _ _ hs
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  have hstep : ∀ t ∈ Icc (0 : ℝ) 1, Stp W₁ (i₁, sdPt (W i₁).length p₁ ε₁ t) (i₀, sdPt
    (W i₀).length q₀ σ t) := by
    intro t ht
    refine ⟨i₁, i₀, p₁, q₀, p, ε₁, σ, t, by rw [hW _ _ hne]; exact hp1, hq1, hne, ht, by rw [hlen],
      by rw [hlen]⟩
  have hD0 := hmem (i := i₀) 0 hq0
  refine ⟨hψ.comp_continuousOn (hDs ▸ hg.1), ?_, fun a ha b hb => ?_⟩
  · rw [hDs, image_comp, hg.2.1, image_univ, hsurj.range_eq]
  · rw [hDs] at ha hb
    refine ⟨fun he => ?_, hPR' a b⟩
    by_cases h1 : g a = g b
    · exact hPR _ _ ((hg.2.2 _ ha _ hb).mp h1)
    obtain ⟨t, ht, h2⟩ := hfib a ha b hb he h1
    have hA := hmem (i := i₁) t hp1
    have hB : (i₀, sdPt (W i₀).length q₀ σ t) ∈ Dsk W := ⟨hD0.1, (norm_per _ _).le⟩
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · have c1 := hPR _ _ ((hg.2.2 _ ha _ hA).mp h3)
      have c2 := hPR _ _ ((hg.2.2 _ hb _ hB).mp h4)
      exact .trans _ _ _ c1 (.trans _ _ _ (.rel _ _ (hstep t ht)) (.symm _ _ c2))
    · have c1 := hPR _ _ ((hg.2.2 _ hb _ hA).mp h3)
      have c2 := hPR _ _ ((hg.2.2 _ ha _ hB).mp h4)
      exact .trans _ _ _ c2 (.trans _ _ _ (.symm _ _ (.rel _ _ (hstep t ht))) (.symm _ _ c1))

end GraphMinor.Surface
