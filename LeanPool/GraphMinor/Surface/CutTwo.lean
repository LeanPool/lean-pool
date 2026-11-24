/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutConn

/-!
# Two components after cutting

If the cut surface has two components, each has its own word. The two words with disjoint labels
form a family of two words
that presents the cut surface (`presents_dW`). Pasting two sides, one in each word, gives a family
for the surface before
cutting (`glue_two`), and this family is equivalent to one word (`two_to_one`). We then find the
normal form of this
word (`state_merge`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-! ### A family of two words -/

theorem PRel.map' {W W' : ℕ → List Letter} {κ : ℕ × ℂ → ℕ × ℂ} (h : ∀ x y, Stp W x y → Stp W' (κ x)
  (κ y)) {a b : ℕ × ℂ}
    (hp : PRel W a b) : PRel W' (κ a) (κ b) := by
  induction hp with
  | rel x y hs => exact .rel _ _ (h _ _ hs)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

theorem dW_zero (u v : List Letter) : dW u v 0 = u := by simp [dW, sW]

theorem dW_one (u v : List Letter) : dW u v 1 = v := by simp [dW]

theorem dW_of_ne (u v : List Letter) {i : ℕ} (h0 : i ≠ 0) (h1 : i ≠ 1) : dW u v i = [] := by
  simp [dW, h1, sW, h0, nW]

theorem dW_eq (u v : List Letter) (i : ℕ) : dW u v i = if i = 0 then u else if i = 1 then v else []
  := by
  by_cases h0 : i = 0
  · subst h0
    simp [dW_zero]
  by_cases h1 : i = 1
  · subst h1
    simp [dW_one]
  · rw [ite_eq_right h0, ite_eq_right h1, dW_of_ne u v h0 h1]

theorem dW_cases (u v : List Letter) (i : ℕ) : (i = 0 ∧ dW u v i = u) ∨ (i = 1 ∧ dW u v i = v)
  ∨ dW u v i = [] := by
  by_cases h0 : i = 0
  · subst h0
    exact .inl ⟨rfl, dW_zero u v⟩
  by_cases h1 : i = 1
  · subst h1
    exact .inr (.inl ⟨rfl, dW_one u v⟩)
  · exact .inr (.inr (dW_of_ne u v h0 h1))

theorem sW_cases (u : List Letter) (i : ℕ) : (i = 0 ∧ sW u i = u) ∨ sW u i = [] := by
  by_cases h0 : i = 0
  · subst h0
    exact .inl ⟨rfl, sW_zero u⟩
  · right
    simp [sW, h0, nW]

/-- A step of the family is a step inside one word. -/
theorem stp_dW {u v : List Letter} (hl : DisjL u v) {a b : ℕ × ℂ} (h : Stp (dW u v) a b) :
    (a.1 = 0 ∧ b.1 = 0 ∧ Stp (sW u) a b) ∨ (a.1 = 1 ∧ b.1 = 1 ∧ Stp (sW v) (0, a.2) (0, b.2)) := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  have hm1 := List.mem_of_getElem? h1
  have hm2 := List.mem_of_getElem? h2
  rcases dW_cases u v i with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | e1
  · rcases dW_cases u v j with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | e2
    · left
      rw [e1] at h1
      rw [e1] at h2
      simp only [e1]
      refine ⟨trivial, trivial, 0, 0, p, q, k, ε, ε', t, ?_, ?_, h3, ht, ?_, ?_⟩
      · simpa only [sW_zero] using h1
      · simpa only [sW_zero] using h2
      · rw [sW_zero]
      · rw [sW_zero]
    · rw [e1] at hm1
      rw [e2] at hm2
      exact (hl _ hm1 _ hm2 rfl).elim
    · rw [e2] at hm2
      simp at hm2
  · rcases dW_cases u v j with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | e2
    · rw [e1] at hm1
      rw [e2] at hm2
      exact (hl _ hm2 _ hm1 rfl).elim
    · right
      rw [e1] at h1
      rw [e1] at h2
      simp only [e1]
      refine ⟨trivial, trivial, 0, 0, p, q, k, ε, ε', t, ?_, ?_, ?_, ht, ?_, ?_⟩
      · simpa only [sW_zero] using h1
      · simpa only [sW_zero] using h2
      · intro he
        exact h3 (by simpa using he)
      · rw [sW_zero]
      · rw [sW_zero]
    · rw [e2] at hm2
      simp at hm2
  · rw [e1] at hm1
    simp at hm1

theorem stp_left {u v : List Letter} {a b : ℕ × ℂ} (h : Stp (sW u) a b) : Stp (dW u v) a b := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  have hi := (sW_get h1).1
  have hj := (sW_get h2).1
  subst hi hj
  rw [sW_zero] at h1 h2
  refine ⟨0, 0, p, q, k, ε, ε', t, by rw [dW_zero]; exact h1, by rw [dW_zero]; exact h2, h3, ht, by
    rw [dW_zero, sW_zero], by rw [dW_zero, sW_zero]⟩

theorem stp_right {u v : List Letter} {a b : ℕ × ℂ} (h : Stp (sW v) a b) :
    Stp (dW u v) (1, a.2) (1, b.2) := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  have hi := (sW_get h1).1
  have hj := (sW_get h2).1
  subst hi hj
  rw [sW_zero] at h1 h2
  refine ⟨1, 1, p, q, k, ε, ε', t, by rw [dW_one]; exact h1, by rw [dW_one]; exact h2, ?_, ht, by
    rw [dW_one, sW_zero], by rw [dW_one, sW_zero]⟩
  intro he
  exact h3 (by simpa using he)

/-- The map of a family of two words, from the maps of the two words. -/
noncomputable def glW {T : Type*} {W₁ W₂ : Set T} (g₁ : ℕ × ℂ → W₁) (g₂ : ℕ × ℂ → W₂) : ℕ × ℂ → T :=
  fun a => if a.1 = 0 then (g₁ (0, a.2)).1 else (g₂ (0, a.2)).1

theorem mem_Dsk_sW {u : List Letter} {a : ℕ × ℂ} (h : a ∈ Dsk (sW u)) : a.1 = 0 ∧ u ≠ [] ∧ ‖a.2‖
  ≤ 1 := by
  rcases sW_cases u a.1 with ⟨h1, h2⟩ | h2
  · exact ⟨h1, h2 ▸ h.1, h.2⟩
  · exact absurd h2 h.1

/-- Two components with their words. -/
theorem presents_dW {T : Type*} [TopologicalSpace T] {u v : List Letter} (hu : u ≠ [])
  (hv : v ≠ []) (hl : DisjL u v) {W₁ W₂ : Set T}
    (hd : Disjoint W₁ W₂) (hU : W₁ ∪ W₂ = univ) {g₁ : ℕ × ℂ → W₁} {g₂ : ℕ × ℂ → W₂} (h₁ : Presents
      (sW u) g₁)
    (h₂ : Presents (sW v) g₂) : Presents (dW u v) (glW g₁ g₂) := by
  have hmem : ∀ {z : ℂ}, ‖z‖ ≤ 1 → ((0, z) : ℕ × ℂ) ∈ Dsk (dW u v) ∧ ((1, z) : ℕ × ℂ) ∈ Dsk
    (dW u v) ∧
      ((0, z) : ℕ × ℂ) ∈ Dsk (sW u) ∧ ((0, z) : ℕ × ℂ) ∈ Dsk (sW v) := fun {z} hz =>
    ⟨⟨by simpa only [dW_zero] using hu, hz⟩,
      ⟨by simpa only [dW_one] using hv, hz⟩,
      ⟨by simpa only [sW_zero] using hu, hz⟩,
      ⟨by simpa only [sW_zero] using hv, hz⟩⟩
  have hsplit : Dsk (dW u v) = ({0} : Set ℕ) ×ˢ Metric.closedBall (0 : ℂ) 1 ∪
    ({1} : Set ℕ) ×ˢ Metric.closedBall (0 : ℂ) 1 := by
    ext ⟨i, z⟩
    simp only [Dsk, mem_ofPred_eq, mem_union, mem_prod, mem_singleton_iff, mem_closedBall_zero_iff]
    rcases dW_cases u v i with ⟨rfl, e⟩ | ⟨rfl, e⟩ | e
    · simp [e, hu]
    · simp [e, hv]
    · have h0 : i ≠ 0 := by
        rintro rfl
        rw [dW_zero] at e
        exact hu e
      have h1 : i ≠ 1 := by
        rintro rfl
        rw [dW_one] at e
        exact hv e
      simp [e, h0, h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ ((isClosed_discrete _).prod
      Metric.isClosed_closedBall)
      ((isClosed_discrete _).prod Metric.isClosed_closedBall)
    · have h3 : ContinuousOn (fun a : ℕ × ℂ => (g₁ (0, a.2)).1) (({0} : Set ℕ) ×ˢ Metric.closedBall
      (0 : ℂ) 1) := by
        refine continuous_subtype_val.comp_continuousOn (h₁.1.comp (by fun_prop) ?_)
        rintro ⟨i, z⟩ ⟨-, hz⟩
        exact (hmem (by simpa using hz)).2.2.1
      refine h3.congr ?_
      rintro ⟨i, z⟩ ⟨hi, -⟩
      have : i = 0 := hi
      subst this
      simp [glW]
    · have h3 : ContinuousOn (fun a : ℕ × ℂ => (g₂ (0, a.2)).1) (({1} : Set ℕ) ×ˢ Metric.closedBall
      (0 : ℂ) 1) := by
        refine continuous_subtype_val.comp_continuousOn (h₂.1.comp (by fun_prop) ?_)
        rintro ⟨i, z⟩ ⟨-, hz⟩
        exact (hmem (by simpa using hz)).2.2.2
      refine h3.congr ?_
      rintro ⟨i, z⟩ ⟨hi, -⟩
      have : i = 1 := hi
      subst this
      simp [glW]
  · refine eq_univ_of_forall fun y => ?_
    rcases (hU ▸ mem_univ y : y ∈ W₁ ∪ W₂) with hy | hy
    · obtain ⟨a, ha, he⟩ : (⟨y, hy⟩ : W₁) ∈ g₁ '' Dsk (sW u) := h₁.2.1 ▸ mem_univ _
      obtain ⟨h0, -, hz⟩ := mem_Dsk_sW ha
      refine ⟨(0, a.2), (hmem hz).1, ?_⟩
      have e : ((0, a.2) : ℕ × ℂ) = a := Prod.ext h0.symm rfl
      simp [glW, e, he]
    · obtain ⟨a, ha, he⟩ : (⟨y, hy⟩ : W₂) ∈ g₂ '' Dsk (sW v) := h₂.2.1 ▸ mem_univ _
      obtain ⟨h0, -, hz⟩ := mem_Dsk_sW ha
      refine ⟨(1, a.2), (hmem hz).2.1, ?_⟩
      have e : ((0, a.2) : ℕ × ℂ) = a := Prod.ext h0.symm rfl
      simp [glW, e, he]
  · have hcase : ∀ a ∈ Dsk (dW u v), a = (0, a.2) ∧ ‖a.2‖ ≤ 1 ∨ a = (1, a.2) ∧ ‖a.2‖ ≤ 1 := by
      intro a ha
      rw [hsplit] at ha
      rcases ha with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact .inl ⟨Prod.ext h3 rfl, by simpa using h4⟩
      · exact .inr ⟨Prod.ext h3 rfl, by simpa using h4⟩
    have hval0 : ∀ z, glW g₁ g₂ (0, z) = (g₁ (0, z)).1 := fun z => by simp [glW]
    have hval1 : ∀ z, glW g₁ g₂ (1, z) = (g₂ (0, z)).1 := fun z => by simp [glW]
    have hrev : ∀ a b, PRel (dW u v) a b → glW g₁ g₂ a = glW g₁ g₂ b := by
      intro a b hp
      induction hp with
      | rel x y hs =>
        obtain ⟨hx, hy⟩ := hs.mem_Dsk
        rcases stp_dW hl hs with ⟨h3, h4, h5⟩ | ⟨h3, h4, h5⟩
        · obtain ⟨hx', hy'⟩ := h5.mem_Dsk
          have e1 : x = (0, x.2) := Prod.ext h3 rfl
          have e2 : y = (0, y.2) := Prod.ext h4 rfl
          rw [e1, e2, hval0, hval0, ← e1, ← e2]
          exact congrArg Subtype.val ((h₁.2.2 x hx' y hy').mpr (.rel _ _ h5))
        · obtain ⟨hx', hy'⟩ := h5.mem_Dsk
          have e1 : x = (1, x.2) := Prod.ext h3 rfl
          have e2 : y = (1, y.2) := Prod.ext h4 rfl
          rw [e1, e2, hval1, hval1]
          exact congrArg Subtype.val ((h₂.2.2 _ hx' _ hy').mpr (.rel _ _ h5))
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
    intro a ha b hb
    refine ⟨fun he => ?_, hrev a b⟩
    rcases hcase a ha with ⟨e1, h3⟩ | ⟨e1, h3⟩ <;> rcases hcase b hb with ⟨e2, h4⟩ | ⟨e2, h4⟩
    · rw [e1, e2, hval0, hval0] at he
      have h5 := (h₁.2.2 _ (hmem h3).2.2.1 _ (hmem h4).2.2.1).mp (Subtype.ext he)
      have h6 : PRel (dW u v) (0, a.2) (0, b.2) := PRel.map' (κ := id) (fun _ _ hs
        => stp_left hs) h5
      rwa [← e1, ← e2] at h6
    · rw [e1, e2, hval0, hval1] at he
      exact absurd he (fun h5 => Set.disjoint_left.mp hd (g₁ _).2 (h5 ▸ (g₂ _).2))
    · rw [e1, e2, hval1, hval0] at he
      exact absurd he.symm (fun h5 => Set.disjoint_left.mp hd (g₁ _).2 (h5 ▸ (g₂ _).2))
    · rw [e1, e2, hval1, hval1] at he
      have h5 := (h₂.2.2 _ (hmem h3).2.2.2 _ (hmem h4).2.2.2).mp (Subtype.ext he)
      have h6 : PRel (dW u v) (1, a.2) (1, b.2) := PRel.map' (κ := fun x => (1, x.2)) (a :=
        (0, a.2)) (b := (0, b.2)) (fun _ _ hs => stp_right hs) h5
      rwa [← e1, ← e2] at h6

theorem SideVal.gl_left {T : Type*} {W₁ W₂ : Set T} {g₁ : ℕ × ℂ → W₁} {g₂ : ℕ × ℂ
  → W₂} {u v : List Letter} {k : ℕ} {ρ : ℝ → W₁}
    (h : SideVal (sW u) g₁ k ρ) : SideVal (dW u v) (glW g₁ g₂) k fun t => (ρ t).1 := by
  obtain ⟨i, p, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  rw [sW_zero] at h2
  refine ⟨0, p, by rw [dW_zero]; exact h3, fun t ht => ?_⟩
  rw [dW_zero]
  simp [glW, h2 t ht]

theorem SideVal.gl_right {T : Type*} {W₁ W₂ : Set T} {g₁ : ℕ × ℂ → W₁} {g₂ : ℕ × ℂ
  → W₂} {u v : List Letter} {k : ℕ} {ρ : ℝ → W₂}
    (h : SideVal (sW v) g₂ k ρ) : SideVal (dW u v) (glW g₁ g₂) k fun t => (ρ t).1 := by
  obtain ⟨i, p, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  rw [sW_zero] at h2
  refine ⟨1, p, by rw [dW_one]; exact h3, fun t ht => ?_⟩
  rw [dW_one]
  simp [glW, h2 t ht]

/-- A family with a side in each word: the two sides pasted. -/
theorem glue_two {S' S : Type*} [TopologicalSpace S'] [TopologicalSpace S] {ψ : S'
  → S} {F : Set S} {a : ℝ → S}
    {ξ η : ℝ → S'} (L : ArcLift ψ F a ξ η) (hψ : Continuous ψ) (hsurj : Surjective ψ) {u A B : List
      Letter} {p q p₁ : ℕ} {σ : Bool}
    (hp1 : u[p₁]? = some (p, true)) (hc1 : cnt u p = 1) (hc2 : cnt (A ++ (q, true) :: B) q = 1)
    (hdis : DisjL u (A ++ (q, true) :: B)) {g : ℕ × ℂ → S'}
    (hg : Presents (dW u (A ++ (q, true) :: B)) g) {i₁ : ℕ} (hi : i₁ = 0) (hsξ : ∀ t ∈ Icc
      (0 : ℝ) 1, g (i₁, sdPt u.length p₁ true t) = ξ t) {ζ : ℝ → S'}
    (hsη : ∀ t ∈ Icc (0 : ℝ) 1, g (1, sdPt (A ++ (q, true) :: B).length A.length true t) = ζ t)
    (hζ : ∀ t ∈ Icc (0 : ℝ) 1, ζ (ofs σ t) = η t) :
    Presents (dW u (A ++ (p, σ) :: B)) (ψ ∘ g) ∧ SideVal (dW u (A ++ (p, σ) :: B)) (ψ ∘ g) p a := by
  subst hi
  set w := A ++ (q, true) :: B with hw
  set w₁ := A ++ (p, σ) :: B with hw₁
  have hl : w₁.length = w.length := by simp [hw, hw₁]
  have hget : ∀ n, n ≠ A.length → w₁[n]? = w[n]? := by
    intro n hn
    rw [hw, hw₁]
    by_cases h1 : n < A.length
    · rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
    · have h2 : A.length ≤ n := not_lt.mp h1
      rw [List.getElem?_append_right h2, List.getElem?_append_right h2]
      obtain ⟨m, hm⟩ : ∃ m, n - A.length = m + 1 := ⟨n - A.length - 1, by omega⟩
      rw [hm]
      simp
  have hq0 : w[A.length]? = some (q, true) := by simp [hw]
  have hq1 : w₁[A.length]? = some (p, σ) := by simp [hw₁]
  have h5 : ∀ t ∈ Icc (0 : ℝ) 1, g (1, sdPt w.length A.length σ t) = η t := fun t ht => by
    rw [sdPt_ofs, hsη _ (ofs_mem ht), hζ t ht]
  have hm0 : ∀ j m e, (dW u w j)[m]? = some (p, e) → (j, m) = (0, p₁) := by
    intro j m e h
    rcases dW_cases u w j with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | e1
    · rw [e1] at h
      rw [unique_of_cnt hc1 h hp1]
    · rw [e1] at h
      exact (hdis _ (List.mem_of_getElem? hp1) _ (List.mem_of_getElem? h) rfl).elim
    · rw [e1] at h
      simp at h
  have hm1 : ∀ j m e, (dW u w j)[m]? = some (q, e) → (j, m) = (1, A.length) := by
    intro j m e h
    rcases dW_cases u w j with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | e1
    · rw [e1] at h
      exact (hdis _ (List.mem_of_getElem? h) _ (List.mem_of_getElem? hq0) rfl).elim
    · rw [e1] at h
      rw [unique_of_cnt hc2 h hq0]
    · rw [e1] at h
      simp at h
  have hv := dW_eq u w₁
  have hv' := dW_eq u w
  refine ⟨presents_glue (W := dW u w) (W₁ := dW u w₁) (i₀ := 1) (q₀ := A.length) (i₁ := 0) (p₁
    := p₁) (p := p) (q := q)
    (σ := σ) (ε₀ := true) (ε₁ := true) hg hψ hsurj ?_ (by rw [dW_one]; exact hq0)
      (by rw [dW_one]; exact hq1)
    (by rw [dW_zero]; exact hp1) (by simp) ?_ hm1 hm0 ?_ ?_, ?_⟩
  · intro i n hn
    rw [hv, hv']
    by_cases h0 : i = 0
    · simp [h0]
    by_cases h1 : i = 1
    · subst h1
      simp only [one_ne_zero, ite_false, ite_true]
      exact hget n fun e => hn (by rw [e])
    · simp [h0, h1]
  · intro i
    rw [hv, hv']
    by_cases h0 : i = 0
    · simp [h0]
    by_cases h1 : i = 1
    · simp [h1, hl]
    · simp [h0, h1]
  · intro t ht
    rw [dW_zero, dW_one, hsξ t ht, h5 t ht, L.hξ t ht, L.hη t ht]
  · intro x _ y _ h6 h7
    obtain ⟨t, ht, h8⟩ := L.fib _ _ h6 h7
    refine ⟨t, ht, ?_⟩
    rw [dW_zero, dW_one, hsξ t ht, h5 t ht]
    exact h8
  · refine ⟨0, p₁, by rw [dW_zero]; exact hp1, fun u' hu' => ?_⟩
    simp only [Function.comp_apply, dW_zero]
    rw [hsξ u' hu', L.hξ u' hu']

/-! ### From two words to one -/

theorem two_to_one {T : Type uu} [TopologicalSpace T] [T2Space T] {A₁ B₁ A₂ B₂ : List Letter} {r :
  ℕ} {σ : Bool}
    (hN : NoLab (B₂ ++ A₂ ++ (B₁ ++ A₁)) r) {f : ℕ × ℂ → T}
    (hf : Presents (dW (A₁ ++ (r, true) :: B₁) (A₂ ++ (r, σ) :: B₂)) f) (hne1 : B₁ ++ A₁ ≠ [])
      (hne2 : B₂ ++ A₂ ≠ []) :
    (σ = false → ∃ f' : ℕ × ℂ → T, Presents (sW ((B₂ ++ A₂) ++ (B₁ ++ A₁))) f') ∧
    (σ = true → ∃ f' : ℕ × ℂ → T, Presents (sW ((winv A₂ ++ winv B₂) ++ (B₁ ++ A₁))) f') := by
  have c1 : PEq.{uu} (dW (A₁ ++ (r, true) :: B₁) (A₂ ++ (r, σ) :: B₂)) (dW ((r, true) ::
    (B₁ ++ A₁)) (A₂ ++ (r, σ) :: B₂)) := by
    have := dW_rot_left.{uu} A₁ ((r, true) :: B₁) (A₂ ++ (r, σ) :: B₂)
    simpa using this
  constructor
  · rintro rfl
    have c2 : PEq.{uu} (dW ((r, true) :: (B₁ ++ A₁)) (A₂ ++ (r, false) :: B₂)) (dW ((r, true) ::
      (B₁ ++ A₁)) ((r, false) :: (B₂ ++ A₂))) := by
      have := dW_rot_right.{uu} A₂ ((r, false) :: B₂) ((r, true) :: (B₁ ++ A₁))
      simpa using this
    have c3 := peq_cut_sW.{uu} (y := r) true hne1 hne2 (u := B₁ ++ A₁) (v := B₂ ++ A₂) hN
    exact ((c1.trans (c2.trans c3.symm)) T).mp ⟨f, hf⟩
  · rintro rfl
    have c2 := dW_rev_right.{uu} (A₂ ++ (r, true) :: B₂) ((r, true) :: (B₁ ++ A₁))
    have e1 : winv (A₂ ++ (r, true) :: B₂) = winv B₂ ++ ((r, false) :: winv A₂) := by
      simp [winv, linv]
    rw [e1] at c2
    have c3 : PEq.{uu} (dW ((r, true) :: (B₁ ++ A₁)) (winv B₂ ++ (r, false) :: winv A₂))
        (dW ((r, true) :: (B₁ ++ A₁)) ((r, false) :: (winv A₂ ++ winv B₂))) := by
      have := dW_rot_right.{uu} (winv B₂) ((r, false) :: winv A₂) ((r, true) :: (B₁ ++ A₁))
      simpa using this
    have hN' : NoLab ((winv A₂ ++ winv B₂) ++ (B₁ ++ A₁)) r := by
      have h1 := noLab_append.mp hN
      have h2 := noLab_append.mp h1.1
      exact noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_winv' h2.2, noLab_winv' h2.1⟩, h1.2⟩
    have hne : winv A₂ ++ winv B₂ ≠ [] := by
      intro he
      apply hne2
      obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp he
      have h3 : A₂ = [] := by simpa [winv] using h1
      have h4 : B₂ = [] := by simpa [winv] using h2
      simp [h3, h4]
    have c4 := peq_cut_sW.{uu} (y := r) true hne1 hne (u := B₁ ++ A₁) (v := winv A₂ ++ winv B₂) hN'
    exact ((c1.trans (c2.trans (c3.trans c4.symm))) T).mp ⟨f, hf⟩

/-- A list of blocks moves through a word. -/
theorem move_blocks {U P Q Z : List Letter} (hU : Blocks U) (hP : DisjL U P) (hQ : DisjL U Q)
  (hZ : DisjL U Z) :
    WEq.{uu} (P ++ U ++ Q ++ Z) (P ++ Q ++ U ++ Z) := by
  have c0 : WEq.{uu} (P ++ U ++ Q ++ Z) (Q ++ (Z ++ P) ++ U) :=
    WEq.rot' (P ++ U) (Q ++ Z) (by simp) (by simp)
  have c1 : WEq.{uu} (Q ++ (Z ++ P) ++ U) (Z ++ P ++ Q ++ U) := by
    simpa using slide hU hQ (hZ.append_right hP)
  have c2 : WEq.{uu} (Z ++ P ++ Q ++ U) (P ++ Q ++ U ++ Z) :=
    WEq.rot' Z (P ++ Q ++ U) (by simp) (by simp)
  exact c0.trans (c1.trans c2)

theorem BC.blocks {H : List Letter} {a b c : ℕ} (h : BC H a b c) : Blocks H := by
  induction h with
  | nil => exact .nil
  | hnd u v hu hX _ ih => exact .cons (.hnd u v hu) hX ih
  | cap y hX _ ih => exact .cons (.cap y) hX ih
  | hole t r hu hX _ ih => exact .cons (isBlock_holB hu) hX ih

/-- The state of the procedure for a word with two sets of blocks. -/
theorem state_merge {H₁ H₂ P Q Q' : List Letter} {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ} (h₁ : BC H₁ a₁ b₁ c₁)
  (h₂ : BC H₂ a₂ b₂ c₂) (hd : DisjL H₂ H₁)
    (hP : DisjL (H₂ ++ H₁) (P ++ Q ++ Q')) (hG : Good (P ++ Q ++ Q')) :
    ∃ X Y Z, Inv (P ++ Q ++ Q') X Y Z (a₂ + a₁) (b₂ + b₁) (c₂ + c₁) ∧
      WEq.{uu} (P ++ H₂ ++ Q ++ H₁ ++ Q') ((P ++ Q ++ Q') ++ X ++ Y ++ Z) := by
  have hB := h₂.append h₁ hd
  obtain ⟨w, ⟨X, Y, Z, rfl, n1, n2, n3, n4, n5, n6⟩, hc, hw⟩ := hB.nf
  have s1 : DisjL H₂ (P ++ Q ++ Q') := hP.left
  have d1 : DisjL H₂ P := s1.inl.inl
  have d2 : DisjL H₂ Q := s1.inl.inr
  have d3 : DisjL H₂ Q' := s1.inr
  have d4 : DisjL H₁ (P ++ Q ++ Q') := hP.right
  have c1 : WEq.{uu} (P ++ H₂ ++ Q ++ (H₁ ++ Q')) (P ++ Q ++ H₂ ++ (H₁ ++ Q')) :=
    move_blocks h₂.blocks d1 d2 (hd.append_right d3)
  have c2 : WEq.{uu} ((P ++ Q) ++ (H₂ ++ H₁) ++ Q' ++ []) ((P ++ Q) ++ Q' ++ (H₂ ++ H₁) ++ []) :=
    move_blocks (P := P ++ Q) (Q := Q') (Z := []) hB.blocks hP.inl hP.inr fun l _ m hm
      => by cases hm
  have c3 := hw (P ++ Q ++ Q') hP
  have hdR : DisjL (X ++ Y ++ Z) (P ++ Q ++ Q') := by
    intro l hl
    have h3 : cnt (H₂ ++ H₁) l.1 ≠ 0 := by
      rw [← hc]
      exact (cnt_pos hl).ne'
    have h4 : l.1 = l.1 := rfl
    obtain ⟨m, hm, hm'⟩ : ∃ m ∈ H₂ ++ H₁, m.1 = l.1 := by
      by_contra h5
      push Not at h5
      exact h3 (noLab_iff_cnt.mp fun m hm => h5 m hm)
    rw [← hm']
    exact hP m hm
  refine ⟨X, Y, Z, ⟨n1, n2, n3, n4, n5, n6, hdR.left.left, hdR.left.right, hdR.right, hG⟩, ?_⟩
  have e1 : P ++ H₂ ++ Q ++ H₁ ++ Q' = P ++ H₂ ++ Q ++ (H₁ ++ Q') := by simp
  have e2 : P ++ Q ++ H₂ ++ (H₁ ++ Q') = (P ++ Q) ++ (H₂ ++ H₁) ++ Q' ++ [] := by simp
  have e3 : (P ++ Q) ++ Q' ++ (H₂ ++ H₁) ++ [] = P ++ Q ++ Q' ++ (H₂ ++ H₁) := by simp
  have e4 : P ++ Q ++ Q' ++ (X ++ Y ++ Z) = P ++ Q ++ Q' ++ X ++ Y ++ Z := by simp
  rw [e1, ← e4]
  rw [e2] at c1
  rw [e3] at c2
  exact c1.trans (c2.trans c3)

end GraphMinor.Surface
