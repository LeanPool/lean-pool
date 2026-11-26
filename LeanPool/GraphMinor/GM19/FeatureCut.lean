/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureLift

/-!
# Cutting a surface along a family of lines

`IsLineFamily` is a finite family of lines of a surface that meet only at their ends. Each line lies
in the boundary or meets
the boundary only at its ends, and the lines cover the boundary. Cutting the word of a dissection
gives a surface `Y` with a
map `ψ` to `S`. Each line has two lifts to `Y`, or one if it lies in the boundary. These lifts cover
`bd(Y)`, and two points of
`Y` over one point of `S` are joined by a chain of pairs of lifts of one point (`AbstractCut`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

/-- A finite family of lines that meet only at their ends, and that cover the boundary. -/
structure IsLineFamily {S : Type u} [TopologicalSpace S] {I : Type} (b : I → 𝕀 → S) (inner : I
  → Prop) : Prop where
  arc : ∀ i, IsArcMap (b i)
  meet : ∀ i j (u v : ℝ), u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → extI (b i) u = extI (b j) v → (i
    = j ∧ u = v) ∨ ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1))
  off : ∀ i, inner i → ∀ u ∈ Ioo (0 : ℝ) 1, extI (b i) u ∉ bd S
  onBd : ∀ i, ¬ inner i → ∀ u ∈ Icc (0 : ℝ) 1, extI (b i) u ∈ bd S
  cover : ∀ x ∈ bd S, ∃ i, x ∈ range (b i)

/-- The result of cutting along a family of lines, without the words. -/
structure AbstractCut {S Y : Type u} [TopologicalSpace S] [TopologicalSpace Y] {I : Type} (b : I
  → 𝕀 → S) (inner : I → Prop) (ψ : Y → S) (ξ η : I → ℝ → Y) : Prop where
  cont : Continuous ψ
  surj : Surjective ψ
  cξ : ∀ i, ContinuousOn (ξ i) (Icc 0 1)
  cη : ∀ i, ContinuousOn (η i) (Icc 0 1)
  hξ : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ψ (ξ i u) = extI (b i) u
  hη : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ψ (η i u) = extI (b i) u
  bdξ : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ξ i u ∈ bd Y
  bdη : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, η i u ∈ bd Y
  ne : ∀ i, inner i → ∀ u ∈ Ioo (0 : ℝ) 1, ξ i u ≠ η i u
  eqb : ∀ i, ¬ inner i → ∀ u ∈ Icc (0 : ℝ) 1, η i u = ξ i u
  cover : ∀ y ∈ bd Y, ∃ i, ∃ u ∈ Icc (0 : ℝ) 1, y = ξ i u ∨ y = η i u
  fib : ∀ y y', ψ y = ψ y' → Relation.EqvGen (fun p q ↦ ∃ i, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ i u ∧ q
    = η i u) y y'

variable {S : Type u} [TopologicalSpace S] [T2Space S] {W : ℕ → List Letter} {f : ℕ × ℂ
  → S} {V : Set S} {E : Set (Set S)}
  {A : Set S → 𝕀 → S} {lab : Set S → ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] {D : Set
    (Set S)} {g : ℕ × ℂ → Y} {ψ : Y → S}

/-- A property of a closed set that holds inside an interval holds on all of it. -/
theorem mem_of_Ioo {T : Type*} [TopologicalSpace T] {ξ : ℝ → T} {Z : Set T} (hZ : IsClosed Z)
  (hc : ContinuousOn ξ (Icc 0 1)) (h : ∀ u ∈ Ioo (0 : ℝ) 1, ξ u ∈ Z) :
    ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ Z := by
  have hcl : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo (by norm_num)
  intro u hu
  have h₁ : ξ '' closure (Ioo (0 : ℝ) 1) ⊆ closure (ξ '' Ioo 0 1) := ContinuousOn.image_closure
    (by rwa [hcl])
  have h₂ : ξ u ∈ closure (ξ '' Ioo 0 1) := h₁ ⟨u, hcl ▸ hu, rfl⟩
  exact closure_minimal (by rintro _ ⟨v, hv, rfl⟩; exact h v hv) hZ h₂

omit [T2Space S] in
/-- Two points of the discs with the same image, off the edges of `D`, stay pasted after cutting. -/
theorem prel_off (h : WordEdges W f V E A lab) (hD : D ⊆ E) {a b : ℕ × ℂ} (hab : PRel W a b) :
    f a = f b ∧ (f a ∉ ⋃₀ D → PRel (cutW W (lab '' D)) a b) := by
  induction hab with
  | rel a b hs =>
    have hfe := presents_eq_of_stp h.pres hs
    refine ⟨hfe, fun hF ↦ ?_⟩
    obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
    refine .rel _ _ (stp_to_cut h1 h2 h3 hu fun hk ↦ ?_)
    obtain ⟨e'', he'', rfl⟩ := hk
    exact hF ⟨e'', he'', by
      rw [h.f_side (hD he'') h1 hu]
      exact h.extI_mem (hD he'') _⟩
  | refl _ => exact ⟨rfl, fun _ ↦ .refl _⟩
  | symm a b _ ih => exact ⟨ih.1.symm, fun hF ↦ .symm _ _ (ih.2 (ih.1 ▸ hF))⟩
  | trans a b c _ _ h1 h2 => exact ⟨h1.1.trans h2.1, fun hF ↦ .trans _ _ _ (h1.2 hF) (h2.2
    (h1.1 ▸ hF))⟩

/-- A side that is free stays free after cutting. -/
theorem freeSide_cut_of_free {L : Set ℕ} {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some (k, e))
  (hk : k ∉ L) (hf : FreeSide W i p) : FreeSide (cutW W L) i p := by
  intro j q k' e₁ e₂ h1 h2
  obtain ⟨l, h3, h4⟩ := cut_get_iff.mp h1
  obtain ⟨l', h5, h6⟩ := cut_get_iff.mp h2
  have hl : l = k := by
    rw [h] at h3
    exact (Prod.mk.inj (Option.some.inj h3)).1.symm
  subst hl
  rcases h4 with ⟨h7, -⟩ | ⟨-, rfl⟩
  · exact absurd h7 hk
  · rcases h6 with ⟨-, h8⟩ | ⟨-, h8⟩
    · omega
    · have : l' = l := by omega
      subst this
      exact hf _ _ _ _ _ h h5

/-- The other way: a side free after cutting with an uncut label was free. -/
theorem freeSide_of_cut {L : Set ℕ} {i p k : ℕ} {e : Bool} (h : (W i)[p]? = some (k, e))
  (hk : k ∉ L) (hf : FreeSide (cutW W L) i p) : FreeSide W i p := by
  intro j q k' e₁ e₂ h1 h2
  have h₁ : k' = k := by
    rw [h] at h1
    exact (Prod.mk.inj (Option.some.inj h1)).1.symm
  subst h₁
  exact hf j q (2 * k') e₁ e₂ (cut_get_iff.mpr ⟨_, h1, .inr ⟨hk, rfl⟩⟩) (cut_get_iff.mpr ⟨_, h2,
    .inr ⟨hk, rfl⟩⟩)

/-- A point of an interval between the terms of a chain lies in one of the steps. -/
theorem exists_chainStep {t : ℕ → ℝ} {m : ℕ} (hm : 0 < m) (h0 : t 0 = 0) (hlt : ∀ p < m, t p < t
  (p + 1)) {u : ℝ} (hu : u ∈ Icc 0 (t m)) :
    ∃ p < m, u ∈ Icc (t p) (t (p + 1)) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases h : u ≤ t n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨0, by omega, ⟨h0 ▸ hu.1, by simpa using hu.2⟩⟩
      · obtain ⟨p, hp, h₁⟩ := ih hn (fun p hp ↦ hlt p (by omega)) ⟨hu.1, h⟩
        exact ⟨p, by omega, h₁⟩
    · exact ⟨n, by omega, ⟨(not_le.1 h).le, hu.2⟩⟩

/-- The parameter on an edge of the dissection along a piece of a line. -/
theorem exists_theta (h : WordEdges W f V E A lab) {x : Set S} (hx : x ∈ E) {a : ℝ → S} {b c : ℝ}
  (ha : ContinuousOn a (Icc b c)) (him : a '' Icc b c = x) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc b c) ∧ (∀ u ∈ Icc b c, θ u ∈ Icc (0 : ℝ) 1)
      ∧ ∀ u ∈ Icc b c, extI (A x) (θ u) = a u := by
  have hcA : ContinuousOn (extI (A x)) (Icc 0 1) := (continuous_extI (h.arc x hx).1.1).continuousOn
  have hiA := extI_injOn (h.arc x hx).1.2
  have himA : extI (A x) '' Icc 0 1 = x := by rw [image_extI, (h.arc x hx).2.1]
  obtain ⟨θ', hθc, hθl⟩ := exists_inv_of_compactOn isCompact_Icc hcA hiA
  rw [himA] at hθc
  have hmem : ∀ u ∈ Icc b c, a u ∈ x := fun u hu ↦ him ▸ mem_image_of_mem _ hu
  have hex : ∀ u ∈ Icc b c, ∃ w ∈ Icc (0 : ℝ) 1, extI (A x) w = a u := fun u hu ↦ by
    have := hmem u hu
    rwa [← himA] at this
  choose! θ hθ₁ hθ₂ using hex
  have hθeq : ∀ u ∈ Icc b c, θ u = θ' (a u) := fun u hu ↦ by
    rw [← hθ₂ u hu, hθl (hθ₁ u hu)]
  exact ⟨θ, (hθc.comp ha (fun u hu ↦ hmem u hu)).congr hθeq, hθ₁, hθ₂⟩

omit [T2Space Y] in
/-- A line in the boundary has a lift, because over its inner points there is only one point. -/
theorem exists_borderLift (h : WordEdges W f V E A lab) (_hD : D ⊆ E) (hg : Presents (cutW W
  (lab '' D)) g) (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a) {a : ℝ → S}
    (ha : ContinuousOn a (Icc 0 1)) {m : ℕ} {t : ℕ → ℝ} {ss : ℕ → Set S} (hm : 0 < m) (ht0 : t 0
      = 0) (htm : t m = 1)
    (hlt : ∀ p < m, t p < t (p + 1)) (hch : ∀ p < m, ss p ∈ E ∧ a '' Icc (t p) (t (p + 1)) = ss p)
    (huniq : ∀ y y', ψ y = ψ y' → (∃ u ∈ Ioo (0 : ℝ) 1, ψ y = a u) → y = y') : ∃ ξ : ℝ
      → Y, ContinuousOn ξ (Icc 0 1) ∧ ∀ u ∈ Icc (0 : ℝ) 1, ψ (ξ u) = a u := by
  have hD' : Dsk (cutW W (lab '' D)) = Dsk W := dsk_cut
  have hmono : ∀ {k k'}, k ≤ k' → k' ≤ m → t k ≤ t k' := fun {k k'} h₁ h₂ ↦ chain_mono' hlt h₁ h₂
  have hI : ∀ k ≤ m, t k ∈ Icc (0 : ℝ) 1 := fun k hk ↦ ⟨ht0 ▸ hmono (Nat.zero_le k) hk, htm ▸ hmono
    hk le_rfl⟩
  have hpiece : ∀ p < m, ∃ ξ : ℝ → Y, ContinuousOn ξ (Icc (t p) (t (p + 1))) ∧ ∀ u ∈ Icc (t p) (t
    (p + 1)), ψ (ξ u) = a u := fun p hp ↦ by
    obtain ⟨θ, hθc, hθ₁, hθ₂⟩ := exists_theta h (hch p hp).1 (ha.mono (Icc_subset_Icc
      (hI p hp.le).1 (hI (p + 1) hp).2)) (hch p hp).2
    have hne : (ss p).Nonempty := by
      rw [← (hch p hp).2]
      exact ⟨_, mem_image_of_mem _ (⟨le_rfl, (hlt p hp).le⟩ : t p ∈ Icc (t p) (t (p + 1)))⟩
    obtain ⟨z, hz⟩ := hne
    obtain ⟨c, hc, hfc⟩ : z ∈ f '' Dsk W := h.pres.2.1 ▸ mem_univ z
    obtain ⟨q, e, x, hx, u, hu, h₁, -, -⟩ := h.exists_side hc ⟨ss p, (hch p hp).1, hfc ▸ hz⟩
    obtain ⟨i, r, k, e', h₃, h₄, h₅⟩ : ∃ (i r k : ℕ) (e' : Bool), (W i)[r]? = some (k, e') ∧ k
      = lab (ss p) ∧ True := by
      obtain ⟨d, hd, hd'⟩ : extI (A (ss p)) (1 / 2) ∈ f '' Dsk W := h.pres.2.1 ▸ mem_univ _
      obtain ⟨q', e₃, x', hx', u', hu', h₆, -, h₇⟩ := h.exists_side hd ⟨ss p,
        (hch p hp).1, hd' ▸ h.extI_mem (hch p hp).1 _⟩
      have hxx : x' = ss p := by
        by_contra hne
        have hV : extI (A (ss p)) (1 / 2) ∈ V := h.graph.disj x' hx' (ss p) (hch p hp).1 hne
          ⟨by rw [← hd', h₇]; exact h.extI_mem hx' _, h.extI_mem (hch p hp).1 _⟩
        exact h.extI_notMem (hch p hp).1 (by norm_num) hV
      subst hxx
      exact ⟨_, _, _, _, h₆, rfl, trivial⟩
    subst h₄
    refine ⟨fun u ↦ g (spt W i r (ofs e' (θ u))), ?_, fun u hu ↦ ?_⟩
    · have h₁ : ContinuousOn (fun u ↦ spt W i r (ofs e' (θ u))) (Icc (t p) (t (p + 1))) :=
      (continuous_spt_ofs W i r e').comp_continuousOn hθc
      exact hg.1.comp h₁ fun u _ ↦ hD' ▸ spt_mem (lt_length h₃) _
    · simp only
      rw [hψ _ (spt_mem (lt_length h₃) _), h.f_side (hch p hp).1 h₃ (ofs_mem (hθ₁ u hu)),
        ofs_ofs, hθ₂ u hu]
  have key : ∀ n, 1 ≤ n → n ≤ m → ∃ ξ : ℝ → Y, ContinuousOn ξ (Icc 0 (t n)) ∧ ∀ u ∈ Icc 0 (t n), ψ
    (ξ u) = a u := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨ξ, h₁, h₂⟩ := hpiece 0 hm
      simp only [zero_add] at h₁ h₂
      rw [ht0] at h₁ h₂
      exact ⟨ξ, h₁, h₂⟩
    | succ n hn ih =>
      intro hle
      obtain ⟨ξ, h₁, h₂⟩ := ih (by omega)
      have hnm : n < m := by omega
      obtain ⟨ξ₁, h₃, h₄⟩ := hpiece n hnm
      have hb₀ := (hI _ hnm.le).1
      have hstep := (hlt _ hnm).le
      have hin : t n ∈ Ioo (0 : ℝ) 1 := ⟨by
        have := hmono (show 1 ≤ n from hn) hnm.le
        have h₅ := hlt 0 hm
        simp only [zero_add] at h₅
        linarith, by
        have := hmono (show n + 1 ≤ m from hnm) le_rfl
        have h₅ := hlt n hnm
        linarith⟩
      have h₅ : ξ (t n) = ξ₁ (t n) := by
        have e₁ := h₂ _ (⟨hb₀, le_rfl⟩ : t n ∈ Icc 0 (t n))
        have e₂ := h₄ _ (⟨le_rfl, hstep⟩ : t n ∈ Icc (t n) (t (n + 1)))
        exact huniq _ _ (e₁.trans e₂.symm) ⟨_, hin, e₁⟩
      refine ⟨fun u ↦ if u ≤ t n then ξ u else ξ₁ u, continuousOn_join hb₀ h₁ h₃ h₅ hstep,
        fun u hu ↦ ?_⟩
      by_cases hl : u ≤ t n
      · simp only [hl, ite_true]
        exact h₂ u ⟨hu.1, hl⟩
      · simp only [hl, ite_false]
        exact h₄ u ⟨(not_le.1 hl).le, hu.2⟩
  rw [← htm]
  exact key m hm le_rfl

private theorem cut_edge_has_two_sides
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {I : Type}
    {b : I → 𝕀 → S}
    {inner : I → Prop}
    (hb : IsLineFamily b inner)
    {V : Set S}
    {E : Set (Set S)}
    (W : ℕ → List Letter)
    (f : ℕ × ℂ → S)
    (A : Set S → 𝕀 → S)
    (lab : Set S → ℕ)
    (hw : WordEdges W f V E A lab)
    (m : I → ℕ)
    (t : I → ℕ → ℝ)
    (ss : I → ℕ → Set S)
    (ε : I → ℕ → Bool)
    (hch : ∀ (i : I), ∀ p < m i, ss i p ∈ E ∧ (fun i => extI (b i)) i '' Icc (t i p) (t i (p + 1))
      = ss i p ∧ (fun i => extI (b i)) i (t i p) = extI (A (ss i p)) (if ε i p = true then 0 else
      1) ∧ (fun i => extI (b i)) i (t i (p + 1)) = extI (A (ss i p)) (if ε i p = true then 1 else
      0))
    (hsub : ∀ (i : I) {p : ℕ}, p < m i → Icc (t i p) (t i (p + 1)) ⊆ Icc 0 1)
    (hendV : ∀ (i : I) {u : ℝ}, u = 0 ∨ u = 1 → (fun i => extI (b i)) i u ∈ V)
    (hpt : ∀ (i : I) {p : ℕ}, p < m i → ∀ z ∈ ss i p, ∃ u ∈ Icc (t i p) (t i (p + 1)), (fun i =>
      extI (b i)) i u = z) :
    ∀ e ∈ ({x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}), ∃ i p j q e₁ e₂, EdgeSides W (lab e) i p j
      q e₁ e₂ := by
  let a := fun i => extI (b i)
  let D := {x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}
  rintro _ ⟨c, hc, p, hp, rfl⟩
  have hmid : edgeMid A (ss c p) ∉ bd S := fun hb' ↦ by
    obtain ⟨u, hu, hau⟩ := hpt c hp _ (hw.extI_mem (hch c p hp).1 _)
    have hu' := hsub c hp hu
    by_cases he : u = 0 ∨ u = 1
    · exact hw.extI_notMem (hch c p hp).1 (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) (by
        have := hendV c he
        rwa [hau] at this)
    · push Not at he
      exact hb.off c hc u ⟨lt_of_le_of_ne hu'.1 he.1.symm, lt_of_le_of_ne hu'.2 he.2⟩ (by
        exact (congrArg (· ∈ bd S) hau).mpr hb')
  obtain ⟨i, p', j, q, e₁, e₂, h1, h2, h3⟩ := hw.exists_sides (hch c p hp).1 hmid
  exact ⟨i, p', j, q, e₁, e₂, ⟨h1, h2, h3⟩⟩

private theorem chain_step_at_interior_endpoint
    {S : Type u}
    [TopologicalSpace S]
    {I : Type}
    {b : I → 𝕀 → S}
    {inner : I → Prop}
    (hb : IsLineFamily b inner)
    {E : Set (Set S)}
    (A : Set S → 𝕀 → S)
    (m : I → ℕ)
    (t : I → ℕ → ℝ)
    (ss : I → ℕ → Set S)
    (ε : I → ℕ → Bool)
    (hm : ∀ (i : I), 0 < m i)
    (ht0 : ∀ (i : I), t i 0 = 0)
    (htm : ∀ (i : I), t i (m i) = 1)
    (hlt : ∀ (i : I), ∀ p < m i, t i p < t i (p + 1))
    (hch : ∀ (i : I), ∀ p < m i, ss i p ∈ E ∧ (fun i => extI (b i)) i '' Icc (t i p) (t i (p + 1))
      = ss i p ∧ (fun i => extI (b i)) i (t i p) = extI (A (ss i p)) (if ε i p = true then 0 else
      1) ∧ (fun i => extI (b i)) i (t i (p + 1)) = extI (A (ss i p)) (if ε i p = true then 1 else
      0))
    (hsne : ∀ (i : I), ∀ p < m i, ∀ q < m i, p ≠ q → ss i p ≠ ss i q)
    (hmono : ∀ (i : I) {k k' : ℕ}, k ≤ k' → k' ≤ m i → t i k ≤ t i k')
    (hI : ∀ (i : I), ∀ k ≤ m i, t i k ∈ Icc 0 1) :
    ∀ (i : I), inner i → ∀ (k : ℕ), 0 < k → k < m i → ∀ p < m i, ∀ (τ : Bool), extI (A (ss i p))
      (eo τ) = (fun i => extI (b i)) i (t i k) → EndCase S A ({x | ∃ i, inner i ∧ ∃ p < m i, x =
      ss i p}) (ss i p) τ := by
  let a := fun i => extI (b i)
  let D := {x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}
  intro i hi k hk0 hkm
  have hkI : t i k ∈ Ioo (0 : ℝ) 1 := ⟨by
    have h₁ := hmono i (show 1 ≤ k from hk0) hkm.le
    have h₂ := hlt i 0 (hm i)
    simp only [zero_add] at h₂
    linarith [ht0 i], by
    have h₁ := hmono i (show k + 1 ≤ m i from hkm) le_rfl
    have h₂ := hlt i k hkm
    linarith [htm i]⟩
  have hkey : ∀ j, ∀ p < m j, ∀ τ, extI (A (ss j p)) (eo τ) = a i (t i k) → j = i ∧ ((p + 1 = k
    ∧ τ = ε i p) ∨ (p = k ∧ τ ≠ ε i p)) := by
    intro j p hp τ he
    have h₁ := chain_hex (hch j p hp).2.2.1 (hch j p hp).2.2.2 τ
    rw [he] at h₁
    have hc : chainAt (ε j) p τ ≤ m j := by
      unfold chainAt
      split_ifs <;> omega
    rcases hb.meet i j (t i k) (t j (chainAt (ε j) p τ)) ⟨hkI.1.le, hkI.2.le⟩
      (hI j _ hc) h₁ with ⟨rfl, h₂⟩ | ⟨h₂, -⟩
    · refine ⟨rfl, ?_⟩
      have h₃ : chainAt (ε i) p τ = k := by
        rcases lt_trichotomy (chainAt (ε i) p τ) k with h₄ | h₄ | h₄
        · exact absurd h₂.symm (chain_mono (hlt i) h₄ hkm.le).ne
        · exact h₄
        · exact absurd h₂ (chain_mono (hlt i) h₄ hc).ne
      unfold chainAt at h₃
      split_ifs at h₃ with h₄
      · exact .inl ⟨h₃, h₄⟩
      · exact .inr ⟨h₃, h₄⟩
    · rcases h₂ with h₂ | h₂
      · exact absurd h₂ hkI.1.ne'
      · exact absurd h₂ hkI.2.ne
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : k' < m i := by omega
  have hA₁ : extI (A (ss i k')) (eo (ε i k')) = a i (t i (k' + 1)) := by
    have := chain_hex (hch i k' hk').2.2.1 (hch i k' hk').2.2.2 (ε i k')
    simpa [chainAt] using this
  have hA₂ : extI (A (ss i (k' + 1))) (eo (!ε i (k' + 1))) = a i (t i (k' + 1)) := by
    have := chain_hex (hch i (k' + 1) hkm).2.2.1 (hch i (k' + 1) hkm).2.2.2 (!ε i (k' + 1))
    simpa [chainAt] using this
  have hD₁ : ss i k' ∈ D := ⟨i, hi, k', hk', rfl⟩
  have hD₂ : ss i (k' + 1) ∈ D := ⟨i, hi, k' + 1, hkm, rfl⟩
  have hoff' : a i (t i (k' + 1)) ∉ bd S := hb.off i hi _ hkI
  have hall : ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = a i (t i (k' + 1)) → (e'' = ss i k' ∧ τ''
    = ε i k') ∨ (e'' = ss i (k' + 1) ∧ τ'' = !ε i (k' + 1)) := by
    rintro _ ⟨j, -, q, hq, rfl⟩ τ'' he
    obtain ⟨rfl, h₁⟩ := hkey j q hq τ'' he
    rcases h₁ with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · obtain rfl : k' = q := by omega
      exact .inl ⟨rfl, h₃⟩
    · subst h₂
      exact .inr ⟨rfl, by cases h₄ : ε j (k' + 1) <;> cases τ'' <;> simp_all⟩
  intro p hp τ he
  obtain ⟨-, h₁⟩ := hkey i p hp τ he
  rcases h₁ with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
  · obtain rfl : k' = p := by omega
    subst h₃
    refine .inl ⟨ss i (k' + 1), hD₂, !ε i (k' + 1), hsne i _ hkm _ hk'
      (by omega), hA₂.trans he.symm, by rw [he]; exact hoff', fun e'' he'' τ'' h₄ ↦ ?_⟩
    exact hall e'' he'' τ'' (h₄.trans he)
  · subst h₂
    have hτ : τ = !ε i (k' + 1) := by
      revert h₃
      generalize ε i (k' + 1) = c
      cases c <;> cases τ <;> simp
    subst hτ
    have hoffE : extI (A (ss i (k' + 1))) (eo (!ε i (k' + 1))) ∉ bd S := by
      rw [he]
      exact hoff'
    refine .inl ⟨ss i k', hD₁, ε i k', hsne i _ hk' _ hkm (by omega), hA₁.trans he.symm,
      hoffE, fun e'' he'' τ'' h₄ ↦ ?_⟩
    rcases hall e'' he'' τ'' (h₄.trans he) with h₅ | h₅
    · exact .inr h₅
    · exact .inl h₅

private theorem lift_endpoints_are_cut_sides
    {S : Type u}
    [TopologicalSpace S]
    {I : Type}
    {inner : I → Prop}
    {V : Set S}
    {E : Set (Set S)}
    (W : ℕ → List Letter)
    (f : ℕ × ℂ → S)
    (A : Set S → 𝕀 → S)
    (lab : Set S → ℕ)
    (hw : WordEdges W f V E A lab)
    (a : I → ℝ → S)
    (m : I → ℕ)
    (t : I → ℕ → ℝ)
    (ss : I → ℕ → Set S)
    (ε : I → ℕ → Bool)
    (hch : ∀ (i : I), ∀ p < m i, ss i p ∈ E ∧ a i '' Icc (t i p) (t i (p + 1)) = ss i p ∧ a i (t i
      p) = extI (A (ss i p)) (if ε i p = true then 0 else 1) ∧ a i (t i (p + 1)) = extI (A (ss i
      p)) (if ε i p = true then 1 else 0))
    (hsub : ∀ (i : I) {p : ℕ}, p < m i → Icc (t i p) (t i (p + 1)) ⊆ Icc 0 1)
    (hpt : ∀ (i : I) {p : ℕ}, p < m i → ∀ z ∈ ss i p, ∃ u ∈ Icc (t i p) (t i (p + 1)), a i u = z)
    (Y : Type u)
    [TopologicalSpace Y]
    (g : ℕ × ℂ → Y)
    (ψ : Y → S)
    (ξ : I → ℝ → Y)
    (η : I → ℝ → Y)
    (hL : ∀ (i : I), inner i → ChainLift W A lab g ψ (a i) (t i) (ss i) (m i) (ξ i) (η i)) :
    ∀ (c : I), inner c → ∀ p' < m c, ∀ {i p j q : ℕ} {e e' : Bool}, (W i)[p]? = some (lab (ss c
      p'), e) → (W j)[q]? = some (lab (ss c p'), e') → (i, p) ≠ (j, q) → ∀ w ∈ Icc 0 1, ∃ v ∈ Icc
      0 1, g (spt W i p (ofs e w)) = ξ c v ∧ g (spt W j q (ofs e' w)) = η c v ∨ g (spt W i p (ofs
      e w)) = η c v ∧ g (spt W j q (ofs e' w)) = ξ c v := by
  intro c hc p' hp' i p j q e e' h₁ h₂ hne' w hw'
  obtain ⟨i₀, q₀, j₀, r₀, e₁, e₂, s₀, hform⟩ := (hL c hc).pieces p' hp'
  obtain ⟨v, hv, hav⟩ := hpt c hp' _ (hw.extI_mem (hch c p' hp').1 w)
  obtain ⟨hf₁, hf₂⟩ := hform v hv w hw' hav.symm
  have hsign : ∀ {i' p' i'' p'' : ℕ} {k : ℕ} {e' e'' : Bool}, (W i')[p']? = some (k, e') →
    (W i'')[p'']? = some (k, e'') → (i', p') = (i'', p'') → e' = e'' := by
    intro i' p' i'' p'' k e' e'' h₃ h₄ h₅
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₅
    rw [h₃] at h₄
    exact (Prod.mk.inj (Option.some.inj h₄)).2
  refine ⟨v, hsub c hp' hv, ?_⟩
  rcases hw.paired.third s₀.one s₀.two h₁ s₀.ne with h₃ | h₃ <;> rcases hw.paired.third s₀.one
    s₀.two h₂ s₀.ne with h₄ | h₄
  · exact (hne' (h₃.trans h₄.symm)).elim
  · obtain rfl := hsign h₁ s₀.one h₃
    obtain rfl := hsign h₂ s₀.two h₄
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₄
    exact .inl ⟨hf₁.symm, hf₂.symm⟩
  · obtain rfl := hsign h₁ s₀.two h₃
    obtain rfl := hsign h₂ s₀.one h₄
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₄
    exact .inr ⟨hf₂.symm, hf₁.symm⟩
  · exact (hne' (h₃.trans h₄.symm)).elim

private theorem border_arc_lift_on_boundary
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {I : Type}
    {b : I → 𝕀 → S}
    {inner : I → Prop}
    (hb : IsLineFamily b inner)
    {V : Set S}
    {E : Set (Set S)}
    (W : ℕ → List Letter)
    (f : ℕ × ℂ → S)
    (A : Set S → 𝕀 → S)
    (lab : Set S → ℕ)
    (hw : WordEdges W f V E A lab)
    (D : Set (Set S))
    (hDE : D ⊆ E)
    (hoffD : ∀ (c : I), ¬inner c → ∀ v ∈ Ioo 0 1, (fun i => extI (b i)) c v ∉ ⋃₀ D)
    (Y : Type u)
    [TopologicalSpace Y]
    (g : ℕ × ℂ → Y)
    (hbdY : bd Y = g '' freePts (cutW W (lab '' D)))
    (ψ : Y → S)
    (hψ : ∀ q ∈ Dsk W, ψ (g q) = f q)
    (hone : ∀ (y y' : Y), ψ y = ψ y' → ψ y ∉ ⋃₀ D → y = y')
    (ξ : I → ℝ → Y)
    (cξ : ∀ (i : I), ContinuousOn (ξ i) (Icc 0 1))
    (hξ : ∀ (i : I), ∀ u ∈ Icc 0 1, ψ (ξ i u) = (fun i => extI (b i)) i u) :
    ∀ (c : I), ¬inner c → ∀ u ∈ Icc 0 1, ξ c u ∈ bd Y := by
  let a := fun i => extI (b i)
  intro c hc
  refine mem_of_Ioo (isClosed_bd Y) (cξ c) fun u hu ↦ ?_
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hz : a c u ∈ f '' freePts W := hw.bd_eq ▸ hb.onBd c hc u hu'
  obtain ⟨_, ⟨i, p, r, hp, hfr, hr, rfl⟩, hzr⟩ := hz
  obtain ⟨k, e, hk⟩ : ∃ k e, (W i)[p]? = some (k, e) := by
    obtain ⟨l, hl⟩ : ∃ l, (W i)[p]? = some l := ⟨_, List.getElem?_eq_getElem hp⟩
    exact ⟨l.1, l.2, hl⟩
  have hkL : k ∉ lab '' D := by
    rintro ⟨x, hx, rfl⟩
    refine hoffD c hc u hu ⟨x, hx, ?_⟩
    change a c u ∈ x
    rw [← hzr, hw.f_side (hDE hx) hk hr]
    exact hw.extI_mem (hDE hx) _
  have hm₁ : spt W i p r ∈ Dsk W := spt_mem hp r
  have hin : g (spt W i p r) ∈ bd Y := by
    rw [hbdY]
    refine ⟨spt W i p r, ⟨i, p, r, ?_, freeSide_cut_of_free hk hkL hfr, hr,
      (spt_cut _ _ _).symm⟩, rfl⟩
    rw [cutW_length]
    exact hp
  have := hone (ξ c u) (g (spt W i p r)) (by rw [hξ c u hu', hψ _ hm₁, hzr])
    (by rw [hξ c u hu']; exact hoffD c hc u hu)
  rwa [this]

private theorem uncut_fiber_preserved
    {S : Type u}
    {I : Type}
    {inner : I → Prop}
    (W : ℕ → List Letter)
    (lab : Set S → ℕ)
    (m : I → ℕ)
    (ss : I → ℕ → Set S)
    (Y : Type u)
    [TopologicalSpace Y]
    (g : ℕ × ℂ → Y)
    (hg : Presents (cutW W (lab '' ({x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}))) g)
    (ξ : I → ℝ → Y)
    (η : I → ℝ → Y)
    (hQ : ∀ (c : I), inner c → ∀ p' < m c, ∀ {i p j q : ℕ} {e e' : Bool}, (W i)[p]? = some (lab
      (ss c p'), e) → (W j)[q]? = some (lab (ss c p'), e') → (i, p) ≠ (j, q) → ∀ w ∈ Icc 0 1, ∃ v
      ∈ Icc 0 1, g (spt W i p (ofs e w)) = ξ c v ∧ g (spt W j q (ofs e' w)) = η c v ∨ g (spt W i p
      (ofs e w)) = η c v ∧ g (spt W j q (ofs e' w)) = ξ c v) :
    ∀ (c d : ℕ × ℂ), PRel W c d → Relation.EqvGen (fun p q => ∃ i, ∃ u ∈ Icc 0 1, p = ξ i u ∧ q =
      η i u) (g c) (g d) := by
  let D := {x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}
  intro c d hcd
  induction hcd with
  | rel c d hs =>
    obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
    by_cases hk : k ∈ lab '' D
    · obtain ⟨x, ⟨c', hc', p', hp', rfl⟩, rfl⟩ := hk
      obtain ⟨v, hv, h₄⟩ := hQ c' hc' p' hp' h1 h2 h3 (ofs e u) (ofs_mem hu)
      rw [ofs_ofs, ofs_flp] at h₄
      rcases h₄ with h₄ | h₄
      · exact .rel _ _ ⟨c', v, hv, h₄.1, h₄.2⟩
      · exact .symm _ _ (.rel _ _ ⟨c', v, hv, h₄.2, h₄.1⟩)
    · have := presents_eq_of_stp hg (stp_to_cut h1 h2 h3 hu hk)
      rw [this]
      exact .refl _
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

private theorem off_original_preimage_of_boundary
    {S : Type u}
    [TopologicalSpace S]
    {I : Type}
    {b : I → 𝕀 → S}
    {inner : I → Prop}
    (hb : IsLineFamily b inner)
    (m : I → ℕ)
    (t : I → ℕ → ℝ)
    (ss : I → ℕ → Set S)
    (hsub : ∀ (i : I) {p : ℕ}, p < m i → Icc (t i p) (t i (p + 1)) ⊆ Icc 0 1)
    (hpt : ∀ (i : I) {p : ℕ}, p < m i → ∀ z ∈ ss i p, ∃ u ∈ Icc (t i p) (t i (p + 1)), extI (b i) u
      = z) :
    ∀ (c : I), ¬inner c → ∀ v ∈ Ioo 0 1, extI (b c) v ∉ ⋃₀ {z | ∃ j, inner j ∧ ∃ p < m j, z
      = ss j p} := by
  rintro c hc v hv ⟨_, ⟨j, hj, p, hp, rfl⟩, hz⟩
  obtain ⟨u, hu, hau⟩ := hpt j hp _ hz
  rcases hb.meet j c u v (hsub j hp hu) ⟨hv.1.le, hv.2.le⟩ hau with ⟨rfl, -⟩ | ⟨-, h₂⟩
  · exact hc hj
  · rcases h₂ with h₂ | h₂
    · exact hv.1.ne' h₂
    · exact hv.2.ne h₂

/-- **Cutting along a family of lines.** -/
theorem exists_abstractCut (hS : IsSurface S) [ConnectedSpace S] {I : Type} [Finite I] {b : I → 𝕀
  → S} {inner : I → Prop} (hb : IsLineFamily b inner)
    {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕) (hV : ∀ i, b i 0 ∈ V ∧ b i 1 ∈ V)
      (hE : ∀ i, range (b i) ⊆ gr V E) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S) (ξ η : I → ℝ
      → Y), IsSurface Y ∧ AbstractCut b inner ψ ξ η := by
  classical
  obtain ⟨W, f, A, lab, hw, hdn⟩ := exists_word_edges hS hd
  set a : I → ℝ → S := fun i ↦ extI (b i) with ha
  have hac : ∀ i, Continuous (a i) := fun i ↦ continuous_extI (hb.arc i).1
  have hinj : ∀ i, InjOn (a i) (Icc 0 1) := fun i ↦ extI_injOn (hb.arc i).2
  have hv0 : ∀ i, a i 0 = b i 0 := fun i ↦ extI_coe (b i) 0
  have hv1 : ∀ i, a i 1 = b i 1 := fun i ↦ extI_coe (b i) 1
  have him : ∀ i, a i '' Icc 0 1 = range (b i) := fun i ↦ image_extI _
  have hne : ∀ i, a i 0 ≠ a i 1 := fun i he ↦ by
    have := hinj i (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) he
    norm_num at this
  have hexch := fun i ↦ exists_chain hw.graph A hw.arc (hac i) ((hinj i).mono Ico_subset_Icc_self)
    ((hinj i).mono Ioc_subset_Icc_self)
    (by rw [him]; exact hE i) (by rw [hv0]; exact (hV i).1) (by rw [hv1]; exact (hV i).2) (.inl
      (hne i))
  choose m t ss ε hm ht0 htm hlt hVt hch hsne using hexch
  have hmono : ∀ i {k k'}, k ≤ k' → k' ≤ m i → t i k ≤ t i k' := fun i {k k'} h₁ h₂ ↦ chain_mono'
    (hlt i) h₁ h₂
  have hI : ∀ i, ∀ k ≤ m i, t i k ∈ Icc (0 : ℝ) 1 := fun i k hk ↦ ⟨ht0 i ▸ hmono i
    (Nat.zero_le k) hk, htm i ▸ hmono i hk le_rfl⟩
  have hsub : ∀ i {p}, p < m i → Icc (t i p) (t i (p + 1)) ⊆ Icc 0 1 := fun i {p} hp ↦
    Icc_subset_Icc (hI i p hp.le).1 (hI i (p + 1) hp).2
  have hendV : ∀ i {u : ℝ}, (u = 0 ∨ u = 1) → a i u ∈ V := fun i {u} hu ↦ by
    rcases hu with rfl | rfl
    · rw [hv0]
      exact (hV i).1
    · rw [hv1]
      exact (hV i).2
  let D : Set (Set S) := {x | ∃ i, inner i ∧ ∃ p < m i, x = ss i p}
  have hDE : D ⊆ E := by
    rintro _ ⟨i, -, p, hp, rfl⟩
    exact (hch i p hp).1
  have hpt : ∀ i {p}, p < m i → ∀ z ∈ ss i p, ∃ u ∈ Icc (t i p) (t i (p + 1)), a i u = z
    := fun i {p} hp z hz ↦ by
    have := hz
    rwa [← (hch i p hp).2.1] at this
  have hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂ := by
    exact cut_edge_has_two_sides (S := S) (I := I) (b := b) (inner := inner) hb (V := V) (E := E)
      W f A lab hw m t ss ε hch hsub hendV hpt
  have hoffD : ∀ c, ¬ inner c → ∀ v ∈ Ioo (0 : ℝ) 1, a c v ∉ ⋃₀ D := by
    exact off_original_preimage_of_boundary (S := S) (I := I) (b := b) (inner := inner) hb m t
      ss hsub hpt
  have hfinL := finW_cut (W := W) (L := lab '' D) hw.fin
  have hPL := isPaired_cut (W := W) (L := lab '' D) hw.paired
  obtain ⟨Y, tY, t2, g, hg⟩ := exists_cut_presented.{u} (W := cutW W (lab '' D)) hfinL hPL
    (by rw [dsk_cut]; exact hdn)
  have hD' : Dsk (cutW W (lab '' D)) = Dsk W := dsk_cut
  obtain ⟨hsurf, hbdY⟩ := surface_of_presents hfinL hPL hg
  obtain ⟨ψ, hψc, hψ⟩ := exists_descend hfinL hg (hD' ▸ hw.pres.1) (fun a ha b hb hab ↦
    (hw.pres.2.2 a (hD' ▸ ha) b (hD' ▸ hb)).mpr (prel_of_prel_cut hab))
  rw [hD'] at hψ
  have hrep : ∀ z : Y, ∃ c ∈ Dsk W, g c = z := fun z ↦ by
    have hz : z ∈ g '' Dsk (cutW W (lab '' D)) := hg.2.1 ▸ mem_univ z
    rwa [hD'] at hz
  have hone : ∀ y y', ψ y = ψ y' → ψ y ∉ ⋃₀ D → y = y' := fun y y' he hn ↦ by
    obtain ⟨c, hc, rfl⟩ := hrep y
    obtain ⟨d, hd', rfl⟩ := hrep y'
    rw [hψ c hc, hψ d hd'] at he
    rw [hψ c hc] at hn
    exact (hg.2.2 _ (hD' ▸ hc) _ (hD' ▸ hd')).mpr ((prel_off hw hDE ((hw.pres.2.2 c hc d hd').mp
      he)).2 hn)
  have hcase : ∀ i, inner i → ∀ k, 0 < k → k < m i → ∀ p < m i, ∀ τ, extI (A (ss i p)) (eo τ) = a i
    (t i k) → EndCase S A D (ss i p) τ := by
    exact chain_step_at_interior_endpoint (S := S) (I := I) (b := b) (inner := inner) hb (E := E)
      A m t ss ε hm ht0 htm hlt hch hsne hmono hI
  have hlift : ∀ i, ∃ ξ η : ℝ → Y, ContinuousOn ξ (Icc 0 1) ∧ ContinuousOn η (Icc 0 1) ∧ (∀ u ∈ Icc
    (0 : ℝ) 1, ψ (ξ u) = a i u) ∧ (∀ u ∈ Icc (0 : ℝ) 1, ψ (η u) = a i u) ∧
      (inner i → ChainLift W A lab g ψ (a i) (t i) (ss i) (m i) ξ η) ∧ (¬ inner i → ∀ u ∈ Icc
        (0 : ℝ) 1, η u = ξ u) := fun i ↦ by
    by_cases hi : inner i
    · obtain ⟨ξ, η, hL⟩ :=
        exists_chainLift hw hDE hg hψ hsd (hac i).continuousOn (hinj i) (hm i)
          (ht0 i) (htm i) (hlt i)
          (fun p hp ↦ ⟨⟨i, hi, p, hp, rfl⟩, (hch i p hp).2⟩) (hcase i hi)
      have e := htm i
      refine ⟨ξ, η, e ▸ hL.cξ, e ▸ hL.cη, e ▸ hL.hξ, e ▸ hL.hη, fun _ ↦ hL, fun h ↦ (h hi).elim⟩
    · obtain ⟨ξ, h₁, h₂⟩ :=
        exists_borderLift hw hDE hg hψ (hac i).continuousOn (hm i) (ht0 i)
          (htm i) (hlt i) (fun p hp ↦ ⟨(hch i p hp).1, (hch i p hp).2.1⟩)
          (fun y y' he ⟨u, hu, hy⟩ ↦ hone y y' he (hy ▸ hoffD i hi u hu))
      exact ⟨ξ, ξ, h₁, h₁, h₂, h₂, fun h ↦ (hi h).elim, fun _ _ _ ↦ rfl⟩
  choose ξ η cξ cη hξ hη hL heq using hlift
  have hQ : ∀ c, inner c → ∀ p' < m c, ∀ {i p j q : ℕ} {e e' : Bool}, (W i)[p]? = some (lab
    (ss c p'), e) → (W j)[q]? = some (lab (ss c p'), e') → (i, p) ≠ (j, q) →
      ∀ w ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1, (g (spt W i p (ofs e w)) = ξ c v ∧ g (spt W j q
        (ofs e' w)) = η c v) ∨
        (g (spt W i p (ofs e w)) = η c v ∧ g (spt W j q (ofs e' w)) = ξ c v) := by
    exact lift_endpoints_are_cut_sides (S := S) (I := I) (inner := inner) (V := V) (E := E) W f A
      lab hw a m t ss ε hch hsub hpt Y g ψ ξ η hL
  have hQ' : ∀ c, inner c → ∀ p' < m c, ∀ {i p : ℕ} {e : Bool}, (W i)[p]? = some (lab (ss c p'), e)
    → ∀ w ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      g (spt W i p (ofs e w)) = ξ c v ∨ g (spt W i p (ofs e w)) = η c v := by
    intro c hc p' hp' i p e h₁ w hw'
    obtain ⟨i₀, q₀, j₀, r₀, e₁, e₂, s₀⟩ := hsd _ (⟨c, hc, p', hp', rfl⟩ : ss c p' ∈ D)
    by_cases hne' : (i, p) = (i₀, q₀)
    · obtain ⟨v, hv, h₂⟩ := hQ c hc p' hp' h₁ s₀.two (hne'.symm ▸ s₀.ne) w hw'
      exact ⟨v, hv, h₂.elim (fun h₃ ↦ .inl h₃.1) fun h₃ ↦ .inr h₃.1⟩
    · obtain ⟨v, hv, h₂⟩ := hQ c hc p' hp' h₁ s₀.one hne' w hw'
      exact ⟨v, hv, h₂.elim (fun h₃ ↦ .inl h₃.1) fun h₃ ↦ .inr h₃.1⟩
  have hfreeD : ∀ c, inner c → ∀ p' < m c, ∀ {i p : ℕ} {e : Bool}, (W i)[p]? = some (lab
    (ss c p'), e) → ∀ w ∈ Icc (0 : ℝ) 1, g (spt W i p (ofs e w)) ∈ bd Y := by
    intro c hc p' hp' i p e h₁ w hw'
    rw [hbdY]
    refine ⟨spt W i p (ofs e w), ⟨i, p, ofs e w, ?_, freeSide_cut h₁ ⟨_, ⟨c, hc, p', hp', rfl⟩,
      rfl⟩, ofs_mem hw', (spt_cut _ _ _).symm⟩, rfl⟩
    rw [cutW_length]
    exact lt_length h₁
  have hbdIn : ∀ c, inner c → ∀ u ∈ Icc (0 : ℝ) 1, ξ c u ∈ bd Y ∧ η c u ∈ bd Y := by
    intro c hc u hu
    obtain ⟨p', hp', hu'⟩ := exists_chainStep (hm c) (ht0 c) (hlt c) (u := u) (by rwa [htm c])
    obtain ⟨i₀, q₀, j₀, r₀, e₁, e₂, s₀, hform⟩ := (hL c hc).pieces p' hp'
    have hmem : a c u ∈ ss c p' := (hch c p' hp').2.1 ▸ mem_image_of_mem _ hu'
    have himA : extI (A (ss c p')) '' Icc 0 1 = ss c p' := by
      rw [image_extI, (hw.arc _ (hch c p' hp').1).2.1]
    rw [← himA] at hmem
    obtain ⟨w, hw', hwe⟩ := hmem
    obtain ⟨h₁, h₂⟩ := hform u hu' w hw' hwe
    exact ⟨h₁ ▸ hfreeD c hc p' hp' s₀.one w hw', h₂ ▸ hfreeD c hc p' hp' s₀.two w hw'⟩
  have hbdB : ∀ c, ¬ inner c → ∀ u ∈ Icc (0 : ℝ) 1, ξ c u ∈ bd Y := by
    exact border_arc_lift_on_boundary (S := S) (I := I) (b := b) (inner := inner) hb (V := V) (E
      := E) W f A lab hw D hDE hoffD Y g hbdY ψ hψ hone ξ cξ hξ
  have hfibr : ∀ c d, PRel W c d → Relation.EqvGen (fun p q ↦ ∃ i, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ i u
    ∧ q = η i u) (g c) (g d) := by
    exact uncut_fiber_preserved (S := S) (I := I) (inner := inner) W lab m ss Y g hg ξ η hQ
  have hZ : IsClosed (⋃ i, (ξ i '' Icc 0 1 ∪ η i '' Icc 0 1)) := by
    refine isClosed_iUnion_of_finite fun i ↦ ?_
    exact ((isCompact_Icc.image_of_continuousOn (cξ i)).union (isCompact_Icc.image_of_continuousOn
      (cη i))).isClosed
  refine ⟨Y, tY, t2, ψ, ξ, η, hsurf, ⟨hψc, ?_, cξ, cη, hξ, hη, ?_, ?_, ?_, heq, ?_, ?_⟩⟩
  · intro x
    obtain ⟨c, hc, rfl⟩ : x ∈ f '' Dsk W := hw.pres.2.1 ▸ mem_univ x
    exact ⟨g c, hψ c hc⟩
  · intro c u hu
    by_cases hc : inner c
    · exact (hbdIn c hc u hu).1
    · exact hbdB c hc u hu
  · intro c u hu
    by_cases hc : inner c
    · exact (hbdIn c hc u hu).2
    · rw [heq c hc u hu]
      exact hbdB c hc u hu
  · exact fun i hi u hu ↦ (hL i hi).ne u (by rw [htm i]; exact hu)
  · intro y hy
    rw [hbdY] at hy
    obtain ⟨_, ⟨i, p, r, hp, hfr, hr, rfl⟩, rfl⟩ := hy
    rw [cutW_length] at hp
    obtain ⟨k, e, hk⟩ : ∃ k e, (W i)[p]? = some (k, e) := by
      obtain ⟨l, hl⟩ : ∃ l, (W i)[p]? = some l := ⟨_, List.getElem?_eq_getElem hp⟩
      exact ⟨l.1, l.2, hl⟩
    rw [spt_cut] at *
    have hc₀ : ContinuousOn (fun r ↦ g (spt W i p r)) (Icc 0 1) := by
      have h₁ : Continuous fun r ↦ spt W i p r := by
        have := continuous_spt_ofs W i p true
        simpa [ofs] using this
      exact hg.1.comp h₁.continuousOn fun u _ ↦ hD' ▸ spt_mem hp u
    have hall := mem_of_Ioo hZ hc₀ (fun u hu ↦ ?_) r hr
    · obtain ⟨c, hc⟩ := mem_iUnion.1 hall
      rcases hc with ⟨u, hu, h₁⟩ | ⟨u, hu, h₁⟩
      · exact ⟨c, u, hu, .inl h₁.symm⟩
      · exact ⟨c, u, hu, .inr h₁.symm⟩
    · have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
      by_cases hkL : k ∈ lab '' D
      · obtain ⟨x, ⟨c, hc, p', hp', rfl⟩, rfl⟩ := hkL
        obtain ⟨v, hv, h₄⟩ := hQ' c hc p' hp' hk (ofs e u) (ofs_mem hu')
        rw [ofs_ofs] at h₄
        rcases h₄ with h₄ | h₄
        · exact mem_iUnion.2 ⟨c, .inl ⟨v, hv, h₄.symm⟩⟩
        · exact mem_iUnion.2 ⟨c, .inr ⟨v, hv, h₄.symm⟩⟩
      · have hfr' := freeSide_of_cut hk hkL hfr
        have hzb : f (spt W i p u) ∈ bd S := hw.bd_eq ▸ mem_image_of_mem _ ⟨i, p, u, hp, hfr', hu',
          rfl⟩
        obtain ⟨x, hx, hxk, -⟩ := hw.side _ _ _ _ hk
        subst hxk
        have hnV : f (spt W i p u) ∉ V := by
          rw [hw.f_side hx hk hu']
          exact hw.extI_notMem hx (ofs_Ioo e hu)
        obtain ⟨c, v, hv⟩ := hb.cover _ hzb
        have hv' : (v : ℝ) ∈ Icc (0 : ℝ) 1 := v.2
        have hav : a c v = f (spt W i p u) := (extI_coe (b c) v).trans hv
        have hvin : (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
          refine ⟨lt_of_le_of_ne hv'.1 fun h₁ ↦ hnV ?_, lt_of_le_of_ne hv'.2 fun h₁ ↦ hnV ?_⟩
          · rw [← hav]
            exact hendV c (.inl h₁.symm)
          · rw [← hav]
            exact hendV c (.inr h₁)
        have hc : ¬ inner c := fun hc ↦ hb.off c hc v hvin (by
          change a c v ∈ bd S
          rw [hav]
          exact hzb)
        have := hone (ξ c v) (g (spt W i p u)) (by rw [hξ c v hv', hψ _ (spt_mem hp u), hav])
          (by rw [hξ c v hv']; exact hoffD c hc v hvin)
        exact mem_iUnion.2 ⟨c, .inl ⟨v, hv', this⟩⟩
  · intro y y' he
    obtain ⟨c, hc, rfl⟩ := hrep y
    obtain ⟨d, hd', rfl⟩ := hrep y'
    rw [hψ c hc, hψ d hd'] at he
    exact hfibr c d ((hw.pres.2.2 c hc d hd').mp he)

end GraphMinor.GM19
