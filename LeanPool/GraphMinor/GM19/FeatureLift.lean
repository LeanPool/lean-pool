/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutSimilar

/-!
# The two lifts of an edge

Let a surface be presented by the word of a dissection, and cut the word along a set `D` of edges.
An arc that is a chain of
edges of `D`, and that has at each inner vertex only the two ends of its own chain, has two lifts to
the cut surface. Unlike
`LiftPair` we allow the two lifts to meet at the ends of the arc, as they do at a vertex of degree
one.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {W : ℕ → List Letter} {f : ℕ × ℂ
  → S} {V : Set S} {E : Set (Set S)}
  {A : Set S → unitInterval → S} {lab : Set S → ℕ}

/-- The condition of `WordEdges.vertex_cut` at the end `τ` of the edge `e`. -/
def EndCase (S : Type u) [TopologicalSpace S] (A : Set S → unitInterval → S) (D : Set (Set S))
  (e : Set S) (τ : Bool) : Prop :=
  (∃ e' ∈ D, ∃ τ', e' ≠ e ∧ extI (A e') (eo τ') = extI (A e) (eo τ) ∧ extI (A e) (eo τ) ∉ bd S ∧
      ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → (e'' = e ∧ τ'' = τ) ∨ (e'' = e'
        ∧ τ'' = τ')) ∨
    (extI (A e) (eo τ) ∈ bd S ∧ ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → e''
      = e ∧ τ'' = τ)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {D : Set (Set S)} {g : ℕ × ℂ → Y} {ψ : Y → S}

section

variable (h : WordEdges W f V E A lab) (hD : D ⊆ E) (hg : Presents (cutW W (lab '' D)) g)
  (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a)
include h hD hg hψ

omit [T2Space S] [T2Space Y] hD hψ in
/-- The two sides of an edge of `D` are apart inside the edge. -/
theorem sides_ne {e : Set S} (heD : e ∈ D) {i p j q : ℕ} {e₁ e₂ : Bool} (s : EdgeSides W
  (lab e) i p j q e₁ e₂) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g (spt W i p (ofs e₁ t)) ≠ g (spt W j q (ofs e₂ t)) := by
  intro he
  have hP' : IsPaired (cutW W (lab '' D)) := isPaired_cut h.paired
  have hD' : Dsk (cutW W (lab '' D)) = Dsk W := dsk_cut
  have hL0 : lab e ∈ lab '' D := ⟨e, heD, rfl⟩
  have hp := lt_length s.one
  have hq := lt_length s.two
  have hm1 : spt W i p (ofs e₁ t) ∈ Dsk W := spt_mem hp _
  have hm2 : spt W j q (ofs e₂ t) ∈ Dsk W := spt_mem hq _
  have hpr := (hg.2.2 _ (hD' ▸ hm1) _ (hD' ▸ hm2)).mp he
  have hu := ofs_Ioo e₁ ht
  have hl' : (cutW W (lab '' D) i)[p]? = some (2 * Nat.pair i p + 1, e₁)
    := cut_get_iff.mpr ⟨_, s.one, .inl ⟨hL0, rfl⟩⟩
  have hpr' : PRel (cutW W (lab '' D)) (spt (cutW W (lab '' D)) i p (ofs e₁ t)) (spt W j q
    (ofs e₂ t)) := by
    rw [spt_cut]
    exact hpr
  have hfree := freeSide_cut (L := lab '' D) s.one hL0
  have heqs : spt W j q (ofs e₂ t) = spt W i p (ofs e₁ t) := by
    rcases hpr'.eq_or_stp hP' hl' hu with h1 | h1
    · rw [h1, spt_cut]
    · exfalso
      obtain ⟨j', q', e', h2, h3, -⟩ := stp_of_side hP' hl' hu h1
      exact h3 (hfree _ _ _ _ _ hl' h2)
  have h1 : j = i := congrArg Prod.fst heqs
  subst h1
  have h2 : per (W j).length (q + ofs e₂ t) = per (W j).length (p + ofs e₁ t)
    := congrArg Prod.snd heqs
  obtain ⟨h3, -⟩ := side_unique hq hp (ofs_Ioo e₂ ht) (ofs_mem ⟨ht.1.le, ht.2.le⟩) h2
  exact s.ne (by rw [h3])

omit [T2Space Y] in
/-- What happens at an end of an edge of `D` with `EndCase`: the two sides end at different points,
and these are all the points over the end. -/
theorem sides_end {e : Set S} (heD : e ∈ D) (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ)
  (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂) {i p j q : ℕ} {e₁ e₂ : Bool}
    (s : EdgeSides W (lab e) i p j q e₁ e₂) {τ : Bool} (hc : EndCase S A D e τ) :
    g (spt W i p (ofs e₁ (eo τ))) ≠ g (spt W j q (ofs e₂ (eo τ))) ∧
      ∀ y : Y, ψ y = extI (A e) (eo τ) → y = g (spt W i p (ofs e₁ (eo τ))) ∨ y = g (spt W j q
        (ofs e₂ (eo τ))) := by
  have hD' : Dsk (cutW W (lab '' D)) = Dsk W := dsk_cut
  obtain ⟨hv₁, hv₂⟩ := h.vertex_cut hD heD hsd s τ hc
  have hspe : spe W (s.end₁ τ) = spt W i p (ofs e₁ (eo τ)) := by
    simp only [spe, EdgeSides.end₁, eo_xn]
  have hspe' : spe W (s.end₂ τ) = spt W j q (ofs e₂ (eo τ)) := by
    simp only [spe, EdgeSides.end₂, eo_xn]
  have hm1 : spe W (s.end₁ τ) ∈ Dsk W := spe_mem _
  have hm2 : spe W (s.end₂ τ) ∈ Dsk W := spe_mem _
  refine ⟨fun he ↦ hv₁ ?_, fun y hy ↦ ?_⟩
  · rw [← hspe, ← hspe'] at he
    exact (hg.2.2 _ (hD' ▸ hm1) _ (hD' ▸ hm2)).mp he
  · obtain ⟨a, ha, rfl⟩ : y ∈ g '' Dsk (cutW W (lab '' D)) := hg.2.1 ▸ mem_univ y
    rw [hD'] at ha
    rw [hψ a ha] at hy
    rcases hv₂ a ha hy with h₁ | h₁
    · left
      rw [← hspe]
      exact ((hg.2.2 _ (hD' ▸ hm1) _ (hD' ▸ ha)).mpr h₁).symm
    · right
      rw [← hspe']
      exact ((hg.2.2 _ (hD' ▸ hm2) _ (hD' ▸ ha)).mpr h₁).symm

end

/-- A lift of the first `n` pieces of a chain to the two sides. -/
structure ChainLift (W : ℕ → List Letter) (A : Set S → unitInterval → S) (lab : Set S → ℕ)
  (g : ℕ × ℂ → Y) (ψ : Y → S) (a : ℝ → S) (t : ℕ → ℝ) (ss : ℕ → Set S)
    (n : ℕ) (ξ η : ℝ → Y) : Prop where
  cξ : ContinuousOn ξ (Icc 0 (t n))
  cη : ContinuousOn η (Icc 0 (t n))
  hξ : ∀ u ∈ Icc 0 (t n), ψ (ξ u) = a u
  hη : ∀ u ∈ Icc 0 (t n), ψ (η u) = a u
  ne : ∀ u ∈ Ioo 0 (t n), ξ u ≠ η u
  pieces : ∀ p < n, ∃ (i q j r : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab (ss p)) i q j r e₁ e₂
    ∧ ∀ u ∈ Icc (t p) (t (p + 1)), ∀ w ∈ Icc (0 : ℝ) 1,
    extI (A (ss p)) w = a u → ξ u = g (spt W i q (ofs e₁ w)) ∧ η u = g (spt W j r (ofs e₂ w))

theorem EdgeSides.swap' {k i p j q : ℕ} {e₁ e₂ : Bool} (s : EdgeSides W k i p j q e₁ e₂) :
  EdgeSides W k j q i p e₂ e₁ :=
  ⟨s.two, s.one, s.ne.symm⟩

/-- Two continuous maps that agree at a point make a continuous map. -/
theorem continuousOn_join {T : Type*} [TopologicalSpace T] {ξ ξ₁ : ℝ → T} {b c : ℝ} (hb : 0 ≤ b)
  (h₁ : ContinuousOn ξ (Icc 0 b)) (h₂ : ContinuousOn ξ₁ (Icc b c))
    (he : ξ b = ξ₁ b) (hbc : b ≤ c) : ContinuousOn (fun u ↦ if u ≤ b then ξ u else ξ₁ u) (Icc 0 c)
      := by
  have e : Icc 0 c = Icc 0 b ∪ Icc b c := (Icc_union_Icc_eq_Icc hb hbc).symm
  rw [e]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · exact h₁.congr fun u hu ↦ ite_eq_left hu.2
  · refine h₂.congr fun u hu ↦ ?_
    by_cases h : u ≤ b
    · have : u = b := le_antisymm h hu.1
      subst this
      simp only [le_refl, ite_true]
      exact he
    · exact ite_eq_right_iff.mpr fun h' ↦ absurd h' h

section

variable (h : WordEdges W f V E A lab) (hD : D ⊆ E) (hg : Presents (cutW W (lab '' D)) g)
  (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a)
include h hD hg hψ

omit [T2Space Y] in
/-- A piece of a chain, seen through one pair of sides. -/
theorem piece_lift {x : Set S} (hx : x ∈ D) {i q j r : ℕ} {e₁ e₂ : Bool} (s : EdgeSides W
  (lab x) i q j r e₁ e₂) {a : ℝ → S} {b c : ℝ} (hbc : b < c)
    (ha : ContinuousOn a (Icc b c)) (hinj : InjOn a (Icc b c)) (him : a '' Icc b c = x)
      (hb : ∃ τ, extI (A x) (eo τ) = a b) (hc : ∃ τ, extI (A x) (eo τ) = a c) :
    ∃ ξ η : ℝ → Y, ContinuousOn ξ (Icc b c) ∧ ContinuousOn η (Icc b c) ∧ (∀ u ∈ Icc b c, ψ (ξ u)
      = a u) ∧ (∀ u ∈ Icc b c, ψ (η u) = a u) ∧
      (∀ u ∈ Ioo b c, ξ u ≠ η u) ∧ ∀ u ∈ Icc b c, ∀ w ∈ Icc (0 : ℝ) 1, extI (A x) w = a u → ξ u = g
        (spt W i q (ofs e₁ w)) ∧ η u = g (spt W j r (ofs e₂ w)) := by
  have hxE := hD hx
  have hD' : Dsk (cutW W (lab '' D)) = Dsk W := dsk_cut
  have hcA : ContinuousOn (extI (A x)) (Icc 0 1) := (continuous_extI (h.arc x hxE).1.1).continuousOn
  have hiA := extI_injOn (h.arc x hxE).1.2
  have himA : extI (A x) '' Icc 0 1 = x := by rw [image_extI, (h.arc x hxE).2.1]
  obtain ⟨θ', hθc, hθl⟩ := exists_inv_of_compactOn isCompact_Icc hcA hiA
  rw [himA] at hθc
  have hmem : ∀ u ∈ Icc b c, a u ∈ x := fun u hu ↦ him ▸ mem_image_of_mem _ hu
  have hex : ∀ u ∈ Icc b c, ∃ w ∈ Icc (0 : ℝ) 1, extI (A x) w = a u := fun u hu ↦ by
    have := hmem u hu
    rwa [← himA] at this
  choose! θ hθ₁ hθ₂ using hex
  have hθeq : ∀ u ∈ Icc b c, θ u = θ' (a u) := fun u hu ↦ by
    rw [← hθ₂ u hu, hθl (hθ₁ u hu)]
  have hθcont : ContinuousOn θ (Icc b c) := (hθc.comp ha (fun u hu ↦ hmem u hu)).congr hθeq
  have hp := lt_length s.one
  have hq := lt_length s.two
  have hcs : ∀ {i p : ℕ} {e : Bool}, p < (W i).length → ContinuousOn (fun u ↦ g (spt W i p (ofs e
    (θ u)))) (Icc b c) := fun {i p e} hp ↦ by
    have h₁ : ContinuousOn (fun u ↦ spt W i p (ofs e (θ u))) (Icc b c) :=
      (continuous_spt_ofs W i p e).comp_continuousOn hθcont
    exact hg.1.comp h₁ fun u _ ↦ hD' ▸ spt_mem hp _
  have hval : ∀ {i p : ℕ} {e : Bool}, (W i)[p]? = some (lab x, e) → ∀ u ∈ Icc b c, ψ (g (spt W i p
    (ofs e (θ u)))) = a u := fun {i p e} he u hu ↦ by
    rw [hψ _ (spt_mem (lt_length he) _), h.f_side hxE he (ofs_mem (hθ₁ u hu)), ofs_ofs, hθ₂ u hu]
  refine ⟨_, _, hcs hp, hcs hq, hval s.one, hval s.two, fun u hu ↦ ?_, fun u hu w hw he ↦ ?_⟩
  · have hu' : u ∈ Icc b c := ⟨hu.1.le, hu.2.le⟩
    have hend : ∀ {v τ}, v ∈ Icc b c → extI (A x) (eo τ) = a v → u ≠ v → θ u ≠ eo τ
      := fun {v τ} hv hτ hne he ↦ by
      have h₁ : a u = a v := by rw [← hθ₂ u hu', he, hτ]
      exact hne (hinj hu' hv h₁)
    have hθu : θ u ∈ Ioo (0 : ℝ) 1 := by
      obtain ⟨τ₁, h₁⟩ := hb
      obtain ⟨τ₂, h₂⟩ := hc
      have n₁ := hend (⟨le_rfl, hbc.le⟩ : b ∈ Icc b c) h₁ hu.1.ne'
      have n₂ := hend (⟨hbc.le, le_rfl⟩ : c ∈ Icc b c) h₂ hu.2.ne
      have hτ : τ₁ ≠ τ₂ := by
        rintro rfl
        exact hbc.ne (hinj ⟨le_rfl, hbc.le⟩ ⟨hbc.le, le_rfl⟩ (h₁.symm.trans h₂))
      have hne : θ u ≠ 0 ∧ θ u ≠ 1 := by
        cases τ₁ <;> cases τ₂ <;> simp_all [eo]
      exact ⟨lt_of_le_of_ne (hθ₁ u hu').1 hne.1.symm, lt_of_le_of_ne (hθ₁ u hu').2 hne.2⟩
    exact sides_ne h hg hx s hθu
  · have hw' : w = θ u := by
      exact hiA hw (hθ₁ u hu) (he.trans (hθ₂ u hu).symm)
    subst hw'
    exact ⟨rfl, rfl⟩

omit [T2Space Y] in
/-- An arc that is a chain of edges of `D` has two lifts. -/
theorem exists_chainLift (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W
  (lab e) i p j q e₁ e₂) {a : ℝ → S}
    (ha : ContinuousOn a (Icc 0 1)) (hinj : InjOn a (Icc 0 1)) {m : ℕ} {t : ℕ → ℝ} {ss : ℕ
      → Set S} {ε : ℕ → Bool} (hm : 0 < m) (ht0 : t 0 = 0) (htm : t m = 1)
    (hlt : ∀ p < m, t p < t (p + 1)) (hch : ∀ p < m, ss p ∈ D ∧ a '' Icc (t p) (t (p + 1)) = ss p
      ∧ a (t p) = extI (A (ss p)) (if ε p then 0 else 1) ∧
      a (t (p + 1)) = extI (A (ss p)) (if ε p then 1 else 0))
    (hc : ∀ k, 0 < k → k < m → ∀ p < m, ∀ τ, extI (A (ss p)) (eo τ) = a (t k) → EndCase S A D
      (ss p) τ) :
    ∃ ξ η, ChainLift W A lab g ψ a t ss m ξ η := by
  have hmono : ∀ {k k'}, k ≤ k' → k' ≤ m → t k ≤ t k' := fun {k k'} h₁ h₂ ↦ chain_mono' hlt h₁ h₂
  have hI : ∀ k ≤ m, t k ∈ Icc (0 : ℝ) 1 := fun k hk ↦ ⟨ht0 ▸ hmono (Nat.zero_le k) hk, htm ▸ hmono
    hk le_rfl⟩
  have hsub : ∀ {p}, p < m → Icc (t p) (t (p + 1)) ⊆ Icc 0 1 := fun {p} hp ↦ Icc_subset_Icc
    (hI p hp.le).1 (hI (p + 1) hp).2
  have hend : ∀ {p}, p < m → (∃ τ, extI (A (ss p)) (eo τ) = a (t p)) ∧ ∃ τ, extI (A (ss p)) (eo τ)
    = a (t (p + 1)) := fun {p} hp ↦ by
    obtain ⟨-, -, h₁, h₂⟩ := hch p hp
    refine ⟨⟨!ε p, ?_⟩, ⟨ε p, ?_⟩⟩
    · rw [h₁]
      cases ε p <;> simp [eo]
    · rw [h₂]
      cases ε p <;> simp [eo]
  have hpiece : ∀ {p}, p < m → ∀ {i q j r : ℕ} {e₁ e₂ : Bool}, EdgeSides W (lab
    (ss p)) i q j r e₁ e₂ → _ := fun {p} hp {i q j r e₁ e₂} s ↦
    piece_lift h hD hg hψ (hch p hp).1 s (hlt p hp) (ha.mono (hsub hp)) (hinj.mono (hsub hp))
      (hch p hp).2.1 (hend hp).1 (hend hp).2
  have key : ∀ n, 1 ≤ n → n ≤ m → ∃ ξ η, ChainLift W A lab g ψ a t ss n ξ η := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hle
      obtain ⟨i, q, j, r, e₁, e₂, s⟩ := hsd _ (hch 0 hm).1
      obtain ⟨ξ, η, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hpiece hm s
      simp only [zero_add] at h₁ h₂ h₃ h₄ h₅ h₆
      rw [ht0] at h₁ h₂ h₃ h₄ h₅ h₆
      refine ⟨ξ, η, ⟨h₁, h₂, h₃, h₄, h₅, fun p hp ↦ ?_⟩⟩
      obtain rfl : p = 0 := by omega
      refine ⟨i, q, j, r, e₁, e₂, s, ?_⟩
      simp only [zero_add]
      rw [ht0]
      exact h₆
    | succ n hn ih =>
      intro hle
      obtain ⟨ξ, η, hL⟩ := ih (by omega)
      have hn₀ : 0 < n := by omega
      have hnm : n < m := by omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hn'm : n' < m := by omega
      obtain ⟨i₀, q₀, j₀, r₀, e₁₀, e₂₀, s₀, hp₀⟩ := hL.pieces n' (by omega)
      obtain ⟨τ₀, hτ₀⟩ := (hend hn'm).2
      obtain ⟨τ₁, hτ₁⟩ := (hend hnm).1
      have hzero : ∀ τ : Bool, eo τ ∈ Icc (0 : ℝ) 1 := fun τ ↦ by cases τ <;> simp [eo]
      have ht₁ : t (n' + 1) ∈ Icc (t n') (t (n' + 1)) := ⟨(hlt n' hn'm).le, le_rfl⟩
      obtain ⟨hv₁, hv₂⟩ := hp₀ _ ht₁ _ (hzero τ₀) hτ₀
      have hne₀ := (sides_end h hD hg hψ (hch n' hn'm).1 hsd s₀ (hc (n' + 1) hn₀ hnm n' hn'm τ₀
        hτ₀)).1
      rw [← hv₁, ← hv₂] at hne₀
      obtain ⟨i, q, j, r, e₁, e₂, s⟩ := hsd _ (hch (n' + 1) hnm).1
      have hcase := hc (n' + 1) hn₀ hnm (n' + 1) hnm τ₁ hτ₁
      obtain ⟨hne₁, hall⟩ := sides_end h hD hg hψ (hch (n' + 1) hnm).1 hsd s hcase
      have htI : t (n' + 1) ∈ Icc 0 (t (n' + 1)) := ⟨(hI _ hnm.le).1, le_rfl⟩
      have ex : ∃ (i q j r : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab (ss (n' + 1))) i q j r e₁ e₂ ∧ ξ
        (t (n' + 1)) = g (spt W i q (ofs e₁ (eo τ₁))) ∧
          η (t (n' + 1)) = g (spt W j r (ofs e₂ (eo τ₁))) := by
        rcases hall _ ((hL.hξ _ htI).trans hτ₁.symm) with h₁ | h₁ <;> rcases hall _
          ((hL.hη _ htI).trans hτ₁.symm) with h₂ | h₂
        · exact (hne₀ (h₁.trans h₂.symm)).elim
        · exact ⟨i, q, j, r, e₁, e₂, s, h₁, h₂⟩
        · exact ⟨j, r, i, q, e₂, e₁, EdgeSides.swap' s, h₁, h₂⟩
        · exact (hne₀ (h₁.trans h₂.symm)).elim
      obtain ⟨i', q', j', r', a₁, a₂, s', hξt, hηt⟩ := ex
      obtain ⟨ξ₁, η₁, c₁, c₂, c₃, c₄, c₅, c₆⟩ := hpiece hnm s'
      have ht₂ : t (n' + 1) ∈ Icc (t (n' + 1)) (t (n' + 1 + 1)) := ⟨le_rfl, (hlt _ hnm).le⟩
      obtain ⟨hv₃, hv₄⟩ := c₆ _ ht₂ _ (hzero τ₁) hτ₁
      have hb₀ := (hI _ hnm.le).1
      have hstep := (hlt _ hnm).le
      refine ⟨fun u ↦ if u ≤ t (n' + 1) then ξ u else ξ₁ u, fun u ↦ if u ≤ t
        (n' + 1) then η u else η₁ u, ⟨continuousOn_join hb₀ hL.cξ c₁ (hξt.trans hv₃.symm) hstep,
        continuousOn_join hb₀ hL.cη c₂ (hηt.trans hv₄.symm) hstep, ?_, ?_, ?_, ?_⟩⟩
      · intro u hu
        by_cases hl : u ≤ t (n' + 1)
        · simp only [hl, ite_true]
          exact hL.hξ u ⟨hu.1, hl⟩
        · simp only [hl, ite_false]
          exact c₃ u ⟨(not_le.1 hl).le, hu.2⟩
      · intro u hu
        by_cases hl : u ≤ t (n' + 1)
        · simp only [hl, ite_true]
          exact hL.hη u ⟨hu.1, hl⟩
        · simp only [hl, ite_false]
          exact c₄ u ⟨(not_le.1 hl).le, hu.2⟩
      · intro u hu
        by_cases hl : u ≤ t (n' + 1)
        · simp only [hl, ite_true]
          rcases hl.lt_or_eq with h₁ | h₁
          · exact hL.ne u ⟨hu.1, h₁⟩
          · rw [h₁]
            exact hne₀
        · simp only [hl, ite_false]
          exact c₅ u ⟨not_le.1 hl, hu.2⟩
      · intro p hp
        by_cases hpn : p = n' + 1
        · subst hpn
          refine ⟨i', q', j', r', a₁, a₂, s', fun u hu w hw he ↦ ?_⟩
          obtain ⟨h₁, h₂⟩ := c₆ u hu w hw he
          by_cases hl : u ≤ t (n' + 1)
          · have : u = t (n' + 1) := le_antisymm hl hu.1
            subst this
            simp only [le_refl, ite_true]
            rw [hξt, hηt]
            have hw' : w = eo τ₁ := extI_injOn (h.arc _ (hD (hch _ hnm).1)).1.2 hw (hzero τ₁)
              (he.trans hτ₁.symm)
            subst hw'
            exact ⟨rfl, rfl⟩
          · simp only [hl, ite_false]
            exact ⟨h₁, h₂⟩
        · obtain ⟨a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := hL.pieces p (by omega)
          refine ⟨a₃, a₄, a₅, a₆, a₇, a₈, a₉, fun u hu w hw he ↦ ?_⟩
          have hl : u ≤ t (n' + 1) := hu.2.trans (hmono (by omega) hnm.le)
          simp only [hl, ite_true]
          exact a₁₀ u hu w hw he
  rw [← htm] at *
  exact key m hm le_rfl

end

end GraphMinor.GM19
