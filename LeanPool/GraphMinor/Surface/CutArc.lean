/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutEdges

/-!
# Cutting a surface along an arc

`exists_cut_arc` and `exists_cut_loop` cut a connected surface along a proper `I`-arc or along an
`O`-arc off the boundary.
We dissect the surface so that the arc is a chain of edges, cut the word of the dissection along
these edges, and fit the
lifts of the edges together.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S'] [T2Space S'] {ψ : S' → S}

omit [TopologicalSpace S] [T2Space S'] in
theorem LiftPair.swap {Z : Set S} {u v : S} {X Y : Set S'} (h : LiftPair ψ Z u v X Y) : LiftPair ψ
  Z v u X Y := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨x1, x0, y1, y0, h1.symm, h2.symm, h3, h4, h5, h6, h9, h10, h7, h8⟩

omit [TopologicalSpace S] [T2Space S'] in
theorem LiftPair.ncard {Z : Set S} {u v : S} {X Y : Set S'} (h : LiftPair ψ Z u v X Y) {x : S}
  (hx : x ∈ Z) :
    (ψ ⁻¹' {x}).encard = 2 ∧ (ψ ⁻¹' {x}).ncard = 2 := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨a, ha, rfl⟩ := h5.surjOn hx
  obtain ⟨b, hb, hab⟩ := h6.surjOn hx
  have hne : a ≠ b := fun he => Set.disjoint_left.mp h3 ha (he ▸ hb)
  have e : ψ ⁻¹' {ψ a} = {a, b} := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ X ∪ Y := by
        rw [h4]
        change ψ z ∈ Z
        rw [show ψ z = ψ a from hz]
        exact hx
      rcases hz' with hz' | hz'
      · exact .inl (h5.injOn hz' ha hz)
      · exact .inr (h6.injOn hz' hb (hab ▸ hz))
    · rintro (rfl | rfl)
      · rfl
      · exact hab
  rw [e]
  exact ⟨encard_pair hne, ncard_pair hne⟩

/-- The index of the vertex at the end `τ` of the edge `p` of a chain. -/
def chainAt (ε : ℕ → Bool) (p : ℕ) (τ : Bool) : ℕ := if τ = ε p then p + 1 else p

theorem chainAt_split {ε : ℕ → Bool} {q k : ℕ} {τ : Bool} (h : chainAt ε q τ = k) :
    (q = k ∧ τ = !ε q) ∨ (q + 1 = k ∧ τ = ε q) := by
  unfold chainAt at h
  split_ifs at h with h1
  · exact .inr ⟨h, h1⟩
  · refine .inl ⟨h, ?_⟩
    cases τ <;> cases hε : ε q <;> simp_all

/-- The ends of the edges of a chain at a vertex. -/
theorem chain_cases {X : Type*} {A : Set X → 𝕀 → X} {bdS : Set X} {ι : ℝ → X} {m : ℕ} {t : ℕ
  → ℝ} {ss : ℕ → Set X}
    {ε : ℕ → Bool} (hex : ∀ p < m, ∀ τ, extI (A (ss p)) (eo τ) = ι (t (chainAt ε p τ)))
    (hinj : ∀ p < m, ∀ q < m, p ≠ q → ss p ≠ ss q) (closed : Prop)
    (hk : ∀ k ≤ m, ∀ k' ≤ m, ι (t k) = ι (t k') → k = k' ∨ (closed ∧ ((k = 0 ∧ k' = m) ∨ (k = m
      ∧ k' = 0))))
    (h2 : closed → 2 ≤ m) (hm : 0 < m) (hb0 : closed → ∀ k ≤ m, ι (t k) ∉ bdS)
    (hb1 : ¬ closed → ι (t 0) ∈ bdS ∧ ι (t m) ∈ bdS ∧ ∀ k, 0 < k → k < m → ι (t k) ∉ bdS)
    (hclose : closed → ι (t 0) = ι (t m)) {p : ℕ} (hp : p < m) (τ : Bool) :
    (∃ e' ∈ ss '' Iio m, ∃ τ', e' ≠ ss p ∧ extI (A e') (eo τ') = extI (A (ss p)) (eo τ) ∧ extI (A
      (ss p)) (eo τ) ∉ bdS ∧
        ∀ e'' ∈ ss '' Iio m, ∀ τ'', extI (A e'') (eo τ'') = extI (A (ss p)) (eo τ) →
          (e'' = ss p ∧ τ'' = τ) ∨ (e'' = e' ∧ τ'' = τ')) ∨
      (extI (A (ss p)) (eo τ) ∈ bdS ∧ ∀ e'' ∈ ss '' Iio m, ∀ τ'', extI (A e'') (eo τ'') = extI (A
        (ss p)) (eo τ) →
        e'' = ss p ∧ τ'' = τ) := by
  set k := chainAt ε p τ with hkdef
  have hat : ∀ q < m, ∀ τ', chainAt ε q τ' ≤ m := fun q hq τ' => by
    unfold chainAt
    split_ifs <;> omega
  have hkm : k ≤ m := hat p hp τ
  have hv : extI (A (ss p)) (eo τ) = ι (t k) := hex p hp τ
  rw [hv]
  have two : ∀ q₂ τ₂, q₂ < m → q₂ ≠ p → ι (t (chainAt ε q₂ τ₂)) = ι (t k) → ι (t k) ∉ bdS →
      (∀ q < m, ∀ τ'', ι (t (chainAt ε q τ'')) = ι (t k) → (q = p ∧ τ'' = τ) ∨ (q = q₂ ∧ τ'' = τ₂))
        →
      ∃ e' ∈ ss '' Iio m, ∃ τ', e' ≠ ss p ∧ extI (A e') (eo τ') = ι (t k) ∧ ι (t k) ∉ bdS ∧
        ∀ e'' ∈ ss '' Iio m, ∀ τ'', extI (A e'') (eo τ'') = ι (t k) → (e'' = ss p ∧ τ'' = τ) ∨ (e''
          = e' ∧ τ'' = τ') := by
    intro q₂ τ₂ h3 h4 h5 h6 h7
    refine ⟨ss q₂, ⟨q₂, h3, rfl⟩, τ₂, hinj q₂ h3 p hp h4, (hex q₂ h3 τ₂).trans h5, h6, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ τ'' h8
    rw [hex q hq τ''] at h8
    rcases h7 q hq τ'' h8 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
  have hreg : ∀ q < m, ∀ τ'', ι (t (chainAt ε q τ'')) = ι (t k) → chainAt ε q τ'' = k ∨
      (closed ∧ ((chainAt ε q τ'' = 0 ∧ k = m) ∨ (chainAt ε q τ'' = m ∧ k = 0))) := fun q hq τ'' h
        =>
    hk _ (hat q hq τ'') _ hkm h
  have hat1 : ∀ r, chainAt ε r (ε r) = r + 1 := fun r => by simp [chainAt]
  have hat2 : ∀ r, chainAt ε r (!ε r) = r := fun r => by simp [chainAt]
  by_cases hk0 : k = 0
  · have hsp := chainAt_split hkdef.symm
    obtain ⟨hp0, hτ⟩ : p = 0 ∧ τ = !ε p := by
      rcases hsp with h | h
      · exact ⟨h.1.trans hk0, h.2⟩
      · omega
    by_cases hcl : closed
    · left
      have hm2 := h2 hcl
      refine two (m - 1) (ε (m - 1)) (by omega) (by omega) ?_ (hb0 hcl k hkm) ?_
      · rw [hat1, show m - 1 + 1 = m by omega, hk0]
        exact (hclose hcl).symm
      · intro q hq τ'' h8
        rcases hreg q hq τ'' h8 with h9 | ⟨-, ⟨-, h9⟩ | ⟨h9, -⟩⟩
        · rcases chainAt_split (h9.trans hk0) with h10 | h10
          · left
            have hqp : q = p := by omega
            subst hqp
            exact ⟨rfl, h10.2.trans hτ.symm⟩
          · omega
        · omega
        · rcases chainAt_split h9 with h10 | h10
          · omega
          · right
            have : q = m - 1 := by omega
            subst this
            exact ⟨rfl, h10.2⟩
    · right
      refine ⟨hk0 ▸ (hb1 hcl).1, ?_⟩
      rintro _ ⟨q, hq, rfl⟩ τ'' h8
      rw [hex q hq τ''] at h8
      rcases hreg q hq τ'' h8 with h9 | ⟨hc, -⟩
      · rcases chainAt_split (h9.trans hk0) with h10 | h10
        · have hq0 : q = 0 := h10.1
          subst hq0
          subst hp0
          exact ⟨rfl, by rw [hτ]; exact h10.2⟩
        · omega
      · exact absurd hc hcl
  by_cases hkm' : k = m
  · have hsp := chainAt_split hkdef.symm
    obtain ⟨hp0, hτ⟩ : p + 1 = m ∧ τ = ε p := by
      rcases hsp with h | h
      · omega
      · exact ⟨h.1.trans hkm', h.2⟩
    by_cases hcl : closed
    · left
      have hm2 := h2 hcl
      refine two 0 (!ε 0) hm (by omega) ?_ (hb0 hcl k hkm) ?_
      · rw [hat2, hkm']
        exact hclose hcl
      · intro q hq τ'' h8
        rcases hreg q hq τ'' h8 with h9 | ⟨-, ⟨h9, -⟩ | ⟨-, h9⟩⟩
        · rcases chainAt_split (h9.trans hkm') with h10 | h10
          · omega
          · left
            have : q = p := by omega
            subst this
            exact ⟨rfl, h10.2.trans hτ.symm⟩
        · rcases chainAt_split h9 with h10 | h10
          · right
            have hq0 : q = 0 := h10.1
            subst hq0
            exact ⟨rfl, h10.2⟩
          · omega
        · omega
    · right
      refine ⟨hkm' ▸ (hb1 hcl).2.1, ?_⟩
      rintro _ ⟨q, hq, rfl⟩ τ'' h8
      rw [hex q hq τ''] at h8
      rcases hreg q hq τ'' h8 with h9 | ⟨hc, -⟩
      · rcases chainAt_split (h9.trans hkm') with h10 | h10
        · have := h10.1
          simp only [mem_Iio] at hq
          omega
        · have : q = p := by omega
          subst this
          exact ⟨rfl, h10.2.trans hτ.symm⟩
      · exact absurd hc hcl
  · left
    have hbv : ι (t k) ∉ bdS := by
      by_cases hcl : closed
      · exact hb0 hcl k hkm
      · exact (hb1 hcl).2.2 k (by omega) (by omega)
    have huni : ∀ q < m, ∀ τ'', ι (t (chainAt ε q τ'')) = ι (t k) → (q = k ∧ τ'' = !ε q) ∨ (q + 1
      = k ∧ τ'' = ε q) := by
      intro q hq τ'' h8
      rcases hreg q hq τ'' h8 with h9 | ⟨-, ⟨-, h9⟩ | ⟨-, h9⟩⟩
      · exact chainAt_split h9
      · omega
      · omega
    have hsp := chainAt_split hkdef.symm
    rcases hsp with ⟨hpk, hτ⟩ | ⟨hpk, hτ⟩
    · refine two (k - 1) (ε (k - 1)) (by omega) (by omega) ?_ hbv ?_
      · rw [hat1, show k - 1 + 1 = k by omega]
      · intro q hq τ'' h8
        rcases huni q hq τ'' h8 with h10 | h10
        · left
          have : q = p := by omega
          subst this
          exact ⟨rfl, h10.2.trans hτ.symm⟩
        · right
          have : q = k - 1 := by omega
          subst this
          exact ⟨rfl, h10.2⟩
    · refine two k (!ε k) (by omega) (by omega) ?_ hbv ?_
      · rw [hat2]
      · intro q hq τ'' h8
        rcases huni q hq τ'' h8 with h10 | h10
        · right
          have : q = k := by omega
          subst this
          exact ⟨rfl, h10.2⟩
        · left
          have : q = p := by omega
          subst this
          exact ⟨rfl, h10.2.trans hτ.symm⟩

theorem chain_hex {X : Type*} {A : Set X → 𝕀 → X} {ι : ℝ → X} {t : ℕ → ℝ} {ss : ℕ → Set X} {ε : ℕ
  → Bool} {p : ℕ}
    (h1 : ι (t p) = extI (A (ss p)) (if ε p then 0 else 1)) (h2 : ι (t (p + 1)) = extI (A (ss p))
      (if ε p then 1 else 0))
    (τ : Bool) : extI (A (ss p)) (eo τ) = ι (t (chainAt ε p τ)) := by
  unfold chainAt
  cases hε : ε p <;> cases τ <;> simp only [hε, eo] at h1 h2 ⊢ <;> simp_all

variable {S₁ : Type u} [TopologicalSpace S₁] [T2Space S₁]

/-- The words of a dissection of a connected surface. -/
theorem exists_word_edges (hS : IsSurface S₁) [ConnectedSpace S₁] {V : Set S₁} {E 𝓕 : Set (Set S₁)}
  (hd : IsDissection V E 𝓕) :
    ∃ (W : ℕ → List Letter) (f : ℕ × ℂ → S₁) (A : Set S₁ → 𝕀 → S₁) (lab : Set S₁
      → ℕ), WordEdges W f V E A lab ∧
      (Dsk W).Nonempty := by
  have hne : 𝓕.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨x⟩ : Nonempty S₁ := inferInstance
    have := hd.cover
    simp at this
    exact eq_empty_iff_forall_notMem.mp this.symm x (mem_univ _)
  obtain ⟨W, f, -, A, lab, h1, h2, h3, -, -, -, h7, h8, h9, h10, h11⟩
    := exists_family_edges hS.2.2 hd hne
  exact ⟨W, f, A, lab, ⟨h1, h11, h3, hd.graph, h7, h8, h9, h10⟩, ⟨(0, 0), h2, by simp⟩⟩

/-- A space presented by the cut word, in the universe of the surface. -/
theorem exists_cut_presented {W : ℕ → List Letter} (hW : FinW W) (hP : IsPaired W) (hne :
  (Dsk W).Nonempty) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (g : ℕ × ℂ → Y), Presents W g := by
  have := t2Space_wordSpace hW hP
  let e : WordSpace W ≃ₜ ULift.{u} (WordSpace W) := Homeomorph.ulift.symm
  exact ⟨ULift.{u} (WordSpace W), inferInstance, e.symm.isEmbedding.t2Space, _,
    presents_comp (presents_wordMap hne) e⟩

/-- Cutting along a chain of edges. -/
theorem exists_cut_of_chain {W : ℕ → List Letter} {f : ℕ × ℂ → S₁} {V : Set S₁} {E : Set
  (Set S₁)} {A : Set S₁ → 𝕀 → S₁}
    {lab : Set S₁ → ℕ} (h : WordEdges W f V E A lab) (hne : (Dsk W).Nonempty) {ι : ℝ
      → S₁} {m : ℕ} {t : ℕ → ℝ} {ss : ℕ → Set S₁}
    {ε : ℕ → Bool} (hs : ∀ p < m, ss p ∈ E ∧ ι (t p) = extI (A (ss p)) (if ε p then 0 else 1) ∧
      ι (t (p + 1)) = extI (A (ss p)) (if ε p then 1 else 0))
    (hinj : ∀ p < m, ∀ q < m, p ≠ q → ss p ≠ ss q) (hmid : ∀ p < m, edgeMid A (ss p) ∉ bd S₁)
      (closed : Prop)
    (hk : ∀ k ≤ m, ∀ k' ≤ m, ι (t k) = ι (t k') → k = k' ∨ (closed ∧ ((k = 0 ∧ k' = m) ∨ (k = m
      ∧ k' = 0))))
    (h2 : closed → 2 ≤ m) (hm : 0 < m) (hb0 : closed → ∀ k ≤ m, ι (t k) ∉ bd S₁)
    (hb1 : ¬ closed → ι (t 0) ∈ bd S₁ ∧ ι (t m) ∈ bd S₁ ∧ ∀ k, 0 < k → k < m → ι (t k) ∉ bd S₁)
    (hclose : closed → ι (t 0) = ι (t m)) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S₁), Continuous ψ
      ∧ Function.Surjective ψ ∧
      InjOn ψ (ψ ⁻¹' (⋃₀ (ss '' Iio m))ᶜ) ∧ ψ ⁻¹' (⋃₀ (ss '' Iio m)) ⊆ bd Y ∧ IsSurface Y ∧
      ∀ p < m, ∃ X X', LiftPair ψ (ss p) (ι (t p)) (ι (t (p + 1))) X X' := by
  classical
  have hDE : ss '' Iio m ⊆ E := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hs p hp).1
  have hsd : ∀ e ∈ ss '' Iio m, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂
    := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, p', j, q, e₁, e₂, h1, h2, h3⟩ := h.exists_sides (hs p hp).1 (hmid p hp)
    exact ⟨i, p', j, q, e₁, e₂, h1, h2, h3⟩
  obtain ⟨Y, tY, t2, g, hg⟩ := exists_cut_presented.{u} (W := cutW W (lab '' (ss '' Iio m)))
    (finW_cut h.fin)
    (isPaired_cut h.paired) (by rw [dsk_cut]; exact hne)
  obtain ⟨ψ, h1, h3, h4, h5, h6, h7⟩ := h.cut_space hDE hsd (fun e he τ => by
    obtain ⟨p, hp, rfl⟩ := he
    exact chain_cases (A := A) (bdS := bd S₁) (ι := ι) (m := m) (t := t) (ss := ss) (ε := ε)
      (fun q hq τ => chain_hex (hs q hq).2.1 (hs q hq).2.2 τ) hinj closed hk h2 hm hb0 hb1 hclose
        hp τ) hg
  refine ⟨Y, tY, t2, ψ, h1, h3, h4, h5, h6, fun p hp => ?_⟩
  obtain ⟨X, X', hX⟩ := h7 (ss p) ⟨p, hp, rfl⟩
  have hv0 : extI (A (ss p)) 0 = extI (A (ss p)) (eo false) := by simp [eo]
  have hv1 : extI (A (ss p)) 1 = extI (A (ss p)) (eo true) := by simp [eo]
  have e0 := (hs p hp).2.1
  have e1 := (hs p hp).2.2
  cases hε : ε p
  · rw [hε] at e0 e1
    simp only [Bool.false_eq_true, ite_false] at e0 e1
    rw [e0, e1]
    exact ⟨X, X', hX.swap⟩
  · rw [hε] at e0 e1
    simp only [ite_true] at e0 e1
    rw [e0, e1]
    exact ⟨X, X', hX⟩

theorem chain_mono {t : ℕ → ℝ} {m : ℕ} (hlt : ∀ p < m, t p < t (p + 1)) {k k' : ℕ} (h : k < k')
  (hk : k' ≤ m) : t k < t k' := by
  induction k', h using Nat.le_induction with
  | base => exact hlt k (by omega)
  | succ q hq ih => exact (ih (by omega)).trans (hlt q (by omega))

theorem chain_mono' {t : ℕ → ℝ} {m : ℕ} (hlt : ∀ p < m, t p < t (p + 1)) {k k' : ℕ} (h : k ≤ k')
  (hk : k' ≤ m) : t k ≤ t k' := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (chain_mono hlt h hk).le

omit [TopologicalSpace S₁] [T2Space S₁] in
/-- The lifts of the edges of a chain fit together. -/
theorem chain_fold {S' : Type u} [TopologicalSpace S'] [T2Space S'] {ψ : S' → S₁} {ι : ℝ
  → S₁} {t : ℕ → ℝ} {ss : ℕ → Set S₁}
    {m : ℕ} (hlt : ∀ p < m, t p < t (p + 1)) (h0 : t 0 = 0) (hss : ∀ p < m, ss p = ι '' Icc (t p)
      (t (p + 1)))
    (hlift : ∀ p < m, ∃ X X', LiftPair ψ (ss p) (ι (t p)) (ι (t (p + 1))) X X') {n : ℕ}
      (hn : 0 < n) (hnm : n ≤ m)
    (hι : InjOn ι (Icc 0 (t n))) : ∃ X X', LiftPair ψ (ι '' Icc 0 (t n)) (ι 0) (ι (t n)) X X' := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨X, X', hX⟩ := hlift 0 (by omega)
    rw [hss 0 (by omega), h0] at hX
    exact ⟨X, X', hX⟩
  | succ n hn ih =>
    have hnm' : n + 1 ≤ m := hnm
    have hstep := hlt n (by omega)
    have h1 : 0 ≤ t n := by
      have := chain_mono' hlt (Nat.zero_le n) (by omega)
      rwa [h0] at this
    have hsub : Icc 0 (t n) ⊆ Icc 0 (t (n + 1)) := Icc_subset_Icc_right hstep.le
    obtain ⟨X₁, Y₁, h2⟩ := ih (by omega) (hι.mono hsub)
    obtain ⟨X₂, Y₂, h3⟩ := hlift n (by omega)
    rw [hss n (by omega)] at h3
    have hi : ι '' Icc 0 (t n) ∩ ι '' Icc (t n) (t (n + 1)) = {ι (t n)} := by
      ext z
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, he⟩⟩
        have h4 : y = x := hι ⟨h1.trans hy.1, hy.2⟩ (hsub hx) he
        have h5 : x = t n := le_antisymm hx.2 (h4 ▸ hy.1)
        rw [h5]
        rfl
      · rintro rfl
        exact ⟨⟨_, ⟨h1, le_rfl⟩, rfl⟩, ⟨_, ⟨le_rfl, hstep.le⟩, rfl⟩⟩
    have hc := (h3.ncard (x := ι (t n)) ⟨_, ⟨le_rfl, hstep.le⟩, rfl⟩).1
    obtain ⟨X, X', hX⟩ := h2.join h3 hi hc.le
    rw [← image_union, Icc_union_Icc_eq_Icc h1 hstep.le] at hX
    exact ⟨X, X', hX⟩

/-- Cutting a connected surface along a proper `I`-arc, by cutting the word of a dissection. -/
theorem exists_cut_arc (hS : IsSurface S₁) [ConnectedSpace S₁] {F : Set S₁} {s t : S₁}
  (hne : s ≠ t) (hF : F ∩ bd S₁ = {s, t})
    (hl : IsLineWithEnds F s t) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S₁), IsSurface Y
      ∧ IsCutting ψ F ∧
      ∃ X X', LiftPair ψ F s t X X' := by
  classical
  have hs : s ∈ bd S₁ := (show s ∈ F ∩ bd S₁ from hF ▸ mem_insert _ _).2
  have ht : t ∈ bd S₁ := (show t ∈ F ∩ bd S₁ from hF ▸ mem_insert_of_mem _ rfl).2
  obtain ⟨V₁, E₁, hg, hV, hgr⟩ := exists_cuff_graph hS
  obtain ⟨E₂, hg2, hgr2, hs2⟩ := hg.add_point s
  obtain ⟨E₃, hg3, hgr3, hs3⟩ := hg2.add_point t
  have hgr1 : gr V₁ E₁ = bd S₁ := by
    rw [← hgr]
    exact union_eq_right.mpr hV
  have hgall : gr (insert t (insert s V₁)) E₃ = bd S₁ := by
    rw [hgr3, hgr2, hgr1, insert_eq_of_mem hs, insert_eq_of_mem ht]
  obtain ⟨hg4, hgr4⟩ := hg3.add_arc hne hl (mem_insert_of_mem _ (mem_insert _ _)) (mem_insert _ _)
    (by rw [hgall, hF])
  have hE₃ : ⋃₀ E₃ = bd S₁ := by
    apply subset_antisymm
    · rw [← hgall]
      exact subset_union_right
    · rw [← hgr]
      exact hs2.trans hs3
  have hE₀ : ⋃₀ insert F E₃ = bd S₁ ∪ F := by
    rw [sUnion_insert, hE₃, union_comm]
  have hfin := (cuff_statement.{u} S₁ hS).2.1
  have hO := (cuff_statement.{u} S₁ hS).2.2
  have hV₀ : insert t (insert s V₁) ⊆ ⋃₀ insert F E₃ := by
    rw [hE₀]
    rintro z (rfl | rfl | hz)
    · exact .inl ht
    · exact .inl hs
    · exact .inl (hgr ▸ hV hz)
  obtain ⟨V, E, 𝓕, hd, hVV, hEE⟩ := exists_dissection_with hS hg4 hV₀ hfin hO subset_rfl
    (.inr ⟨F, s, t, by rw [hE₀, sUnion_cuffs], hl, hne, by rwa [sUnion_cuffs], by rwa
      [sUnion_cuffs]⟩)
  obtain ⟨W, f, A, lab, hw, hdn⟩ := exists_word_edges hS hd
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hιc := continuous_extI ha.1
  have hinj := extI_injOn ha.2
  have hval0 : extI a 0 = a 0 := extI_coe a 0
  have hval1 : extI a 1 = a 1 := extI_coe a 1
  have himg : extI a '' Icc 0 1 = range a := image_extI a
  have hFg : range a ⊆ gr V E := fun z hz => hEE (hE₀ ▸ .inr hz)
  have hstart : extI a 0 ∈ V := by
    rw [hval0]
    exact hVV (mem_insert_of_mem _ (mem_insert _ _))
  have hfinish : extI a 1 ∈ V := by
    rw [hval1]
    exact hVV (mem_insert _ _)
  obtain ⟨m, τ, ss, ε, hm, ht0, htm, hlt, -, hch, hsne⟩ := exists_chain hw.graph A hw.arc hιc
    (hinj.mono Ico_subset_Icc_self) (hinj.mono Ioc_subset_Icc_self) (himg ▸ hFg) hstart hfinish
    (.inl (by rw [hval0, hval1]; exact hne))
  have hτI : ∀ k ≤ m, τ k ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨ht0 ▸ chain_mono' hlt (Nat.zero_le k) hk, htm ▸ chain_mono' hlt hk le_rfl⟩
  have hιk : ∀ k ≤ m, ∀ k' ≤ m, extI a (τ k) = extI a (τ k') → k = k' := fun k hk k' hk' he => by
    have h1 := hinj (hτI k hk) (hτI k' hk') he
    rcases lt_trichotomy k k' with h2 | h2 | h2
    · exact absurd h1 (chain_mono hlt h2 hk').ne
    · exact h2
    · exact absurd h1 (chain_mono hlt h2 hk).ne'
  have hsF : ∀ p < m, ss p ⊆ range a := fun p hp => by
    rw [← (hch p hp).2.1, ← himg]
    exact image_mono (Icc_subset_Icc (hτI p hp.le).1 (hτI (p + 1) hp).2)
  have hmid : ∀ p < m, edgeMid A (ss p) ∉ bd S₁ := fun p hp hb => by
    have hmem : edgeMid A (ss p) ∈ range a ∩ bd S₁ := ⟨hsF p hp (hw.extI_mem (hch p hp).1 _), hb⟩
    rw [hF] at hmem
    have hVm : edgeMid A (ss p) ∈ V := by
      rcases hmem with h | h
      · exact h ▸ hVV (mem_insert_of_mem _ (mem_insert _ _))
      · exact h ▸ hVV (mem_insert _ _)
    exact hw.extI_notMem (hch p hp).1 (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) hVm
  obtain ⟨Y, tY, t2, ψ, h1, h2, h3, h4, h5, h6⟩ := exists_cut_of_chain hw hdn (ι := extI a) (m
    := m) (t := τ) (ss := ss)
    (ε := ε) (fun p hp => ⟨(hch p hp).1, (hch p hp).2.2⟩) hsne hmid False
    (fun k hk k' hk' he => .inl (hιk k hk k' hk' he)) (fun h => h.elim) hm (fun h => h.elim)
    (fun _ => ⟨by rw [ht0, hval0]; exact hs, by rw [htm, hval1]; exact ht, fun k hk0 hkm hb => by
      have hmem : extI a (τ k) ∈ range a ∩ bd S₁ := ⟨⟨_, rfl⟩, hb⟩
      rw [hF] at hmem
      rcases hmem with h | h
      · have := hιk k hkm.le 0 (Nat.zero_le _) (by rw [ht0, hval0]; exact h)
        omega
      · have := hιk k hkm.le m le_rfl (by rw [htm, hval1]; exact h)
        omega⟩) (fun h => h.elim)
  obtain ⟨X, X', hX⟩ := chain_fold (ψ := ψ) hlt ht0 (fun p hp => (hch p hp).2.1.symm) h6 hm le_rfl
    (by rw [htm]; exact hinj)
  rw [htm, himg, hval0, hval1] at hX
  have hun : ⋃₀ (ss '' Iio m) = range a := by
    apply subset_antisymm
    · rintro z ⟨_, ⟨p, hp, rfl⟩, hz⟩
      exact hsF p hp hz
    · have key : ∀ k, k ≤ m → extI a '' Icc 0 (τ k) ⊆ ⋃₀ (ss '' Iio m) := by
        intro k
        induction k with
        | zero =>
          intro _ z hz
          obtain ⟨x, hx, rfl⟩ := hz
          rw [ht0] at hx
          have hx0 : x = 0 := le_antisymm hx.2 hx.1
          refine ⟨ss 0, ⟨0, hm, rfl⟩, ?_⟩
          rw [← (hch 0 hm).2.1, ht0]
          exact ⟨x, ⟨hx.1, by rw [hx0]; exact (ht0 ▸ hlt 0 hm).le⟩, rfl⟩
        | succ k ih =>
          intro hk z hz
          obtain ⟨x, hx, rfl⟩ := hz
          by_cases hxk : x ≤ τ k
          · exact ih (by omega) ⟨x, ⟨hx.1, hxk⟩, rfl⟩
          · refine ⟨ss k, ⟨k, by simpa using hk, rfl⟩, ?_⟩
            rw [← (hch k (by omega)).2.1]
            exact ⟨x, ⟨(not_le.mp hxk).le, hx.2⟩, rfl⟩
      have := key m le_rfl
      rw [htm, himg] at this
      exact this
  rw [hun] at h3 h4
  exact ⟨Y, tY, t2, ψ, h5, ⟨h1, h2, h3, fun x hx => (hX.ncard hx).2, h4⟩, X, X', hX⟩

/-- Cutting a connected surface along an `O`-arc off the boundary, by cutting the word of a
dissection. -/
theorem exists_cut_loop (hS : IsSurface S₁) [ConnectedSpace S₁] {F : Set S₁} (hO : IsOArc F)
  (hd : Disjoint F (bd S₁)) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S₁), IsSurface Y
      ∧ IsCutting ψ F ∧
      ((∃ X X', Disjoint X X' ∧ X ∪ X' = ψ ⁻¹' F ∧ IsOArc X ∧ IsOArc X' ∧ BijOn ψ X F
        ∧ BijOn ψ X' F) ∨ IsOArc (ψ ⁻¹' F)) ∧
      ∃ Z₁ Z₂ u c X₁ Y₁ X₂ Y₂, LiftPair ψ Z₁ u c X₁ Y₁ ∧ LiftPair ψ Z₂ c u X₂ Y₂ ∧ Z₁ ∩ Z₂ = {u, c}
        ∧ Z₁ ∪ Z₂ = F ∧ u ≠ c ∧
        (ψ ⁻¹' {u}).encard ≤ 2 ∧ (ψ ⁻¹' {c}).encard ≤ 2 := by
  classical
  obtain ⟨V₁, E₁, hg, hV, hgr⟩ := exists_cuff_graph hS
  have hgr1 : gr V₁ E₁ = bd S₁ := by
    rw [← hgr]
    exact union_eq_right.mpr hV
  have hconn : FinConn (F \ gr V₁ E₁) := by
    rw [hgr1, hd.sdiff_eq_left]
    exact ⟨{F}, finite_singleton _, fun J hJ => by
      rw [mem_singleton_iff.mp hJ]
      exact hO.isPreconnected, sUnion_singleton _⟩
  obtain ⟨V₂, E₂, hV₂, hg2, hgr2, hno⟩ := hg.add_curve hO hconn
  have hno2 := hno hV
  obtain ⟨x, y, -, hx, hy, -, hxy, -, -⟩ := hO.exists_three
  obtain ⟨E₃, hg3, hgr3, hs3⟩ := hg2.add_point x
  obtain ⟨E₄, hg4, hgr4, hs4⟩ := hg3.add_point y
  have hE₂ : ⋃₀ E₂ = bd S₁ ∪ F := by
    rw [← hgr1, ← hgr2]
    exact (union_eq_right.mpr hno2).symm
  have hgall : gr (insert y (insert x V₂)) E₄ = bd S₁ ∪ F := by
    rw [hgr4, hgr3, hgr2, hgr1, insert_eq_of_mem (a := x) (Or.inr hx : x ∈ bd S₁ ∪ F),
      insert_eq_of_mem (a := y) (Or.inr hy : y ∈ bd S₁ ∪ F)]
  have hE₄ : ⋃₀ E₄ = bd S₁ ∪ F := by
    apply subset_antisymm
    · rw [← hgall]
      exact subset_union_right
    · rw [← hE₂]
      exact hs3.trans hs4
  have hfin := (cuff_statement.{u} S₁ hS).2.1
  have hOc := (cuff_statement.{u} S₁ hS).2.2
  have hV₀ : insert y (insert x V₂) ⊆ ⋃₀ E₄ := by
    rw [hE₄]
    rintro z (rfl | rfl | hz)
    · exact .inr hy
    · exact .inr hx
    · rw [← hE₂]
      exact hno2 hz
  have hsA : ⋃₀ insert F (cuffs S₁) = bd S₁ ∪ F := by
    rw [sUnion_insert, sUnion_cuffs, union_comm]
  obtain ⟨V, E, 𝓕, hdis, hVV, hEE⟩ := exists_dissection_with hS hg4 hV₀ (hfin.insert F)
    (fun C hC => hC.elim (fun h => h ▸ hO) (hOc C)) (subset_insert _ _) (.inl (by rw [hE₄, hsA]))
  obtain ⟨W, f, A, lab, hw, hdn⟩ := exists_word_edges hS hdis
  obtain ⟨ι, hιc, hι0, hι1, hinj, hinj', hιim⟩ := hO.exists_iota hx
  have hxV : x ∈ V := hVV (mem_insert_of_mem _ (mem_insert _ _))
  have hyV : y ∈ V := hVV (mem_insert _ _)
  have hIcc : ι '' Icc 0 1 = F := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_or_lt_of_le hz.2 with rfl | h1
      · rw [hι1]
        exact hx
      · exact hιim ▸ mem_image_of_mem ι ⟨hz.1, h1⟩
    · exact hιim ▸ image_mono Ico_subset_Icc_self
  obtain ⟨x₀, hx₀, hx₀y⟩ : ∃ x₀ ∈ Ioo (0 : ℝ) 1, ι x₀ = y := by
    have hy' : y ∈ ι '' Ico 0 1 := hιim ▸ hy
    obtain ⟨z, hz, rfl⟩ := hy'
    refine ⟨z, ⟨lt_of_le_of_ne hz.1 ?_, hz.2⟩, rfl⟩
    rintro rfl
    exact hxy (hι0.symm)
  have hFg : ι '' Icc 0 1 ⊆ gr V E := fun z hz => hEE (by
    rw [hE₄]
    exact .inr (hIcc ▸ hz))
  obtain ⟨m, τ, ss, ε, hm, ht0, htm, hlt, hsort, hch, hsne⟩ := exists_chain hw.graph A hw.arc hιc
    hinj hinj' hFg
    (by rw [hι0]; exact hxV) (by rw [hι1]; exact hxV) (.inr ⟨x₀, hx₀, hx₀y ▸ hyV⟩)
  have hm2 : 2 ≤ m := by
    obtain ⟨p, hp, hx₁⟩ := hsort x₀ ⟨hx₀.1.le, hx₀.2.le⟩ (hx₀y ▸ hyV)
    by_contra hc
    have hm1 : m = 1 := by omega
    subst hm1
    interval_cases p
    · linarith [hx₀.1]
    · linarith [hx₀.2]
  have hτI : ∀ k ≤ m, τ k ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨ht0 ▸ chain_mono' hlt (Nat.zero_le k) hk, htm ▸ chain_mono' hlt hk le_rfl⟩
  have hτlt : ∀ k < m, τ k < 1 := fun k hk => htm ▸ chain_mono hlt hk le_rfl
  have hτpos : ∀ k, 0 < k → k ≤ m → 0 < τ k := fun k h0 hk => ht0 ▸ chain_mono hlt h0 hk
  have hne : ∀ k k', k < k' → k' ≤ m → τ k ≠ τ k' := fun k k' h hk => (chain_mono hlt h hk).ne
  have hιk : ∀ k ≤ m, ∀ k' ≤ m, ι (τ k) = ι (τ k') → k = k' ∨ (True ∧ ((k = 0 ∧ k' = m) ∨ (k = m
    ∧ k' = 0))) := by
    intro k hk k' hk' he
    by_cases h1 : k < m ∧ k' < m
    · have h2 := hinj ⟨(hτI k hk).1, hτlt k h1.1⟩ ⟨(hτI k' hk').1, hτlt k' h1.2⟩ he
      rcases lt_trichotomy k k' with h3 | h3 | h3
      · exact absurd h2 (hne k k' h3 hk')
      · exact .inl h3
      · exact absurd h2.symm (hne k' k h3 hk)
    by_cases h4 : 0 < k ∧ 0 < k'
    · have h2 := hinj' ⟨hτpos k h4.1 hk, (hτI k hk).2⟩ ⟨hτpos k' h4.2 hk', (hτI k' hk').2⟩ he
      rcases lt_trichotomy k k' with h3 | h3 | h3
      · exact absurd h2 (hne k k' h3 hk')
      · exact .inl h3
      · exact absurd h2.symm (hne k' k h3 hk)
    · have h5 : k = m ∨ k' = m := by omega
      have h6 : k = 0 ∨ k' = 0 := by omega
      rcases h5 with h5 | h5 <;> rcases h6 with h6 | h6
      · omega
      · exact .inr ⟨trivial, .inr ⟨h5, h6⟩⟩
      · exact .inr ⟨trivial, .inl ⟨h6, h5⟩⟩
      · omega
  have hsF : ∀ p < m, ss p ⊆ F := fun p hp => by
    rw [← (hch p hp).2.1, ← hIcc]
    exact image_mono (Icc_subset_Icc (hτI p hp.le).1 (hτI (p + 1) hp).2)
  have hmid : ∀ p < m, edgeMid A (ss p) ∉ bd S₁ := fun p hp hb =>
    Set.disjoint_left.mp hd (hsF p hp (hw.extI_mem (hch p hp).1 _)) hb
  have hιF : ∀ k ≤ m, ι (τ k) ∈ F := fun k hk => hIcc ▸ mem_image_of_mem ι (hτI k hk)
  obtain ⟨Y, tY, t2, ψ, h1, h2, h3, h4, h5, h6⟩ := exists_cut_of_chain hw hdn (ι := ι) (m := m) (t
    := τ) (ss := ss)
    (ε := ε) (fun p hp => ⟨(hch p hp).1, (hch p hp).2.2⟩) hsne hmid True hιk (fun _ => hm2) hm
    (fun _ k hk hb => Set.disjoint_left.mp hd (hιF k hk) hb) (fun h => absurd trivial h)
    (fun _ => by rw [ht0, htm, hι0, hι1])
  have hn : 0 < m - 1 := by omega
  have hn1 : m - 1 + 1 = m := by omega
  have hsub : Icc 0 (τ (m - 1)) ⊆ Ico (0 : ℝ) 1 := fun z hz => ⟨hz.1, hz.2.trans_lt (hτlt _
    (by omega))⟩
  obtain ⟨X₁, Y₁, h7⟩ := chain_fold (ψ := ψ) hlt ht0 (fun p hp => (hch p hp).2.1.symm) h6 hn
    (by omega) (hinj.mono hsub)
  obtain ⟨X₂, Y₂, h8⟩ := h6 (m - 1) (by omega)
  rw [hn1, htm, hι1, ← hι0, ← (hch (m - 1) (by omega)).2.1, hn1, htm] at h8
  have hc0 : 0 < τ (m - 1) := hτpos _ hn (by omega)
  have hc1 : τ (m - 1) < 1 := hτlt _ (by omega)
  have hi : ι '' Icc 0 (τ (m - 1)) ∩ ι '' Icc (τ (m - 1)) 1 = {ι 0, ι (τ (m - 1))} := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨w, hw', he⟩⟩
      rcases eq_or_lt_of_le hw'.2 with rfl | hw1
      · have h9 : ι u = ι 0 := by rw [← he, hι1, hι0]
        have : u = 0 := hinj ⟨hu.1, hu.2.trans_lt hc1⟩ ⟨le_rfl, zero_lt_one⟩ h9
        rw [this]
        exact .inl rfl
      · have h9 : w = u := hinj ⟨hc0.le.trans hw'.1, hw1⟩ ⟨hu.1, hu.2.trans_lt hc1⟩ he
        have : u = τ (m - 1) := le_antisymm hu.2 (h9 ▸ hw'.1)
        rw [this]
        exact .inr rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, hc0.le⟩, rfl⟩, ⟨1, ⟨hc1.le, le_rfl⟩, by rw [hι0, hι1]⟩⟩
      · exact ⟨⟨_, ⟨hc0.le, le_rfl⟩, rfl⟩, ⟨_, ⟨le_rfl, hc1.le⟩, rfl⟩⟩
  have hun : ι '' Icc 0 (τ (m - 1)) ∪ ι '' Icc (τ (m - 1)) 1 = F := by
    rw [← image_union, Icc_union_Icc_eq_Icc hc0.le hc1.le, hIcc]
  have huc : ι 0 ≠ ι (τ (m - 1)) := fun he => by
    have := hinj ⟨le_rfl, zero_lt_one⟩ ⟨hc0.le, hc1⟩ he
    exact hc0.ne this
  have hfu := (h8.ncard (x := ι 0) ⟨1, ⟨hc1.le, le_rfl⟩, by rw [hι0, hι1]⟩).1
  have hfc := (h8.ncard (x := ι (τ (m - 1))) ⟨_, ⟨le_rfl, hc1.le⟩, rfl⟩).1
  have hclose := h7.close h8 hi huc hfu.le hfc.le
  rw [hun] at hclose
  have hsu : ⋃₀ (ss '' Iio m) = F := by
    apply subset_antisymm
    · rintro z ⟨_, ⟨p, hp, rfl⟩, hz⟩
      exact hsF p hp hz
    · have key : ∀ k, k ≤ m → ι '' Icc 0 (τ k) ⊆ ⋃₀ (ss '' Iio m) := by
        intro k
        induction k with
        | zero =>
          intro _ z hz
          obtain ⟨u, hu, rfl⟩ := hz
          rw [ht0] at hu
          have hx0 : u = 0 := le_antisymm hu.2 hu.1
          refine ⟨ss 0, ⟨0, hm, rfl⟩, ?_⟩
          rw [← (hch 0 hm).2.1, ht0]
          exact ⟨u, ⟨hu.1, by rw [hx0]; exact (ht0 ▸ hlt 0 hm).le⟩, rfl⟩
        | succ k ih =>
          intro hk z hz
          obtain ⟨u, hu, rfl⟩ := hz
          by_cases hxk : u ≤ τ k
          · exact ih (by omega) ⟨u, ⟨hu.1, hxk⟩, rfl⟩
          · refine ⟨ss k, ⟨k, by simpa using hk, rfl⟩, ?_⟩
            rw [← (hch k (by omega)).2.1]
            exact ⟨u, ⟨(not_le.mp hxk).le, hu.2⟩, rfl⟩
      have := key m le_rfl
      rw [htm, hIcc] at this
      exact this
  rw [hsu] at h3 h4
  have hcount : ∀ z ∈ F, (ψ ⁻¹' {z}).ncard = 2 := by
    intro z hz
    rw [← hun] at hz
    rcases hz with hz | hz
    · exact (h7.ncard hz).2
    · exact (h8.ncard hz).2
  exact ⟨Y, tY, t2, ψ, h5, ⟨h1, h2, h3, hcount, h4⟩, hclose, _, _, _, _, _, _, _, _, h7, h8, hi,
    hun, huc, hfu.le, hfc.le⟩

end GraphMinor.Surface
