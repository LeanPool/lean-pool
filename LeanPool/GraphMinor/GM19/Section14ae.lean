/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14ad
public import LeanPool.GraphMinor.GM19.SideScheme

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, Section 14: the sequence in `Σ'`

Suppose that all the paintings of a sequence have the same frame `Φ'` and the same data at the
singular places, and that the sectors at the singular places increase along the sequence.
Then the condition `S₂` gives a linear inflation between two of the paintings `Γ'`, and so an
outline. This is the last step of the proof of (14.1) in the paper.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The order of the colours of the long sides. Each colour stands for a sector of one of the
paintings, and two sectors are comparable if they have the same code. -/
theorem exists_colOrder {I : Type} [Countable I] [Infinite α] {β : Type*} {τ : Type*} {Ω :
  QuasiOrder β} (hΩ : Ω.IsWQO) (R : Set I) (cod : I → τ) (val : I → β) {C : Set τ} (hC : C.Finite)
    (hc : ∀ x ∈ R, cod x ∈ C) (hv : ∀ x ∈ R, val x ∈ Ω.E) :
    ∃ (enc : I → α) (Ωc : QuasiOrder α), Ωc.IsWQO ∧ (∀ x ∈ R, enc x ∈ Ωc.E) ∧ ∀ x y, Ωc.le (enc x)
      (enc y) → cod y = cod x ∧ Ω.le (val x) (val y) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_nat I
  let enc : I → α := fun x ↦ Infinite.natEmbedding α (f x)
  have hinj : Function.Injective enc := (Infinite.natEmbedding α).injective.comp hf
  let Ωc : QuasiOrder α :=
    { E := enc '' R
      le := fun a b ↦ ∃ x y, a = enc x ∧ b = enc y ∧ cod y = cod x ∧ Ω.le (val x) (val y)
      refl := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, x, rfl, rfl, rfl, Ω.refl _ (hv x hx)⟩
      trans := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ ⟨x₁, y₁, e₁, e₂, h₁, h₂⟩ ⟨y₂, z₂, e₃,
          e₄, h₃, h₄⟩
        obtain rfl := hinj e₁
        obtain rfl := hinj e₂
        obtain rfl := hinj e₃
        obtain rfl := hinj e₄
        exact ⟨x, z, rfl, rfl, h₃.trans h₁, Ω.trans _ (hv x hx) _ (hv y hy) _ (hv z hz) h₂ h₄⟩ }
  refine ⟨enc, Ωc, ?_, fun x hx ↦ ⟨x, hx, rfl⟩, ?_⟩
  · intro g hg
    choose x hx hxg using hg
    have := hC.to_subtype
    obtain ⟨c, hci⟩ := Finite.exists_infinite_fiber (fun i ↦ (⟨cod (x i), hc _ (hx i)⟩ : ↥C))
    have hI : ({i | (⟨cod (x i), hc _ (hx i)⟩ : ↥C) = c} : Set ℕ).Infinite
      := Set.infinite_coe_iff.mp hci
    obtain ⟨i, hi, j, hj, hij, hle⟩ := hΩ.exists_pair (f := fun i ↦ val (x i)) hI fun i _ ↦ hv _
      (hx i)
    have hcod : cod (x j) = cod (x i) := congrArg Subtype.val (show _ = _ from (hj.trans
      (Eq.symm hi)))
    exact ⟨i, j, hij, x i, x j, (hxg i).symm, (hxg j).symm, hcod, hle⟩
  · rintro x y ⟨x₁, y₁, e₁, e₂, h₁, h₂⟩
    obtain rfl := hinj e₁
    obtain rfl := hinj e₂
    exact ⟨h₁, h₂⟩

omit [T2Space S] in
/-- The orders of `χ'` on the internal edges. The order `Ω(k)` loses the elements above `ω₀`. -/
theorem exists_orders (χ : ColourScheme S α) {k : ℕ} {ω₀ : α} (h : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3
  ∧ ω₀ ∈ χ.Ω3.E)) :
    ∃ Ω2' Ω3' : QuasiOrder α, Ω2'.IsWQO ∧ Ω3'.IsWQO ∧ Ω3'.IsSubIdeal χ.Ω3 ∧ Ω2'.IsSubIdeal χ.Ω2 ∧
      (Ω3'.IsStrictSubIdeal χ.Ω3 ∨ Ω2'.IsStrictSubIdeal χ.Ω2) ∧
      (∀ c ∈ χ.Ω2.E, ¬ χ.unionLE ω₀ c → c ∈ Ω2'.E) ∧ ∀ c ∈ χ.Ω3.E, ¬ χ.unionLE ω₀ c → c ∈ Ω3'.E
        := by
  have hrefl : ∀ Ω : QuasiOrder α, Ω.IsSubIdeal Ω := fun Ω ↦ ⟨subset_rfl, fun _ _ _ hx _ ↦ hx, fun
    _ _ _ _ ↦ Iff.rfl⟩
  rcases h with ⟨-, hw⟩ | ⟨-, hw⟩
  · have hs := QuasiOrder.isStrictSubIdeal_withoutAbove hw
    exact ⟨_, χ.Ω3, QuasiOrder.isWQO_withoutAbove χ.isWQO_2 ω₀, χ.isWQO_3, hrefl _, hs.1,
      .inr hs, fun c hc hn ↦ ⟨hc, fun hle ↦ hn (.inl ⟨hw, hc, hle⟩)⟩, fun _ hc _ ↦ hc⟩
  · have hs := QuasiOrder.isStrictSubIdeal_withoutAbove hw
    exact ⟨χ.Ω2, _, χ.isWQO_2, QuasiOrder.isWQO_withoutAbove χ.isWQO_3 ω₀, hs.1, hrefl _,
      .inl hs, fun _ hc _ ↦ hc, fun c hc hn ↦ ⟨hc, fun hle ↦ hn (.inr (.inl ⟨hw, hc, hle⟩))⟩⟩

/-- The paintings of the sequence, with all that they have in common. -/
structure Family {T : Set S} [Nonempty ↥Tᶜ] (D : ℕ → TangleDatum cap χ) (s : ∀ i, Slice T (D i))
  (N Z : Set ↥Tᶜ) (ε : Set ↥Tᶜ → Bool) (t : ↥Tᶜ → Option ZData) {β : Type*} (Ω : QuasiOrder β)
    (ξ : ∀ i, Arm (D i).P.Γ → β) (ω₀ : α) (b : ℕ) (𝒮 : Set (ColouredPainting χ)) : Prop where
  hN : ∀ i, (s i).markN = N
  hZ : ∀ i, (s i).markZ = Z
  hε : ∀ i, ∀ C ∈ cuffs ↥Tᶜ, ε C = (s i).cuffDir C
  ht : ∀ i, ∀ z ∈ Z, (s i).ztag z = t z
  hb : ∀ i W, ((s i).fr W).ρ ≤ b
  hcov : ∀ i, ∀ e ∈ (D i).Γ.E, χ.unionLE ω₀ ((D i).P.φ e) → ∃ W ∈ (s i).𝒲, cap.emb '' e ⊆ W
  hξ : ∀ i, ∀ A ∈ (coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj (s i).fr).arms, ξ i A ∈ Ω.E
  mono : ∀ i j, i < j → ∀ W p, p ∈ (s i).sing W → ∀ W' q, q ∈ (s j).sing W' → (s i).zx W p =
    (s j).zx W' q →
    Ω.le (ξ i (((s i).fr W).secArm p)) (ξ j (((s j).fr W').secArm q)) ∧
      ∀ (hc : ((s i).fr W).H.V.ncard ≠ 1) (hc' : ((s j).fr W').H.V.ncard ≠ 1), Ω.le (ξ i
        (((s i).fr W).hubArm hc)) (ξ j (((s j).fr W').hubArm hc'))
  hm : ∀ i, (D i).P ∈ 𝒮

namespace Family

variable {T : Set S} [Nonempty ↥Tᶜ] {D : ℕ → TangleDatum cap χ} {s : ∀ i, Slice T
  (D i)} {N Z : Set ↥Tᶜ} {ε : Set ↥Tᶜ → Bool} {t : ↥Tᶜ → Option ZData} {β : Type*} {Ω : QuasiOrder
    β}
    {ξ : ∀ i, Arm (D i).P.Γ → β} {ω₀ : α} {b : ℕ} {𝒮 : Set (ColouredPainting χ)}

theorem internal_of_infl {Da Db : TangleDatum cap χ} {sa : Slice T Da} {sb : Slice T Db} {ε : Set
  ↥Tᶜ → Bool} {σv : ↥Tᶜ → Set ↥Tᶜ} {σe : Set ↥Tᶜ → Set ↥Tᶜ} (h : IsLinearInflation (sa.paint ε)
    (sb.paint ε) σv σe)
    {e : Set ↥Tᶜ} (he : e ∈ (sa.paint ε).E) (hi : Painting.IsInternal e) : Painting.IsInternal
      (σe e) := by
  refine disjoint_left.mpr fun x hx hxb ↦ ?_
  obtain ⟨C, hC, hxC⟩ := sUnion_cuffs (S := ↥Tᶜ) ▸ hxb
  obtain ⟨y, hy, hyC⟩ := (h.borders_iff e he C hC).mpr ⟨x, hx, hxC⟩
  obtain ⟨W, hW⟩ := sa.exists_wheel ⟨C, hC⟩
  exact disjoint_left.mp hi hy (sa.cf_sub_bd W.2 (hW ▸ hyC))

variable [Infinite α] (h : Family D s N Z ε t Ω ξ ω₀ b 𝒮)
include h

theorem exists_pair (hd : χ.IsDisjoint) (hcl : IsPaintingClass χ 𝒮) (hS2 : ConditionS2 χ cap)
  (hΩ : Ω.IsWQO) {k : ℕ} (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E)) :
    ∃ i j, i < j ∧ ∃ τ : Arm (D i).P.Γ → Arm (D j).P.Γ,
      IsOutline (⟨hd, (D i).P, coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj
        (s i).fr⟩ : Place χ) ⟨hd, (D j).P, coverLoc (s j).𝒲 (s j).cut.finite (s j).cut.disj
          (s j).fr⟩ τ ∧
        ∀ A ∈ (coverLoc (s i).𝒲 (s i).cut.finite (s i).cut.disj (s i).fr).arms, Ω.le (ξ i A) (ξ j
          (τ A)) := by
  classical
  have hS := χ.isSurface
  have hconn := χ.connected
  have hX := (s 0).isSurface
  have hc := (s 0).connected
  have hfN : N.Finite := h.hN 0 ▸ (s 0).finite_markN
  have hsub : N ⊆ bd ↥Tᶜ := fun x hx ↦ ((s 0).markN_sub (h.hN 0 ▸ hx)).2
  have h2 : ∀ C : cuffs ↥Tᶜ, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q := h.hN 0 ▸ (s 0).two_marks
  have hl : ∀ s₁ ∈ arcComponentsIn (bd ↥Tᶜ \ N), ∀ s₂ ∈ arcComponentsIn (bd ↥Tᶜ \ N), s₁ ≠ s₂
    → Disjoint s₁ Z → Disjoint s₂ Z → Disjoint (tilde s₁) (tilde s₂) := by
    rw [← h.hN 0, ← h.hZ 0]
    exact (s 0).long_disjoint
  let Φ' : Frame ↥Tᶜ := cutFrame hX N Z ε hfN hsub h2 hl
  have hF : ∀ i, (s i).IsCutFrame Φ' Z ε := fun i ↦ ⟨(h.hN i).symm, (h.hZ i).symm, fun _ ↦ Iff.rfl,
    fun _ ↦ rfl⟩
  obtain ⟨Ω2', Ω3', h2w, h3w, h3s, h2s, hstrict, hm2, hm3⟩ := exists_orders χ hk
  let I : Type := Σ i, ↥(s i).𝒲 × ℕ
  have : ∀ i, Finite ↥(s i).𝒲 := fun i ↦ (s i).finite_𝒲
  have : Countable I := inferInstance
  let R : Set I := {x | x.2.2 < ((s x.1).fr x.2.1).R.k}
  obtain ⟨enc, Ωc, hcw, henc, hele⟩ := exists_colOrder (α := α) hΩ R (fun x : I ↦
    ((s x.1).fr x.2.1).code x.2.2) (fun x : I ↦ ξ x.1 (((s x.1).fr x.2.1).secArm x.2.2))
      (finite_codeSet (2 * b + 3))
    (fun x _ ↦ codeSet_mono (by have := h.hb x.1 x.2.1; omega) (((s x.1).fr x.2.1).code_mem _))
    (fun x hx ↦ h.hξ _ _ (mem_iUnion.mpr ⟨x.2.1, .inl ⟨_, hx, rfl⟩⟩))
  let a₀ : α := Classical.arbitrary α
  let col : ∀ i, ↥(s i).𝒲 → ℕ → α := fun i W p ↦ enc ⟨i, W, p⟩
  have hO : ∀ i, (s i).IsCutOrders ω₀ Ω2' Ω3' Ωc (col i) := fun i ↦ ⟨hm2, hm3, h.hcov i, fun W p hp
    _ ↦ henc ⟨i, W, p⟩ hp⟩
  let χ' := cutScheme hX hc Φ' Ω2' Ω3' Ωc h2w h3w hcw a₀
  let P' : ℕ → ColouredPainting χ' := fun i ↦ (s i).colPaint ε (hF i) h2w h3w hcw a₀ (col i) (hO i)
  have hsim : IsSimilarlyOriented χ' P' := by
    rcases hcl.similarly_oriented with h' | ⟨ω, hω⟩
    · exact Or.inl fun hO' ↦ h' ((s 0).orientable hO')
    · obtain ⟨ω₁, hω₁⟩ := GraphMinor.GM19.fragmentOrientation S _ (s 0).K Subtype.val hS hconn
        (s 0).fd.pull.frag ω
      refine Or.inr ⟨ω₁, fun i e he h3 a b' c hl' ↦ (s i).paint_pos ε hω₁
        (fun e' he' h3' ↦ ?_) e he h3 a b' c hl'⟩
      exact hω _ (hcl.image_mem _ (h.hm i) _ _ (s i).hf.symm (s i).isImage) e' he' h3'
  obtain ⟨i, j, hij, σv, σe, hI⟩ : ∃ i j, i < j ∧ ∃ σv σe, IsColouredLinearInflation χ' (P' i)
    (P' j) σv σe := by
    by_contra hb'
    exact hS2 ↥Tᶜ Shat χ' (s 0).nonempty_capped ⟨Homeomorph.refl _⟩ h3s h2s hstrict ⟨P',
      fun i j hij hex ↦ hb' ⟨i, j, hij, hex⟩, hsim⟩
  have hint : ∀ e ∈ ((s i).paint ε).E, Painting.IsInternal e → χ.unionLE ((s i).cutφ
    (col i) a₀ Z e) ((s j).cutφ (col j) a₀ Z (σe e)) := by
    intro e he hi
    have hie := internal_of_infl hI.isLinear he hi
    have hEb := hI.isLinear.edge_mem e he
    have hsz := hI.isLinear.edge_size e he
    rcases ((s i).paint ε).edge_shape e he with ⟨h₂, -⟩ | ⟨h₃, -⟩
    · have m₁ := (P' i).internal_2_mem e he hi h₂
      have m₂ := (P' j).internal_2_mem (σe e) hEb hie (hsz.trans h₂)
      exact .inl ⟨h2s.E_subset m₁, h2s.E_subset m₂, (h2s.le_iff _ m₁ _ m₂).mp
        (hI.le_internal_2 e he hi h₂)⟩
    · have m₁ := (P' i).internal_3_mem e he hi h₃
      have m₂ := (P' j).internal_3_mem (σe e) hEb hie (hsz.trans h₃)
      exact .inr (.inl ⟨h3s.E_subset m₁, h3s.E_subset m₂, (h3s.le_iff _ m₁ _ m₂).mp
        (hI.le_internal_3 e he hi h₃)⟩)
  have hp : CutPair (s i) (s j) ε Φ' Z σv σe Ω (ξ i) (ξ j) (col i) (col j) a₀ Ωc := by
    refine ⟨hF i, hF j, (s i).march_arc (h.hε i), (s j).march_arc (h.hε j), hI.isLinear,
      hI.respects, hint, ?_, ?_, ?_⟩
    · intro e he hb' c hc' hl' hsub'
      have := hI.le_border e he c hc' ⟨hb', hsub'⟩
      change (if Φ'.isLong c then Ωc else QuasiOrder.single a₀).le _ _ at this
      rw [ite_eq_left hl'] at this
      exact this
    · intro W p W' q hle
      exact hele ⟨i, W, p⟩ ⟨j, W', q⟩ hle
    · intro W p hp' W' q hq' hz
      have hzZ : (s i).zx W p ∈ Z := h.hZ i ▸ mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hp', rfl⟩⟩
      have hzZ' : (s j).zx W' q ∈ Z := hz ▸ hzZ
      have e₁ := ((s i).ztag_zx hp').symm.trans (h.ht i _ hzZ)
      have e₂ := ((s j).ztag_zx hq').symm.trans (h.ht j _ hzZ')
      rw [← hz] at e₂
      have e₃ : (s i).zdata W p = (s j).zdata W' q := Option.some.inj (e₁.trans e₂.symm)
      simp only [Slice.zdata, Prod.mk.injEq, decide_eq_decide] at e₃
      obtain ⟨hk', hc', hlen, hcc⟩ := e₃
      obtain ⟨hle₁, hle₂⟩ := h.mono i j hij W p hp' W' q hq' hz
      exact ⟨hk', hc'.symm, hle₁, hlen.symm, fun hc₀ ↦ ⟨hcc.mp hc₀, hle₂ hc₀ (hcc.mp hc₀)⟩⟩
  obtain ⟨τ, h₁, h₂⟩ := hp.exists_outline hd
  exact ⟨i, j, hij, τ, h₁, h₂⟩

end Family

end GraphMinor.GM19
