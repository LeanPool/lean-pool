/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TriCoh
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.FieldTheory.Finiteness

/-!
# Gluing primitives over a triangulation

Two local cocycles whose cocycles on the triangulation differ by a coboundary are equivalent
(`rep_rel`). We correct the primitives on the faces by constants so that they take the given values
at the vertices. Then they agree on common edges and glue to a function on the surface.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Matrix

local notation "K" => ZMod 2

variable {X : Type} [TopologicalSpace X] [T2Space X]

namespace IsTriang

variable {V : Set X} {E 𝓕 : Set (Set X)} [Fintype V] [Fintype E] [Fintype 𝓕]

omit [T2Space X] in
theorem _root_.GraphMinor.Surface.Prim.add_const {φ : X → X → K} {Φ : Set X} {g : X → K}
  (h : Prim φ Φ g) (c : K) :
    Prim φ Φ (fun x => g x + c) := fun p hp => by
  obtain ⟨W, hW, h1⟩ := h p hp
  refine ⟨W, hW, fun x hx x' hx' => ?_⟩
  rw [h1 x hx x' hx']
  have h2 : g x + c + (g x' + c) = g x + g x' + (c + c) := by ring
  rw [h2, CharTwo.add_self_eq_zero, add_zero]

omit [Fintype ↑E] [Fintype ↑𝓕] in
/-- **Cocycles that differ by a coboundary come from equivalent local cocycles.** -/
theorem rep_rel (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {φ φ' : X → X
  → K} {y y' : E → K}
    (hφ : IsCoc φ) (hφ' : IsCoc φ') (hy : Rep V E 𝓕 φ y) (hy' : Rep V E 𝓕 φ' y') {w : V → K}
    (hw : (h.cx hT).N.mulVec w = y + y') : CohRel φ φ' := by
  classical
  obtain ⟨g, hg, hrep⟩ := hy
  obtain ⟨g', hg', hrep'⟩ := hy'
  let ψ : X → X → K := fun x x' => φ x x' + φ' x x'
  let u : Set X → X → K := fun Φ x => g Φ x + g' Φ x
  have hu : ∀ Φ ∈ 𝓕, Prim ψ Φ (u Φ) := fun Φ hΦ => (hg Φ hΦ).add (hg' Φ hΦ)
  have hbase : ∀ Φ : Set X, ∃ a : V, Φ ∈ 𝓕 → a.1 ∈ Φ := fun Φ => by
    by_cases hΦ : Φ ∈ 𝓕
    · obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts hΦ
      have ha : a ∈ Φ ∩ V := hE ▸ Or.inl rfl
      exact ⟨⟨a, ha.2⟩, fun _ => ha.1⟩
    · obtain ⟨Φ', hΦ', -⟩ := h.exists_face (Classical.choice ‹ConnectedSpace X›.toNonempty)
      obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts hΦ'
      have ha : a ∈ Φ' ∩ V := hE ▸ Or.inl rfl
      exact ⟨⟨a, ha.2⟩, fun h' => absurd h' hΦ⟩
  choose a₀ ha₀ using hbase
  let v : Set X → X → K := fun Φ x => u Φ x + (u Φ (a₀ Φ).1 + w (a₀ Φ))
  have hv : ∀ Φ ∈ 𝓕, Prim ψ Φ (v Φ) := fun Φ hΦ => (hu Φ hΦ).add_const _
  have hvV : ∀ Φ ∈ 𝓕, ∀ b : V, b.1 ∈ Φ → v Φ b.1 = w b := fun Φ hΦ b hb => by
    by_cases hab : (a₀ Φ) = b
    · simp only [v, ← hab]
      have h1 : u Φ (a₀ Φ).1 + (u Φ (a₀ Φ).1 + w (a₀ Φ)) = (u Φ (a₀ Φ).1 + u Φ (a₀ Φ).1) + w (a₀ Φ)
        := by ring
      rw [h1, CharTwo.add_self_eq_zero, zero_add]
    · have hab' : (a₀ Φ).1 ≠ b.1 := fun h' => hab (Subtype.ext h')
      obtain ⟨e, he, hs, hi⟩ := h.face_pair hΦ ⟨ha₀ Φ hΦ, (a₀ Φ).2⟩ ⟨hb, b.2⟩ hab'
      have hs' := hs.trans (discBd_subset Φ)
      have h1 := congrFun hw ⟨e, he⟩
      rw [(h.cx hT).sum_ends ⟨e, he⟩ hab (h.cx_ends hT ⟨e, he⟩ _ _ hi), Pi.add_apply,
        hrep ⟨e, he⟩ Φ hΦ hs' _ (hi ▸ Or.inl rfl) _ (hi ▸ Or.inr rfl) hab',
        hrep' ⟨e, he⟩ Φ hΦ hs' _ (hi ▸ Or.inl rfl) _ (hi ▸ Or.inr rfl) hab'] at h1
      have h2 : v Φ b.1 + w b = (u Φ b.1 + u Φ (a₀ Φ).1) + (w (a₀ Φ) + w b) := by
        simp only [v]
        ring
      refine CharTwo.add_eq_zero.mp ?_
      rw [h2, h1]
      have h3 : u Φ b.1 + u Φ (a₀ Φ).1 + (g Φ (a₀ Φ).1 + g Φ b.1 + (g' Φ (a₀ Φ).1 + g' Φ b.1)) =
          (u Φ b.1 + u Φ b.1) + (u Φ (a₀ Φ).1 + u Φ (a₀ Φ).1) := by
        simp only [u]
        ring
      rw [h3, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have hagree : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, ∀ x ∈ Φ, x ∈ Φ' → v Φ x = v Φ' x := fun Φ hΦ Φ' hΦ' x hx hx'
    => by
    by_cases heq : Φ = Φ'
    · rw [heq]
    by_cases hxV : x ∈ V
    · rw [hvV Φ hΦ ⟨x, hxV⟩ hx, hvV Φ' hΦ' ⟨x, hxV⟩ hx']
    have hb := h.mem_bd_of_ne hΦ hΦ' heq hx hx'
    obtain ⟨e, he, hxe⟩ := h.dis.bd Φ hΦ hb
    have s1 := (h.edge_sub he hΦ hxe hxV hx).trans (discBd_subset Φ)
    have s2 := (h.edge_sub he hΦ' hxe hxV hx').trans (discBd_subset Φ')
    obtain ⟨p, q, -, -, hi⟩ := h.dis.graph.edge e he
    have hp : p ∈ e ∩ V := hi ▸ Or.inl rfl
    have h1 := (hv Φ hΦ).const (hv Φ' hΦ') (h.isPreconnected_edge he) s1 s2 hxe hp.1
    rw [hvV Φ hΦ ⟨p, hp.2⟩ (s1 hp.1), hvV Φ' hΦ' ⟨p, hp.2⟩ (s2 hp.1),
      CharTwo.add_self_eq_zero] at h1
    exact CharTwo.add_eq_zero.mp h1
  have hfc : ∀ x : X, ∃ Φ ∈ 𝓕, x ∈ Φ := h.exists_face
  choose fc hfc₁ hfc₂ using hfc
  let k : X → K := fun x => v (fc x) x
  have hk : ∀ Φ ∈ 𝓕, ∀ x ∈ Φ, v Φ x = k x := fun Φ hΦ x hx => hagree Φ hΦ _ (hfc₁ x) x hx (hfc₂ x)
  obtain ⟨N₁, hN₁, hc₁⟩ := hφ
  obtain ⟨N₂, hN₂, hc₂⟩ := hφ'
  have hnear : ∀ p : X, ∃ W ∈ 𝓝 p, W ×ˢ W ⊆ N₁ ∩ N₂ ∧ ∀ x ∈ W, ψ p x = k p + k x ∧ ψ x p
    = k x + k p := fun p => by
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem (hN₁ p) (hN₂ p))
    have hC : IsClosed (⋃₀ {Φ ∈ 𝓕 | p ∉ Φ}) :=
      (h.dis.fin.subset (fun _ (hΦ : _ ∈ {Φ ∈ 𝓕 | p ∉ Φ}) => hΦ.1)).isClosed_sUnion
        fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
    have hW₁ : (⋃₀ {Φ ∈ 𝓕 | p ∉ Φ})ᶜ ∈ 𝓝 p := hC.isOpen_compl.mem_nhds (by
      rintro ⟨Φ, hΦ, h1⟩
      exact hΦ.2 h1)
    have hch : ∀ Φ : Set X, ∃ W ∈ 𝓝 p, Φ ∈ 𝓕 → p ∈ Φ → ∀ x ∈ W ∩ Φ, ∀ x' ∈ W ∩ Φ, ψ x x'
      = v Φ x + v Φ x' := fun Φ => by
      by_cases h1 : Φ ∈ 𝓕 ∧ p ∈ Φ
      · obtain ⟨W, hW, h2⟩ := hv Φ h1.1 p h1.2
        exact ⟨W, hW, fun _ _ => h2⟩
      · exact ⟨univ, univ_mem, fun h2 h3 => absurd ⟨h2, h3⟩ h1⟩
    choose Wf hWf hWp using hch
    have hW₂ : (⋂ Φ ∈ 𝓕, Wf Φ) ∈ 𝓝 p := (Filter.biInter_mem h.dis.fin).mpr fun Φ _ => hWf Φ
    refine ⟨A ∩ B ∩ (⋃₀ {Φ ∈ 𝓕 | p ∉ Φ})ᶜ ∩ ⋂ Φ ∈ 𝓕, Wf Φ, inter_mem (inter_mem
      (inter_mem hA hB) hW₁) hW₂, ?_, ?_⟩
    · rintro ⟨x, x'⟩ ⟨hx, hx'⟩
      exact hAB ⟨hx.1.1.1, hx'.1.1.2⟩
    · intro x hx
      have hxΦ := hfc₂ x
      have hΦ := hfc₁ x
      have hpΦ : p ∈ fc x := by
        by_contra h1
        exact hx.1.2 ⟨fc x, ⟨hΦ, h1⟩, hxΦ⟩
      have hpW : p ∈ Wf (fc x) := mem_of_mem_nhds (hWf _)
      have hxW : x ∈ Wf (fc x) := mem_iInter₂.mp hx.2 _ hΦ
      have h1 := hWp (fc x) hΦ hpΦ p ⟨hpW, hpΦ⟩ x ⟨hxW, hxΦ⟩
      have h2 := hWp (fc x) hΦ hpΦ x ⟨hxW, hxΦ⟩ p ⟨hpW, hpΦ⟩
      rw [hk _ hΦ p hpΦ, hk _ hΦ x hxΦ] at h1 h2
      exact ⟨h1, h2⟩
  choose W hW hWN hWk using hnear
  refine ⟨k, ⋃ p, W p ×ˢ W p, fun q => Filter.mem_of_superset (prod_mem_nhds (hW q) (hW q))
    (subset_iUnion (fun p => W p ×ˢ W p) q), ?_⟩
  intro x x' hxx
  obtain ⟨p, hp⟩ := mem_iUnion.mp hxx
  have hpW : p ∈ W p := mem_of_mem_nhds (hW p)
  have m1 : (x, p) ∈ N₁ ∩ N₂ := hWN p (show (x, p) ∈ W p ×ˢ W p from ⟨hp.1, hpW⟩)
  have m2 : (p, x') ∈ N₁ ∩ N₂ := hWN p (show (p, x') ∈ W p ×ˢ W p from ⟨hpW, hp.2⟩)
  have m3 : (x, x') ∈ N₁ ∩ N₂ := hWN p hp
  have h1 := hc₁ x p x' m1.1 m2.1 m3.1
  have h2 := hc₂ x p x' m1.2 m2.2 m3.2
  have h3 := (hWk p x hp.1).2
  have h4 := (hWk p x' hp.2).1
  simp only [ψ] at h3 h4
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, ← h1, ← h2]
  have h5 : φ x p + φ p x' + (φ' x p + φ' p x') = (φ x p + φ' x p) + (φ p x' + φ' p x') := by ring
  rw [h5, h3, h4]
  have h6 : k x + k p + (k p + k x') = k x' + k x + (k p + k p) := by ring
  rw [h6, CharTwo.add_self_eq_zero, add_zero]

/-- The value of a function on edges at a pair of vertices. -/
noncomputable def Yf (E : Set (Set X)) (V : Set X) (y : E → K) (a b : X) : K := by
  classical
  exact if h : ∃ e : E, e.1 ∩ V = {a, b} then y h.choose else 0

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
omit [T2Space X] in
theorem Yf_eq (h : IsTriang V E 𝓕) (y : E → K) {a b : X} (e : E) (hi : e.1 ∩ V
  = {a, b}) : Yf E V y a b = y e := by
  classical
  have hex : ∃ e : E, e.1 ∩ V = {a, b} := ⟨e, hi⟩
  have h1 : hex.choose = e := Subtype.ext (h.simple _ hex.choose.2 _ e.2
    (hex.choose_spec.trans hi.symm))
  simp only [Yf, dite_eq_left hex, h1]

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
omit [T2Space X] in
theorem Yf_self (h : IsTriang V E 𝓕) (y : E → K) (a : X) : Yf E V y a a = 0 := by
  classical
  have hn : ¬ ∃ e : E, e.1 ∩ V = {a, a} := fun ⟨e, he⟩ => by
    have h1 := h.ends_ncard e.2
    rw [he, pair_eq_singleton, ncard_singleton] at h1
    omega
  simp only [Yf, dite_eq_right hn]

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
omit [T2Space X] in
theorem Yf_comm (h : IsTriang V E 𝓕) (y : E → K) (a b : X) : Yf E V y a b = Yf E V y b a := by
  classical
  by_cases hex : ∃ e : E, e.1 ∩ V = {a, b}
  · obtain ⟨e, he⟩ := hex
    rw [h.Yf_eq y e he, h.Yf_eq y e (he.trans (pair_comm a b))]
  · have hex' : ¬ ∃ e : E, e.1 ∩ V = {b, a} := by rwa [pair_comm b a]
    simp only [Yf, dite_eq_right hex, dite_eq_right hex']

omit [Fintype ↑V] [Fintype ↑𝓕] in
/-- A cocycle adds up on the vertices of a face. -/
theorem Yf_add (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {y : E → K}
    (hy : (h.cx hT).M.mulVec y = 0) {Φ : Set X} (hΦ : Φ ∈ 𝓕) {a b c : X} (ha : a ∈ Φ ∩ V)
      (hb : b ∈ Φ ∩ V) (hc : c ∈ Φ ∩ V) :
    Yf E V y a b + Yf E V y b c = Yf E V y a c := by
  have : Finite V := h.dis.graph.fin.to_subtype
  have : Finite 𝓕 := h.dis.fin.to_subtype
  by_cases hab : a = b
  · subst hab
    rw [h.Yf_self, zero_add]
  by_cases hbc : b = c
  · subst hbc
    rw [h.Yf_self, add_zero]
  by_cases hac : a = c
  · subst hac
    rw [h.Yf_self, h.Yf_comm y b a, CharTwo.add_self_eq_zero]
  obtain ⟨e₁, h1, e₂, h2, e₃, h3, s1, s2, s3, i1, i2, i3, n12, n13, n23⟩
    := h.exists_three_edges hΦ ha hb hc hab hac hbc
  have hn : ∀ {e f : Set X} (he : e ∈ E) (hf : f ∈ E), e ≠ f → (⟨e, he⟩ : E) ≠ ⟨f, hf⟩
    := fun _ _ hn h' => hn (congrArg Subtype.val h')
  have h4 := (h.cx hT).sum_three y ⟨Φ, hΦ⟩ ((h.cx_I hT ⟨e₁, h1⟩ ⟨Φ, hΦ⟩).mpr s1)
    ((h.cx_I hT ⟨e₂, h2⟩ ⟨Φ, hΦ⟩).mpr s2)
    ((h.cx_I hT ⟨e₃, h3⟩ ⟨Φ, hΦ⟩).mpr s3) (hn _ _ n12) (hn _ _ n13) (hn _ _ n23)
  rw [congrFun hy] at h4
  rw [h.Yf_eq y ⟨e₁, h1⟩ i1, h.Yf_eq y ⟨e₂, h2⟩ i2, h.Yf_eq y ⟨e₃, h3⟩ i3]
  exact CharTwo.add_eq_zero.mp h4.symm

omit [Fintype ↑V] [Fintype ↑𝓕] in
/-- **Each cocycle of the triangulation comes from a local cocycle.** -/
theorem exists_coc (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {y : E → K}
    (hy : (h.cx hT).M.mulVec y = 0) : ∃ φ : X → X → K, IsCoc φ ∧ BdTriv φ ∧ Rep V E 𝓕 φ y := by
  have : Finite V := h.dis.graph.fin.to_subtype
  have : Finite 𝓕 := h.dis.fin.to_subtype
  classical
  obtain ⟨hcpt, -, hint⟩ := id hT
  have hne : Nonempty X := ‹ConnectedSpace X›.toNonempty
  let St : V → Set X := fun v => (⋃₀ {Φ ∈ 𝓕 | v.1 ∉ Φ})ᶜ
  have hStO : ∀ v, IsOpen (St v) := fun v => by
    have hC : IsClosed (⋃₀ {Φ ∈ 𝓕 | v.1 ∉ Φ}) :=
      (h.dis.fin.subset (fun _ (hΦ : _ ∈ {Φ ∈ 𝓕 | v.1 ∉ Φ}) => hΦ.1)).isClosed_sUnion
        fun Φ hΦ => (h.dis.disc Φ hΦ.1).isClosed
    exact hC.isOpen_compl
  have hSt : ∀ v, ∀ x ∈ St v, ∀ Φ ∈ 𝓕, x ∈ Φ → v.1 ∈ Φ := fun v x hx Φ hΦ h1 => by
    by_contra h2
    exact hx ⟨Φ, ⟨hΦ, h2⟩, h1⟩
  have hStV : ∀ v : V, v.1 ∈ St v := fun v => by
    rintro ⟨Φ, hΦ, h1⟩
    exact hΦ.2 h1
  have hcov : ∀ x : X, ∃ v, x ∈ St v := fun x => by
    by_cases hxV : x ∈ V
    · exact ⟨⟨x, hxV⟩, hStV _⟩
    by_cases hxE : x ∈ ⋃₀ E
    · obtain ⟨e, he, hxe⟩ := hxE
      obtain ⟨p, q, -, -, hi⟩ := h.dis.graph.edge e he
      have hp : p ∈ e ∩ V := hi ▸ Or.inl rfl
      refine ⟨⟨p, hp.2⟩, ?_⟩
      rintro ⟨Φ, hΦ, h1⟩
      exact hΦ.2 (discBd_subset Φ (h.edge_sub he hΦ.1 hxe hxV h1 hp.1))
    · obtain ⟨Φ, hΦ, hx⟩ := h.exists_face x
      obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts hΦ
      have ha : a ∈ Φ ∩ V := hE ▸ Or.inl rfl
      refine ⟨⟨a, ha.2⟩, ?_⟩
      rintro ⟨Φ', hΦ', h1⟩
      have hne' : Φ ≠ Φ' := fun h2 => hΦ'.2 (h2 ▸ ha.1)
      have hb := h.mem_bd_of_ne hΦ hΦ'.1 hne' hx h1
      exact hxE (h.dis.bd Φ hΦ hb)
  have hnorm : NormalSpace X := inferInstance
  obtain ⟨K₀, hK₀u, hK₀c, hK₀s⟩ := exists_subset_iUnion_closed_subset (u := St) isClosed_univ hStO
    (fun x _ => Set.toFinite _) (fun x _ => mem_iUnion.mpr (hcov x))
  let C : V → Set X := fun v => insert v.1 (K₀ v)
  have hCc : ∀ v, IsClosed (C v) := fun v => by
    have h1 := (isClosed_singleton (x := v.1)).union (hK₀c v)
    rwa [singleton_union] at h1
  have hCs : ∀ v, C v ⊆ St v := fun v => insert_subset (hStV v) (hK₀s v)
  have hs : ∀ x : X, ∃ v : V, x ∈ C v ∧ ∀ hx : x ∈ V, v = ⟨x, hx⟩ := fun x => by
    by_cases hxV : x ∈ V
    · exact ⟨⟨x, hxV⟩, .inl rfl, fun _ => rfl⟩
    · obtain ⟨v, hv⟩ := mem_iUnion.mp (hK₀u (mem_univ x))
      exact ⟨v, .inr hv, fun h' => absurd h' hxV⟩
  choose s hsC hsV using hs
  let N : Set (X × X) := ⋂ v : V, {p | (p.1 ∈ C v → p.2 ∈ St v) ∧ (p.2 ∈ C v → p.1 ∈ St v)}
  have hN : NearDiag N := fun p => by
    refine (Filter.iInter_mem).mpr fun v => ?_
    change {q : X × X | q.1 ∈ C v → q.2 ∈ St v} ∩
      {q : X × X | q.2 ∈ C v → q.1 ∈ St v} ∈ 𝓝 (p, p)
    refine inter_mem ?_ ?_
    · by_cases hp : p ∈ C v
      · have h1 : (fun q : X × X => q.2) ⁻¹' St v ∈ 𝓝 (p, p) :=
          continuous_snd.continuousAt.preimage_mem_nhds ((hStO v).mem_nhds (hCs v hp))
        exact Filter.mem_of_superset h1 fun q hq _ => hq
      · have h1 : (fun q : X × X => q.1) ⁻¹' (C v)ᶜ ∈ 𝓝 (p, p) :=
          continuous_fst.continuousAt.preimage_mem_nhds ((hCc v).isOpen_compl.mem_nhds hp)
        exact Filter.mem_of_superset h1 fun q hq h' => absurd h' hq
    · by_cases hp : p ∈ C v
      · have h1 : (fun q : X × X => q.1) ⁻¹' St v ∈ 𝓝 (p, p) :=
          continuous_fst.continuousAt.preimage_mem_nhds ((hStO v).mem_nhds (hCs v hp))
        exact Filter.mem_of_superset h1 fun q hq _ => hq
      · have h1 : (fun q : X × X => q.2) ⁻¹' (C v)ᶜ ∈ 𝓝 (p, p) :=
          continuous_snd.continuousAt.preimage_mem_nhds ((hCc v).isOpen_compl.mem_nhds hp)
        exact Filter.mem_of_superset h1 fun q hq h' => absurd h' hq
  let φ : X → X → K := fun x x' => Yf E V y (s x).1 (s x').1
  have hface : ∀ {Φ : Set X}, Φ ∈ 𝓕 → ∀ x ∈ Φ, (s x).1 ∈ Φ ∩ V := fun hΦ x hx =>
    ⟨hSt _ x (hCs _ (hsC x)) _ hΦ hx, (s x).2⟩
  refine ⟨φ, ⟨N, hN, fun x x' z h1 h2 h3 => ?_⟩, ⟨0, univ, fun _ => univ_mem,
    fun x hx => absurd (hint x) hx⟩, ?_⟩
  · have h1' := mem_iInter.mp h1
    have h2' := mem_iInter.mp h2
    have h3' := mem_iInter.mp h3
    have za : z ∈ St (s x) := (h3' (s x)).1 (hsC x)
    have zb : z ∈ St (s x') := (h2' (s x')).1 (hsC x')
    have zc : z ∈ St (s z) := hCs _ (hsC z)
    obtain ⟨Φ, hΦ, hz⟩ := h.exists_face z
    exact h.Yf_add hT hy hΦ ⟨hSt _ z za Φ hΦ hz, (s x).2⟩ ⟨hSt _ z zb Φ hΦ hz,
      (s x').2⟩ ⟨hSt _ z zc Φ hΦ hz, (s z).2⟩
  · have hb : ∀ Φ : Set X, ∃ a₀ : V, Φ ∈ 𝓕 → a₀.1 ∈ Φ := fun Φ => by
      by_cases hΦ : Φ ∈ 𝓕
      · obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts hΦ
        have ha : a ∈ Φ ∩ V := hE ▸ Or.inl rfl
        exact ⟨⟨a, ha.2⟩, fun _ => ha.1⟩
      · obtain ⟨Φ', hΦ', -⟩ := h.exists_face (Classical.choice hne)
        obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts hΦ'
        have ha : a ∈ Φ' ∩ V := hE ▸ Or.inl rfl
        exact ⟨⟨a, ha.2⟩, fun h' => absurd h' hΦ⟩
    choose a₀ ha₀ using hb
    refine ⟨fun Φ x => Yf E V y (a₀ Φ).1 (s x).1, fun Φ hΦ p hp => ?_,
      fun e Φ hΦ hs' a ha b hb hab => ?_⟩
    · obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hN p)
      refine ⟨A ∩ B, inter_mem hA hB, fun x hx x' hx' => ?_⟩
      have h1 := h.Yf_add hT hy hΦ ⟨ha₀ Φ hΦ, (a₀ Φ).2⟩ (hface hΦ x hx.2) (hface hΦ x' hx'.2)
      change Yf E V y (s x).1 (s x').1 = Yf E V y (a₀ Φ).1 (s x).1 + Yf E V y (a₀ Φ).1 (s x').1
      rw [← h1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · have h1 := h.Yf_add hT hy hΦ ⟨ha₀ Φ hΦ, (a₀ Φ).2⟩ ⟨hs' ha.1, ha.2⟩ ⟨hs' hb.1, hb.2⟩
      have hsa : (s a).1 = a := by rw [hsV a ha.2]
      have hsb : (s b).1 = b := by rw [hsV b hb.2]
      have hi : e.1 ∩ V = {a, b} := by
        have hsub : ({a, b} : Set X) ⊆ e.1 ∩ V := insert_subset ha (singleton_subset_iff.mpr hb)
        exact (eq_of_subset_of_ncard_le hsub (by rw [h.ends_ncard e.2,
          ncard_pair hab]) (Set.toFinite _)).symm
      change y e = Yf E V y (a₀ Φ).1 (s a).1 + Yf E V y (a₀ Φ).1 (s b).1
      rw [hsa, hsb, ← h.Yf_eq y e hi, ← h1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
omit [T2Space X] in
theorem nonempty_faces (h : IsTriang V E 𝓕) [ConnectedSpace X] : Nonempty 𝓕 := by
  obtain ⟨Φ, hΦ, -⟩ := h.exists_face (Classical.choice ‹ConnectedSpace X›.toNonempty)
  exact ⟨⟨Φ, hΦ⟩⟩

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
omit [T2Space X] in
theorem nonempty_verts (h : IsTriang V E 𝓕) [ConnectedSpace X] : Nonempty V := by
  obtain ⟨Φ⟩ := h.nonempty_faces
  obtain ⟨a, b, c, -, -, -, hE⟩ := h.exists_verts Φ.2
  have ha : a ∈ Φ.1 ∩ V := hE ▸ Or.inl rfl
  exact ⟨⟨a, ha.2⟩⟩

omit [TopologicalSpace X] [T2Space X] [Fintype ↑E] in
theorem sub_fn (a b : E → K) : a - b = a + b := funext fun _ => CharTwo.sub_eq_add _ _

omit [Fintype ↑𝓕] in
/-- **The classes of local cocycles are the classes of the triangulation.** -/
theorem card_kCl (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] :
    Nat.card (KCl X K) = 2 ^ (Module.finrank K (↥(LinearMap.ker (h.cx hT).M.mulVecLin) ⧸
      (LinearMap.range (h.cx hT).N.mulVecLin).comap (LinearMap.ker (h.cx hT).M.mulVecLin).subtype))
        := by
  classical
  set Z := LinearMap.ker (h.cx hT).M.mulVecLin with hZ
  set B := (LinearMap.range (h.cx hT).N.mulVecLin).comap Z.subtype with hB
  have hch : ∀ φ : KSet X K, ∃ y : Z, Rep V E 𝓕 φ.1 y.1 := fun φ => by
    obtain ⟨y, hy, hr⟩ := h.exists_rep hT φ.2.1
    exact ⟨⟨y, LinearMap.mem_ker.mpr hy⟩, hr⟩
  choose yf hyf using hch
  let f : KSet X K → Z ⧸ B := fun φ => Submodule.Quotient.mk (yf φ)
  have hrespect : ∀ φ φ' : KSet X K, (kSetoid X K).r φ φ' → f φ = f φ' := fun φ φ' hr => by
    obtain ⟨w, hw⟩ := h.rep_coboundary hT (hyf φ) (hyf φ') hr
    refine (Submodule.Quotient.eq B).mpr ?_
    refine ⟨w, ?_⟩
    change (h.cx hT).N.mulVec w = (yf φ).1 - (yf φ').1
    rw [hw, sub_fn]
  let F : KCl X K → Z ⧸ B := Quotient.lift f hrespect
  have hF : Function.Bijective F := by
    constructor
    · refine Quotient.ind₂ fun φ φ' he => Quotient.sound ?_
      obtain ⟨w, hw⟩ := (Submodule.Quotient.eq B).mp (show f φ = f φ' from he)
      refine h.rep_rel hT φ.2.1 φ'.2.1 (hyf φ) (hyf φ') (w := w) ?_
      have hw' : (h.cx hT).N.mulVec w = (yf φ).1 - (yf φ').1 := hw
      rw [hw', sub_fn]
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨φ, h1, h2, h3⟩ := h.exists_coc hT (LinearMap.mem_ker.mp y.2)
        refine ⟨Quotient.mk _ ⟨φ, h1, h2⟩, ?_⟩
        refine (Submodule.Quotient.eq B).mpr ?_
        have hw := h.rep_coboundary hT (hyf ⟨φ, h1, h2⟩) h3 (.refl φ)
        obtain ⟨w, hw⟩ := hw
        refine ⟨w, ?_⟩
        change (h.cx hT).N.mulVec w = (yf ⟨φ, h1, h2⟩).1 - y.1
        rw [hw, sub_fn]
  have h9 : Nat.card (Z ⧸ B) = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Z ⧸ B)
    := Module.natCard_eq_pow_finrank
  rw [Nat.card_congr (Equiv.ofBijective F hF), h9, Nat.card_zmod]

/-- **Euler's formula.** For a triangulation of a connected closed surface with `2 ^ κ` classes of
local cocycles, `|V| - |E| + |F| + κ = 2`. -/
theorem euler_eq (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] :
    ∃ κ : ℕ, Nat.card (KCl X K) = 2 ^ κ ∧ (Fintype.card V : ℤ) - Fintype.card E + Fintype.card 𝓕 +
      κ = 2 := by
  have : Nonempty V := h.nonempty_verts
  have : Nonempty 𝓕 := h.nonempty_faces
  refine ⟨_, h.card_kCl hT, ?_⟩
  have h1 := (h.cx hT).finrank_ker_M
  have h2 := (h.cx hT).finrank_range_N
  set Z := LinearMap.ker (h.cx hT).M.mulVecLin with hZ
  have hle : LinearMap.range (h.cx hT).N.mulVecLin ≤ Z := by
    rintro _ ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    change (h.cx hT).M.mulVec ((h.cx hT).N.mulVec w) = 0
    rw [Matrix.mulVec_mulVec, TriCx.M_mul_N, Matrix.zero_mulVec]
  have h3 := Submodule.finrank_quotient_add_finrank ((LinearMap.range
    (h.cx hT).N.mulVecLin).comap Z.subtype)
  have h4 : Module.finrank K ((LinearMap.range (h.cx hT).N.mulVecLin).comap Z.subtype) =
      Module.finrank K (LinearMap.range (h.cx hT).N.mulVecLin) :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  omega

end IsTriang

end GraphMinor.Surface
