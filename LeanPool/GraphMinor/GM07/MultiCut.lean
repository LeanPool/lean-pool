/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM19.Section6a

/-!
# Cutting along several edges

For step 2 of (9.1), page 243: "By $r = |E(H)|$ applications of (7.4), we can find distinct edges
$e_1, \dots, e_r$ of $G$ which are not loops
such that...". `IsMultiCut` records the surface `Σ_r` got by cutting `Σ` along all of these edges,
and `exists_multiCut` builds it, one cut at a time.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

/-- `θ : S_r → S` cuts `S` along the closures of the edges in `𝓔`, and `G_r` is the preimage of `G`
minus these edges. -/
structure IsMultiCut {S S_r : Type u} [TopologicalSpace S] [TopologicalSpace S_r] (G : Drawing S)
  (𝓔 : Set (Set S)) (θ : S_r → S) (G_r : Drawing S_r) : Prop where
  finite : 𝓔.Finite
  sub : 𝓔 ⊆ G.E
  off_bd : ∀ e ∈ 𝓔, Disjoint (closure e) (bd S)
  not_loop : ∀ e ∈ 𝓔, (tilde e).ncard = 2
  disj : ∀ e ∈ 𝓔, ∀ e' ∈ 𝓔, e ≠ e' → Disjoint (closure e) (closure e')
  quot : IsQuotientMap θ
  preV : G_r.V = θ ⁻¹' G.V
  preU : G_r.U = θ ⁻¹' (G.U \ ⋃₀ 𝓔)
  inj : ∀ x y, θ x = θ y → x = y ∨ θ x ∈ ⋃₀ 𝓔
  bd_eq : bd S_r = θ ⁻¹' (bd S ∪ ⋃ e ∈ 𝓔, closure e)
  edges : ∀ f ∈ G_r.E, θ '' f ∈ G.E ∧ Disjoint (θ '' f) (⋃₀ 𝓔) ∧ f = θ ⁻¹' (θ '' f)

variable {S S_r Y : Type u} [TopologicalSpace S] [TopologicalSpace S_r] [TopologicalSpace Y]

theorem isMultiCut_refl (G : Drawing S) : IsMultiCut G ∅ (id : S → S) G where
  finite := finite_empty
  sub := empty_subset _
  off_bd := by simp
  not_loop := by simp
  disj := by simp
  quot := IsQuotientMap.id
  preV := rfl
  preU := by simp
  inj := by simp
  bd_eq := by simp
  edges f hf := by simpa using hf

theorem IsCutAlongEdge.ncard_bd_le {G : Drawing S} {e : Set S} {a b c : ℕ} {φ : Y
  → S} {G_e : Drawing Y}
    (hCut : IsCutAlongEdge G e a b c Y φ G_e) : (G_e.V ∩ bd Y).ncard ≤ (G.V ∩ bd S).ncard + 2 := by
  classical
  have he := hCut.mem_E
  have hl := hCut.not_loop
  have hs := hCut.quotientMap.surjective
  obtain ⟨u, v, -, hcap, -⟩ : ∃ u v : S, u ≠ v ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds
    (closure e) u v := by
    rcases G.edge_cond e he with h1 | ⟨u, hcap, -⟩
    · exact h1
    · rw [GraphMinor.GM19.tilde_eq_inter_V G he, hcap] at hl
      simp at hl
  have heV : ∀ x ∈ e, x ∉ G.V := fun x hx => (he.2.1 hx).2
  obtain ⟨u', hu⟩ := hs u
  obtain ⟨v', hv⟩ := hs v
  have hucap : u ∈ closure e ∩ G.V := by rw [hcap]; simp
  have hvcap : v ∈ closure e ∩ G.V := by rw [hcap]; simp
  have huniq : ∀ x, φ x = u ∨ φ x = v → x = u' ∨ x = v' := by
    rintro x (h | h)
    · exact .inl ((hCut.inj x u' (h.trans hu.symm)).resolve_right fun h1 => heV _ h1 (h ▸ hucap.2))
    · exact .inr ((hCut.inj x v' (h.trans hv.symm)).resolve_right fun h1 => heV _ h1 (h ▸ hvcap.2))
  have hGV : ∀ x, x ∈ G_e.V ↔ φ x ∈ G.V := fun x => by rw [hCut.preimage_V]; rfl
  have hbde : ∀ x, x ∈ bd Y ↔ φ x ∈ bd S ∨ φ x ∈ closure e := fun x => by rw [hCut.bd_eq]; rfl
  have hfinG : (G.V ∩ bd S).Finite := G.finite_V.subset inter_subset_left
  have hsub : G_e.V ∩ bd Y ⊆ ((G_e.V ∩ bd Y) \ {u', v'}) ∪ {u', v'} := fun x hx => by
    by_cases h : x ∈ ({u', v'} : Set Y)
    · exact .inr h
    · exact .inl ⟨hx, h⟩
  have hmaps : MapsTo φ ((G_e.V ∩ bd Y) \ {u', v'}) (G.V ∩ bd S) := fun x hx => by
    have h1 := (hGV x).mp hx.1.1
    refine ⟨h1, ?_⟩
    rcases (hbde x).mp hx.1.2 with h2 | h2
    · exact h2
    · have h3 : φ x ∈ closure e ∩ G.V := ⟨h2, h1⟩
      rw [hcap] at h3
      exact absurd (huniq x (by simpa using h3)) hx.2
  have hinj : InjOn φ ((G_e.V ∩ bd Y) \ {u', v'}) := fun x hx y hy hxy =>
    (hCut.inj x y hxy).resolve_right fun h1 => heV _ h1 (hmaps hx).1
  have hfin : ((G_e.V ∩ bd Y) \ {u', v'}).Finite := Set.Finite.of_injOn hmaps hinj hfinG
  calc (G_e.V ∩ bd Y).ncard ≤ (((G_e.V ∩ bd Y) \ {u', v'}) ∪ {u', v'}).ncard :=
      ncard_le_ncard hsub (hfin.union (by simp))
    _ ≤ ((G_e.V ∩ bd Y) \ {u', v'}).ncard + ({u', v'} : Set Y).ncard := ncard_union_le _ _
    _ ≤ (G.V ∩ bd S).ncard + 2 := Nat.add_le_add (ncard_le_ncard_of_injOn φ hmaps hinj hfinG)
      ((ncard_insert_le _ _).trans (by simp))

theorem IsMultiCut.step [T2Space S] [CompactSpace S_r] [T2Space S_r] [CompactSpace Y]
  {G : Drawing S} {𝓔 : Set (Set S)} {θ : S_r → S} {G_r : Drawing S_r}
    (hm : IsMultiCut G 𝓔 θ G_r) {e' : Set S_r} {a b c : ℕ} {φ : Y → S_r} {G' : Drawing Y}
      (hCut : IsCutAlongEdge G_r e' a b c Y φ G') :
    θ '' e' ∉ 𝓔 ∧ IsMultiCut G (insert (θ '' e') 𝓔) (θ ∘ φ) G' := by
  classical
  have hc := hm.quot.continuous
  have hs := hm.quot.surjective
  have he' := hCut.mem_E
  obtain ⟨heG, heoff, hepre⟩ := hm.edges e' he'
  set e := θ '' e' with hedef
  have hcl : closure e = θ '' closure e' :=
    (image_closure_subset_closure_image hc).antisymm' (closure_minimal (image_mono subset_closure)
      (isClosed_closure.isCompact.image hc).isClosed)
  have hbdθ : ∀ x, x ∈ bd S_r ↔ θ x ∈ bd S ∪ ⋃ f ∈ 𝓔, closure f := fun x => by rw [hm.bd_eq]; rfl
  have hoff : ∀ x ∈ closure e', θ x ∉ bd S ∪ ⋃ f ∈ 𝓔, closure f := fun x hx hn => by
    have h1 : x ∈ closure e' ∩ bd S_r := ⟨hx, (hbdθ x).mpr hn⟩
    rw [hCut.disjoint_bd] at h1
    exact h1
  have hcloff : ∀ f ∈ 𝓔, Disjoint (closure e) (closure f) := fun f hf => by
    rw [hcl, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ h2
    exact hoff x hx (.inr (mem_iUnion₂.mpr ⟨f, hf, h2⟩))
  have hebd : Disjoint (closure e) (bd S) := by
    rw [hcl, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ h2
    exact hoff x hx (.inl h2)
  have hne : e.Nonempty := by
    obtain ⟨x, hx⟩ := he'.2.2.1.nonempty
    exact ⟨θ x, x, hx, rfl⟩
  have hnot : e ∉ 𝓔 := fun h => by
    obtain ⟨x, hx⟩ := hne
    exact disjoint_left.mp (hcloff e h) (subset_closure hx) (subset_closure hx)
  have hoffU : ∀ x, x ∈ G_r.U → θ x ∉ ⋃₀ 𝓔 := fun x hx => by
    rw [hm.preU] at hx
    exact hx.2
  have hpre : θ ⁻¹' closure e = closure e' := by
    apply Subset.antisymm
    · intro y hy
      change θ y ∈ closure e at hy
      rw [hcl] at hy
      obtain ⟨y', hy', he⟩ := hy
      rcases hm.inj y' y he with rfl | h
      · exact hy'
      · exact absurd h (hoffU y' (G_r.closure_subset_U he' hy'))
    · intro y hy
      change θ y ∈ closure e
      rw [hcl]
      exact ⟨y, hy, rfl⟩
  refine ⟨hnot, ?_⟩
  refine ⟨hm.finite.insert _, insert_subset heG hm.sub, ?_, ?_, ?_,
    hm.quot.comp hCut.quotientMap, ?_, ?_, ?_, ?_, ?_⟩
  · rintro f (rfl | hf)
    · exact hebd
    · exact hm.off_bd f hf
  · rintro f (rfl | hf)
    · rw [GraphMinor.GM19.tilde_eq_inter_V G heG]
      have h1 : closure e ∩ G.V = θ '' (closure e' ∩ G_r.V) := by
        rw [hcl]
        ext z
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hz⟩
          exact ⟨x, ⟨hx, by rw [hm.preV]; exact hz⟩, rfl⟩
        · rintro ⟨x, ⟨hx, hxV⟩, rfl⟩
          rw [hm.preV] at hxV
          exact ⟨⟨x, hx, rfl⟩, hxV⟩
      have hinj : InjOn θ (closure e' ∩ G_r.V) := fun x hx y hy hxy =>
        (hm.inj x y hxy).resolve_right (hoffU x (G_r.V_subset_U hx.2))
      rw [h1, hinj.ncard_image, ← GraphMinor.GM19.tilde_eq_inter_V G_r he']
      exact hCut.not_loop
    · exact hm.not_loop f hf
  · rintro f (rfl | hf) f' (rfl | hf') hne
    · exact absurd rfl hne
    · exact hcloff f' hf'
    · exact (hcloff f hf).symm
    · exact hm.disj f hf f' hf' hne
  · rw [hCut.preimage_V, hm.preV]
    rfl
  · rw [hCut.preimage_U, hm.preU, sUnion_insert]
    ext x
    simp only [mem_preimage, mem_sdiff, mem_union, not_or, Function.comp, hepre]
    tauto
  · intro x y hxy
    rcases hm.inj _ _ hxy with h | h
    · rcases hCut.inj x y h with h1 | h1
      · exact .inl h1
      · exact Or.inr (by rw [sUnion_insert]; exact Or.inl ⟨φ x, h1, rfl⟩)
    · exact .inr (by rw [sUnion_insert]; exact .inr h)
  · have h1 : ⋃ f ∈ insert e 𝓔, closure f = closure e ∪ ⋃ f ∈ 𝓔, closure f := by
      rw [biUnion_insert]
    rw [hCut.bd_eq, hm.bd_eq, h1, ← hpre]
    ext x
    simp only [mem_preimage, mem_union, Function.comp]
    tauto
  · intro f hf
    obtain ⟨h1, h2, h3⟩ := hCut.exists_edge hf
    obtain ⟨h4, h5, h6⟩ := hm.edges _ h1
    have him : (θ ∘ φ) '' f = θ '' (φ '' f) := image_comp θ φ f
    rw [him]
    refine ⟨h4, ?_, ?_⟩
    · rw [sUnion_insert, disjoint_union_right]
      refine ⟨?_, h5⟩
      rw [disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ ⟨y₂, hy₂, he⟩
      rcases hm.inj y₂ y he with rfl | h7
      · exact disjoint_left.mp h2 hy hy₂
      · exact disjoint_left.mp h5 ⟨y, hy, rfl⟩ (he ▸ h7)
    · rw [preimage_comp, ← h6]
      exact h3

/-- `r` applications of (7.4). -/
theorem exists_multiCut {S : Type u} [TopologicalSpace S] [T1Space S]
  (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty
    (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (hBL : IsBoundaryLinked G) {k v r : ℕ} (hk : 1 ≤ k) (hv : 1 ≤ v) (hcount :
      (G.V ∩ bd S).ncard + 2 * r ≤ 2 * k)
    (hα : 42 * k * 5 ^ r * v ≤ alpha G) : ∀ i, i ≤ r → ∃ (S_i : Type u) (_ : TopologicalSpace S_i)
      (_ : T1Space S_i) (θ : S_i → S) (G_i : Drawing S_i) (𝓔 : Set (Set S)),
      IsMultiCut G 𝓔 θ G_i ∧ 𝓔.ncard = i ∧ IsSurface S_i ∧ Nonempty (S_i ≃ₜ SurfaceModel a b
        (c + i)) ∧ IsBoundaryLinked G_i ∧
        42 * k * 5 ^ (r - i) * v ≤ alpha G_i ∧ (G_i.V ∩ bd S_i).ncard ≤ (G.V ∩ bd S).ncard + 2 * i
          := by
  have ht2 : T2Space S := hS.2.1
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨S, inferInstance, inferInstance, id, G, ∅, isMultiCut_refl G, by simp, hS, hm, hBL,
      by simpa using hα, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨S_i, tS, t1S, θ, G_i, 𝓔, hmc, hcard, hSi, hmi, hBLi, hαi, hbdi⟩ := ih (by omega)
    have ht2i : T2Space S_i := hSi.2.1
    have hci : CompactSpace S_i := hSi.1
    set s := 42 * k * 5 ^ (r - (i + 1)) * v with hs
    have h5 : 5 ^ (r - i) = 5 * 5 ^ (r - (i + 1)) := by
      rw [show r - i = r - (i + 1) + 1 by omega, pow_succ]
      ring
    have hαs : 5 * s ≤ alpha G_i := by
      rw [h5] at hαi
      calc 5 * s = 42 * k * (5 * 5 ^ (r - (i + 1))) * v := by rw [hs]; ring
        _ ≤ _ := hαi
    have hslow : 42 ≤ s := by
      have h1 : 1 ≤ 5 ^ (r - (i + 1)) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 1 * 1 * 1 ≤ k * 5 ^ (r - (i + 1)) * v := Nat.mul_le_mul (Nat.mul_le_mul hk h1) hv
      rw [hs]
      nlinarith
    have hslow2 : 2 * k + 1 ≤ s := by
      have h1 : 1 ≤ 5 ^ (r - (i + 1)) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 1 * 1 ≤ 5 ^ (r - (i + 1)) * v := Nat.mul_le_mul h1 hv
      have h3' : k * (1 * 1) ≤ k * (5 ^ (r - (i + 1)) * v) := Nat.mul_le_mul_left k h2
      rw [hs]
      nlinarith
    have hcuff : ∀ C ∈ cuffs S_i, (G_i.V ∩ C).ncard ≤ s - 1 := by
      intro C hC
      have hsub : C ⊆ bd S_i := by
        rw [← sUnion_cuffs]
        exact subset_sUnion_of_mem hC
      have := ncard_le_ncard (inter_subset_inter_right G_i.V hsub) (G_i.finite_V.subset
        inter_subset_left)
      omega
    obtain ⟨e', Y, tY, t1Y, φ, G', hCut, hBL', hα'⟩ := theorem_7_4_proof hSi
      (by omega) hmi G_i s hBLi (by omega) (by omega) hcuff
    have hY := hCut.isSurface
    have ht2Y : T2Space Y := hY.2.1
    have hcY : CompactSpace Y := hY.1
    obtain ⟨hnew, hmc'⟩ := hmc.step hCut
    refine ⟨Y, tY, t1Y, θ ∘ φ, G', _, hmc', ?_, hY, hCut.homeo_model, hBL', hα', ?_⟩
    · rw [ncard_insert_of_notMem hnew hmc.finite, hcard]
    · have := hCut.ncard_bd_le
      omega

end GraphMinor.GM07
