/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TriCohGlue
public import LeanPool.GraphMinor.Surface.PushOff
public import LeanPool.GraphMinor.Surface.CohCard
public import LeanPool.GraphMinor.Surface.NormalWord

/-!
# Local cocycles on a capped surface

Capping the cuffs of a surface with closed discs does not add classes of local cocycles
(`kCl_cap_injective`). A class on the capped surface restricts to a class on the surface, and two
classes with the same restriction are equal, by gluing primitives over the caps (`glue_prim`).

This is what we need to compare a surface with its capped form in the proof of Graph Minors XIX,
(6.5) (page 341).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Filter

local notation "K" => ZMod 2

section Glue

variable {X : Type} [TopologicalSpace X]

/-- A function that is a primitive of `φ + φ'` on each of finitely many closed sets that cover the
space shows that `φ` and `φ'` are equivalent. -/
theorem glue_prim {𝓒 : Set (Set X)} (hf : 𝓒.Finite) (hc : ∀ P ∈ 𝓒, IsClosed P) (hu : ⋃₀ 𝓒
  = univ) {φ φ' : X → X → K} (hφ : IsCoc φ)
    (hφ' : IsCoc φ') {k : X → K} (hk : ∀ P ∈ 𝓒, Prim (fun x y => φ x y + φ' x y) P k) : CohRel φ φ'
      := by
  classical
  obtain ⟨N₁, hN₁, hc₁⟩ := hφ
  obtain ⟨N₂, hN₂, hc₂⟩ := hφ'
  let ψ : X → X → K := fun x y => φ x y + φ' x y
  have hcov : ∀ x : X, ∃ P ∈ 𝓒, x ∈ P := fun x => by
    have : x ∈ ⋃₀ 𝓒 := hu ▸ mem_univ x
    exact this
  have hnear : ∀ p : X, ∃ W ∈ 𝓝 p, W ×ˢ W ⊆ N₁ ∩ N₂ ∧ ∀ x ∈ W, ψ p x = k p + k x ∧ ψ x p
    = k x + k p := fun p => by
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem (hN₁ p) (hN₂ p))
    have hfinite : {P ∈ 𝓒 | p ∉ P}.Finite :=
      hf.subset fun _ hP => hP.1
    have hC : IsClosed (⋃₀ {P ∈ 𝓒 | p ∉ P}) :=
      hfinite.isClosed_sUnion fun P hP => hc P hP.1
    have hW₁ : (⋃₀ {P ∈ 𝓒 | p ∉ P})ᶜ ∈ 𝓝 p := hC.isOpen_compl.mem_nhds (by
      rintro ⟨P, hP, h1⟩
      exact hP.2 h1)
    have hch : ∀ P : Set X, ∃ W ∈ 𝓝 p, P ∈ 𝓒 → p ∈ P → ∀ x ∈ W ∩ P, ∀ x' ∈ W ∩ P, ψ x x'
      = k x + k x' := fun P => by
      by_cases h1 : P ∈ 𝓒 ∧ p ∈ P
      · obtain ⟨W, hW, h2⟩ := hk P h1.1 p h1.2
        exact ⟨W, hW, fun _ _ => h2⟩
      · exact ⟨univ, univ_mem, fun h2 h3 => absurd ⟨h2, h3⟩ h1⟩
    choose Wf hWf hWp using hch
    have hW₂ : (⋂ P ∈ 𝓒, Wf P) ∈ 𝓝 p := (Filter.biInter_mem hf).mpr fun P _ => hWf P
    refine ⟨A ∩ B ∩ (⋃₀ {P ∈ 𝓒 | p ∉ P})ᶜ ∩ ⋂ P ∈ 𝓒, Wf P, inter_mem (inter_mem
      (inter_mem hA hB) hW₁) hW₂, ?_, ?_⟩
    · rintro ⟨x, x'⟩ ⟨hx, hx'⟩
      exact hAB ⟨hx.1.1.1, hx'.1.1.2⟩
    · intro x hx
      obtain ⟨P, hP, hxP⟩ := hcov x
      have hpP : p ∈ P := by
        by_contra h1
        exact hx.1.2 ⟨P, ⟨hP, h1⟩, hxP⟩
      have hpW : p ∈ Wf P := mem_of_mem_nhds (hWf _)
      have hxW : x ∈ Wf P := mem_iInter₂.mp hx.2 _ hP
      exact ⟨hWp P hP hpP p ⟨hpW, hpP⟩ x ⟨hxW, hxP⟩, hWp P hP hpP x ⟨hxW, hxP⟩ p ⟨hpW, hpP⟩⟩
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

end Glue

variable {S T : Type} [TopologicalSpace S] [TopologicalSpace T]

theorem isCoc_pbk {j : S → T} (hj : Continuous j) {φ : T → T → K} (h : IsCoc φ) : IsCoc (pbk j φ)
  := by
  obtain ⟨N, hN, h1⟩ := h
  refine ⟨(fun p : S × S => (j p.1, j p.2)) ⁻¹' N, fun x => ?_, fun x y z h2 h3 h4
    => h1 _ _ _ h2 h3 h4⟩
  have hc : Continuous fun p : S × S => (j p.1, j p.2) := (hj.comp continuous_fst).prodMk
    (hj.comp continuous_snd)
  exact hc.continuousAt.preimage_mem_nhds (hN (j x))

/-- A class on a capped surface restricts to a class on the surface, and the restriction is
injective. -/
theorem kCl_cap_injective [T2Space T] {j : S → T} (hj : IsClosedEmbedding j) {C : Set T}
  (hu : range j ∪ C = univ)
    (hi : range j ∩ C = j '' bd S) {𝓓 : Set (Set T)} (hf : 𝓓.Finite) (hU : ⋃₀ 𝓓 = C)
    (hd : ∀ D ∈ 𝓓, IsClosedDisc D ∧ IsPreconnected (D ∩ range j) ∧ (D ∩ range j).Nonempty)
    (hdj : ∀ D ∈ 𝓓, ∀ D' ∈ 𝓓, D ≠ D' → Disjoint D D') :
    ∃ f : KCl T K → KCl S K, Function.Injective f := by
  classical
  have hdsc : ∀ t : T, ∃ D : Set T, t ∈ C → D ∈ 𝓓 ∧ t ∈ D := fun t => by
    by_cases ht : t ∈ C
    · obtain ⟨D, hD, h1⟩ := (hU ▸ ht : t ∈ ⋃₀ 𝓓)
      exact ⟨D, fun _ => ⟨hD, h1⟩⟩
    · exact ⟨∅, fun h' => absurd h' ht⟩
  choose dsc hdsc using hdsc
  have hdsc_eq : ∀ D ∈ 𝓓, ∀ t ∈ D, dsc t = D := fun D hD t ht => by
    have htC : t ∈ C := hU ▸ ⟨D, hD, ht⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdj _ (hdsc t htC).1 D hD hne) (hdsc t htC).2 ht
  have hclosed : ∀ D ∈ 𝓓, IsClosed D := fun D hD => (hd D hD).1.isClosed
  have hCcl : IsClosed C := hU ▸ hf.isClosed_sUnion hclosed
  have hb : ∀ {x}, x ∈ bd S → j x ∈ C := fun {x} hx => by
    have : j x ∈ range j ∩ C := hi ▸ mem_image_of_mem j hx
    exact this.2
  have hpull : ∀ φ ∈ KSet T K, pbk j φ ∈ KSet S K := fun φ hφ => by
    refine ⟨isCoc_pbk hj.continuous hφ.1, ?_⟩
    have hprim : ∀ D : Set T, ∃ g, D ∈ 𝓓 → Prim φ D g := fun D => by
      by_cases hD : D ∈ 𝓓
      · obtain ⟨g, hg⟩ := exists_prim_disc hφ.1 (hd D hD).1
        exact ⟨g, fun _ => hg⟩
      · exact ⟨0, fun h' => absurd h' hD⟩
    choose g hg using hprim
    let k₀ : T → K := fun t => g (dsc t) t
    have hW : ∀ p : T, ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ C, ∀ x' ∈ W ∩ C, φ x x' = k₀ x + k₀ x' := fun p => by
      by_cases hp : p ∈ C
      · obtain ⟨hD, hpD⟩ := hdsc p hp
        obtain ⟨W, hW, h1⟩ := hg _ hD p hpD
        have hR : IsClosed (⋃₀ (𝓓 \ {dsc p})) := (hf.subset sdiff_subset).isClosed_sUnion fun D h
          => hclosed D h.1
        have hpR : p ∉ ⋃₀ (𝓓 \ {dsc p}) := by
          rintro ⟨D, hD', h2⟩
          exact hD'.2 (hdsc_eq D hD'.1 p h2).symm
        refine ⟨W ∩ (⋃₀ (𝓓 \ {dsc p}))ᶜ, inter_mem hW (hR.isOpen_compl.mem_nhds hpR),
          fun x hx x' hx' => ?_⟩
        have hin : ∀ {y}, y ∈ (W ∩ (⋃₀ (𝓓 \ {dsc p}))ᶜ) ∩ C → y ∈ dsc p ∧ dsc y = dsc p
          := fun {y} hy => by
          have h2 := hdsc y hy.2
          by_cases he : dsc y = dsc p
          · exact ⟨he ▸ h2.2, he⟩
          · exact absurd ⟨dsc y, ⟨h2.1, he⟩, h2.2⟩ hy.1.2
        obtain ⟨h3, h4⟩ := hin hx
        obtain ⟨h5, h6⟩ := hin hx'
        change φ x x' = g (dsc x) x + g (dsc x') x'
        rw [h4, h6]
        exact h1 x ⟨hx.1.1, h3⟩ x' ⟨hx'.1.1, h5⟩
      · exact ⟨Cᶜ, hCcl.isOpen_compl.mem_nhds hp, fun x hx => absurd hx.2 hx.1⟩
    choose W hW hWp using hW
    refine ⟨k₀ ∘ j, ⋃ p, (j ⁻¹' W p) ×ˢ (j ⁻¹' W p), fun a => ?_, fun x hx y hy hxy => ?_⟩
    · have h1 : j ⁻¹' W (j a) ∈ 𝓝 a := hj.continuous.continuousAt.preimage_mem_nhds (hW (j a))
      exact Filter.mem_of_superset (prod_mem_nhds h1 h1) (subset_iUnion (fun p => (j ⁻¹' W p) ×ˢ
        (j ⁻¹' W p)) (j a))
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hxy
      have h1 := hWp p (j x) ⟨hp.1, hb hx⟩ (j y) ⟨hp.2, hb hy⟩
      change φ (j x) (j y) = _
      rw [h1, CharTwo.neg_eq]
      rfl
  have hrel : ∀ φ φ' : T → T → K, CohRel φ φ' → CohRel (pbk j φ) (pbk j φ') := fun φ φ' h => by
    obtain ⟨g, N, hN, h1⟩ := h
    have hc : Continuous fun p : S × S => (j p.1, j p.2) :=
      (hj.continuous.comp continuous_fst).prodMk (hj.continuous.comp continuous_snd)
    exact ⟨g ∘ j, (fun p : S × S => (j p.1, j p.2)) ⁻¹' N, fun x =>
      hc.continuousAt.preimage_mem_nhds (hN (j x)),
      fun x y hxy => h1 _ _ hxy⟩
  let F : KCl T K → KCl S K := Quotient.map' (s₁ := kSetoid T K) (s₂ := kSetoid S K) (fun φ
    => ⟨pbk j φ.1, hpull φ.1 φ.2⟩)
    (fun φ φ' h => hrel φ.1 φ'.1 h)
  refine ⟨F, ?_⟩
  refine Quotient.ind₂ fun φ φ' he => Quotient.sound ?_
  obtain ⟨g, N, hN, h1⟩ : CohRel (pbk j φ.1) (pbk j φ'.1) := Quotient.exact he
  let ψ : T → T → K := fun x y => φ.1 x y + φ'.1 x y
  have hψc : IsCoc ψ := by
    obtain ⟨N₁, hN₁, c₁⟩ := φ.2.1
    obtain ⟨N₂, hN₂, c₂⟩ := φ'.2.1
    refine ⟨N₁ ∩ N₂, fun x => inter_mem (hN₁ x) (hN₂ x), fun x y z h2 h3 h4 => ?_⟩
    simp only [ψ]
    rw [← c₁ x y z h2.1 h3.1 h4.1, ← c₂ x y z h2.2 h3.2 h4.2]
    ring
  let gt : T → K := Function.extend j g 0
  have hgt : ∀ x, gt (j x) = g x := fun x => hj.injective.extend_apply g 0 x
  have hp₀ : Prim ψ (range j) gt := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hN a)
    have h2 : A ∩ B ∈ comap j (𝓝 (j a)) := by
      rw [← hj.isInducing.nhds_eq_comap]
      exact inter_mem hA hB
    obtain ⟨W, hW, h3⟩ := mem_comap.mp h2
    refine ⟨W, hW, ?_⟩
    rintro _ ⟨hx, x, rfl⟩ _ ⟨hx', x', rfl⟩
    have h4 := h1 x x' (hAB ⟨(h3 hx).1, (h3 hx').2⟩)
    change φ.1 (j x) (j x') + φ'.1 (j x) (j x') = gt (j x) + gt (j x')
    change φ.1 (j x) (j x') - φ'.1 (j x) (j x') = _ at h4
    rw [hgt, hgt, ← CharTwo.sub_eq_add, h4, CharTwo.sub_eq_add, add_comm]
  have hext : ∀ D : Set T, ∃ h : T → K, (D ∈ 𝓓 → Prim ψ D h) ∧ (D ∈ 𝓓 → ∀ t ∈ D ∩ range j, h t
    = gt t) := fun D => by
    by_cases hD : D ∈ 𝓓
    · obtain ⟨h₀, hh⟩ := exists_prim_disc hψc (hd D hD).1
      obtain ⟨a, ha⟩ := (hd D hD).2.2
      let c := h₀ a + gt a
      refine ⟨fun t => h₀ t + c, fun _ p hp => ?_, fun _ t ht => ?_⟩
      · obtain ⟨W, hW, h2⟩ := hh p hp
        refine ⟨W, hW, fun x hx x' hx' => ?_⟩
        rw [h2 x hx x' hx']
        have h3 : h₀ x + c + (h₀ x' + c) = h₀ x + h₀ x' + (c + c) := by ring
        rw [h3, CharTwo.add_self_eq_zero, add_zero]
      · have h2 := hh.const hp₀ (hd D hD).2.1 inter_subset_left inter_subset_right ht ha
        have h3 : h₀ t + gt t + gt t = h₀ a + gt a + gt t := by rw [h2]
        have h4 : h₀ t + gt t + gt t = h₀ t + (gt t + gt t) := by ring
        rw [h4, CharTwo.add_self_eq_zero, add_zero] at h3
        change h₀ t + (h₀ a + gt a) = gt t
        rw [h3]
        have h5 : h₀ a + gt a + gt t + (h₀ a + gt a) = (h₀ a + gt a) + (h₀ a + gt a) + gt t := by
          ring
        rw [h5, CharTwo.add_self_eq_zero, zero_add]
    · exact ⟨0, fun h' => absurd h' hD, fun h' => absurd h' hD⟩
  choose hx hxp hxe using hext
  let k : T → K := fun t => if t ∈ C then hx (dsc t) t else gt t
  have hkD : ∀ D ∈ 𝓓, ∀ t ∈ D, k t = hx D t := fun D hD t ht => by
    have htC : t ∈ C := hU ▸ ⟨D, hD, ht⟩
    simp only [k, htC, ite_true, hdsc_eq D hD t ht]
  have hkj : ∀ t ∈ range j, k t = gt t := fun t ht => by
    by_cases htC : t ∈ C
    · obtain ⟨hD, hmem⟩ := hdsc t htC
      rw [hkD _ hD t hmem]
      exact hxe _ hD t ⟨hmem, ht⟩
    · simp only [k, htC, ite_false]
  have hcongr : ∀ {P : Set T} {u : T → K}, Prim ψ P u → (∀ t ∈ P, k t = u t) → Prim ψ P k
    := fun {P u} hu' he' p hp => by
    obtain ⟨W, hW, h2⟩ := hu' p hp
    refine ⟨W, hW, fun x hx' x' hx'' => ?_⟩
    rw [he' x hx'.2, he' x' hx''.2]
    exact h2 x hx' x' hx''
  refine glue_prim (𝓒 := insert (range j) 𝓓) (hf.insert _) ?_ ?_ φ.2.1 φ'.2.1 (k := k) ?_
  · rintro P (rfl | hP)
    · exact hj.isClosed_range
    · exact hclosed P hP
  · rw [sUnion_insert, hU, hu]
  · rintro P (rfl | hP)
    · exact hcongr hp₀ hkj
    · exact hcongr (hxp P hP) (hkD P hP)

theorem card_kCl_of_model {X : Type} [TopologicalSpace X] {a b c : ℕ}
  (e : X ≃ₜ SurfaceModel a b c) :
    Nat.card (KCl X K) = 2 ^ (2 * a + b) := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  rw [card_kCl_congr e, GraphMinor.Surface.card_kCl hf, card_lam_two]

end GraphMinor.Surface
