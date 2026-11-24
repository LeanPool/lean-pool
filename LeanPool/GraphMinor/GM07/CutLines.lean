/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutStages
public import LeanPool.GraphMinor.GM07.DiscPlace

/-!
# Lifting a line through a cut

Let `θ` undo a cut, so that `θ` is one to one off a closed set `B`. An arc that meets `B` at most at
its first point lifts to an arc (`exists_lift_arc`). The lift off `B` is forced. The point to prove
is that the lift has one limit
at the first point, even though the fiber over it can have several points: the fiber is finite, and
the preimage of a small piece of the arc is connected, so it stays near one point of the fiber.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM19

universe u

local notation "𝕀" => unitInterval

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

theorem exists_Iio_subset {N : Set 𝕀} (hN : IsOpen N) (h0 : (0 : 𝕀) ∈ N) : ∃ e : 𝕀, 0 < e
  ∧ Iio e ⊆ N := by
  have h := (nhds_bot_basis (α := 𝕀)).mem_iff.mp (hN.mem_nhds h0)
  exact h

/-- Over the first point of the arc, the closure of the lift off `B` has at most one point. -/
theorem eq_of_mem_closure_lift [CompactSpace Y] [T2Space Y] [T2Space S] {B : Set S} {θ : Y → S}
  (hθ : IsCutMap θ B) (hB : IsClosed B) {a : 𝕀 → S} (ha : IsArcMap a) (hoff : ∀ t, t ≠ 0 → a t ∉ B)
    {x y : Y} (hx : x ∈ closure (θ ⁻¹' (a '' {t | t ≠ 0}))) (hy : y ∈ closure (θ ⁻¹'
      (a '' {t | t ≠ 0}))) (hx0 : θ x = a 0) (hy0 : θ y = a 0) : x = y := by
  classical
  by_contra hne
  have hfin : (θ ⁻¹' {a 0} \ {x}).Finite := (hθ.2.2.2.1 (a 0)).subset sdiff_subset
  obtain ⟨U, V, hU, hV, hxU, hsV, hUV⟩ := SeparatedNhds.of_finite (finite_singleton x) hfin
    (by simp)
  have hxU' : x ∈ U := hxU rfl
  have hyV : y ∈ V := hsV ⟨hy0, fun h => hne (Eq.symm h)⟩
  have hK : IsClosed (θ '' (U ∪ V)ᶜ) := hθ.1.isClosedMap _ (hU.union hV).isClosed_compl
  have h0 : (0 : 𝕀) ∈ a ⁻¹' (θ '' (U ∪ V)ᶜ)ᶜ := by
    rintro ⟨z, hz, he⟩
    by_cases hzx : z = x
    · exact hz (.inl (hzx ▸ hxU'))
    · exact hz (.inr (hsV ⟨he, hzx⟩))
  obtain ⟨e, he, hsub⟩ := exists_Iio_subset (hK.isOpen_compl.preimage ha.1) h0
  let W : Set Y := θ ⁻¹' (a '' Ioo 0 e)
  have hWsub : W ⊆ U ∪ V := fun z ⟨t, ht, hz⟩ => by
    by_contra hn
    exact hsub ht.2 ⟨z, hn, hz.symm⟩
  have hWp : IsPreconnected W := isPreconnected_preimage_of_isCutMap hθ hB (by
    rintro _ ⟨t, ht, rfl⟩
    exact hoff t ht.1.ne') (isPreconnected_Ioo.image a ha.1.continuousOn)
  have hclosed : IsClosed (θ ⁻¹' (a '' Ici e)) := ((isClosed_Ici.isCompact.image
    ha.1).isClosed).preimage hθ.1
  have hcov : θ ⁻¹' (a '' {t | t ≠ 0}) ⊆ W ∪ θ ⁻¹' (a '' Ici e) := fun z ⟨t, ht, hz⟩ => by
    by_cases hte : t < e
    · exact .inl ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht, hte⟩, hz⟩
    · exact .inr ⟨t, not_lt.mp hte, hz⟩
  have hin : ∀ {z : Y}, z ∈ closure (θ ⁻¹' (a '' {t | t ≠ 0})) → θ z = a 0 → z ∈ closure W
    := fun hz h0z => by
    have h1 := closure_mono hcov hz
    rw [closure_union, hclosed.closure_eq] at h1
    rcases h1 with h1 | ⟨t, ht, h2⟩
    · exact h1
    · have : t = 0 := ha.2 (h2.trans h0z)
      exact absurd (mem_Ici.mp ht) (by rw [this]; exact not_le.mpr he)
  rcases IsPreconnected.subset_or_subset hU hV hUV hWsub hWp with h | h
  · obtain ⟨z, hzV, hzW⟩ := mem_closure_iff.mp (hin hy hy0) V hV hyV
    exact disjoint_left.mp hUV (h hzW) hzV
  · obtain ⟨z, hzU, hzW⟩ := mem_closure_iff.mp (hin hx hx0) U hU hxU'
    exact disjoint_left.mp hUV hzU (h hzW)

/-- **An arc lifts through a cut.** An arc that meets `B` at most at its first point lifts to an
arc. -/
theorem exists_lift_arc [CompactSpace Y] [T2Space Y] [T2Space S] {B : Set S} {θ : Y → S}
  (hθ : IsCutMap θ B) (hB : IsClosed B) {a : 𝕀 → S} (ha : IsArcMap a) (hoff : ∀ t, t ≠ 0
    → a t ∉ B) :
    ∃ b : 𝕀 → Y, IsArcMap b ∧ ∀ t, θ (b t) = a t := by
  classical
  let W : Set Y := θ ⁻¹' (a '' {t | t ≠ 0})
  have hTc : IsCompact (closure W) := isClosed_closure.isCompact
  have hsub : ∀ z ∈ closure W, ∃ t, θ z = a t := fun z hz => by
    have hc : IsClosed (θ ⁻¹' range a) := (isCompact_range ha.1).isClosed.preimage hθ.1
    have h1 : closure W ⊆ θ ⁻¹' range a := closure_minimal (fun w ⟨t, _, hw⟩ => ⟨t, hw⟩) hc
    obtain ⟨t, ht⟩ := h1 hz
    exact ⟨t, ht.symm⟩
  have hon : ∀ t, ∃ z ∈ closure W, θ z = a t := fun t => by
    by_cases ht : t = 0
    · subst ht
      by_contra hn
      have hcl : IsClosed (θ '' closure W) := hθ.1.isClosedMap _ isClosed_closure
      have h0 : (0 : 𝕀) ∈ a ⁻¹' (θ '' closure W)ᶜ := fun ⟨z, hz, he⟩ => hn ⟨z, hz, he⟩
      obtain ⟨e, he, hs⟩ := exists_Iio_subset (hcl.isOpen_compl.preimage ha.1) h0
      obtain ⟨m, hm0, hme⟩ := exists_between he
      obtain ⟨z, hz⟩ := hθ.2.1 (a m)
      exact hs hme ⟨z, subset_closure ⟨m, hm0.ne', hz.symm⟩, hz⟩
    · obtain ⟨z, hz⟩ := hθ.2.1 (a t)
      exact ⟨z, subset_closure ⟨t, ht, hz.symm⟩, hz⟩
  have hinj : InjOn θ (closure W) := fun x hx y hy he => by
    obtain ⟨t, ht⟩ := hsub x hx
    by_cases h0 : t = 0
    · subst h0
      exact eq_of_mem_closure_lift hθ hB ha hoff hx hy ht (he ▸ ht)
    · have h1 : θ x ∈ Bᶜ := ht ▸ hoff t h0
      exact hθ.2.2.1 h1 (show θ y ∈ Bᶜ from he ▸ h1) he
  have : CompactSpace (closure W) := isCompact_iff_compactSpace.mp hTc
  let j : closure W → S := fun z => θ z.1
  have hj : Continuous j := hθ.1.comp continuous_subtype_val
  have hji : Function.Injective j := fun x y he => Subtype.ext (hinj x.2 y.2 he)
  have hemb := hj.isClosedEmbedding hji
  choose z hzT hz using hon
  let b' : 𝕀 → closure W := fun t => ⟨z t, hzT t⟩
  have hb' : Continuous b' := by
    rw [hemb.isInducing.continuous_iff]
    have : j ∘ b' = a := funext hz
    rw [this]
    exact ha.1
  refine ⟨fun t => z t, ⟨continuous_subtype_val.comp hb', fun s t he => ha.2 ?_⟩, hz⟩
  have he' : z s = z t := he
  rw [← hz s, ← hz t, he']

/-- **A line lifts through a cut.** -/
theorem exists_lift_line [CompactSpace Y] [T2Space Y] [T2Space S] {B : Set S} {θ : Y → S}
  (hθ : IsCutMap θ B) (hB : IsClosed B) {A : Set S} {p q : S} (hA : IsLineWithEnds A p q)
    (hAB : A ∩ B ⊆ {p}) :
    ∃ (A' : Set Y) (p' q' : Y), IsLineWithEnds A' p' q' ∧ θ p' = p ∧ θ q' = q ∧ θ '' A' = A
      ∧ InjOn θ A' ∧ θ ⁻¹' (A ∪ B) = A' ∪ θ ⁻¹' B := by
  obtain ⟨a, ha, hr, ha0, ha1⟩ := hA.exists_arc
  have hoff : ∀ t, t ≠ 0 → a t ∉ B := fun t ht hb => by
    have h1 : a t = p := hAB ⟨hr ▸ mem_range_self t, hb⟩
    exact ht (ha.2 (h1.trans ha0.symm))
  obtain ⟨b, hb, hba⟩ := exists_lift_arc hθ hB ha hoff
  have hrθ : θ '' range b = A := by
    rw [← hr, ← range_comp]
    congr 1
    exact funext hba
  refine ⟨range b, b 0, b 1, ?_, by rw [hba, ha0], by rw [hba, ha1], hrθ, ?_, ?_⟩
  · exact isLineWithEnds_range_of_arc hb
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ he
    rw [ha.2 (by rw [← hba, ← hba, he] : a s = a t)]
  · ext z
    constructor
    · rintro (hz | hz)
      · rw [← hr] at hz
        obtain ⟨t, ht⟩ := hz
        by_cases h0 : t = 0
        · subst h0
          by_cases hpB : p ∈ B
          · exact .inr (show θ z ∈ B by rw [← ht, ha0]; exact hpB)
          · have h1 : θ z ∈ Bᶜ := by rw [← ht, ha0]; exact hpB
            have h2 : θ (b 0) ∈ Bᶜ := by rw [hba, ha0]; exact hpB
            exact .inl ⟨0, hθ.2.2.1 h2 h1 (by rw [hba, ht])⟩
        · have h1 : θ z ∈ Bᶜ := by rw [← ht]; exact hoff t h0
          have h2 : θ (b t) ∈ Bᶜ := by rw [hba]; exact hoff t h0
          exact .inl ⟨t, hθ.2.2.1 h2 h1 (by rw [hba, ht])⟩
      · exact .inr hz
    · rintro (⟨t, rfl⟩ | hz)
      · refine .inl ?_
        rw [hba, ← hr]
        exact mem_range_self t
      · exact .inr hz

end GraphMinor.GM07
