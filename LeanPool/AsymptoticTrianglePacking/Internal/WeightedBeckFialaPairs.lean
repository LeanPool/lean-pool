/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — Beck–Fiala rounding controlling degrees *and* codegrees

`Nibble.BeckFiala.exists_rounding` rounds a fractional selection `y : H → [0,1]` of an `r`-uniform
hypergraph to an integral subhypergraph whose *vertex degrees* match the fractional degrees up to
`r`.  For the weighted nibble one also needs the *codegrees* of the rounded hypergraph to be
controlled by the fractional (weighted) codegrees.

This file obtains both at once by running the same Beck–Fiala theorem on the auxiliary hypergraph
whose vertices are the subsets of size at most `2`:

* `Nibble.BeckFiala.pairClosure T` — the family `{s ⊆ T : |s| ≤ 2}`.  It has at most `1 + r²`
  elements, and `T` is recovered from it as `⋃ pairClosure T`, so `pairClosure` is injective.
* `Nibble.BeckFiala.exists_rounding_pairs` — the rounding theorem: degrees *and* codegrees of the
  rounded subhypergraph differ from the fractional ones by at most `1 + r²`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedBeckFiala

@[expose] public section

open Finset

namespace Nibble.BeckFiala

variable {V : Type*} [DecidableEq V]

/-- The subsets of `T` of size at most `2`. -/
def pairClosure (T : Finset V) : Finset (Finset V) := T.powerset.filter (fun s => s.card ≤ 2)

omit [DecidableEq V] in
theorem mem_pairClosure {T s : Finset V} : s ∈ pairClosure T ↔ s ⊆ T ∧ s.card ≤ 2 := by
  simp [pairClosure, Finset.mem_filter, Finset.mem_powerset]

/-- `T` is recovered from `pairClosure T` as the union of its members. -/
theorem biUnion_pairClosure (T : Finset V) : (pairClosure T).biUnion id = T := by
  ext v
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨s, hs, hvs⟩
    exact (mem_pairClosure.mp hs).1 hvs
  · intro hv
    exact ⟨{v}, mem_pairClosure.mpr ⟨Finset.singleton_subset_iff.mpr hv, by simp⟩, by simp⟩

theorem pairClosure_injective : Function.Injective (pairClosure : Finset V → Finset (Finset V)) := by
  intro a b hab
  rw [← biUnion_pairClosure a, hab, biUnion_pairClosure]

omit [DecidableEq V] in
theorem singleton_mem_pairClosure {T : Finset V} {v : V} : {v} ∈ pairClosure T ↔ v ∈ T := by
  rw [mem_pairClosure]
  simp [Finset.singleton_subset_iff]

theorem pair_mem_pairClosure {T : Finset V} {x z : V} :
    ({x, z} : Finset V) ∈ pairClosure T ↔ (x ∈ T ∧ z ∈ T) := by
  rw [mem_pairClosure]
  constructor
  · rintro ⟨hsub, -⟩
    exact ⟨hsub (by simp), hsub (by simp)⟩
  · rintro ⟨hx, hz⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hx
      · rw [Finset.mem_singleton] at ha'; subst ha'; exact hz
    · exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- The auxiliary vertex set of an edge has at most `1 + |T|²` elements. -/
theorem card_pairClosure_le (T : Finset V) : (pairClosure T).card ≤ 1 + T.card * T.card := by
  have hsub : pairClosure T ⊆ insert (∅ : Finset V)
      ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V))) := by
    intro s hs
    obtain ⟨hsub, hcard⟩ := mem_pairClosure.mp hs
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · exact Finset.mem_insert_self _ _
    refine Finset.mem_insert_of_mem ?_
    interval_cases h : s.card
    · exact absurd (Finset.card_eq_zero.mp h) (Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩)
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h
      subst hb
      refine Finset.mem_image.mpr ⟨(b, b), Finset.mem_product.mpr
        ⟨hsub (by simp), hsub (by simp)⟩, ?_⟩
      simp
    · obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp h
      exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr
        ⟨hsub (by simp), hsub (by simp)⟩, rfl⟩
  calc (pairClosure T).card
      ≤ (insert (∅ : Finset V) ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V)))).card :=
        Finset.card_le_card hsub
    _ ≤ 1 + ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V))).card := by
        have := Finset.card_insert_le (∅ : Finset V)
          ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V)))
        omega
    _ ≤ 1 + (T ×ˢ T).card := by
        have := Finset.card_image_le (s := T ×ˢ T)
          (f := fun p : V × V => ({p.1, p.2} : Finset V))
        omega
    _ = 1 + T.card * T.card := by rw [Finset.card_product]

/-- **Beck–Fiala rounding with codegree control.**  Every fractional selection `y : H → [0,1]` of an
`r`-uniform hypergraph `H` can be rounded to a subhypergraph `S ⊆ H` whose degrees *and* codegrees
differ from the fractional degrees and codegrees by at most `1 + r²`. -/
theorem exists_rounding_pairs (r : ℕ) (H : Finset (Finset V)) (hunif : ∀ T ∈ H, T.card = r)
    (y : Finset V → ℝ) (hy0 : ∀ T ∈ H, 0 ≤ y T) (hy1 : ∀ T ∈ H, y T ≤ 1) :
    ∃ S ⊆ H,
      (∀ v : V, |((S.filter (fun T => v ∈ T)).card : ℝ)
          - ∑ T ∈ H.filter (fun T => v ∈ T), y T| ≤ 1 + (r : ℝ) * r) ∧
      (∀ x z : V, |((S.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
          - ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T| ≤ 1 + (r : ℝ) * r) := by
  classical
  set k : ℕ := 1 + r * r with hkdef
  set Hs : Finset (Finset (Finset V)) := H.image pairClosure with hHsdef
  set ys : Finset (Finset V) → ℝ := fun U => y (U.biUnion id) with hysdef
  -- every auxiliary edge is a `pairClosure`
  have hmemHs : ∀ U ∈ Hs, (U.biUnion id) ∈ H ∧ U = pairClosure (U.biUnion id) := by
    intro U hU
    rw [hHsdef, Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [biUnion_pairClosure]
    exact ⟨hT, rfl⟩
  have hk : ∀ U ∈ Hs, U.card ≤ k := by
    intro U hU
    rw [hHsdef, Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    have := card_pairClosure_le T
    rw [hunif T hT] at this
    exact this
  have hys0 : ∀ U ∈ Hs, 0 ≤ ys U := fun U hU => hy0 _ (hmemHs U hU).1
  have hys1 : ∀ U ∈ Hs, ys U ≤ 1 := fun U hU => hy1 _ (hmemHs U hU).1
  obtain ⟨Ss, hSsHs, -, -, hbound⟩ := exists_rounding k Hs hk ys hys0 hys1
  -- injectivity of the projection on the auxiliary family
  have hinjOn : ∀ (A : Finset (Finset (Finset V))), A ⊆ Hs →
      Set.InjOn (fun U : Finset (Finset V) => U.biUnion id) ↑A := by
    intro A hA U hU U' hU' heq
    have h1 := (hmemHs U (hA hU)).2
    have h2 := (hmemHs U' (hA hU')).2
    have heq' : U.biUnion id = U'.biUnion id := heq
    calc U = pairClosure (U.biUnion id) := h1
      _ = pairClosure (U'.biUnion id) := by rw [heq']
      _ = U' := h2.symm
  refine ⟨Ss.image (fun U => U.biUnion id), ?_, ?_, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmemHs U (hSsHs hU)).1
  · -- degrees
    intro v
    have hcard : (((Ss.image (fun U => U.biUnion id)).filter (fun T => v ∈ T)).card : ℝ)
        = ((Ss.filter (fun U => ({v} : Finset V) ∈ U)).card : ℝ) := by
      have h1 : (Ss.image (fun U => U.biUnion id)).filter (fun T => v ∈ T)
          = (Ss.filter (fun U => v ∈ U.biUnion id)).image (fun U => U.biUnion id) :=
        Finset.filter_image
      have h2 : Ss.filter (fun U => v ∈ U.biUnion id)
          = Ss.filter (fun U => ({v} : Finset V) ∈ U) := by
        refine Finset.filter_congr ?_
        intro U hU
        rw [(hmemHs U (hSsHs hU)).2]
        simp only [biUnion_pairClosure, singleton_mem_pairClosure]
      rw [h1, h2, Finset.card_image_of_injOn (hinjOn _ (Finset.Subset.trans
        (Finset.filter_subset _ _) hSsHs))]
    have hsum : ∑ U ∈ Hs.filter (fun U => ({v} : Finset V) ∈ U), ys U
        = ∑ T ∈ H.filter (fun T => v ∈ T), y T := by
      have h1 : Hs.filter (fun U => ({v} : Finset V) ∈ U)
          = (H.filter (fun T => v ∈ T)).image pairClosure := by
        rw [hHsdef, Finset.filter_image]
        congr 1
        refine Finset.filter_congr ?_
        intro T _
        simp [singleton_mem_pairClosure]
      rw [h1, Finset.sum_image (fun a _ b _ h => pairClosure_injective h)]
      exact Finset.sum_congr rfl (fun T _ => by rw [hysdef]; simp [biUnion_pairClosure])
    have h := hbound ({v} : Finset V)
    rw [hsum] at h
    rw [hcard]
    exact le_trans h (by push_cast [hkdef]; linarith)
  · -- codegrees
    intro x z
    have hcard : (((Ss.image (fun U => U.biUnion id)).filter
          (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
        = ((Ss.filter (fun U => ({x, z} : Finset V) ∈ U)).card : ℝ) := by
      have h1 : (Ss.image (fun U => U.biUnion id)).filter (fun T => x ∈ T ∧ z ∈ T)
          = (Ss.filter (fun U => x ∈ U.biUnion id ∧ z ∈ U.biUnion id)).image
              (fun U => U.biUnion id) := Finset.filter_image
      have h2 : Ss.filter (fun U => x ∈ U.biUnion id ∧ z ∈ U.biUnion id)
          = Ss.filter (fun U => ({x, z} : Finset V) ∈ U) := by
        refine Finset.filter_congr ?_
        intro U hU
        rw [(hmemHs U (hSsHs hU)).2]
        simp only [biUnion_pairClosure, pair_mem_pairClosure]
      rw [h1, h2, Finset.card_image_of_injOn (hinjOn _ (Finset.Subset.trans
        (Finset.filter_subset _ _) hSsHs))]
    have hsum : ∑ U ∈ Hs.filter (fun U => ({x, z} : Finset V) ∈ U), ys U
        = ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T := by
      have h1 : Hs.filter (fun U => ({x, z} : Finset V) ∈ U)
          = (H.filter (fun T => x ∈ T ∧ z ∈ T)).image pairClosure := by
        rw [hHsdef, Finset.filter_image]
        congr 1
        refine Finset.filter_congr ?_
        intro T _
        simp [pair_mem_pairClosure]
      rw [h1, Finset.sum_image (fun a _ b _ h => pairClosure_injective h)]
      exact Finset.sum_congr rfl (fun T _ => by rw [hysdef]; simp [biUnion_pairClosure])
    have h := hbound ({x, z} : Finset V)
    rw [hsum] at h
    rw [hcard]
    exact le_trans h (by push_cast [hkdef]; linarith)

end Nibble.BeckFiala
