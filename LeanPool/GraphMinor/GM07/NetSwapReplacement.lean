/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetSwapArcs

/-!
# The lifted cutting line and the mate of a side

In VII (2.6), page 218, pasting identifies the chosen boundary
subarc with its mate. The cutting line meets the chosen side
only at its two ends. Its lift from the attached piece can
therefore meet the old mate only at the two matching endpoints.
This supplies the intersection needed to splice the new side.
-/

public section

namespace GraphMinor.GM07

open Set Surface

/-- In the pasted disc, the lift of the cutting line meets the
old mate precisely at the two matching endpoint parameters.
This is the intersection calculation for the replacement side
in VII (2.6), page 218. -/
theorem cutting_lift_meets_mate_only_at_ends
    {X T : Type*} [TopologicalSpace X]
    {x₀ x₁ y₀ y₁ : X} (a : Path x₀ x₁) (b : Path y₀ y₁)
    (ha : IsArcMap a) (hb : IsArcMap b) {u v : unitInterval} (huv : u < v)
    (c : Path (a u) (a v)) (hc : IsArcMap c)
    (hca : range c ∩ range a = {a u, a v})
    {A B : Set X} (hcA : ∀ s, c s ∈ A) (hbB : ∀ t, b t ∈ B)
    (α : A → T) (β : B → T)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ r, x.val = (a.subpath u v) r ∧ y.val = (b.subpath u v) r) :
    ∀ s t, α ⟨c s, hcA s⟩ = β ⟨b t, hbB t⟩ →
      (s = 0 ∧ t = u) ∨ (s = 1 ∧ t = v) := by
  intro s t heq
  obtain ⟨r, hcr, hbr⟩ := (hcross ⟨c s, hcA s⟩ ⟨b t, hbB t⟩).mp heq
  have hca' : c s ∈ {a u, a v} := hca.subset
    ⟨mem_range_self s, ⟨Icc.convexComb u v r, hcr.symm⟩⟩
  have har := isArcMap_subpath_of_lt a ha huv
  rcases hca' with hcu | hcv
  · have hs : s = 0 := hc.2 (hcu.trans c.source.symm)
    have hr : r = 0 := har.2 (hcr.symm.trans (hcu.trans (a.subpath u v).source.symm))
    have ht : t = u := hb.2 (hbr.trans (hr ▸ (b.subpath u v).source))
    exact Or.inl ⟨hs, ht⟩
  · have hcv' : c s = a v := mem_singleton_iff.mp hcv
    have hs : s = 1 := hc.2 (hcv'.trans c.target.symm)
    have hr : r = 1 := har.2 (hcr.symm.trans (hcv'.trans (a.subpath u v).target.symm))
    have ht : t = v := hb.2 (hbr.trans (hr ▸ (b.subpath u v).target))
    exact Or.inr ⟨hs, ht⟩

/-- Splice the attached lift into the mate side. The pasting
fiber equation proves that the inserted path meets the old
mate only at its two ends, so the result is an arc. -/
theorem isArcMap_spliced_mate_path
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {x₀ x₁ y₀ y₁ : X} (a : Path x₀ x₁) (b : Path y₀ y₁)
    (ha : IsArcMap a) (hb : IsArcMap b)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (c : Path (a u) (a v)) (hc : IsArcMap c)
    (hca : range c ∩ range a = {a u, a v})
    {A B : Set X} (hcA : ∀ s, c s ∈ A) (hbB : ∀ t, b t ∈ B)
    (α : A → T) (β : B → T) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ r, x.val = (a.subpath u v) r ∧ y.val = (b.subpath u v) r)
    {z₀ z₁ : T} (base : Path z₀ z₁) (mid : Path (base u) (base v))
    (hbase : ∀ t, base t = β ⟨b t, hbB t⟩)
    (hmid : ∀ s, mid s = α ⟨c s, hcA s⟩) :
    IsArcMap (((base.subpath 0 u).trans mid).trans (base.subpath v 1)) := by
  have hbaseArc : IsArcMap base := by
    refine ⟨base.continuous, ?_⟩
    intro s t heq
    rw [hbase s, hbase t] at heq
    exact hb.2 (congrArg Subtype.val (hβ heq))
  have hmidArc : IsArcMap mid := by
    refine ⟨mid.continuous, ?_⟩
    intro s t heq
    rw [hmid s, hmid t] at heq
    exact hc.2 (congrArg Subtype.val (hα heq))
  have hmeet : range mid ∩ range base = {base u, base v} := by
    apply Subset.antisymm
    · rintro z ⟨⟨s, hsz⟩, ⟨t, htz⟩⟩
      have heq : α ⟨c s, hcA s⟩ = β ⟨b t, hbB t⟩ := by
        rw [← hmid s, ← hbase t]
        exact hsz.trans htz.symm
      rcases cutting_lift_meets_mate_only_at_ends a b ha hb huv c hc hca hcA hbB
          α β hcross s t heq with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
      · exact Or.inl htz.symm
      · exact Or.inr htz.symm
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, mid.source⟩, mem_range_self u⟩
      · exact ⟨⟨1, mid.target⟩, mem_range_self v⟩
  exact isArcMap_spliced_path base hbaseArc hu huv hv mid hmidArc hmeet

/-- Replacing the middle portions of two internally disjoint sides
preserves internal disjointness when the inserted portions miss the
other side and each other. The retained portions are compared through
an injective map of the retained piece. In VII (2.6), page 218, the
inserted portions are the two lifts of the cutting line. -/
theorem internally_disjoint_replacement_sides
    {X T : Type*} (a b : unitInterval → X) {B : Set X} (β : B → T)
    (hβ : Function.Injective β)
    (hab : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range b)
    (hba : ∀ t ∈ Ioo (0 : unitInterval) 1, b t ∉ range a)
    (p q : unitInterval → T) (hp : Function.Injective p) (hq : Function.Injective q)
    {P Q : Set T}
    (hpr : range p ⊆ β '' {x : B | x.val ∈ range a} ∪ P)
    (hqr : range q ⊆ β '' {x : B | x.val ∈ range b} ∪ Q)
    (hP : Disjoint P (β '' {x : B | x.val ∈ range b}))
    (hQ : Disjoint Q (β '' {x : B | x.val ∈ range a}))
    (hPQ : Disjoint P Q)
    (hp0 : p 0 ∈ β '' {x : B | x.val = a 0})
    (hp1 : p 1 ∈ β '' {x : B | x.val = a 1})
    (hq0 : q 0 ∈ β '' {x : B | x.val = b 0})
    (hq1 : q 1 ∈ β '' {x : B | x.val = b 1}) :
    (∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range q) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, q t ∉ range p) := by
  have hends : ∀ (d : unitInterval → X) (k : unitInterval → T),
      k 0 ∈ β '' {x : B | x.val = d 0} →
      k 1 ∈ β '' {x : B | x.val = d 1} →
      ∀ x : B, x.val ∈ ({d 0, d 1} : Set X) → β x ∈ ({k 0, k 1} : Set T) := by
    intro d k hk0 hk1 x hx
    obtain ⟨x₀, hx₀, hx₀k⟩ := hk0
    obtain ⟨x₁, hx₁, hx₁k⟩ := hk1
    rcases hx with hx | hx
    · exact Or.inl ((congrArg β (Subtype.ext (hx.trans hx₀.symm))).trans hx₀k)
    · exact Or.inr ((congrArg β (Subtype.ext
        ((mem_singleton_iff.mp hx).trans hx₁.symm))).trans hx₁k)
  have hmeet : ∀ z ∈ range p ∩ range q,
      z ∈ ({p 0, p 1} : Set T) ∧ z ∈ ({q 0, q 1} : Set T) := by
    intro z hz
    rcases hpr hz.1 with ⟨x, ⟨s, hsx⟩, hxz⟩ | hzP
    · rcases hqr hz.2 with ⟨y, ⟨t, hty⟩, hyz⟩ | hzQ
      · have hxy : x = y := hβ (hxz.trans hyz.symm)
        have heq : a s = b t := hsx.trans ((congrArg Subtype.val hxy).trans hty.symm)
        have hs := range_inter_subset_endpoints a hab
          ⟨mem_range_self s, ⟨t, heq.symm⟩⟩
        have ht := range_inter_subset_endpoints b hba
          ⟨mem_range_self t, ⟨s, heq⟩⟩
        constructor
        · exact hxz ▸ hends a p hp0 hp1 x (hsx ▸ hs)
        · exact hyz ▸ hends b q hq0 hq1 y (hty ▸ ht)
      · exact (disjoint_left.mp hQ hzQ ⟨x, ⟨s, hsx⟩, hxz⟩).elim
    · rcases hqr hz.2 with hzB | hzQ
      · exact (disjoint_left.mp hP hzP hzB).elim
      · exact (disjoint_left.mp hPQ hzP hzQ).elim
  constructor
  · intro t ht hqt
    exact not_mem_endpoints_of_injective hp ht (hmeet _ ⟨mem_range_self t, hqt⟩).1
  · intro t ht hpt
    exact not_mem_endpoints_of_injective hq ht (hmeet _ ⟨hpt, mem_range_self t⟩).2

/-- Compare a replacement side with an unchanged side on the retained
piece. Only the replacement's inserted portion needs a new intersection
check. All retained contacts follow from the old two sides. -/
theorem internally_disjoint_replacement_retained_side
    {X T : Type*} (a b : unitInterval → X) {B : Set X} (β : B → T)
    (hβ : Function.Injective β) (hb : Function.Injective b)
    (hab : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range b)
    (hba : ∀ t ∈ Ioo (0 : unitInterval) 1, b t ∉ range a)
    (p q : unitInterval → T) (hp : Function.Injective p)
    {P : Set T} (hpr : range p ⊆ β '' {x : B | x.val ∈ range a} ∪ P)
    (hP : Disjoint P (β '' {x : B | x.val ∈ range b}))
    (hp0 : p 0 ∈ β '' {x : B | x.val = a 0})
    (hp1 : p 1 ∈ β '' {x : B | x.val = a 1})
    (hbB : ∀ t, b t ∈ B) (hq : ∀ t, q t = β ⟨b t, hbB t⟩) :
    (∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range q) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, q t ∉ range p) := by
  have hqi : Function.Injective q := by
    intro s t heq
    rw [hq s, hq t] at heq
    exact hb (congrArg Subtype.val (hβ heq))
  have hqr : range q ⊆ β '' {x : B | x.val ∈ range b} ∪ (∅ : Set T) := by
    rintro z ⟨t, rfl⟩
    exact Or.inl ⟨⟨b t, hbB t⟩, mem_range_self t, (hq t).symm⟩
  exact internally_disjoint_replacement_sides a b β hβ hab hba p q hp hqi hpr hqr
    hP (empty_disjoint _) (disjoint_empty _) hp0 hp1
    ⟨⟨b 0, hbB 0⟩, rfl, (hq 0).symm⟩ ⟨⟨b 1, hbB 1⟩, rfl, (hq 1).symm⟩

end GraphMinor.GM07
