/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM07.NetSwapDisc
import LeanPool.GraphMinor.GM07.NetSwapFrontier
import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# The quotient map for pasting the net pieces

VII (2.6), page 218, pastes a paired subarc after cutting the
source disc along a proper line. The two-piece disc model gives
a continuous surjection onto a closed disc. Compactness makes
it a quotient map. Its fibers identify exactly the prescribed
boundary points, so a map constant on the pasted pairs can be
carried to the new disc.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

universe u v

/-- The quotient map pasting two closed discs along the given
boundary parametrizations, for the net exchange in VII (2.6),
page 218. No other identifications are made. -/
theorem exists_disc_pasting_quotient
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : unitInterval → X) (g : unitInterval → Y) (hf : IsArcMap f) (hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B) :
    ∃ ψ : A ⊕ B → closedBall (0 : ℂ) 1,
      IsQuotientMap ψ ∧ Function.Injective (ψ ∘ Sum.inl) ∧
      Function.Injective (ψ ∘ Sum.inr) ∧
      (∀ (x : A) (y : B), ψ (Sum.inl x) = ψ (Sum.inr y) ↔
        ∃ t, x.val = f t ∧ y.val = g t) ∧
      (∀ x : A, ψ (Sum.inl x) ∈ bd (closedBall (0 : ℂ) 1) ↔
        x.val ∈ discBd A ∧ x.val ∉ f '' Ioo (0 : unitInterval) 1) ∧
      (∀ y : B, ψ (Sum.inr y) ∈ bd (closedBall (0 : ℂ) 1) ↔
        y.val ∈ discBd B ∧ y.val ∉ g '' Ioo (0 : unitInterval) 1) := by
  obtain ⟨p, q, hpc, hqc, hpi, hqi, hcover, hmatch, hpair⟩ :=
    exists_disc_pasting_model hA hB f g hf hg hfbd hgbd
  have hpball : ∀ x ∈ A, p x ∈ closedBall (0 : ℂ) 1 :=
    fun x hx => hcover ▸ Or.inl (mem_image_of_mem p hx)
  have hqball : ∀ y ∈ B, q y ∈ closedBall (0 : ℂ) 1 :=
    fun y hy => hcover ▸ Or.inr (mem_image_of_mem q hy)
  let p' : A → closedBall (0 : ℂ) 1 := fun x => ⟨p x.val, hpball x.val x.property⟩
  let q' : B → closedBall (0 : ℂ) 1 := fun y => ⟨q y.val, hqball y.val y.property⟩
  let ψ : A ⊕ B → closedBall (0 : ℂ) 1 := Sum.elim p' q'
  have hpc' : Continuous p' := hpc.domRestrict.subtype_mk _
  have hqc' : Continuous q' := hqc.domRestrict.subtype_mk _
  have hψc : Continuous ψ := hpc'.sumElim hqc'
  have hψs : Function.Surjective ψ := by
    intro z
    have hz : z.val ∈ p '' A ∪ q '' B := hcover.symm ▸ z.property
    rcases hz with ⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, Subtype.ext hxz⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, Subtype.ext hyz⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  have hunit : ∀ z : closedBall (0 : ℂ) 1,
      z ∈ bd (closedBall (0 : ℂ) 1) ↔ z.val ∈ sphere (0 : ℂ) 1 := by
    intro z
    rw [← isClosedDisc_closedBall.2]
    change z ∈ bd (closedBall (0 : ℂ) 1) ↔ z.val ∈ Subtype.val '' bd (closedBall (0 : ℂ) 1)
    constructor
    · exact fun hz => ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      exact Subtype.val_injective hwz ▸ hw
  refine ⟨ψ, IsQuotientMap.of_surjective_continuous hψs hψc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y heq
    exact Subtype.ext (hpi x.property y.property (congrArg Subtype.val heq))
  · intro x y heq
    exact Subtype.ext (hqi x.property y.property (congrArg Subtype.val heq))
  · intro x y
    exact (Subtype.ext_iff).trans (hmatch x.val x.property y.val y.property)
  · intro x
    exact (hunit (ψ (Sum.inl x))).trans
      (mem_boundary_of_disc_pasting_model hA hB f g hf hg hfbd hgbd p q hpc hqc hpi hqi
        hcover hmatch hpair x.property)
  · intro y
    have hmatch' : ∀ y ∈ B, ∀ x ∈ A, q y = p x ↔ ∃ t, y = g t ∧ x = f t := by
      intro y hy x hx
      constructor
      · intro heq
        obtain ⟨t, ht, ht'⟩ := (hmatch x hx y hy).mp heq.symm
        exact ⟨t, ht', ht⟩
      · rintro ⟨t, rfl, rfl⟩
        exact (hpair t).symm
    have hcover' : q '' B ∪ p '' A = closedBall (0 : ℂ) 1 := by
      rw [union_comm]
      exact hcover
    exact (hunit (ψ (Sum.inr y))).trans
      (mem_boundary_of_disc_pasting_model hB hA g f hg hf hgbd hfbd q p hqc hpc hqi hpi
        hcover' hmatch' (fun t => (hpair t).symm) y.property)

/-- A continuous map on each piece, agreeing on the pasted
parameters, descends continuously to the new closed disc.
This carries the original net surjection through the pasting
step of VII (2.6), page 218. -/
theorem exists_map_on_pasted_disc
    {X : Type u} {Y : Type v} {S : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : unitInterval → X) (g : unitInterval → Y) (hf : IsArcMap f) (hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B)
    (α : X → S) (β : Y → S) (hα : ContinuousOn α A) (hβ : ContinuousOn β B)
    (hαβ : ∀ t, α (f t) = β (g t)) :
    ∃ (ψ : A ⊕ B → closedBall (0 : ℂ) 1) (φ : closedBall (0 : ℂ) 1 → S),
      IsQuotientMap ψ ∧ Continuous φ ∧
      (∀ x : A, φ (ψ (Sum.inl x)) = α x.val) ∧
      (∀ y : B, φ (ψ (Sum.inr y)) = β y.val) ∧
      Function.Injective (ψ ∘ Sum.inl) ∧ Function.Injective (ψ ∘ Sum.inr) ∧
      (∀ (x : A) (y : B), ψ (Sum.inl x) = ψ (Sum.inr y) ↔
        ∃ t, x.val = f t ∧ y.val = g t) ∧
      (∀ x : A, ψ (Sum.inl x) ∈ bd (closedBall (0 : ℂ) 1) ↔
        x.val ∈ discBd A ∧ x.val ∉ f '' Ioo (0 : unitInterval) 1) ∧
      (∀ y : B, ψ (Sum.inr y) ∈ bd (closedBall (0 : ℂ) 1) ↔
        y.val ∈ discBd B ∧ y.val ∉ g '' Ioo (0 : unitInterval) 1) := by
  classical
  obtain ⟨ψ, hψ, hinl, hinr, hcross, hbA, hbB⟩ := exists_disc_pasting_quotient hA hB f g hf hg hfbd
    hgbd
  let h : A ⊕ B → S := Sum.elim (fun x => α x.val) (fun y => β y.val)
  have hcongr : ∀ x y, ψ x = ψ y → h x = h y := by
    intro x y heq
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg (fun x : A => α x.val) (hinl heq)
      | inr y =>
        obtain ⟨t, hx, hy⟩ := (hcross x y).mp heq
        change α x.val = β y.val
        rw [hx, hy]
        exact hαβ t
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨t, hy, hx⟩ := (hcross y x).mp heq.symm
        change β x.val = α y.val
        rw [hx, hy]
        exact (hαβ t).symm
      | inr y => exact congrArg (fun y : B => β y.val) (hinr heq)
  let φ : closedBall (0 : ℂ) 1 → S := h ∘ Function.surjInv hψ.surjective
  have hφψ : ∀ x, φ (ψ x) = h x := fun x =>
    hcongr _ x (Function.surjInv_eq hψ.surjective (ψ x))
  have hc : Continuous φ := by
    apply hψ.continuous_iff.mpr
    rw [show φ ∘ ψ = h from funext hφψ]
    exact hα.domRestrict.sumElim hβ.domRestrict
  exact ⟨ψ, φ, hψ, hc, fun x => hφψ (Sum.inl x), fun y => hφψ (Sum.inr y),
    hinl, hinr, hcross, hbA, hbB⟩

end GraphMinor.GM07
