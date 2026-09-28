/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development007
/-!
# Moving sofa: related mathematical developments

* `Area.NicheDecomposition`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Niche Decomposition
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem niche_three_regions_area (K : SpecialCapSpace) :
    ∀ E₀ Eᵣ Eₗ : Set Point,
      E₀ = capNiche K.val \ ((distinguishedCapSides K.val).1.upperHalfPlane ∪
        (distinguishedCapSides K.val).2.upperHalfPlane) →
      Eᵣ = capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane →
      Eₗ = capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane →
      MeasurableSet E₀ ∧ MeasurableSet Eᵣ ∧ MeasurableSet Eₗ ∧
      MeasureTheory.volume E₀ < ⊤ ∧ MeasureTheory.volume Eᵣ < ⊤ ∧
      MeasureTheory.volume Eₗ < ⊤ ∧
      Disjoint E₀ Eᵣ ∧ Disjoint E₀ Eₗ ∧ Disjoint Eᵣ Eₗ ∧
      E₀ ∪ Eᵣ ∪ Eₗ = capNiche K.val ∧
      ClassicalResults.area (capNiche K.val) =
        ClassicalResults.area E₀ + ClassicalResults.area Eᵣ + ClassicalResults.area Eₗ := by
  intro E₀ Eᵣ Eₗ h₀ hᵣ hₗ
  set N := capNiche K.val with hN
  set HR := (distinguishedCapSides K.val).1.upperHalfPlane with hHR
  set HL := (distinguishedCapSides K.val).2.upperHalfPlane with hHL
  subst h₀ hᵣ hₗ
  -- Borel measurability: the niche is Borel and both tail half-planes are closed.
  have hNmeas : MeasurableSet N := measurableSet_capNiche K.val
  have hRmeas : MeasurableSet HR := (isClosed_normalHalfPlane _ _ true).measurableSet
  have hLmeas : MeasurableSet HL := (isClosed_normalHalfPlane _ _ true).measurableSet
  have hm₀ : MeasurableSet (N \ (HR ∪ HL)) := hNmeas.diff (hRmeas.union hLmeas)
  have hmᵣ : MeasurableSet (N ∩ HR) := hNmeas.inter hRmeas
  have hmₗ : MeasurableSet (N ∩ HL) := hNmeas.inter hLmeas
  -- Finite area: the uniform niche bounds confine the niche to a bounded rectangle.
  have hNfin : MeasureTheory.volume N < ⊤ := (niche_uniform_bounds.1 _ K.val).2.2.1
  have hf₀ : MeasureTheory.volume (N \ (HR ∪ HL)) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hNfin
  have hfᵣ : MeasureTheory.volume (N ∩ HR) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hNfin
  have hfₗ : MeasureTheory.volume (N ∩ HL) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hNfin
  -- Disjointness: the outer region avoids both tails by definition, and the two tails
  -- meet the niche in disjoint sets by the strengthened separation theorem.
  have hd₀ᵣ : Disjoint (N \ (HR ∪ HL)) (N ∩ HR) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 (Or.inl hy.2)
  have hd₀ₗ : Disjoint (N \ (HR ∪ HL)) (N ∩ HL) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 (Or.inr hy.2)
  have hdᵣₗ : Disjoint (N ∩ HR) (N ∩ HL) :=
    Set.disjoint_left.mpr fun x hx hy ↦
      Set.eq_empty_iff_forall_notMem.mp (cap_and_niche_tail_separation K).2 x ⟨hx, hy.2⟩
  -- The three regions exhaust the niche by cases on half-plane membership.
  have hunion : (N \ (HR ∪ HL)) ∪ (N ∩ HR) ∪ (N ∩ HL) = N := by
    rw [Set.union_assoc, ← Set.inter_union_distrib_left, Set.sdiff_union_inter]
  refine ⟨hm₀, hmᵣ, hmₗ, hf₀, hfᵣ, hfₗ, hd₀ᵣ, hd₀ₗ, hdᵣₗ, hunion, ?_⟩
  -- Additivity of the extended measures, transferred to real areas by finiteness.
  have hvol : MeasureTheory.volume N = MeasureTheory.volume (N \ (HR ∪ HL)) +
      MeasureTheory.volume (N ∩ HR) + MeasureTheory.volume (N ∩ HL) := by
    rw [← MeasureTheory.measure_union hd₀ᵣ hmᵣ,
      ← MeasureTheory.measure_union (hd₀ₗ.union_left hdᵣₗ) hmₗ, hunion]
  simp only [ClassicalResults.area]
  rw [hvol, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hf₀.ne, hfᵣ.ne⟩) hfₗ.ne,
    ENNReal.toReal_add hf₀.ne hfᵣ.ne]

end MovingSofa

end

end

end
