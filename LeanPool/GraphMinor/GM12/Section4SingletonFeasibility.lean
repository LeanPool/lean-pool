/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4DisjointDiscs
import LeanPool.GraphMinor.GM12.Section4DiscTangency
import LeanPool.GraphMinor.GM12.Section4MarkedDiscMatch
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Topological feasibility of singleton prescriptions

XII (4.4), page 251, says that topological feasibility holds when
each prescribed disc has one marked boundary point. Start with
one disjoint connecting disc for each class. Attach a new contact
disc at a fresh boundary point of its assigned connecting disc.
Match it to the next prescribed disc while fixing all prescriptions
already placed. Carry the connecting discs through this motion.
Their contact equations are preserved, and the new equation is
exactly the required singleton contact.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The singleton topological feasibility assertion in XII (4.4),
page 251, for any assignment of prescribed points to classes. -/
theorem topologicallyFeasible_singleton_prescriptions
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p t : ℕ} (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
    (z : Fin t → S) (hz : ∀ i, z i ∈ discBd (Δ i)) (κ : Fin t → Fin p) :
    IsTopologicallyFeasible Δ (fun v => z '' {i | κ i = v}) := by
  classical
  have hex : ∀ F : Set (Fin t), F.Finite →
      ∃ D : Fin p → Set S, (∀ v, IsClosedDisc (D v)) ∧
        (∀ v w, v ≠ w → Disjoint (D v) (D w)) ∧
        ∀ v i, i ∈ F → D v ∩ Δ i = if κ i = v then {z i} else ∅ := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty =>
      obtain ⟨D, hD, hDD⟩ := exists_finite_disjoint_closed_discs hS p
      exact ⟨D, hD, hDD, by simp⟩
    | @insert i F hi hF ih =>
      obtain ⟨D, hD, hDD, hcontact⟩ := ih
      let v := κ i
      obtain ⟨x, hxBd, hxold⟩ :=
        ((infinite_oArc (hD v).isOArc_discBd).sdiff (hF.image z)).nonempty
      let Z := (⋃ w : {w : Fin p // w ≠ v}, D w.val) ∪ ⋃ j ∈ F, Δ j
      have hZ : IsClosed Z :=
        (isClosed_iUnion_of_finite fun w : {w : Fin p // w ≠ v} => (hD w.val).isClosed).union
          (hF.isClosed_biUnion fun j _ => (hΔ j).isClosed)
      have hxZ : x ∉ Z := by
        intro hx
        rcases hx with hxother | hxprior
        · obtain ⟨w, hxw⟩ := mem_iUnion.mp hxother
          exact Set.disjoint_left.mp (hDD v w.val w.property.symm)
            (discBd_subset _ hxBd) hxw
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxprior
          have hc := (hcontact v j hj).subset ⟨discBd_subset _ hxBd, hxj⟩
          by_cases hκ : κ j = v
          · rw [ite_eq_left hκ] at hc
            exact hxold ⟨j, hj, (Set.mem_singleton_iff.mp hc).symm⟩
          · rw [ite_eq_right hκ] at hc
            exact hc.elim
      obtain ⟨Q, q, hQ, hQD, hQZ, hxq, hQbd⟩ :=
        exists_disc_touching_boundary_point hS (hD v) hZ hxBd hxZ
      obtain ⟨q', hq'Bd, hq'ne⟩ :=
        ((infinite_oArc (hΔ i).isOArc_discBd).sdiff (finite_singleton (z i))).nonempty
      let P : F → Set S := fun j => Δ j.val
      have hP : ∀ j, IsClosedDisc (P j) := fun j => hΔ j.val
      have hPP : Pairwise (fun j k => Disjoint (P j) (P k)) :=
        fun j k hjk => hdisj j.val k.val (fun h => hjk (Subtype.ext h))
      have hQP : Disjoint Q (⋃ j : F, P j) :=
        hQZ.mono_right (by
          intro a ha
          obtain ⟨j, hj⟩ := mem_iUnion.mp ha
          exact Or.inr (mem_iUnion₂.mpr ⟨j.val, j.property, hj⟩))
      have hΔP : Disjoint (Δ i) (⋃ j : F, P j) := by
        apply Set.disjoint_left.mpr
        intro a hai haP
        obtain ⟨j, haj⟩ := mem_iUnion.mp haP
        exact Set.disjoint_left.mp (hdisj i j.val (fun hij => hi (hij ▸ j.property))) hai haj
      obtain ⟨e, heQ, hex, heq, hefix⟩ := exists_marked_disc_match_fixing_discs
        hS P hP hPP hQ (hΔ i) hQP hΔP (hQbd (by simp)) (hQbd (by simp)) hxq
        (hz i) hq'Bd (fun heq => hq'ne (Set.mem_singleton_iff.mpr heq.symm))
      have heΔ : ∀ j ∈ F, e '' Δ j = Δ j := by
        intro j hj
        apply Set.Subset.antisymm
        · rintro _ ⟨a, ha, rfl⟩
          rw [hefix ⟨j, hj⟩ a ha]
          exact ha
        · intro a ha
          exact ⟨a, ha, hefix ⟨j, hj⟩ a ha⟩
      have hnew : ∀ w, (e '' D w) ∩ Δ i = if κ i = w then {z i} else ∅ := by
        intro w
        rw [← heQ, ← image_inter e.injective]
        by_cases hw : w = v
        · subst w
          rw [inter_comm, hQD, image_singleton, hex, ite_eq_left rfl]
        · have hQw : Disjoint Q (D w) := hQZ.mono_right
            (fun a ha => Or.inl (mem_iUnion.mpr ⟨⟨w, hw⟩, ha⟩))
          rw [hQw.symm.inter_eq, image_empty, ite_eq_right (Ne.symm hw)]
      refine ⟨fun w => e '' D w, ?_, ?_, ?_⟩
      · intro w
        exact ((hD w).image e.continuous.continuousOn e.symm.continuous.continuousOn
          (fun a _ => e.symm_apply_apply a)).1
      · intro w w' hww'
        apply Set.disjoint_left.mpr
        rintro a ⟨b, hb, hba⟩ ⟨c, hc, hca⟩
        have hbc := e.injective (hba.trans hca.symm)
        exact Set.disjoint_left.mp (hDD w w' hww') hb (hbc.symm ▸ hc)
      · intro w j hj
        rcases hj with hji | hj
        · subst j
          exact hnew w
        · rw [← heΔ j hj, ← image_inter e.injective, hcontact w j hj]
          by_cases hκ : κ j = w
          · rw [ite_eq_left hκ, image_singleton, hefix ⟨j, hj⟩ _ (discBd_subset _ (hz j))]
          · rw [ite_eq_right hκ, image_empty]
  obtain ⟨D, hD, hDD, hcontact⟩ := hex univ (Set.toFinite _)
  refine ⟨D, hD, hDD, ?_⟩
  intro v
  ext x
  constructor
  · rintro ⟨hxD, hxΔ⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxΔ
    have hc := (hcontact v i (mem_univ i)).subset ⟨hxD, hxi⟩
    by_cases hκ : κ i = v
    · rw [ite_eq_left hκ] at hc
      exact ⟨i, hκ, (Set.mem_singleton_iff.mp hc).symm⟩
    · rw [ite_eq_right hκ] at hc
      exact hc.elim
  · rintro ⟨i, hi, rfl⟩
    have hc : z i ∈ D v ∩ Δ i := by
      rw [hcontact v i (mem_univ i), ite_eq_left (show κ i = v from hi)]
      simp
    exact ⟨hc.1, mem_iUnion.mpr ⟨i, hc.2⟩⟩

end GraphMinor.GM12
