/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessExhaustion
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Compactness Time Exhaustion

Supporting estimates for the Navier–Stokes development.
-/

public section

open Set Topology

namespace CKN.Leray

/-- A compact exhaustion of an open time domain by ambient compact sets. -/
theorem exists_compact_exhaustion_of_open_real
    (I : Set ℝ) (hI : IsOpen I) :
    ∃ J : ℕ → Set ℝ,
      (∀ n, IsCompact (J n)) ∧ (∀ n, J n ⊆ I) ∧
      (∀ n, J n ⊆ J (n + 1)) ∧
      (∀ n, J n ⊆ interior (J (n + 1))) ∧ ⋃ n, J n = I := by
  let X := {t : ℝ // t ∈ I}
  let : LocallyCompactSpace X := hI.locallyCompactSpace
  let : WeaklyLocallyCompactSpace X := inferInstance
  let : SecondCountableTopology X := inferInstance
  let : SigmaCompactSpace X := by infer_instance
  let E : CompactExhaustion X := CompactExhaustion.choice X
  let J : ℕ → Set ℝ := fun n => Subtype.val '' E n
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (E.isCompact n).image continuous_subtype_val
  · intro n t ht
    rcases ht with ⟨s, hs, rfl⟩
    exact s.property
  · intro n
    exact image_mono (E.subset_succ n)
  · intro n t ht
    rcases ht with ⟨s, hs, rfl⟩
    have hsInterior : s ∈ interior (E (n + 1)) :=
      E.subset_interior_succ n hs
    have hopen : IsOpen (Subtype.val '' interior (E (n + 1))) :=
      hI.isOpenMap_subtype_val _ isOpen_interior
    have hsubset : Subtype.val '' interior (E (n + 1)) ⊆ J (n + 1) :=
      image_mono interior_subset
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds ⟨s, hsInterior, rfl⟩) hsubset)
  · rw [← image_iUnion, E.iUnion_eq]
    ext t
    simp

/-- A compact subset of an open time domain lies in one sufficiently large
member of a nested compact exhaustion. -/
theorem compact_time_subset_eventually_in_exhaustion
    {I T : Set ℝ} (hT : IsCompact T) (hTI : T ⊆ I)
    (J : ℕ → Set ℝ) (hmono : ∀ j, J j ⊆ J (j + 1))
    (hinner : ∀ j, J j ⊆ interior (J (j + 1)))
    (hcover : ⋃ j, J j = I) :
    ∃ j, T ⊆ J j := by
  classical
  have hmonotone : Monotone J := monotone_nat_of_le_succ hmono
  have hOpenCover : T ⊆ ⋃ j, interior (J (j + 1)) := by
    intro t ht
    have htI : t ∈ ⋃ j, J j := by rw [hcover]; exact hTI ht
    obtain ⟨j, htj⟩ := Set.mem_iUnion.mp htI
    exact Set.mem_iUnion.mpr ⟨j, hinner j htj⟩
  obtain ⟨F, hF⟩ := hT.elim_finite_subcover
    (fun j => interior (J (j + 1))) (fun _ => isOpen_interior) hOpenCover
  refine ⟨F.sup (fun j => j + 1), ?_⟩
  intro t ht
  obtain ⟨j, hjF, htj⟩ := Set.mem_iUnion₂.mp (hF ht)
  exact hmonotone (Finset.le_sup hjF) (interior_subset htj)

/-- A compact time set inside an interval fits inside a compact interval
contained in the same domain. -/
theorem compact_time_subset_compact_interval
    {I T : Set ℝ} (hI : OrdConnected I)
    (hT : IsCompact T) (hTI : T ⊆ I) :
    ∃ a b : ℝ, T ⊆ Icc a b ∧ Icc a b ⊆ I := by
  by_cases hTempty : T = ∅
  · refine ⟨1, 0, ?_, ?_⟩
    · simp [hTempty]
    · simp
  · have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hTempty
    obtain ⟨a, ha⟩ := hT.exists_isLeast hTne
    obtain ⟨b, hb⟩ := hT.exists_isGreatest hTne
    refine ⟨a, b, ?_, hI.out (hTI ha.1) (hTI hb.1)⟩
    intro t ht
    exact ⟨ha.2 ht, hb.2 ht⟩

end CKN.Leray
