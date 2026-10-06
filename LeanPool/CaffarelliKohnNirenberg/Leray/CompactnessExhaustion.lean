/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupSmoothBoundSupport
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compactness Exhaustion

Supporting estimates for the Navier–Stokes development.
-/

public section

open Set Topology
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- A compact exhaustion of the subtype of an open subset of a finite
dimensional Euclidean space. -/
@[expose]
noncomputable def compactExhaustionSubtypeVec3 (U : Set Vec3) (hU : IsOpen U) :
    CompactExhaustion {x : Vec3 // x ∈ U} := by
  let X := {x : Vec3 // x ∈ U}
  letI : LocallyCompactSpace X := hU.locallyCompactSpace
  letI : WeaklyLocallyCompactSpace X := inferInstance
  letI : SecondCountableTopology X := inferInstance
  letI : SigmaCompactSpace X := by infer_instance
  exact CompactExhaustion.choice X

/-- A compact exhaustion of an open Euclidean domain, written as compact
ambient sets. -/
theorem exists_compact_exhaustion_of_open_vec3
    (U : Set Vec3) (hU : IsOpen U) :
    ∃ K : ℕ → Set Vec3,
      (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧
      (∀ n, K n ⊆ K (n + 1)) ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧ ⋃ n, K n = U := by
  let E := compactExhaustionSubtypeVec3 U hU
  let K : ℕ → Set Vec3 := fun n => Subtype.val '' E n
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (E.isCompact n).image continuous_subtype_val
  · intro n x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  · intro n
    exact image_mono (E.subset_succ n)
  · intro n x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyInterior : y ∈ interior (E (n + 1)) := E.subset_interior_succ n hy
    have hopen : IsOpen (Subtype.val '' interior (E (n + 1))) :=
      hU.isOpenMap_subtype_val _ isOpen_interior
    have hsubset : Subtype.val '' interior (E (n + 1)) ⊆ K (n + 1) :=
      image_mono interior_subset
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds ⟨y, hyInterior, rfl⟩) hsubset)
  · rw [← image_iUnion, E.iUnion_eq]
    ext x
    simp

/-- Smooth compactly supported cutoffs equal to one on a compact exhaustion
of an open spatial domain. -/
theorem exists_compact_exhaustion_cutoffs_vec3
    (U : Set Vec3) (hU : IsOpen U) :
    ∃ K : ℕ → Set Vec3, ∃ χ : ℕ → Vec3 → ℝ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ U ∧ K n ⊆ K (n + 1) ∧
        K n ⊆ interior (K (n + 1))) ∧
      (⋃ n, K n = U) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ U ∧ (∀ x, χ n x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ x ∈ K n, χ n x = 1) := by
  classical
  obtain ⟨K, hK, hKU, hKn, hKinner, hcover⟩ :=
    exists_compact_exhaustion_of_open_vec3 U hU
  choose χ hχsmooth hχcompact hχrange hχsupport W hWopen hKW hWU hχone using
    fun n => CKN.Foundation.Heat.exists_smooth_cutoff_one_near_compact
      (hK n) hU (hKU n)
  refine ⟨K, χ, ?_, hcover, ?_⟩
  · intro n
    exact ⟨hK n, hKU n, hKn n, hKinner n⟩
  · intro n
    exact ⟨hχsmooth n, hχcompact n, hχsupport n, hχrange n,
      fun x hx => hχone n x (hKW n hx)⟩

/-- Every compact subset of an open domain lies in one member of an
exhaustion whose successive members contain the previous ones in their
interiors. -/
theorem compact_subset_eventually_in_exhaustion
    {U C : Set Vec3} (hC : IsCompact C) (hCU : C ⊆ U)
    (K : ℕ → Set Vec3) (hmono : ∀ j, K j ⊆ K (j + 1))
    (hinner : ∀ j, K j ⊆ interior (K (j + 1)))
    (hcover : ⋃ j, K j = U) :
    ∃ j, C ⊆ K j := by
  classical
  have hmonotone : Monotone K := monotone_nat_of_le_succ hmono
  have hOpenCover : C ⊆ ⋃ j, interior (K (j + 1)) := by
    intro x hx
    have hxU : x ∈ ⋃ j, K j := by rw [hcover]; exact hCU hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    exact Set.mem_iUnion.mpr ⟨j, hinner j hxj⟩
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover
    (fun j => interior (K (j + 1))) (fun _ => isOpen_interior) hOpenCover
  refine ⟨F.sup (fun j => j + 1), ?_⟩
  intro x hx
  obtain ⟨j, hjF, hxj⟩ := Set.mem_iUnion₂.mp (hF hx)
  exact hmonotone (Finset.le_sup hjF) (interior_subset hxj)

/-- Rational closed intervals compactly contained in an open time domain. -/
abbrev RationalCompactTimeWindow (I : Set ℝ) :=
  {p : ℚ × ℚ // (p.1 : ℝ) < p.2 ∧ Set.Icc (p.1 : ℝ) p.2 ⊆ I}

/-- Every time in an open domain lies in the interior of a rational compact
time window contained in that domain. -/
theorem exists_rational_compact_time_window_around
    {I : Set ℝ} (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) :
    ∃ p : RationalCompactTimeWindow I,
      t ∈ Set.Ioo (p.1.1 : ℝ) (p.1.2 : ℝ) := by
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds ht)
  obtain ⟨q, haq, hqt⟩ := exists_rat_btwn hat
  obtain ⟨r, htr, hrb⟩ := exists_rat_btwn htb
  have hqr : (q : ℝ) < r := hqt.trans htr
  have hsubset : Set.Icc (q : ℝ) r ⊆ I := by
    intro x hx
    exact hab ⟨lt_of_lt_of_le haq hx.1, lt_of_le_of_lt hx.2 hrb⟩
  exact ⟨⟨(q, r), hqr, hsubset⟩, ⟨hqt, htr⟩⟩

end CKN.Leray
