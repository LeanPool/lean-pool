/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.VortexCut

/-!
# The painting of the cut surface

Second step of the proof of XVII (13.1), page 203. We remove the polygons from the surface
(`cut_surface`). The discs of the small societies and the lunes,
as subsets of the cut surface, are closed discs that meet only at points of the arrangement, so they
make a painting (`exists_cut_painting`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09 GM14 GM16 Graph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S] {G : Graph α β} {Seg
  : Set (Society α β)} {D : Society α β → Set S} {ν : α → S} {ρ : ℕ}
  {V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ}

omit [T2Space S] in
theorem VortexCut.nx_ne {s : Society α β} {E : Set S} (W : VortexCut s E ν ρ)
  (i : Fin W.k) : W.nx i ≠ i := by
  intro h
  have h1 := W.hnx i
  rw [h] at h1
  have h2 := W.four
  have h3 := i.2
  by_cases hc : i.1 + 1 < W.k
  · rw [Nat.mod_eq_of_lt hc] at h1
    omega
  · have : i.1 + 1 = W.k := by omega
    rw [this, Nat.mod_self] at h1
    omega

variable (harr : IsProperArrangement Seg D ν) (hS : IsClosedSurface S) (hfin : Seg.Finite)
include harr hS hfin

omit [TopologicalSpace S] [T2Space S] harr hS in
theorem finite_Maj : Finite (Maj Seg) := (hfin.subset (sep_subset _ _)).to_subtype

omit [TopologicalSpace S] [T2Space S] harr hS in
theorem finite_Mnr : Finite (Mnr Seg) := (hfin.subset (sep_subset _ _)).to_subtype

omit [T2Space S] harr hS in
theorem finite_Idx : Finite (Idx V) := by
  have := finite_Maj hfin
  have := finite_Mnr hfin
  infer_instance

omit [T2Space S] in
/-- The surface with the polygons removed. -/
theorem cut_surface [ConnectedSpace S] :
    IsClosed (Cut V) ∧ IsSurface ↥(Cut V) ∧ bd ↥(Cut V) = Subtype.val ⁻¹' (⋃ m, discBd (V m).P)
      ∧ ConnectedSpace ↥(Cut V) ∧
      cuffs ↥(Cut V) = range fun m => (Subtype.val ⁻¹' discBd (V m).P : Set ↥(Cut V)) := by
  have := finite_Maj hfin
  exact remove_discs ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩ hS.2.2 (fun m =>
    (V m).disc_P) fun m m' h => disjoint_P harr h

/-- A disc of the painting, in the cut surface. -/
def dT (V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ) (i : Idx V) : Set ↥(Cut V)
  := Subtype.val ⁻¹' Ds V i

/-- The nodes of the painting. -/
def NT (V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ) : Set ↥(Cut V) := Subtype.val ⁻¹' Nd Seg ν

theorem dT_disc [ConnectedSpace S] (i : Idx V) : IsClosedDisc (dT V i) ∧ discBd (dT V i)
  = Subtype.val ⁻¹' discBd (Ds V i) := by
  obtain ⟨h1, h2, -, h4, -⟩ := cut_surface (V := V) harr hS hfin
  have : CompactSpace ↥(Cut V) := h2.1
  obtain ⟨z, hz⟩ := (IsOArc.isConnected' (Ds_disc harr i).isOArc_discBd).nonempty
  have : Nonempty ↥(Cut V) := ⟨⟨z, Ds_sub_Cut harr i (discBd_subset _ hz)⟩⟩
  exact isClosedDisc_preimage h1.isClosedEmbedding_subtypeVal (Ds_disc harr i) (by
    rw [Subtype.range_coe]
    exact Ds_sub_Cut harr i)

omit [TopologicalSpace S] [T2Space S] harr hS in
theorem finite_Nd : (Nd Seg ν).Finite := by
  refine Set.Finite.image _ ?_
  exact hfin.biUnion fun s _ => s.Ω.finite_bar

omit [T2Space S] harr hS hfin in
theorem NT_inter (i : Idx V) : NT V ∩ dT V i = Subtype.val ⁻¹' (Nd Seg ν ∩ Ds V i) := rfl

omit [T2Space S] harr hS in
theorem ncard_NT_le (i : Idx V) : (NT V ∩ dT V i).ncard ≤ (Nd Seg ν ∩ Ds V i).ncard := by
  have hf := (finite_Nd (ν := ν) hfin).subset (inter_subset_left (t := Ds V i))
  rw [NT_inter]
  exact Set.ncard_le_ncard_of_injOn Subtype.val (fun x hx => hx) Subtype.val_injective.injOn hf

omit hS hfin in
omit [T2Space S] in
theorem pt_ne_next (m : Maj Seg) (i : Fin (V m).k) : ν ((V m).t i) ≠ ν ((V m).t ((V m).nx i))
  := fun he => by
  have h1 := harr.1.injOn_pts (bar_sub_verts m.2.1 (t_mem_bar m i)) (bar_sub_verts m.2.1
    (t_mem_bar m _)) he
  exact (V m).nx_ne i ((V m).dec.injective_t h1).symm

theorem lune_ends [ConnectedSpace S] (m : Maj Seg) (i : Fin (V m).k) :
    ∃ u v : ↥(Cut V), u ≠ v ∧ u.1 = ν ((V m).t i) ∧ v.1 = ν ((V m).t ((V m).nx i)) ∧ NT V ∩ dT V
      (.inr ⟨m, i⟩) = {u, v} ∧
      dT V (.inr ⟨m, i⟩) ∩ bd ↥(Cut V) = Subtype.val ⁻¹' (V m).F i ∧ IsLineWithEnds
        (Subtype.val ⁻¹' (V m).F i : Set ↥(Cut V)) u v := by
  obtain ⟨-, -, h3, -, -⟩ := cut_surface (V := V) harr hS hfin
  have hsub : (V m).F i ⊆ range (Subtype.val : ↥(Cut V) → S) := by
    rw [Subtype.range_coe]
    refine Subset.trans ?_ (Ds_sub_Cut harr (.inr ⟨m, i⟩))
    change (V m).F i ⊆ (V m).L i
    rw [← (V m).L_inter i]
    exact inter_subset_left
  obtain ⟨u, v, hu, hv, hl⟩ := IsLineWithEnds.pull IsEmbedding.subtypeVal ((V m).F_line i) hsub
  have hne : u ≠ v := fun h => pt_ne_next harr m i (by rw [← hu, ← hv, h])
  refine ⟨u, v, hne, hu, hv, ?_, ?_, hl⟩
  · rw [NT_inter]
    change _ ⁻¹' (Nd Seg ν ∩ (V m).L i) = _
    rw [Nd_inter_inr harr]
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, ← hu, ← hv, Subtype.val_inj]
  · rw [h3, ← lune_inter_bd harr m i]
    rfl

theorem exists_cut_painting [ConnectedSpace S] :
    ∃ Γ : Painting ↥(Cut V), Γ.U = (⋃ i, dT V i) ∧ Γ.N = NT V ∧ Γ.C = range (fun i
      => dT V i \ NT V) ∧
      ∀ i, closure (dT V i \ NT V) = dT V i ∧ tilde (dT V i \ NT V) = NT V ∩ dT V i := by
  have := finite_Idx (V := V) hfin
  obtain ⟨-, h2, h3, -, -⟩ := cut_surface (V := V) harr hS hfin
  have : T2Space ↥(Cut V) := h2.2.1
  refine exists_painting_of_discs (fun i => (dT_disc harr hS hfin i).1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (finite_Nd (ν := ν) hfin).preimage Subtype.val_injective.injOn
  · intro i x hx
    rw [(dT_disc harr hS hfin i).2]
    exact Nd_sub_discBd harr hS i hx
  · intro i j hij x hx
    exact inter_sub_Nd harr hij hx
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (Nd_sub_Ds (V := V) harr hx)
    exact mem_iUnion.2 ⟨i, hi⟩
  · intro i
    refine (ncard_NT_le hfin i).trans ?_
    rcases i with a | ⟨m, a⟩
    · change (Nd Seg ν ∩ D a.1).ncard ≤ 3
      rw [Nd_inter_inl harr]
      exact (Set.ncard_image_le a.1.Ω.finite_bar).trans (not_lt.mp a.2.2)
    · change (Nd Seg ν ∩ (V m).L a).ncard ≤ 3
      rw [Nd_inter_inr harr]
      exact (Set.ncard_insert_le _ _).trans (by simp)
  · intro x hx
    rw [h3] at hx
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    rw [(V m).bd_P] at hm
    obtain ⟨j, hj⟩ := mem_iUnion.1 hm
    refine mem_iUnion.2 ⟨.inr ⟨m, j⟩, ?_⟩
    change x.1 ∈ (V m).L j
    rw [← (V m).L_inter j] at hj
    exact hj.1
  · rintro (a | ⟨m, a⟩) ⟨x, hx, hb⟩
    · rw [h3] at hb
      exact absurd (mnr_inter_bd harr a ⟨hx.1, hb⟩) hx.2
    · obtain ⟨u, v, hne, -, -, h4, h5, hl⟩ := lune_ends harr hS hfin m a
      refine ⟨by rw [h4, Set.ncard_pair hne], ?_, ?_⟩
      · rw [h5]
        obtain ⟨f, -, -⟩ := hl
        exact ⟨f⟩
      · rw [h5, h4]
        exact lineEnds_eq hl

end GraphMinor.GM17
