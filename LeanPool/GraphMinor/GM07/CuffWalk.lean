/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.FlatMinimal
public import LeanPool.GraphMinor.GM17.RegionFrontier
public import LeanPool.GraphMinor.GM17.PasteCuff
public import LeanPool.GraphMinor.GM19.FragmentRegion

/-!
# From a flat complement to a path between cuffs

This file is the end of the topological part of the proof of (4.3) of Graph Minors VII (page 223).
Let `Y` be connected, flat and such that closed discs with boundary in `Y` lie in `Y`. Paste a
closed disc onto
each cuff. By (4.2) the set `Y` is an open disc in the new surface, and so its frontier is
connected. It follows that `U(K) ∪ bd(Σ)` is connected, and hence `K` has a path between two cuffs
(`exists_walk_between_cuffs`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- The complement of an open disc in a connected compact surface does not split into two disjoint
nonempty closed sets. Otherwise the connected frontier of the disc lies in one of them, and the
other one is open. -/
theorem not_split_of_isOpenDisc {T : Type} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [ConnectedSpace T] {O P Q : Set T} (hO : IsOpenDisc O) (hP : IsClosed P) (hQ : IsClosed Q)
    (hd : Disjoint P Q)
    (hu : Oᶜ = P ∪ Q) (hPn : P.Nonempty) (hQn : Q.Nonempty) : False := by
  have hF := GM17.isPreconnected_frontier hO
  have hFs : closure O \ O ⊆ P ∪ Q := fun z hz => hu ▸ hz.2
  have haux : ∀ {P Q : Set T}, IsClosed P → IsClosed Q → Disjoint P Q → Oᶜ = P ∪ Q → P.Nonempty
    → Q.Nonempty → closure O \ O ⊆ P → False := fun {P Q} hP hQ hd hu hPn hQn hs => by
    have hQO : Disjoint Q (closure O) := disjoint_left.mpr fun z hz hc => by
      have h1 : z ∉ O := by
        have : z ∈ Oᶜ := hu ▸ .inr hz
        exact this
      exact disjoint_left.mp hd (hs ⟨hc, h1⟩) hz
    have hQo : IsOpen Q := by
      have e : Q = (closure O ∪ P)ᶜ := by
        ext z
        constructor
        · rintro hz (h | h)
          · exact disjoint_left.mp hQO hz h
          · exact disjoint_left.mp hd h hz
        · intro hz
          have h1 : z ∉ O := fun h => hz (.inl (subset_closure h))
          have : z ∈ Oᶜ := h1
          rw [hu] at this
          exact this.resolve_left fun h => hz (.inr h)
      rw [e]
      exact (isClosed_closure.union hP).isOpen_compl
    rcases isClopen_iff.mp ⟨hQ, hQo⟩ with h | h
    · exact hQn.ne_empty h
    · obtain ⟨z, hz⟩ := hPn
      exact disjoint_left.mp hd hz (h ▸ mem_univ z)
  by_cases h1 : closure O \ O ⊆ P
  · exact haux hP hQ hd hu hPn hQn h1
  by_cases h2 : closure O \ O ⊆ Q
  · exact haux hQ hP hd.symm (by rw [union_comm]; exact hu) hQn hPn h2
  obtain ⟨a, ha, haP⟩ := not_subset.mp h1
  obtain ⟨b, hb, hbQ⟩ := not_subset.mp h2
  have haQ : a ∈ Q := (hFs ha).resolve_left haP
  have hbP : b ∈ P := (hFs hb).resolve_right hbQ
  obtain ⟨z, -, hz⟩ := isPreconnected_closed_iff.mp hF P Q hP hQ hFs ⟨b, hb, hbP⟩ ⟨a, ha, haQ⟩
  exact disjoint_left.mp hd hz.1 hz.2

variable [T1Space S]

omit [T1Space S] in
theorem edge_eq_of_mem {K : Drawing S} {e f : Set S} (he : e ∈ K.E) (hf : f ∈ K.E) {z : S}
  (hze : z ∈ e) (hzf : z ∈ f) : e = f :=
  arcComponent_eq he hf hze hzf

/-- The vertices joined by a walk of `K` to a vertex on `C`. -/
def reachFrom (K : Drawing S) (C : Set S) : Set S := {y | ∃ a ∈ K.V ∩ C, Nonempty
  (GraphWalk K.toGraph a y)}

omit [T1Space S] in
theorem reachFrom_subset (K : Drawing S) (C : Set S) : reachFrom K C ⊆ K.V := by
  rintro y ⟨a, -, ⟨W⟩⟩
  exact W.mem_vertexSet_of_mem_support W.end_mem_support

omit [T1Space S] in
theorem reachFrom_step {K : Drawing S} {C : Set S} {e : Set S} (he : e ∈ K.E) {y z : S}
    (hy : y ∈ reachFrom K C) (hye : y ∈ closure e) (hz : z ∈ closure e ∩ K.V) :
    z ∈ reachFrom K C := by
  have hyV := reachFrom_subset K C hy
  by_cases hyz : y = z
  · exact hyz ▸ hy
  obtain ⟨a, ha, ⟨W⟩⟩ := hy
  refine ⟨a, ha, ⟨W.append (.cons (e := e) ⟨he, hyV, hz.2, ?_⟩ (.nil hz.2))⟩⟩
  rcases K.edge_cond e he with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
  · have h1 : y ∈ ({u, v} : Set S) := hcap ▸ ⟨hye, hyV⟩
    have h2 : z ∈ ({u, v} : Set S) := hcap ▸ hz
    rw [hcap]
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact (hyz rfl).elim
    · obtain rfl : z = v := h2
      rfl
    · obtain rfl : y = v := h1
      exact pair_comm _ _
    · obtain rfl : y = v := h1
      obtain rfl : z = y := h2
      exact (hyz rfl).elim
  · have h1 : y ∈ ({u} : Set S) := hcap ▸ ⟨hye, hyV⟩
    have h2 : z ∈ ({u} : Set S) := hcap ▸ hz
    exact (hyz (h1.trans h2.symm)).elim

private theorem cuff_reachability_sides_disjoint
    {S : Type}
    [TopologicalSpace S]
    {C : Set S}
    (hC : C ∈ cuffs S)
    {K : Drawing S}
    (hsubc : ∀ D ∈ cuffs S, D ⊆ bd S) :
    let EP : Set (Set S) := {e | e ∈ K.E ∧ (closure e ∩ reachFrom K C).Nonempty}
    let EQ : Set (Set S) := {e | e ∈ K.E ∧ closure e ∩ reachFrom K C = ∅}
    let P : Set S := C ∪ reachFrom K C ∪ ⋃ e ∈ EP, closure e
    let Q : Set S := bd S \ C ∪ K.V \ reachFrom K C ∪ ⋃ e ∈ EQ, closure e
    (∀ z ∈ P, z ∈ K.V → z ∈ reachFrom K C) →
    (∀ z ∈ P, z ∈ bd S → z ∈ C) →
    (∀ z ∈ Q, z ∈ K.V → z ∉ reachFrom K C) →
    (∀ z ∈ Q, z ∈ bd S → z ∉ C) →
    Disjoint P Q := by
  intro EP EQ P Q ha hb hc hd
  refine disjoint_left.mpr ?_
  intro z hzP hzQ
  by_cases hv : z ∈ K.V
  · exact hc z hzQ hv (ha z hzP hv)
  by_cases hbz : z ∈ bd S
  · exact hd z hzQ hbz (hb z hzP hbz)
  obtain ⟨e, he, hze⟩ : ∃ e ∈ EP, z ∈ closure e := by
    rcases hzP with (h | h) | h
    · exact (hbz (hsubc C hC h)).elim
    · exact (hv (reachFrom_subset K C h)).elim
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact ⟨e, he, hz⟩
  obtain ⟨f, hf, hzf⟩ : ∃ f ∈ EQ, z ∈ closure f := by
    rcases hzQ with (h | h) | h
    · exact (hbz h.1).elim
    · exact (hv h.1).elim
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact ⟨e, he, hz⟩
  have h1 : z ∈ e := by
    rw [← K.closure_diff_V he.1]
    exact ⟨hze, hv⟩
  have h2 : z ∈ f := by
    rw [← K.closure_diff_V hf.1]
    exact ⟨hzf, hv⟩
  have : e = f := edge_eq_of_mem he.1 hf.1 h1 h2
  obtain ⟨y, hy⟩ := he.2
  have h3 : y ∈ closure f ∩ reachFrom K C := this ▸ hy
  rw [hf.2] at h3
  exact h3

private theorem capped_cuff_sides_disjoint
    {S : Type}
    [TopologicalSpace S]
    {C : Set S}
    (P : Set S)
    (Q : Set S)
    (hb : ∀ z ∈ P, z ∈ bd S → z ∈ C)
    (hd : ∀ z ∈ Q, z ∈ bd S → z ∉ C)
    (hPQ : Disjoint P Q)
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    (𝓓 : Set (Set T))
    (h𝓓d : ∀ D ∈ 𝓓, ∀ D' ∈ 𝓓, D ≠ D' → Disjoint D D')
    (htr : ∀ D ∈ 𝓓, j ⁻¹' D ⊆ bd S)
    (htrC : ∀ D ∈ 𝓓, (j ⁻¹' D ∩ C).Nonempty → j ⁻¹' D ⊆ C) :
    let DP : Set (Set T) := {D | D ∈ 𝓓 ∧ (j ⁻¹' D ∩ C).Nonempty}
    let DQ : Set (Set T) := {D | D ∈ 𝓓 ∧ ¬(j ⁻¹' D ∩ C).Nonempty}
    Disjoint (j '' P ∪ ⋃₀ DP) (j '' Q ∪ ⋃₀ DQ) := by
  intro DP DQ
  rw [disjoint_left]
  rintro z (⟨y, hy, rfl⟩ | ⟨D, hD, hz⟩) (⟨y', hy', e⟩ | ⟨D', hD', hz'⟩)
  · obtain rfl := hj.injective e
    exact disjoint_left.mp hPQ hy hy'
  · have hyb : y ∈ bd S := htr D' hD'.1 hz'
    exact hD'.2 ⟨y, hz', hb y hy hyb⟩
  · subst e
    have hyb : y' ∈ bd S := htr D hD.1 hz
    exact hd y' hy' hyb (htrC D hD.1 hD.2 hz)
  · by_cases heq : D = D'
    · subst heq
      exact hD'.2 hD.2
    · exact disjoint_left.mp (h𝓓d D hD.1 D' hD'.1 heq) hz hz'

/-- **The end of the proof of (4.3)** (Graph Minors VII, page 223). -/
theorem exists_walk_between_cuffs (hS : IsSurface S) [ConnectedSpace S] {C C' : Set S}
  (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C') {K : Drawing S} (hK : K.IsProper)
    (hY : IsPreconnected (offSet K)) (hYn : (offSet K).Nonempty) (hflat : IsFlat (offSet K))
      (hdisc : ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ ⊆ offSet K → Δ ⊆ offSet K) :
    ∃ a ∈ K.V ∩ C, ∃ b ∈ K.V ∩ (bd S \ C), Nonempty (GraphWalk K.toGraph a b) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hbc : IsClosed (bd S) := (cuff_statement.{0} S hS).1
  have hfinc : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
  have hclc : ∀ D ∈ cuffs S, IsClosed D := fun D hD => ((cuff_statement.{0} S hS).2.2 D
    hD).isCompact.isClosed
  have hsubc : ∀ D ∈ cuffs S, D ⊆ bd S := fun D hD => by
    obtain ⟨x, -, rfl⟩ := hD
    exact connectedComponentIn_subset _ _
  have hbdC : IsClosed (bd S \ C) := by
    have e : bd S \ C = ⋃ D ∈ cuffs S \ {C}, D := by
      ext z
      constructor
      · intro hz
        refine mem_iUnion₂.mpr ⟨connectedComponentIn (bd S) z, ⟨⟨z, hz.1, rfl⟩, fun h => ?_⟩,
          mem_connectedComponentIn hz.1⟩
        exact hz.2 (mem_singleton_iff.mp h ▸ mem_connectedComponentIn hz.1)
      · intro hz
        obtain ⟨D, hD, hzD⟩ := mem_iUnion₂.mp hz
        exact ⟨hsubc D hD.1 hzD, fun h => hD.2 (GM17.cuffs_disjoint_eq hD.1 hC hzD h)⟩
    rw [e]
    exact (hfinc.subset sdiff_subset).isClosed_biUnion fun D hD => hclc D hD.1
  by_contra hno
  have hnobd : ∀ y ∈ reachFrom K C, y ∈ bd S → y ∈ C := fun y hy hb => by
    by_contra hyC
    obtain ⟨a, ha, hW⟩ := hy
    exact hno ⟨a, ha, y, ⟨reachFrom_subset K C ⟨a, ha, hW⟩, hb, hyC⟩, hW⟩
  have hVC : ∀ z ∈ K.V, z ∈ C → z ∈ reachFrom K C := fun z hz hzC => ⟨z, ⟨hz, hzC⟩, ⟨.nil hz⟩⟩
  have hbU : ∀ z ∈ K.U, z ∈ bd S → z ∈ K.V := fun z h1 h2 => hK ⟨h2, h1⟩
  let EP : Set (Set S) := {e | e ∈ K.E ∧ (closure e ∩ reachFrom K C).Nonempty}
  let EQ : Set (Set S) := {e | e ∈ K.E ∧ closure e ∩ reachFrom K C = ∅}
  let P : Set S := C ∪ reachFrom K C ∪ ⋃ e ∈ EP, closure e
  let Q : Set S := (bd S \ C) ∪ (K.V \ reachFrom K C) ∪ ⋃ e ∈ EQ, closure e
  have hfinE : K.E.Finite := K.finite_edges
  have hfinV : K.V.Finite := K.finite_V
  have hEPfin : EP.Finite := hfinE.subset fun _ he => he.1
  have hEQfin : EQ.Finite := hfinE.subset fun _ he => he.1
  have hPc : IsClosed P := ((hclc C hC).union (hfinV.subset (reachFrom_subset K C)).isClosed).union
    (hEPfin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hQc : IsClosed Q := (hbdC.union (hfinV.subset sdiff_subset).isClosed).union
    (hEQfin.isClosed_biUnion fun _ _ => isClosed_closure)
  have ha : ∀ z ∈ P, z ∈ K.V → z ∈ reachFrom K C := by
    rintro z ((h | h) | h) hv
    · exact hVC z hv h
    · exact h
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      obtain ⟨y, hy, hy'⟩ := he.2
      exact reachFrom_step he.1 hy' hy ⟨hz, hv⟩
  have hb : ∀ z ∈ P, z ∈ bd S → z ∈ C := fun z hz hbz => by
    rcases hz with (h | h) | h
    · exact h
    · exact hnobd z h hbz
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact hnobd z (ha z (.inr (mem_iUnion₂.mpr ⟨e, he, hz⟩)) (hbU z
        (K.closure_subset_U he.1 hz) hbz)) hbz
  have hc : ∀ z ∈ Q, z ∈ K.V → z ∉ reachFrom K C := fun z hz hv hr => by
    rcases hz with (h | h) | h
    · exact h.2 (hnobd z hr h.1)
    · exact h.2 hr
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      have : z ∈ closure e ∩ reachFrom K C := ⟨hz, hr⟩
      rw [he.2] at this
      exact this
  have hd : ∀ z ∈ Q, z ∈ bd S → z ∉ C := fun z hz hbz hzC => by
    have hzU : z ∈ K.V → False := fun hv => hc z hz hv (hVC z hv hzC)
    rcases hz with (h | h) | h
    · exact h.2 hzC
    · exact hzU h.1
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact hzU (hbU z (K.closure_subset_U he.1 hz) hbz)
  have hPQ : Disjoint P Q := by
    exact cuff_reachability_sides_disjoint (S := S) (C := C) hC (K := K) hsubc ha hb hc
      hd
  have hPs : P ⊆ K.U ∪ bd S := by
    rintro z ((h | h) | h)
    · exact .inr (hsubc C hC h)
    · exact .inl (K.V_subset_U (reachFrom_subset K C h))
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact .inl (K.closure_subset_U he.1 hz)
  have hQs : Q ⊆ K.U ∪ bd S := by
    rintro z ((h | h) | h)
    · exact .inr h.1
    · exact .inl (K.V_subset_U h.1)
    · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
      exact .inl (K.closure_subset_U he.1 hz)
  have hcov : K.U ∪ bd S ⊆ P ∪ Q := by
    rintro z (h | h)
    · rw [K.U_eq] at h
      rcases h with h | h
      · by_cases hr : z ∈ reachFrom K C
        · exact .inl (.inl (.inr hr))
        · exact .inr (.inl (.inr ⟨h, hr⟩))
      · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp h
        by_cases hr : (closure e ∩ reachFrom K C).Nonempty
        · exact .inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hr⟩, hz⟩))
        · exact .inr (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, not_nonempty_iff_eq_empty.mp hr⟩, hz⟩))
    · by_cases hzC : z ∈ C
      · exact .inl (.inl (.inl hzC))
      · exact .inr (.inl (.inl ⟨h, hzC⟩))
  -- Now paste discs onto the cuffs.
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hu, hi, hcon, 𝓓, h𝓓f, h𝓓u, h𝓓, h𝓓d⟩ := exists_capAll_discs S hS
  have hconT : ConnectedSpace T := hcon inferInstance
  have ht2T : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  have hUb : IsClosed (K.U ∪ bd S) := K.isClosed_U.union hbc
  let O : Set T := j '' offSet K
  have hOc : Oᶜ = j '' (K.U ∪ bd S) ∪ Kc := by
    ext z
    constructor
    · intro hz
      by_cases hzK : z ∈ Kc
      · exact .inr hzK
      · rcases (hu.symm ▸ mem_univ z : z ∈ range j ∪ Kc) with ⟨y, rfl⟩ | h
        · refine .inl ⟨y, ?_, rfl⟩
          by_contra hy
          exact hz ⟨y, hy, rfl⟩
        · exact (hzK h).elim
    · rintro (⟨y, hy, rfl⟩ | h) ⟨y', hy', e⟩
      · obtain rfl := hj.injective e
        exact hy' hy
      · have : j y' ∈ range j ∩ Kc := ⟨⟨y', rfl⟩, e ▸ h⟩
        rw [hi] at this
        obtain ⟨y'', hy'', e'⟩ := this
        obtain rfl := hj.injective e'
        exact hy' (.inr hy'')
  have hOo : IsOpen O := by
    have : O = (j '' (K.U ∪ bd S) ∪ Kc)ᶜ := by rw [← hOc, compl_compl]
    rw [this]
    exact ((hj.isClosedMap _ hUb).union hKc).isOpen_compl
  have hOconn : IsConnected O := ⟨hYn.image j, hY.image j hj.continuous.continuousOn⟩
  have hdiscT : ∀ F : Set T, F ⊆ O → IsOArc F → ∃ Δ : Set T, Δ ⊆ O ∧ IsClosedDisc Δ ∧ discBd Δ = F
    := fun F hF hFO => by
    have hFr : F ⊆ range j := hF.trans (image_subset_range _ _)
    have hF₀ : IsOArc (j ⁻¹' F) := IsOArc.pull_of_embedding hj.isEmbedding hFO hFr
    have hF₀Y : j ⁻¹' F ⊆ offSet K := fun z hz => by
      obtain ⟨y, hy, e⟩ := hF hz
      exact hj.injective e ▸ hy
    obtain ⟨Δ, hΔ, hΔb⟩ := nullHomotopicOArc_bounds_disc hS hF₀ (isNullHomotopicOArc_of_isFlat
      hflat hF₀Y hF₀)
    have him := hΔ.image_injOn hj.continuous.continuousOn hj.injective.injOn
    refine ⟨j '' Δ, image_mono (hdisc Δ hΔ (hΔb ▸ hF₀Y)), him.1, ?_⟩
    rw [him.2, hΔb, image_preimage_eq_of_subset hFr]
  have hOdisc : IsOpenDisc O := by
    rcases open_disc T O hT hconT hOconn hOo hdiscT with ⟨-, h⟩ | h
    · exfalso
      obtain ⟨c, hc'⟩ : C.Nonempty := by
        obtain ⟨x, hx, rfl⟩ := hC
        exact ⟨x, mem_connectedComponentIn hx⟩
      obtain ⟨y, hy, e⟩ := (h ▸ mem_univ (j c) : j c ∈ O)
      obtain rfl := hj.injective e
      exact (mem_offSet.mp hy).2 (hsubc C hC hc')
    · exact h
  -- Each disc meets the surface inside one cuff, or misses `C`.
  have htr : ∀ D ∈ 𝓓, j ⁻¹' D ⊆ bd S := fun D hD z hz => by
    have h1 : j z ∈ range j ∩ Kc := ⟨⟨z, rfl⟩, h𝓓u ▸ mem_sUnion_of_mem hz hD⟩
    rw [hi] at h1
    obtain ⟨y, hy, e⟩ := h1
    exact hj.injective e ▸ hy
  have htrp : ∀ D ∈ 𝓓, IsPreconnected (j ⁻¹' D) := fun D hD => by
    rw [← hj.isInducing.isPreconnected_image, image_preimage_eq_inter_range]
    exact (h𝓓 D hD).2.1
  have htrC : ∀ D ∈ 𝓓, (j ⁻¹' D ∩ C).Nonempty → j ⁻¹' D ⊆ C := fun D hD ⟨x, hx, hxC⟩ => by
    obtain ⟨c, hc', rfl⟩ := hC
    rw [connectedComponentIn_eq hxC]
    exact (htrp D hD).subset_connectedComponentIn hx (htr D hD)
  let DP : Set (Set T) := {D | D ∈ 𝓓 ∧ (j ⁻¹' D ∩ C).Nonempty}
  let DQ : Set (Set T) := {D | D ∈ 𝓓 ∧ ¬ (j ⁻¹' D ∩ C).Nonempty}
  have hclosedD : ∀ {A : Set (Set T)}, A ⊆ 𝓓 → IsClosed (⋃₀ A) := fun {A} hA =>
    (h𝓓f.subset hA).isClosed_sUnion fun D hD => (h𝓓 D (hA hD)).1.isCompact.isClosed
  have hdisjoint : Disjoint (j '' P ∪ ⋃₀ DP) (j '' Q ∪ ⋃₀ DQ) := by
    exact capped_cuff_sides_disjoint (S := S) (C := C) P Q hb hd hPQ T j hj 𝓓 h𝓓d htr htrC
  have hunion : Oᶜ = (j '' P ∪ ⋃₀ DP) ∪ (j '' Q ∪ ⋃₀ DQ) := by
    rw [hOc]
    apply Subset.antisymm
    · rintro z (⟨y, hy, rfl⟩ | h)
      · rcases hcov hy with h | h
        · exact .inl (.inl ⟨y, h, rfl⟩)
        · exact .inr (.inl ⟨y, h, rfl⟩)
      · rw [← h𝓓u] at h
        obtain ⟨D, hD, hz⟩ := h
        by_cases hn : (j ⁻¹' D ∩ C).Nonempty
        · exact .inl (.inr ⟨D, ⟨hD, hn⟩, hz⟩)
        · exact .inr (.inr ⟨D, ⟨hD, hn⟩, hz⟩)
    · rintro z ((⟨y, hy, rfl⟩ | ⟨D, hD, hz⟩) | (⟨y, hy, rfl⟩ | ⟨D, hD, hz⟩))
      · exact .inl ⟨y, hPs hy, rfl⟩
      · exact .inr (h𝓓u ▸ mem_sUnion_of_mem hz hD.1)
      · exact .inl ⟨y, hQs hy, rfl⟩
      · exact .inr (h𝓓u ▸ mem_sUnion_of_mem hz hD.1)
  obtain ⟨c, hc'⟩ : C.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨c₂, hc₂⟩ : C'.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hC'
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hDP : IsClosed (⋃₀ DP) := hclosedD (A := DP) fun _ hD => hD.1
  have hDQ : IsClosed (⋃₀ DQ) := hclosedD (A := DQ) fun _ hD => hD.1
  refine not_split_of_isOpenDisc hOdisc ((hj.isClosedMap _ hPc).union hDP)
    ((hj.isClosedMap _ hQc).union hDQ) hdisjoint hunion
    ⟨j c, .inl ⟨c, .inl (.inl hc'), rfl⟩⟩ ?_
  exact ⟨j c₂, .inl ⟨c₂, .inl (.inl ⟨hsubc C' hC' hc₂, fun h => hne (GM17.cuffs_disjoint_eq hC hC'
    h hc₂)⟩), rfl⟩⟩

/-- The set off a proper graph is not empty. -/
theorem offSet_nonempty (hS : IsSurface S) [ConnectedSpace S] {C : Set S} {C' : Set S}
  (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C') {K : Drawing S} (hK : K.IsProper) :
    (offSet K).Nonempty := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hfin : K.V.Finite := K.finite_V
  obtain ⟨p, hp⟩ : ((bd S)ᶜ \ K.V).Nonempty := by
    by_contra hem
    have hsub : (bd S)ᶜ ⊆ K.V := fun z hz => by
      by_contra hzV
      exact hem ⟨z, hz, hzV⟩
    have hu : (univ : Set S) ⊆ K.V := by
      rw [← (GM19.dense_interior' hS).closure_eq]
      exact closure_minimal hsub hfin.isClosed
    obtain ⟨a, ha⟩ : C.Nonempty := by
      obtain ⟨x, hx, rfl⟩ := hC
      exact ⟨x, mem_connectedComponentIn hx⟩
    obtain ⟨b, hb⟩ : C'.Nonempty := by
      obtain ⟨x, hx, rfl⟩ := hC'
      exact ⟨x, mem_connectedComponentIn hx⟩
    have hab : a ≠ b := fun h => hne (GM17.cuffs_disjoint_eq hC hC' ha (h ▸ hb))
    have hinf : (univ : Set S).Infinite := isPreconnected_univ.infinite_of_nontrivial ⟨a, trivial,
      b, trivial, hab⟩
    exact hinf (hfin.subset hu)
  by_cases hpU : p ∈ K.U
  · obtain ⟨e, he, hpe⟩ : ∃ e ∈ K.E, p ∈ e := by
      rw [K.U_eq] at hpU
      rcases hpU with h | h
      · exact (hp.2 h).elim
      · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp h
        refine ⟨e, he, ?_⟩
        rw [← K.closure_diff_V he]
        exact ⟨hpe, hp.2⟩
    obtain ⟨-, A, -, -, -, -, hA, -, -, -, -, hAp, -, -, -, -⟩ := exists_edge_sides hS hK he hpe
    exact hAp.nonempty.mono hA
  · exact ⟨p, mem_offSet.mpr ⟨hpU, hp.1⟩⟩

end GraphMinor.GM07
