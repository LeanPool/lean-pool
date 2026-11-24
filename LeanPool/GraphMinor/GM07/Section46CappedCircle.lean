/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.CutBounds
import LeanPool.GraphMinor.GM07.Section11a
import LeanPool.GraphMinor.GM07.Section46SeamComplement
import LeanPool.GraphMinor.GM07.Section46DiscSides
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.AddCrosscap
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification

/-!
# The capped circle in the unique seam region

In VII (4.6), page 226, a circle in the seam that is null-homotopic after
capping a cuff `C` must equal `C`. Use the disc it bounds in the capped
surface and the dense connected complement of the seam. The disc cannot
contain the original surface: another cuff would then lie in its boundary,
forcing the circle to equal that other cuff, contrary to its containing
the prescribed graph vertices of `C`. The disc therefore meets the
original surface only in its boundary and lies in the added cap.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The capped-cuff case of the circle argument in VII (4.6), page 226. -/
theorem Net.capped_circle_eq_cuff {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G : Drawing S} {F C : Set S} (hF : IsOArc F) (hFU : F ⊆ N.seamU)
    (hC : C ∈ cuffs S) (hnull : IsNullHomotopicOArcInCappedCuff C F)
    (hVC : (G.V ∩ C).Nonempty) (hVCF : G.V ∩ C ⊆ F) : F = C := by
  have : T2Space S := hS.2.1
  obtain ⟨T, _, j, D, hcap, hbdT⟩ := exists_cappedCuff hS hC
  have : T2Space T := hcap.isSurface.2.1
  have hOjF : IsOArc (j '' F) := isOArc_image hcap.isEmbedding hF
  have hn : IsNullHomotopicOArc (j '' F) := hnull.2.2 T j D hcap
  obtain ⟨R, hR, hRbd⟩ := nullHomotopicOArc_bounds_disc hcap.isSurface hOjF hn
  let Q := j '' N.seamUᶜ
  have hQ : IsPreconnected Q := N.isPreconnected_compl_seamU.image j
    hcap.isEmbedding.continuous.continuousOn
  have hdense : range j ⊆ closure Q := by
    rintro x ⟨y, rfl⟩
    exact image_closure_subset_closure_image hcap.isEmbedding.continuous
      ⟨y, N.dense_compl_seamU y, rfl⟩
  have hdis : Disjoint Q (discBd R) := by
    rw [hRbd]
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzj⟩
    have hzy := hcap.isEmbedding.injective hzj
    exact hy (hFU (hzy ▸ hz))
  have hside := disc_side_of_dense_connected_set hcap.isSurface.2.2 hR hQ hdense hdis
  have hnotcover : ¬range j ⊆ R := by
    intro hcover
    obtain ⟨C', hC', hne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (cuffs S).ncard) C
    have hCO : IsOArc C' := (cuff_statement S hS).2.2 C' hC'
    have hOjC : IsOArc (j '' C') := isOArc_image hcap.isEmbedding hCO
    have hC'F : j '' C' ⊆ j '' F := by
      rintro x ⟨y, hy, rfl⟩
      have hybd : y ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C', hC', hy⟩
      have hyC : y ∉ C := fun h => disjoint_left.mp (cuffs_disjoint hC' hC hne) hy h
      have hyT : j y ∈ bd T := hbdT ▸ ⟨y, ⟨hybd, hyC⟩, rfl⟩
      have hyR : j y ∈ R := hcover (mem_range_self y)
      have hyRbd : j y ∈ discBd R := by
        by_contra hnb
        exact hyT (isInteriorPoint_of_mem_discInt hcap.isSurface.2.2 hR ⟨hyR, hnb⟩)
      exact hRbd ▸ hyRbd
    have heq := eq_of_oArc_subset hOjC hOjF hC'F
    obtain ⟨p, hpV, hpC⟩ := hVC
    have hpF := hVCF ⟨hpV, hpC⟩
    have hpj : j p ∈ j '' C' := heq.symm ▸ mem_image_of_mem j hpF
    obtain ⟨q, hq, hqp⟩ := hpj
    have hqp' := hcap.isEmbedding.injective hqp
    exact disjoint_left.mp (cuffs_disjoint hC' hC hne) (hqp' ▸ hq) hpC
  have hboundary : R ∩ range j ⊆ discBd R := hside.resolve_left hnotcover
  have hIntCap : discInt R ⊆ D := by
    intro x hx
    have hxall : x ∈ range j ∪ D := hcap.union_eq ▸ mem_univ x
    rcases hxall with hj | hD
    · exact (hx.2 (hboundary ⟨hx.1, hj⟩)).elim
    · exact hD
  have hRCap : R ⊆ D := hR.subset_closure_discInt.trans (closure_minimal hIntCap
    hcap.isClosedDisc.isClosed)
  have hFsub : F ⊆ C := by
    intro x hx
    have hjF : j x ∈ discBd R := hRbd.symm ▸ mem_image_of_mem j hx
    have hjR : j x ∈ R := Surface.discBd_subset R hjF
    have hjC : j x ∈ j '' C := hcap.inter_eq ▸ ⟨mem_range_self x, hRCap hjR⟩
    obtain ⟨y, hy, hyx⟩ := hjC
    exact (hcap.isEmbedding.injective hyx) ▸ hy
  exact eq_of_oArc_subset hF ((cuff_statement S hS).2.2 C hC) hFsub

end GraphMinor.GM07
