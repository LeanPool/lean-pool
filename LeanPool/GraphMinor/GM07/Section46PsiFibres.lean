/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
import LeanPool.GraphMinor.GM07.Section46SurfaceApproach
import LeanPool.GraphMinor.GM07.Section46UniqueLiftLimit
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# The fibres of the second cutting map off the matching

VII (4.6), page 228, says `|ψ⁻¹(v)| = 1` for a point `v` of `Σ′` off the
matching. Two points of one such fibre would be two limits at `v` of the
inverse of `ψ` on the open disc. A small neighbourhood of `v` misses the
matching and is connected after removing the boundary. So the two limits
are equal by the unique limit argument of page 226.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S D : Type u} [TopologicalSpace S] [TopologicalSpace D]

/-- A cut map is one-to-one off its graph, in VII (4.6), page 228. -/
theorem IsCutAlongGraph.eq_of_eq_of_notMem [T2Space D] {K : Drawing S} {ψ : D → S}
    (hψ : IsCutAlongGraph K D ψ) (hS : IsSurface S) {x y : D} (hxy : ψ x = ψ y)
    (hv : ψ x ∉ K.U) : x = y := by
  classical
  have hD := hψ.isSurface
  have : CompactSpace D := hD.1
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hc : Continuous ψ := hψ.quotientMap.continuous
  have hs : Function.Surjective ψ := hψ.quotientMap.surjective
  let U : Set S := (bd S ∪ K.U)ᶜ
  have hbdU : ∀ z, z ∉ bd D → ψ z ∈ U := by
    intro z hz hb
    apply hz
    rw [← hψ.preimage_bd_union_U]
    exact hb
  have huniq : ∀ a ∈ U, ∀ z w : D, ψ z = a → ψ w = a → z = w := by
    intro a ha z w hz hw
    have hzb : z ∉ bd D := by
      intro hb
      rw [← hψ.preimage_bd_union_U] at hb
      exact ha (by rw [← hz]; exact hb)
    exact hψ.interior_inj z hzb w (hz.trans hw.symm)
  choose g hg using hs
  have hgc : ContinuousOn g U := by
    intro a ha
    rw [ContinuousWithinAt, tendsto_nhds]
    intro O hO hgx
    have hK : IsClosed (ψ '' Oᶜ) := hc.isClosedMap _ hO.isClosed_compl
    have hxK : a ∈ (ψ '' Oᶜ)ᶜ := by
      rintro ⟨w, hw, hwa⟩
      exact hw (huniq a ha w (g a) hwa (hg a) ▸ hgx)
    apply mem_nhdsWithin.mpr
    refine ⟨_, hK.isOpen_compl, hxK, ?_⟩
    rintro z ⟨hz, -⟩
    by_contra hzO
    exact hz ⟨g z, hzO, hg z⟩
  have hclosure : ∀ z, (ψ z, z) ∈ closure ((fun a => (a, g a)) '' U) := by
    intro z
    rw [mem_closure_iff]
    intro T hT hmem
    obtain ⟨O, P, hO, hP, hzO, hzP, hsub⟩ := isOpen_prod_iff.mp hT _ _ hmem
    have hopen : IsOpen (P ∩ ψ ⁻¹' O) := hP.inter (hO.preimage hc)
    obtain ⟨w, hw, hwb⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hD.2.2 z)) _ hopen ⟨hzP, hzO⟩
    have hU : ψ w ∈ U := hbdU w hwb
    have hgw : g (ψ w) = w := huniq _ hU _ _ (hg _) rfl
    refine ⟨(ψ w, w), hsub ⟨hw.2, hw.1⟩, ⟨ψ w, hU, ?_⟩⟩
    simp [hgw]
  have hyx : (ψ x, y) ∈ closure ((fun a => (a, g a)) '' U) := hxy ▸ hclosure y
  refine unique_lift_limit_of_connected_approach (f := id) (U := U) (g := g) (θ := ψ)
    continuous_id hgc hc hψ.finite_fiber (fun a _ => hg a) ?_ (hclosure x) hyx
  intro O hO hxO
  have hopen : IsOpen (O ∩ K.Uᶜ) := hO.inter K.isClosed_U.isOpen_compl
  obtain ⟨W, hWo, hxW, hWsub, hWc⟩ := surface_connected_approach (hS.2.2 (ψ x)) hopen ⟨hxO, hv⟩
  refine ⟨W, hWo, hxW, fun z hz => (hWsub hz).1, ?_⟩
  have heq : W ∩ U = W ∩ (bd S)ᶜ := by
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hz, fun hb => hzU (.inl hb)⟩
    · rintro ⟨hz, hzb⟩
      refine ⟨hz, ?_⟩
      rintro (h | h)
      · exact hzb h
      · exact (hWsub hz).2 h
  rw [heq]
  exact hWc

end GraphMinor.GM07
