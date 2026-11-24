/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapFamily
import LeanPool.GraphMinor.GM07.NetSwapFibers
import LeanPool.GraphMinor.GM07.NetSwapEquivalence

/-!
# Packaging the exchanged disc as a net

The cut-and-paste maps of VII (2.6), page 218, give a genuine
net: the replacement side family supplies the boundary arcs,
and the fiber calculations verify both identification conditions.
The number of paired sides and the seam vertices stay unchanged.
-/

public section
namespace GraphMinor.GM07
open Set Surface
universe u

/-- Package the actual cut-and-paste maps as a net for the same
surface, with the same number of pairs and the same seam vertices.
All net fields are proved from the cut configuration, as required
by the new-net construction in VII (2.6), page 218. -/
theorem Net.exists_swap_net_of_maps
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (hSurface : IsSurface T)
    (hDisc : IsClosedDisc (univ : Set T)) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (hBd : discBd B = C ∪ F)
    (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧ y.val = pieceA (N.g i) u.val v.val t)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφ : Topology.IsQuotientMap φ) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∃ M : Net S, ∃ e : T ≃ₜ M.D,
      M.r = N.r ∧ M.φ ∘ e = φ ∧ M.seamV = N.seamV := by
  obtain ⟨f, g, hfi, hgi, hfbd, hgbd, hff, hgg, hfg, hgf, hpair, hends,
    hotherf, hotherg, hfr, hgr⟩ :=
    N.exists_replacement_side_family i u v hu huv hv hF hFbd hI hAd hcover hBd
      α β hcα hcβ hiα hiβ hcross hαbd hβbd φ hφA hφB
  have hInterior := N.swap_map_interior_inj i u v hu huv hv hFbd hI hAd hBd hcover
    α β hT hcross hαbd hβbd φ hφA hφB
  have hEquiv := N.swap_map_eqvGen i u v hu huv hv hF hFbd hAB hI hAd hBd hcover
    α β hT hcross φ hφA hφB f g hpair hends hotherf hotherg hfr hgr
  let M : Net S :=
    { D := T
      topD := inferInstance
      isSurface_D := hSurface
      isClosedDisc_D := hDisc
      r := N.r
      f := f
      g := g
      φ := φ
      injective_f := hfi
      range_f_subset_bd := hfbd
      injective_g := hgi
      range_g_subset_bd := hgbd
      internally_disjoint_ff := hff
      internally_disjoint_gg := hgg
      internally_disjoint_fg := hfg
      internally_disjoint_gf := hgf
      quotientMap_φ := hφ
      pasting_eq := hpair
      interior_inj := hInterior
      bd_eq_iff := hEquiv }
  have h0 : ∀ j, φ (f j 0) = N.φ (N.f j 0) := by
    intro j
    obtain ⟨x, hx, hxf⟩ := (hends j).1
    exact (congrArg φ hxf).symm.trans ((hφB x).trans (congrArg N.φ hx))
  have h1 : ∀ j, φ (f j 1) = N.φ (N.f j 1) := by
    intro j
    obtain ⟨x, hx, hxf⟩ := (hends j).2.1
    exact (congrArg φ hxf).symm.trans ((hφB x).trans (congrArg N.φ hx))
  refine ⟨M, Homeomorph.refl T, rfl, rfl, ?_⟩
  change {z | ∃ j, φ (f j 0) = z ∨ φ (f j 1) = z} = N.seamV
  simp_rw [h0, h1]
  rfl

end GraphMinor.GM07
