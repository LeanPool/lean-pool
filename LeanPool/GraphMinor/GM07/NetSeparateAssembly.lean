/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSeparateFamily
import LeanPool.GraphMinor.GM07.NetSeparateFibers
import LeanPool.GraphMinor.GM07.NetSeparateEquivalence
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The net of a separating-pair exchange

For the general type-(ii) exchange in VII (2.6), page 218,
paste the selected pair across the two cut pieces and use the
two cutting-line lifts as its replacement. The side family
and fiber calculations verify every net field. The number
of pairs is unchanged, and the seam is contained in the old
seam together with the cutting-line image.
-/

public section
namespace GraphMinor.GM07
open Set Surface
universe u

/-- Package the actual separating-pair exchange as a net for the
same surface, proving every net condition from the cut maps. This
is the general new-net construction in VII (2.6), page 218. -/
theorem Net.exists_separating_net_of_maps
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (hSurface : IsSurface T)
    (hDisc : IsClosedDisc (univ : Set T)) (i : Fin N.r) {F A B : Set N.D} {s t : N.D}
    (hF : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t})
    (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = N.f i r ∧ y.val = N.g i r)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφ : Topology.IsQuotientMap φ) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∃ M : Net S, ∃ e : T ≃ₜ M.D,
      M.r = N.r ∧ M.φ ∘ e = φ ∧ M.seamU ⊆ N.seamU ∪ N.φ '' F := by
  obtain ⟨k, f, g, _, hkF, _, _, hfi, hgi, hfbd, hgbd, hff, hgg, hfg, hgf,
    hpair, hkf, hkg, hotherf, hotherg⟩ :=
    N.exists_separating_side_family i hF hFbd hs ht hA hB hAB hI hAd hBd
      α β hcα hcβ hiα hiβ hcross hαbd hβbd φ hφA hφB
  have hInterior := N.separating_map_interior_inj i hFbd hs ht hI hAd hBd hfA hgB
    α β hT hcross hαbd hβbd φ hφA hφB
  have hEquiv := N.separating_map_eqvGen i hAB hI
    (hfA.trans (discBd_subset A)) (hgB.trans (discBd_subset B))
    α β hT hcross φ hφA hφB k hkF f g hpair hkf hkg hotherf hotherg
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
  refine ⟨M, Homeomorph.refl T, rfl, rfl, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  rcases hT.symm ▸ mem_univ w with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · change φ (α x) ∈ N.seamU ∪ N.φ '' F
    rw [hφA]
    have hx := ((hαbd x).mp hw).1
    rcases hAd ▸ hx with hxOld | hxF
    · exact Or.inl ⟨x.val, hxOld.2, rfl⟩
    · exact Or.inr ⟨x.val, hxF, rfl⟩
  · change φ (β y) ∈ N.seamU ∪ N.φ '' F
    rw [hφB]
    have hy := ((hβbd y).mp hw).1
    rcases hBd ▸ hy with hyOld | hyF
    · exact Or.inl ⟨y.val, hyOld.2, rfl⟩
    · exact Or.inr ⟨y.val, hyF, rfl⟩

end GraphMinor.GM07
