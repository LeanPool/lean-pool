/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Interior fibers for a separating paired side

In the general type-(ii) exchange of VII (2.6), page 218, a
whole refined pair lies across the two cut pieces. Its open
arc fibers are merged by pasting. The two cutting endpoints
are outside the open paired sides, so both lifts of the cut remain boundary
points. All remaining interior fibers come from old interior
points and stay singletons.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The associated map of a separating-pair exchange is injective
at every interior point of its new disc. This is the interior-fiber
condition for the general new net in VII (2.6), page 218. -/
theorem Net.separating_map_interior_inj
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) {A B F : Set N.D} {s t : N.D}
    (hFbd : F ∩ bd N.D = {s, t}) (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s
      ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F)
    (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (α : A → T) (β : B → T) (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ r, x.val = N.f i r ∧ y.val = N.g i r)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∀ z ∈ (bd T)ᶜ, ∀ w, φ z = φ w → z = w := by
  have hfAvoid : Disjoint F (N.f i '' Ioo (0 : unitInterval) 1) := by
    apply disjoint_left.mpr
    rintro x hxF ⟨r, hr, rfl⟩
    rcases hFbd.subset ⟨hxF, N.range_f_subset_bd i (mem_range_self r)⟩ with hxs | hxt
    · exact (hs i r hr).1 hxs
    · exact (ht i r hr).1 (mem_singleton_iff.mp hxt)
  have hgAvoid : Disjoint F (N.g i '' Ioo (0 : unitInterval) 1) := by
    apply disjoint_left.mpr
    rintro x hxF ⟨r, hr, rfl⟩
    rcases hFbd.subset ⟨hxF, N.range_g_subset_bd i (mem_range_self r)⟩ with hxs | hxt
    · exact (hs i r hr).2 hxs
    · exact (ht i r hr).2 (mem_singleton_iff.mp hxt)
  have hcutA : ∀ x : A, x.val ∈ F → α x ∈ bd T := by
    intro x hx
    exact (hαbd x).mpr ⟨hAd ▸ Or.inr hx, fun h => disjoint_left.mp hfAvoid hx h⟩
  have hcutB : ∀ y : B, y.val ∈ F → β y ∈ bd T := by
    intro y hy
    exact (hβbd y).mpr ⟨hBd ▸ Or.inr hy, fun h => disjoint_left.mp hgAvoid hy h⟩
  have hpasted : ∀ x : A, x.val ∈ N.f i '' Ioo (0 : unitInterval) 1 →
      ∀ z, φ (α x) = φ z → α x = z := by
    intro x hx z heq
    obtain ⟨r, hr, hrx⟩ := hx
    have hgB' : N.g i r ∈ B := discBd_subset B (hgB (mem_range_self r))
    have hxy : α x = β ⟨N.g i r, hgB'⟩ :=
      (hcross x ⟨N.g i r, hgB'⟩).mpr ⟨r, hrx.symm, rfl⟩
    have hmem : ∀ y, N.φ x.val = N.φ y → y ∈ ({N.f i r, N.g i r} : Set N.D) := by
      intro y hy
      rw [← N.fiber_eq_pair_of_mem_Ioo i hr]
      exact hy.symm.trans (congrArg N.φ hrx.symm)
    rcases hT.symm ▸ mem_univ z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rcases hmem y.val ((hφA x).symm.trans (heq.trans (hφA y))) with hyf | hyg
      · exact congrArg α (Subtype.ext (hrx.symm.trans hyf.symm))
      · have hyg' := mem_singleton_iff.mp hyg
        have hyF : y.val ∈ F := hI ▸ ⟨y.property, hyg'.symm ▸ hgB'⟩
        exact (disjoint_left.mp hgAvoid hyF ⟨r, hr, hyg'.symm⟩).elim
    · rcases hmem y.val ((hφA x).symm.trans (heq.trans (hφB y))) with hyf | hyg
      · have hyF : y.val ∈ F := hI ▸ ⟨(hyf.trans hrx).symm ▸ x.property, y.property⟩
        exact (disjoint_left.mp hfAvoid hyF ⟨r, hr, hyf.symm⟩).elim
      · exact hxy.trans (congrArg β (Subtype.ext (mem_singleton_iff.mp hyg).symm))
  have hleft : ∀ x : A, α x ∉ bd T → ∀ z, φ (α x) = φ z → α x = z := by
    intro x hx z heq
    by_cases hxbd : x.val ∈ bd N.D
    · have hxp : x.val ∈ N.f i '' Ioo (0 : unitInterval) 1 := by
        by_contra h
        exact hx ((hαbd x).mpr ⟨hAd ▸ Or.inl ⟨x.property, hxbd⟩, h⟩)
      exact hpasted x hxp z heq
    · rcases hT.symm ▸ mem_univ z with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hxy := N.interior_inj x.val hxbd y.val
          ((hφA x).symm.trans (heq.trans (hφA y)))
        exact congrArg α (Subtype.ext hxy)
      · have hxy := N.interior_inj x.val hxbd y.val
          ((hφA x).symm.trans (heq.trans (hφB y)))
        exact (hx (hcutA x (hI ▸ ⟨x.property, hxy.symm ▸ y.property⟩))).elim
  intro z hz w heq
  rcases hT.symm ▸ mem_univ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hleft x hz w heq
  · by_cases hybd : y.val ∈ bd N.D
    · have hyp : y.val ∈ N.g i '' Ioo (0 : unitInterval) 1 := by
        by_contra h
        exact hz ((hβbd y).mpr ⟨hBd ▸ Or.inl ⟨y.property, hybd⟩, h⟩)
      obtain ⟨r, hr, hry⟩ := hyp
      have hfA' : N.f i r ∈ A := discBd_subset A (hfA (mem_range_self r))
      let x : A := ⟨N.f i r, hfA'⟩
      have hxy : α x = β y := (hcross x y).mpr ⟨r, rfl, hry.symm⟩
      exact hxy.symm.trans (hleft x (hxy.symm ▸ hz) w ((congrArg φ hxy).trans heq))
    · rcases hT.symm ▸ mem_univ w with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · have hyx := N.interior_inj y.val hybd x.val
          ((hφB y).symm.trans (heq.trans (hφA x)))
        exact (hz (hcutB y (hI ▸ ⟨hyx.symm ▸ x.property, y.property⟩))).elim
      · have hyx := N.interior_inj y.val hybd x.val
          ((hφB y).symm.trans (heq.trans (hφB x)))
        exact congrArg β (Subtype.ext hyx)

end GraphMinor.GM07
