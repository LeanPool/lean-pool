/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSeparateEquivalence
import LeanPool.GraphMinor.GM07.NetSwapFibers
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.GM07.NetSwapSides
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The equivalence relation of the exchanged net

In VII (2.6), page 218, the new paired sides must generate exactly
the fibers of the associated surjection. Lift each old identification
through the two cut pieces. Pasted subarc points become equal, retained
paired points stay paired, and the two lifts of each cutting point
are paired by the inserted portions of the new sides.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The replacement side family generates exactly the fibers of the
associated map after the subarc exchange in VII (2.6), page 218. -/
theorem Net.swap_map_eqvGen
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (α : A → T) (β : B → T) (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val)
    (f g : Fin N.r → Curve T) (hpair : ∀ j t, φ (f j t) = φ (g j t))
    (hends : ∀ j, f j 0 ∈ β '' {x : B | x.val = N.f j 0} ∧
      f j 1 ∈ β '' {x : B | x.val = N.f j 1} ∧
      g j 0 ∈ β '' {x : B | x.val = N.g j 0} ∧
      g j 1 ∈ β '' {x : B | x.val = N.g j 1})
    (hotherf : ∀ j, j ≠ i → ∀ t, ∃ x : B, x.val = N.f j t ∧ f j t = β x)
    (hotherg : ∀ j, j ≠ i → ∀ t, ∃ x : B, x.val = N.g j t ∧ g j t = β x)
    (hfr : range (f i) = (β '' {x : B | x.val ∈ N.f i '' Icc 0 u} ∪
      β '' {x : B | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.f i '' Icc v 1})
    (hgr : range (g i) = (β '' {x : B | x.val ∈ N.g i '' Icc 0 u} ∪
      α '' {x : A | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.g i '' Icc v 1}) :
    ∀ z w, φ z = φ w ↔ Relation.EqvGen
      (fun a b : T => ∃ (j : Fin N.r) (t : unitInterval), a = f j t ∧ b = g j t) z w := by
  classical
  let R : T → T → Prop := Relation.EqvGen
    (fun a b : T => ∃ (j : Fin N.r) (t : unitInterval), a = f j t ∧ b = g j t)
  have hRsymm {x y : T} : R x y → R y x := Relation.EqvGen.symm x y
  have hRpair : ∀ j t, R (f j t) (g j t) := fun j t => .rel _ _ ⟨j, t, rfl, rfl⟩
  have hqCoarse : range (g i) ⊆ β '' {x : B | x.val ∈ range (N.g i)} ∪
      α '' {x : A | x.val ∈ F} := by
    rw [hgr]
    rintro z ((⟨x, hx, rfl⟩ | hz) | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
  have hpCut : β '' {x : B | x.val ∈ F} ⊆ range (f i) := by
    rw [hfr]
    exact fun _ h => Or.inl (Or.inr h)
  have hCut : ∀ (x : A) (y : B), x.val = y.val → R (α x) (β y) := by
    intro x y hxy
    have hxF : x.val ∈ F := hI ▸ ⟨x.property, hxy.symm ▸ y.property⟩
    obtain ⟨t, hpt, hqt⟩ := N.swap_cutting_lifts_match i u v hu huv hv hFbd
      α β hcross φ hφA hφB (f i) (g i) (hpair i) hpCut hqCoarse x y hxy hxF
    have h := hRpair i t
    rw [hpt, hqt] at h
    exact hRsymm h
  let σ : A ⊕ B → N.D := Sum.elim Subtype.val Subtype.val
  let μ : A ⊕ B → T := Sum.elim α β
  obtain ⟨_, hmates, hleft, hright⟩ := N.sides_on_retained_piece i u v hu huv hv hF hcover hBd
  have hgB : ∀ t, N.g i t ∈ B :=
    fun t => discBd_subset B (hmates i (mem_range_self t))
  have hOldPair : ∀ j t, ∃ a b, σ a = N.f j t ∧ σ b = N.g j t ∧ R (μ a) (μ b) := by
    intro j t
    by_cases hji : j = i
    · subst j
      by_cases ht0 : t = 0
      · subst t
        obtain ⟨x, hx, hxf⟩ := (hends i).1
        obtain ⟨y, hy, hyg⟩ := (hends i).2.2.1
        refine ⟨Sum.inr x, Sum.inr y, hx, hy, ?_⟩
        change R (β x) (β y)
        rw [hxf, hyg]
        exact hRpair i 0
      by_cases ht1 : t = 1
      · subst t
        obtain ⟨x, hx, hxf⟩ := (hends i).2.1
        obtain ⟨y, hy, hyg⟩ := (hends i).2.2.2
        refine ⟨Sum.inr x, Sum.inr y, hx, hy, ?_⟩
        change R (β x) (β y)
        rw [hxf, hyg]
        exact hRpair i 1
      by_cases ht : t ∈ Icc u v
      · obtain ⟨r, hrf, hrg⟩ := exists_pieceA_common_parameter (N.f i) (N.g i) u v t ht
        have hfA : N.f i t ∈ A :=
          discBd_subset A (hAd ▸ Or.inl ⟨r, hrf⟩)
        let x : A := ⟨N.f i t, hfA⟩
        let y : B := ⟨N.g i t, hgB t⟩
        have hxy : α x = β y := (hcross x y).mpr ⟨r, hrf.symm, hrg.symm⟩
        refine ⟨Sum.inl x, Sum.inr y, rfl, rfl, ?_⟩
        change R (α x) (β y)
        rw [hxy]
        exact .refl _
      · have hout : t ≤ u ∨ v ≤ t := by
          rcases le_total t u with htu | hut
          · exact Or.inl htu
          · exact Or.inr (le_of_lt (lt_of_not_ge (fun htv => ht ⟨hut, htv⟩)))
        have hfB : N.f i t ∈ B := by
          apply discBd_subset B
          rcases hout with htu | hvt
          · exact hleft ⟨t, ⟨unitInterval.nonneg t, htu⟩, rfl⟩
          · exact hright ⟨t, ⟨hvt, unitInterval.le_one t⟩, rfl⟩
        let x : B := ⟨N.f i t, hfB⟩
        let y : B := ⟨N.g i t, hgB t⟩
        have hxp : β x ∈ range (f i) := by
          rw [hfr]
          rcases hout with htu | hvt
          · exact Or.inl (Or.inl ⟨x, ⟨t, ⟨unitInterval.nonneg t, htu⟩, rfl⟩, rfl⟩)
          · exact Or.inr ⟨x, ⟨t, ⟨hvt, unitInterval.le_one t⟩, rfl⟩, rfl⟩
        obtain ⟨s, hfs, hgs⟩ := N.swap_retained_lifts_match i u v hu huv hv hFbd
          α β hcross φ hφA hφB (f i) (g i) (hpair i) hqCoarse
          (Net.mem_Ioo_of_ne ht0 ht1) x y rfl rfl hxp
        refine ⟨Sum.inr x, Sum.inr y, rfl, rfl, ?_⟩
        have h := hRpair i s
        rw [hfs, hgs] at h
        exact h
    · obtain ⟨x, hx, hxf⟩ := hotherf j hji t
      obtain ⟨y, hy, hyg⟩ := hotherg j hji t
      refine ⟨Sum.inr x, Sum.inr y, hx, hy, ?_⟩
      have h := hRpair j t
      rw [hxf, hyg] at h
      exact h
  exact N.map_eqvGen_of_cut_lifts hAB α β hT φ hφA hφB f g hpair hCut hOldPair

end GraphMinor.GM07
