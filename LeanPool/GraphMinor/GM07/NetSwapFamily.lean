/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapPair
import LeanPool.GraphMinor.GM07.NetSwapSides
import LeanPool.GraphMinor.GM07.NetSwapReplacement
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# All paired sides after the net exchange

For the cut and paste in VII (2.6), page 218, retain every
unselected pair on the second piece and insert the two replacement
sides. The fiber equation and the old net's internal disjointness
show that all these sides are pairwise internally disjoint.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- Construct the full family of paired boundary arcs for the net
exchange in VII (2.6), page 218. The index set is unchanged. -/
theorem Net.exists_replacement_side_family
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (hBd : discBd B = C ∪ F)
    (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧ y.val = pieceA (N.g i) u.val v.val t)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∃ f g : Fin N.r → Curve T,
      (∀ j, Function.Injective (f j)) ∧ (∀ j, Function.Injective (g j)) ∧
      (∀ j, range (f j) ⊆ bd T) ∧ (∀ j, range (g j) ⊆ bd T) ∧
      (∀ j k, j ≠ k → ∀ t ∈ Ioo (0 : unitInterval) 1, f j t ∉ range (f k)) ∧
      (∀ j k, j ≠ k → ∀ t ∈ Ioo (0 : unitInterval) 1, g j t ∉ range (g k)) ∧
      (∀ j k, ∀ t ∈ Ioo (0 : unitInterval) 1, f j t ∉ range (g k)) ∧
      (∀ j k, ∀ t ∈ Ioo (0 : unitInterval) 1, g j t ∉ range (f k)) ∧
      (∀ j t, φ (f j t) = φ (g j t)) ∧
      (∀ j, f j 0 ∈ β '' {x : B | x.val = N.f j 0} ∧
        f j 1 ∈ β '' {x : B | x.val = N.f j 1} ∧
        g j 0 ∈ β '' {x : B | x.val = N.g j 0} ∧
        g j 1 ∈ β '' {x : B | x.val = N.g j 1}) ∧
      (∀ j, j ≠ i → ∀ t, ∃ x : B, x.val = N.f j t ∧ f j t = β x) ∧
      (∀ j, j ≠ i → ∀ t, ∃ x : B, x.val = N.g j t ∧ g j t = β x) ∧
      range (f i) = (β '' {x : B | x.val ∈ N.f i '' Icc 0 u} ∪
        β '' {x : B | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.f i '' Icc v 1} ∧
      range (g i) = (β '' {x : B | x.val ∈ N.g i '' Icc 0 u} ∪
        α '' {x : A | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.g i '' Icc v 1} := by
  classical
  obtain ⟨p, q, hpi, hqi, hpq, _, _, _, _, hpr, hqr, hpbd, hqbd,
    hp0, hp1, hq0, hq1, hpqd, hqpd⟩ :=
    N.exists_replacement_pair i u v hu huv hv hF hFbd hI hAd hcover hBd
      α β hcα hcβ hiα hiβ hcross hαbd hβbd φ hφA hφB
  obtain ⟨hother, hmates, _, _⟩ := N.sides_on_retained_piece i u v hu huv hv hF hcover hBd
  have hfB : ∀ j, j ≠ i → ∀ t, N.f j t ∈ B :=
    fun j hj t => discBd_subset B (hother j hj (mem_range_self t))
  have hgB : ∀ j t, N.g j t ∈ B :=
    fun j t => discBd_subset B (hmates j (mem_range_self t))
  let lift (a : Curve N.D) (ha : ∀ t, a t ∈ B) : Curve T :=
    ⟨fun t => β ⟨a t, ha t⟩, hcβ.comp (a.continuous.subtype_mk ha)⟩
  let f : Fin N.r → Curve T := fun j => if hj : j = i then p else lift (N.f j) (hfB j hj)
  let g : Fin N.r → Curve T := fun j => if j = i then q else lift (N.g j) (hgB j)
  have hfi : f i = p := dite_eq_left rfl
  have hgi : g i = q := ite_eq_left rfl
  have hfj : ∀ j (hj : j ≠ i), f j = lift (N.f j) (hfB j hj) := fun j hj => dite_eq_right hj
  have hgj : ∀ j, j ≠ i → g j = lift (N.g j) (hgB j) := fun j hj => ite_eq_right hj
  have hliftInj : ∀ (a : Curve N.D) (ha : ∀ t, a t ∈ B),
      Function.Injective a → Function.Injective (lift a ha) := by
    intro a ha hai s t heq
    exact hai (congrArg Subtype.val (hiβ heq))
  have hliftDisj : ∀ (a b : Curve N.D) (ha : ∀ t, a t ∈ B) (hb : ∀ t, b t ∈ B),
      (∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range b) →
      ∀ t ∈ Ioo (0 : unitInterval) 1, lift a ha t ∉ range (lift b hb) := by
    intro a b ha hb hab t ht
    rintro ⟨s, hs⟩
    exact hab t ht ⟨s, congrArg Subtype.val (hiβ hs)⟩
  have hpCoarse : range p ⊆ β '' {x : B | x.val ∈ range (N.f i)} ∪
      β '' {x : B | x.val ∈ F} := by
    rw [hpr]
    rintro z ((⟨x, hx, rfl⟩ | hz) | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
  have hqCoarse : range q ⊆ β '' {x : B | x.val ∈ range (N.g i)} ∪
      α '' {x : A | x.val ∈ F} := by
    rw [hqr]
    rintro z ((⟨x, hx, rfl⟩ | hz) | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
  obtain ⟨hFf, hFg⟩ := N.cutting_line_disjoint_other_sides i hu huv hv hFbd
  have hβdisj : ∀ K : Set N.D, Disjoint F K →
      Disjoint (β '' {x : B | x.val ∈ F}) (β '' {x : B | x.val ∈ K}) := by
    intro K hK
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact disjoint_left.mp hK hx ((hiβ heq) ▸ hy)
  obtain ⟨hαf, hαg⟩ := N.attached_piece_disjoint_other_sides i hu huv hv α β hcross
  have hαdisj : ∀ K : Set N.D, Disjoint (range α) (β '' {x : B | x.val ∈ K}) →
      Disjoint (α '' {x : A | x.val ∈ F}) (β '' {x : B | x.val ∈ K}) :=
    fun K hK => hK.mono_left (image_subset_range _ _)
  have hpf : ∀ j (hj : j ≠ i),
      (∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range (lift (N.f j) (hfB j hj))) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, lift (N.f j) (hfB j hj) t ∉ range p) := by
    intro j hj
    exact internally_disjoint_replacement_retained_side (N.f i) (N.f j) β hiβ
      (N.injective_f j) (N.internally_disjoint_ff i j hj.symm)
      (N.internally_disjoint_ff j i hj) p (lift (N.f j) (hfB j hj)) hpi hpCoarse
      (hβdisj _ (hFf j hj)) hp0 hp1 (hfB j hj) (fun _ => rfl)
  have hpg : ∀ j,
      (∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range (lift (N.g j) (hgB j))) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, lift (N.g j) (hgB j) t ∉ range p) := by
    intro j
    exact internally_disjoint_replacement_retained_side (N.f i) (N.g j) β hiβ
      (N.injective_g j) (N.internally_disjoint_fg i j) (N.internally_disjoint_gf j i)
      p (lift (N.g j) (hgB j)) hpi hpCoarse
      (hβdisj _ (hFg j)) hp0 hp1 (hgB j) (fun _ => rfl)
  have hqf : ∀ j,
      ∀ hj : j ≠ i,
      (∀ t ∈ Ioo (0 : unitInterval) 1, q t ∉ range (lift (N.f j) (hfB j hj))) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, lift (N.f j) (hfB j hj) t ∉ range q) := by
    intro j hj
    exact internally_disjoint_replacement_retained_side (N.g i) (N.f j) β hiβ
      (N.injective_f j) (N.internally_disjoint_gf i j) (N.internally_disjoint_fg j i)
      q (lift (N.f j) (hfB j hj)) hqi hqCoarse
      (hαdisj _ (hαf j)) hq0 hq1 (hfB j hj) (fun _ => rfl)
  have hqg : ∀ j (hj : j ≠ i),
      (∀ t ∈ Ioo (0 : unitInterval) 1, q t ∉ range (lift (N.g j) (hgB j))) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, lift (N.g j) (hgB j) t ∉ range q) := by
    intro j hj
    exact internally_disjoint_replacement_retained_side (N.g i) (N.g j) β hiβ
      (N.injective_g j) (N.internally_disjoint_gg i j hj.symm)
      (N.internally_disjoint_gg j i hj) q (lift (N.g j) (hgB j)) hqi hqCoarse
      (hαdisj _ (hαg j hj)) hq0 hq1 (hgB j) (fun _ => rfl)
  have hbound : ∀ (a : Curve N.D), range a ⊆ discBd B →
      Disjoint (range a) (pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) →
      ∀ ha : ∀ t, a t ∈ B, range (lift a ha) ⊆ bd T := by
    intro a had hdis ha z hz
    obtain ⟨t, rfl⟩ := hz
    apply (hβbd _).mpr
    exact ⟨had (mem_range_self t), fun h => disjoint_left.mp hdis (mem_range_self t) h⟩
  have hfdis : ∀ j, Disjoint (range (N.f j))
      (pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
    intro j
    rw [image_pieceA_Ioo_unitInterval (N.g i) u v huv]
    apply disjoint_left.mpr
    rintro x hx ⟨t, ht, rfl⟩
    exact N.internally_disjoint_gf i j t ⟨hu.trans ht.1, ht.2.trans hv⟩ hx
  have hgdis : ∀ j, j ≠ i → Disjoint (range (N.g j))
      (pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
    intro j hj
    rw [image_pieceA_Ioo_unitInterval (N.g i) u v huv]
    apply disjoint_left.mpr
    rintro x hx ⟨t, ht, rfl⟩
    exact N.internally_disjoint_gg i j hj.symm t ⟨hu.trans ht.1, ht.2.trans hv⟩ hx
  refine ⟨f, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j; exact hfi ▸ hpi
    · rw [hfj j hj]; exact hliftInj _ _ (N.injective_f j)
  · intro j
    by_cases hj : j = i
    · subst j; exact hgi ▸ hqi
    · rw [hgj j hj]; exact hliftInj _ _ (N.injective_g j)
  · intro j
    by_cases hj : j = i
    · subst j; exact hfi ▸ hpbd
    · rw [hfj j hj]; exact hbound _ (hother j hj) (hfdis j) _
  · intro j
    by_cases hj : j = i
    · subst j; exact hgi ▸ hqbd
    · rw [hgj j hj]; exact hbound _ (hmates j) (hgdis j hj) _
  · intro j k hjk
    by_cases hj : j = i
    · subst j; rw [hfi, hfj k hjk.symm]; exact (hpf k hjk.symm).1
    · by_cases hk : k = i
      · subst k; rw [hfj j hj, hfi]; exact (hpf j hj).2
      · rw [hfj j hj, hfj k hk]
        exact hliftDisj _ _ _ _ (N.internally_disjoint_ff j k hjk)
  · intro j k hjk
    by_cases hj : j = i
    · subst j; rw [hgi, hgj k hjk.symm]; exact (hqg k hjk.symm).1
    · by_cases hk : k = i
      · subst k; rw [hgj j hj, hgi]; exact (hqg j hj).2
      · rw [hgj j hj, hgj k hk]
        exact hliftDisj _ _ _ _ (N.internally_disjoint_gg j k hjk)
  · intro j k
    by_cases hj : j = i
    · subst j
      by_cases hk : k = i
      · subst k; rw [hfi, hgi]; exact hpqd
      · rw [hfi, hgj k hk]; exact (hpg k).1
    · by_cases hk : k = i
      · subst k; rw [hfj j hj, hgi]; exact (hqf j hj).2
      · rw [hfj j hj, hgj k hk]
        exact hliftDisj _ _ _ _ (N.internally_disjoint_fg j k)
  · intro j k
    by_cases hj : j = i
    · subst j
      by_cases hk : k = i
      · subst k; rw [hgi, hfi]; exact hqpd
      · rw [hgi, hfj k hk]; exact (hqf k hk).1
    · by_cases hk : k = i
      · subst k; rw [hgj j hj, hfi]; exact (hpg j).2
      · rw [hgj j hj, hfj k hk]
        exact hliftDisj _ _ _ _ (N.internally_disjoint_gf j k)
  · intro j t
    by_cases hj : j = i
    · subst j; rw [hfi, hgi]; exact hpq t
    · rw [hfj j hj, hgj j hj]
      exact (hφB ⟨N.f j t, hfB j hj t⟩).trans
        ((N.pasting_eq j t).trans (hφB ⟨N.g j t, hgB j t⟩).symm)
  · intro j
    by_cases hj : j = i
    · subst j; rw [hfi, hgi]; exact ⟨hp0, hp1, hq0, hq1⟩
    · rw [hfj j hj, hgj j hj]
      exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  · intro j hj t
    rw [hfj j hj]
    exact ⟨_, rfl, rfl⟩
  · intro j hj t
    rw [hgj j hj]
    exact ⟨_, rfl, rfl⟩
  · rw [hfi]; exact hpr
  · rw [hgi]; exact hqr

end GraphMinor.GM07
