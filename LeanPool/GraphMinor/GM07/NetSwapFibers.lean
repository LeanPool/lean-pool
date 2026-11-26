/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.GM07.NetSwapSides
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Interior fibers after exchanging a net subarc

For VII (2.6), page 218, the open pasted subarc becomes interior
to the new disc. Its old two-point fibers are merged by the pasting.
Every other interior point comes from an old interior point. The
two lifts of the cutting line remain on the boundary, so they do
not create an interior identification.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The associated map of the exchanged disc makes no identification
at an interior point. The old two-point fibers on the pasted subarc
become single points, while both lifts of the cut remain boundary
points. This verifies the interior-fiber condition in the new net
of VII (2.6), page 218. -/
theorem Net.swap_map_interior_inj
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (α : A → T) (β : B → T) (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∀ z ∈ (bd T)ᶜ, ∀ w : T, φ z = φ w → z = w := by
  have hfopen : Disjoint F (N.f i '' Ioo u v) := by
    apply disjoint_left.mpr
    rintro x hxF ⟨t, ht, rfl⟩
    rcases hFbd.subset ⟨hxF, N.range_f_subset_bd i (mem_range_self t)⟩ with h | h
    · exact ht.1.ne' (N.injective_f i h)
    · exact ht.2.ne (N.injective_f i (mem_singleton_iff.mp h))
  have hFg : Disjoint F (range (N.g i)) := by
    apply disjoint_left.mpr
    intro x hxF hxg
    rcases hFbd.subset ⟨hxF, N.range_g_subset_bd i hxg⟩ with h | h
    · exact N.internally_disjoint_fg i i u ⟨hu, huv.trans hv⟩ (h ▸ hxg)
    · exact N.internally_disjoint_fg i i v ⟨hu.trans huv, hv⟩
        ((mem_singleton_iff.mp h) ▸ hxg)
  have hcutA : ∀ x : A, x.val ∈ F → α x ∈ bd T := by
    intro x hx
    apply (hαbd x).mpr
    refine ⟨hAd ▸ Or.inr hx, ?_⟩
    rw [image_pieceA_Ioo_unitInterval (N.f i) u v huv]
    exact fun h => disjoint_left.mp hfopen hx h
  have hcutB : ∀ y : B, y.val ∈ F → β y ∈ bd T := by
    intro y hy
    apply (hβbd y).mpr
    refine ⟨hBd ▸ Or.inr hy, ?_⟩
    intro h
    exact disjoint_left.mp hFg hy (image_subset_range _ _
      ((range_pieceA_unitInterval (N.g i) u v huv.le).subset (image_subset_range _ _ h)))
  have hOldA : ∀ x : A, x.val ∈ bd N.D → x.val ∈ discBd A := by
    intro x hx
    rcases hcover.symm ▸ hx with hf | hC
    · exact hAd ▸ Or.inl hf
    · have hxB : x.val ∈ B := discBd_subset B (hBd ▸ Or.inl hC)
      exact hAd ▸ Or.inr (hI ▸ ⟨x.property, hxB⟩)
  have hOldB : ∀ y : B, y.val ∈ bd N.D → y.val ∈ discBd B := by
    intro y hy
    rcases hcover.symm ▸ hy with hf | hC
    · have hyA : y.val ∈ A := discBd_subset A (hAd ▸ Or.inl hf)
      exact hBd ▸ Or.inr (hI ▸ ⟨hyA, y.property⟩)
    · exact hBd ▸ Or.inl hC
  have hpasted : ∀ x : A,
      x.val ∈ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1 →
      ∀ z, φ (α x) = φ z → α x = z := by
    intro x hx z heq
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨t, ht, hft, hgt⟩ := pieceA_common_parameter (N.f i) (N.g i) u v huv.le r
    have hxt : x.val = N.f i t := hrx.symm.trans hft
    have ht' : t ∈ Ioo u v := by
      obtain ⟨s, hs, hsx⟩ := (image_pieceA_Ioo_unitInterval (N.f i) u v huv).subset
        ⟨r, hr, hrx⟩
      have hst : s = t := N.injective_f i (hsx.trans hxt)
      exact hst ▸ hs
    have hfA : N.f i t ∈ A := hxt ▸ x.property
    have hgB : N.g i t ∈ B := by
      have hgbd : N.g i t ∈ bd N.D := N.range_g_subset_bd i (mem_range_self t)
      have hgnot : N.g i t ∉ range (pieceA (N.f i) u.val v.val) := by
        intro h
        obtain ⟨s, hs, hsx⟩ := (range_pieceA_unitInterval (N.f i) u v huv.le).subset h
        exact N.internally_disjoint_fg i i s ⟨hu.trans_le hs.1, hs.2.trans_lt hv⟩ ⟨t, hsx.symm⟩
      have hgC : N.g i t ∈ C := (hcover.symm ▸ hgbd).resolve_left hgnot
      exact discBd_subset B (hBd ▸ Or.inl hgC)
    have hxy : α x = β ⟨N.g i t, hgB⟩ :=
      (hcross x ⟨N.g i t, hgB⟩).mpr ⟨r, hrx.symm, hgt.symm⟩
    have hmem : ∀ y, N.φ x.val = N.φ y → y ∈ ({N.f i t, N.g i t} : Set N.D) := by
      intro y hy
      rw [← N.fiber_eq_pair_of_mem_Ioo i ⟨hu.trans ht'.1, ht'.2.trans hv⟩]
      exact hy.symm.trans (congrArg N.φ hxt)
    rcases hT.symm ▸ mem_univ z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy := hmem y.val ((hφA x).symm.trans (heq.trans (hφA y)))
      rcases hy with hy | hy
      · exact congrArg α (Subtype.ext (hxt.trans hy.symm))
      · have hyF : y.val ∈ F := hI ▸ ⟨y.property, (mem_singleton_iff.mp hy).symm ▸ hgB⟩
        exact (disjoint_left.mp hFg hyF ⟨t, (mem_singleton_iff.mp hy).symm⟩).elim
    · have hy := hmem y.val ((hφA x).symm.trans (heq.trans (hφB y)))
      rcases hy with hy | hy
      · have hyF : y.val ∈ F := hI ▸ ⟨hy.symm ▸ hfA, y.property⟩
        exact (disjoint_left.mp hfopen hyF ⟨t, ht', hy.symm⟩).elim
      · exact hxy.trans (congrArg β (Subtype.ext (mem_singleton_iff.mp hy).symm))
  have hleft : ∀ x : A, α x ∉ bd T → ∀ z, φ (α x) = φ z → α x = z := by
    intro x hx z heq
    by_cases hxbd : x.val ∈ bd N.D
    · have hxp : x.val ∈ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1 := by
        by_contra h
        exact hx ((hαbd x).mpr ⟨hOldA x hxbd, h⟩)
      exact hpasted x hxp z heq
    · rcases hT.symm ▸ mem_univ z with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hxy := N.interior_inj x.val hxbd y.val
          ((hφA x).symm.trans (heq.trans (hφA y)))
        exact congrArg α (Subtype.ext hxy)
      · have hxy := N.interior_inj x.val hxbd y.val
          ((hφA x).symm.trans (heq.trans (hφB y)))
        have hxF : x.val ∈ F := hI ▸ ⟨x.property, hxy.symm ▸ y.property⟩
        exact (hx (hcutA x hxF)).elim
  intro z hz w heq
  rcases hT.symm ▸ mem_univ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hleft x hz w heq
  · by_cases hybd : y.val ∈ bd N.D
    · have hyp : y.val ∈ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1 := by
        by_contra h
        exact hz ((hβbd y).mpr ⟨hOldB y hybd, h⟩)
      obtain ⟨r, hr, hry⟩ := hyp
      have hfA : pieceA (N.f i) u.val v.val r ∈ A :=
        discBd_subset A (hAd ▸ Or.inl (mem_range_self r))
      let x : A := ⟨pieceA (N.f i) u.val v.val r, hfA⟩
      have hxy : α x = β y := (hcross x y).mpr ⟨r, rfl, hry.symm⟩
      exact hxy.symm.trans (hleft x (hxy.symm ▸ hz) w ((congrArg φ hxy).trans heq))
    · rcases hT.symm ▸ mem_univ w with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · have hyx := N.interior_inj y.val hybd x.val
          ((hφB y).symm.trans (heq.trans (hφA x)))
        have hyF : y.val ∈ F := hI ▸ ⟨hyx.symm ▸ x.property, y.property⟩
        exact (hz (hcutB y hyF)).elim
      · have hyx := N.interior_inj y.val hybd x.val
          ((hφB y).symm.trans (heq.trans (hφB x)))
        exact congrArg β (Subtype.ext hyx)

/-- The two lifts of each cutting-line point occur at the same
parameter of the replacement pair. This includes cutting endpoints
which are vertices of the original graph. It supplies the new
identifications along the cut in VII (2.6), page 218. -/
theorem Net.swap_cutting_lifts_match
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F A B : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (α : A → T) (β : B → T)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val)
    (p q : Curve T) (hpq : ∀ t, φ (p t) = φ (q t))
    (hpRange : β '' {y : B | y.val ∈ F} ⊆ range p)
    (hqRange : range q ⊆ β '' {y : B | y.val ∈ range (N.g i)} ∪
      α '' {x : A | x.val ∈ F}) :
    ∀ (x : A) (y : B), x.val = y.val → x.val ∈ F →
      ∃ t, p t = β y ∧ q t = α x := by
  have hFg := (N.cutting_line_disjoint_other_sides i hu huv hv hFbd).2 i
  have hfu0 : pieceA (N.f i) u.val v.val 0 = N.f i u := by
    rw [pieceA_zero, extI_coe]
  have hfu1 : pieceA (N.f i) u.val v.val 1 = N.f i v := by
    rw [pieceA_one, extI_coe]
  have hgu0 : pieceA (N.g i) u.val v.val 0 = N.g i u := by
    rw [pieceA_zero, extI_coe]
  have hgu1 : pieceA (N.g i) u.val v.val 1 = N.g i v := by
    rw [pieceA_one, extI_coe]
  intro x y hxy hxF
  obtain ⟨t, hpt⟩ := hpRange ⟨y, (show y.val ∈ F from hxy ▸ hxF), rfl⟩
  refine ⟨t, hpt, ?_⟩
  have heq : N.φ x.val = φ (q t) :=
    (congrArg N.φ hxy).trans ((hφB y).symm.trans
      ((congrArg φ hpt).symm.trans (hpq t)))
  rcases hqRange (mem_range_self t) with ⟨z, hz, hzt⟩ | ⟨z, hz, hzt⟩
  · have hxz : N.φ x.val = N.φ z.val :=
      heq.trans ((congrArg φ hzt).symm.trans (hφB z))
    rcases N.fiber_of_cutting_line_point i hu huv hv hFbd hxF hxz with h | ⟨hxu, hzu⟩ | ⟨hxv, hzv⟩
    · exact (disjoint_left.mp hFg hxF (h ▸ hz)).elim
    · have hαβ : α x = β z := (hcross x z).mpr
        ⟨0, hxu.trans hfu0.symm, hzu.trans hgu0.symm⟩
      exact hzt.symm.trans hαβ.symm
    · have hαβ : α x = β z := (hcross x z).mpr
        ⟨1, hxv.trans hfu1.symm, hzv.trans hgu1.symm⟩
      exact hzt.symm.trans hαβ.symm
  · have hxz : N.φ x.val = N.φ z.val :=
      heq.trans ((congrArg φ hzt).symm.trans (hφA z))
    have hxz' := N.injOn_cutting_line i hu huv hv hFbd hxF hz hxz
    exact hzt.symm.trans (congrArg α (Subtype.ext hxz'.symm))

/-- On the replacement mate side, an old interior mate point has
only its retained image above its image in the surface. At either
cutting endpoint the attached lift has already been pasted to this
retained image. This is the boundary-fiber calculation for VII (2.6),
page 218. -/
theorem Net.swap_mate_fiber_unique
    {S T : Type*} [TopologicalSpace S]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F A B : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (α : A → T) (β : B → T)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1)
    (y : B) (hy : y.val = N.g i t) {z : T}
    (hz : z ∈ β '' {w : B | w.val ∈ range (N.g i)} ∪ α '' {w : A | w.val ∈ F})
    (heq : φ z = N.φ (N.f i t)) : z = β y := by
  have hFg := (N.cutting_line_disjoint_other_sides i hu huv hv hFbd).2 i
  have hmem : ∀ x, N.φ x = N.φ (N.f i t) →
      x ∈ ({N.f i t, N.g i t} : Set N.D) := by
    intro x hx
    rw [← N.fiber_eq_pair_of_mem_Ioo i ht]
    exact hx
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · rcases hmem x.val ((hφB x).symm.trans heq) with hxf | hxg
    · exact (N.internally_disjoint_fg i i t ht (hxf ▸ hx)).elim
    · exact congrArg β (Subtype.ext ((mem_singleton_iff.mp hxg).trans hy.symm))
  · rcases hmem x.val ((hφA x).symm.trans heq) with hxf | hxg
    · have hxtF : N.f i t ∈ F := hxf ▸ hx
      have htend := hFbd.subset ⟨hxtF, N.range_f_subset_bd i (mem_range_self t)⟩
      rcases htend with htu | htv
      · have htu' : t = u := N.injective_f i htu
        apply (hcross x y).mpr
        refine ⟨0, ?_, ?_⟩
        · rw [pieceA_zero, extI_coe]
          exact hxf.trans htu
        · rw [pieceA_zero, extI_coe]
          exact hy.trans (congrArg (N.g i) htu')
      · have htv' : t = v := N.injective_f i (mem_singleton_iff.mp htv)
        apply (hcross x y).mpr
        refine ⟨1, ?_, ?_⟩
        · rw [pieceA_one, extI_coe]
          exact hxf.trans (mem_singleton_iff.mp htv)
        · rw [pieceA_one, extI_coe]
          exact hy.trans (congrArg (N.g i) htv')
    · exact (disjoint_left.mp hFg hx ⟨t, (mem_singleton_iff.mp hxg).symm⟩).elim

/-- Every retained old pair point with interior parameter is still
paired at some common parameter of the new side maps. The two outer
side pieces can be reparametrized, but their paired points remain
paired. This is used to lift the old net's equivalence relation in
VII (2.6), page 218. -/
theorem Net.swap_retained_lifts_match
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F A B : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (α : A → T) (β : B → T)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val)
    (p q : Curve T) (hpq : ∀ s, φ (p s) = φ (q s))
    (hqRange : range q ⊆ β '' {y : B | y.val ∈ range (N.g i)} ∪
      α '' {x : A | x.val ∈ F})
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1)
    (x y : B) (hx : x.val = N.f i t) (hy : y.val = N.g i t)
    (hxp : β x ∈ range p) : ∃ s, p s = β x ∧ q s = β y := by
  obtain ⟨s, hps⟩ := hxp
  refine ⟨s, hps, ?_⟩
  apply N.swap_mate_fiber_unique i u v hu huv hv hFbd α β hcross φ hφA hφB ht y hy
    (hqRange (mem_range_self s))
  exact (hpq s).symm.trans ((congrArg φ hps).trans ((hφB x).trans (congrArg N.φ hx)))

end GraphMinor.GM07
