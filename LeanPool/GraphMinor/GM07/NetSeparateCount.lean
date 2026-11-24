/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.GM07.NetSwapCounts
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The exact count of a separating exchange

Paste the pair `f = g` across the two pieces of a cut along `F`, as in VII (2.6), page 218. The open
sides leave the boundary, which removes two preimages of each vertex on `e`. Each inner vertex of
`F`
gains two preimages. Each end of `F` splits into two boundary points, and each end of the pair is
merged. So the count is `Net.separating_contact_balance`. The printed proof leaves out the last two
effects. See the correction to the proof of (2.6) in `corrections/GM07.md`.
-/

public section
namespace GraphMinor.GM07
open Set Surface

variable {S : Type*} [TopologicalSpace S]

/-- The map `φ` is one to one on an open second side. -/
theorem Net.injOn_image_open_side_g (N : Net S) (i : Fin N.r) :
    InjOn N.φ (N.g i '' Ioo (0 : unitInterval) 1) := by
  rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ heq
  have hfib := N.fiber_eq_pair_of_mem_Ioo i hr
  have hmem : N.g i q ∈ N.φ ⁻¹' {N.φ (N.f i r)} := by
    change N.φ (N.g i q) = N.φ (N.f i r)
    rw [← heq, N.pasting_eq]
  rw [hfib] at hmem
  rcases hmem with h | h
  · exact absurd ⟨r, h.symm⟩ (N.internally_disjoint_gf i i q hq)
  · exact h.symm

private theorem Net.separated_boundary_contacts
    (N M : Net S) (i : Fin N.r) {A B F : Set N.D} {s t : N.D}
    (hsbd : s ∈ bd N.D) (htbd : t ∈ bd N.D)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (α : A → M.D) (β : B → M.D) (hT : range α ∪ range β = univ)
    (hαbd : ∀ x : A, α x ∈ bd M.D ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd M.D ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1)
    (hφA : ∀ x : A, M.φ (α x) = N.φ x.val) (hφB : ∀ y : B, M.φ (β y) = N.φ y.val)
    (V : Set S) :
    let X := bd N.D ∩ N.φ ⁻¹' V
    let fO := N.f i '' Ioo (0 : unitInterval) 1
    let gO := N.g i '' Ioo (0 : unitInterval) 1
    let Y := (F \ {s, t}) ∩ N.φ ⁻¹' V
    let P₀ := (A ∩ X) \ fO
    let Q₀ := (B ∩ X) \ gO
    let P := P₀ ∪ Y
    let Q := Q₀ ∪ Y
    let val₁ : A → N.D := Subtype.val
    let val₂ : B → N.D := Subtype.val
    (∀ x ∈ Y, x ∉ bd N.D) →
    bd M.D ∩ M.φ ⁻¹' V = α '' (val₁ ⁻¹' P) ∪ β '' (val₂ ⁻¹' Q) := by
  classical
  intro X fO gO Y P₀ Q₀ P Q val₁ val₂ hYbd
  have hfObd : ∀ x ∈ fO, x ∈ bd N.D := fun x ⟨r, _, h⟩ => h ▸ N.range_f_subset_bd i ⟨r, rfl⟩
  have hgObd : ∀ x ∈ gO, x ∈ bd N.D := fun x ⟨r, _, h⟩ => h ▸ N.range_g_subset_bd i ⟨r, rfl⟩
  ext w
  constructor
  · rintro ⟨hw, hwV⟩
    rcases hT.symm ▸ mem_univ w with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · refine Or.inl ⟨x, ?_, rfl⟩
      obtain ⟨hx, hxf⟩ := (hαbd x).mp hw
      have hxV : N.φ x.val ∈ V := hφA x ▸ hwV
      rw [hAd] at hx
      rcases hx with hx | hx
      · exact Or.inl ⟨⟨x.2, hx.2, hxV⟩, hxf⟩
      · by_cases he : x.val ∈ ({s, t} : Set N.D)
        · have hb : x.val ∈ bd N.D := by
            rcases he with h | h
            · exact h ▸ hsbd
            · exact (mem_singleton_iff.mp h) ▸ htbd
          exact Or.inl ⟨⟨x.2, hb, hxV⟩, hxf⟩
        · exact Or.inr ⟨⟨hx, he⟩, hxV⟩
    · refine Or.inr ⟨y, ?_, rfl⟩
      obtain ⟨hy, hyg⟩ := (hβbd y).mp hw
      have hyV : N.φ y.val ∈ V := hφB y ▸ hwV
      rw [hBd] at hy
      rcases hy with hy | hy
      · exact Or.inl ⟨⟨y.2, hy.2, hyV⟩, hyg⟩
      · by_cases he : y.val ∈ ({s, t} : Set N.D)
        · have hb : y.val ∈ bd N.D := by
            rcases he with h | h
            · exact h ▸ hsbd
            · exact (mem_singleton_iff.mp h) ▸ htbd
          exact Or.inl ⟨⟨y.2, hb, hyV⟩, hyg⟩
        · exact Or.inr ⟨⟨hy, he⟩, hyV⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · rcases hx with hx | hx
      · refine ⟨(hαbd x).mpr ⟨hAd ▸ Or.inl ⟨x.2, hx.1.2.1⟩, hx.2⟩, ?_⟩
        change M.φ (α x) ∈ V
        rw [hφA]
        exact hx.1.2.2
      · refine ⟨(hαbd x).mpr ⟨hAd ▸ Or.inr hx.1.1, fun h => hYbd _ hx (hfObd _ h)⟩, ?_⟩
        change M.φ (α x) ∈ V
        rw [hφA]
        exact hx.2
    · rcases hy with hy | hy
      · refine ⟨(hβbd y).mpr ⟨hBd ▸ Or.inl ⟨y.2, hy.1.2.1⟩, hy.2⟩, ?_⟩
        change M.φ (β y) ∈ V
        rw [hφB]
        exact hy.1.2.2
      · refine ⟨(hβbd y).mpr ⟨hBd ▸ Or.inr hy.1.1, fun h => hYbd _ hy (hgObd _ h)⟩, ?_⟩
        change M.φ (β y) ∈ V
        rw [hφB]
        exact hy.2

private theorem Net.separated_boundary_overlap
    (N M : Net S) (i : Fin N.r) {A B F : Set N.D} {s t : N.D}
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (α : A → M.D) (β : B → M.D)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = N.f i r ∧ y.val = N.g i r)
    (V : Set S) :
    let X := bd N.D ∩ N.φ ⁻¹' V
    let fO := N.f i '' Ioo (0 : unitInterval) 1
    let gO := N.g i '' Ioo (0 : unitInterval) 1
    let Y := (F \ {s, t}) ∩ N.φ ⁻¹' V
    let P₀ := (A ∩ X) \ fO
    let Q₀ := (B ∩ X) \ gO
    let P := P₀ ∪ Y
    let Q := Q₀ ∪ Y
    let val₁ : A → N.D := Subtype.val
    let val₂ : B → N.D := Subtype.val
    (∀ x ∈ Y, x ∉ bd N.D) →
    let O := ({N.f i 0, N.f i 1} : Set N.D) ∩ N.φ ⁻¹' V
    α '' (val₁ ⁻¹' P) ∩ β '' (val₂ ⁻¹' Q) = α '' (val₁ ⁻¹' O) := by
  classical
  intro X fO gO Y P₀ Q₀ P Q val₁ val₂ hYbd O
  have hsub : ∀ x ∈ discBd A, x ∈ A := fun _ hx => discBd_subset A hx
  have hsubB : ∀ x ∈ discBd B, x ∈ B := fun _ hx => discBd_subset B hx
  have hfinj := N.injective_f i
  have hginj := N.injective_g i
  have hnotO : ∀ r : unitInterval, (r = 0 ∨ r = 1) → N.f i r ∉ fO ∧ N.g i r ∉ gO := by
    intro r hr
    constructor
    · rintro ⟨q, hq, h⟩
      obtain rfl := hfinj h
      rcases hr with rfl | rfl
      · exact lt_irrefl _ hq.1
      · exact lt_irrefl _ hq.2
    · rintro ⟨q, hq, h⟩
      obtain rfl := hginj h
      rcases hr with rfl | rfl
      · exact lt_irrefl _ hq.1
      · exact lt_irrefl _ hq.2
  have hend : ∀ r : unitInterval, (r = 0 ∨ r = 1) → N.φ (N.f i r) ∈ V →
      N.f i r ∈ P₀ ∧ N.g i r ∈ Q₀ := by
    intro r hr hrV
    refine ⟨⟨⟨hsub _ (hfA ⟨r, rfl⟩), N.range_f_subset_bd i ⟨r, rfl⟩, hrV⟩, (hnotO r hr).1⟩,
      ⟨⟨hsubB _ (hgB ⟨r, rfl⟩), N.range_g_subset_bd i ⟨r, rfl⟩, ?_⟩, (hnotO r hr).2⟩⟩
    change N.φ (N.g i r) ∈ V
    rw [← N.pasting_eq]
    exact hrV
  ext w
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    obtain ⟨r, hr₁, hr₂⟩ := (hcross x y).mp hxy.symm
    refine ⟨x, ?_, rfl⟩
    have hxV : N.φ x.val ∈ V := by
      rcases hx with hx | hx
      · exact hx.1.2.2
      · exact hx.2
    have hxr : r = 0 ∨ r = 1 := by
      by_contra hn
      push Not at hn
      have hro : r ∈ Ioo (0 : unitInterval) 1 := Net.mem_Ioo_of_ne hn.1 hn.2
      rcases hx with hx | hx
      · exact hx.2 ⟨r, hro, hr₁.symm⟩
      · refine hYbd _ hx ?_
        change x.val ∈ bd N.D
        rw [hr₁]
        exact N.range_f_subset_bd i ⟨r, rfl⟩
    refine ⟨?_, hxV⟩
    rcases hxr with rfl | rfl
    · exact Or.inl hr₁
    · exact Or.inr hr₁
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxe, hxV⟩ := hx
    have key : ∃ r : unitInterval, (r = 0 ∨ r = 1) ∧ x.val = N.f i r := by
      rcases hxe with h | h
      · exact ⟨0, Or.inl rfl, h⟩
      · exact ⟨1, Or.inr rfl, h⟩
    obtain ⟨r, hr, hxr⟩ := key
    have hrV : N.φ (N.f i r) ∈ V := hxr ▸ hxV
    obtain ⟨h₁, h₂⟩ := hend r hr hrV
    refine ⟨⟨x, Or.inl (hxr ▸ h₁ : x.val ∈ P₀), rfl⟩,
      ⟨⟨N.g i r, hsubB _ (hgB ⟨r, rfl⟩)⟩, Or.inl h₂, ?_⟩⟩
    exact ((hcross x ⟨N.g i r, _⟩).mpr ⟨r, hxr, rfl⟩).symm

/-- See the module docstring. The sets `A` and `B` are the cut pieces, and `α`, `β` the maps from
them to the new disc. Terms such as `({N.φ s} ∩ V).ncard` are 1 when the point is in `V`. -/
theorem Net.separating_contact_balance
    (N M : Net S) (i : Fin N.r) {A B F : Set N.D} {s t : N.D} (hst : s ≠ t)
    (hFbd : F ∩ bd N.D = {s, t})
    (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (α : A → M.D) (β : B → M.D) (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = N.f i r ∧ y.val = N.g i r)
    (hαbd : ∀ x : A, α x ∈ bd M.D ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd M.D ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1)
    (hφA : ∀ x : A, M.φ (α x) = N.φ x.val) (hφB : ∀ y : B, M.φ (β y) = N.φ y.val)
    (V : Set S) (hV : V.Finite) :
    (bd M.D ∩ M.φ ⁻¹' V).ncard + 2 * (N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) ∩ V).ncard +
        ({N.φ (N.f i 0)} ∩ V).ncard + ({N.φ (N.f i 1)} ∩ V).ncard =
      (bd N.D ∩ N.φ ⁻¹' V).ncard + 2 * (N.φ '' (F \ {s, t}) ∩ V).ncard +
        ({N.φ s} ∩ V).ncard + ({N.φ t} ∩ V).ncard := by
  classical
  have hsub : ∀ x ∈ discBd A, x ∈ A := fun x hx => discBd_subset A hx
  have hsubB : ∀ x ∈ discBd B, x ∈ B := fun x hx => discBd_subset B hx
  set X := bd N.D ∩ N.φ ⁻¹' V with hX
  set fO := N.f i '' Ioo (0 : unitInterval) 1 with hfO
  set gO := N.g i '' Ioo (0 : unitInterval) 1 with hgO
  set Y := (F \ {s, t}) ∩ N.φ ⁻¹' V with hY
  have hXfin : X.Finite := (N.finite_preimage_of_finite hV).subset inter_subset_right
  have hYfin : Y.Finite := (N.finite_preimage_of_finite hV).subset inter_subset_right
  have hFA : F ⊆ A := fun x hx => (hI.symm ▸ hx : x ∈ A ∩ B).1
  have hFB : F ⊆ B := fun x hx => (hI.symm ▸ hx : x ∈ A ∩ B).2
  have hsF : s ∈ F := (hFbd.symm.subset (Or.inl rfl)).1
  have htF : t ∈ F := (hFbd.symm.subset (Or.inr rfl)).1
  have hsbd : s ∈ bd N.D := (hFbd.symm.subset (Or.inl rfl)).2
  have htbd : t ∈ bd N.D := (hFbd.symm.subset (Or.inr rfl)).2
  have hYbd : ∀ x ∈ Y, x ∉ bd N.D := fun x hx h => hx.1.2 (hFbd.subset ⟨hx.1.1, h⟩)
  have hfObd : ∀ x ∈ fO, x ∈ bd N.D := fun x ⟨r, _, h⟩ => h ▸ N.range_f_subset_bd i ⟨r, rfl⟩
  have hgObd : ∀ x ∈ gO, x ∈ bd N.D := fun x ⟨r, _, h⟩ => h ▸ N.range_g_subset_bd i ⟨r, rfl⟩
  have hfOF : ∀ x ∈ fO, x ∉ F := by
    rintro _ ⟨r, hr, rfl⟩ h
    rcases hFbd.subset ⟨h, hfObd _ ⟨r, hr, rfl⟩⟩ with h' | h'
    · exact (hs i r hr).1 h'
    · exact (ht i r hr).1 h'
  have hgOF : ∀ x ∈ gO, x ∉ F := by
    rintro _ ⟨r, hr, rfl⟩ h
    rcases hFbd.subset ⟨h, hgObd _ ⟨r, hr, rfl⟩⟩ with h' | h'
    · exact (hs i r hr).2 h'
    · exact (ht i r hr).2 h'
  have hfOA : ∀ x ∈ fO, x ∈ A := fun x ⟨r, _, h⟩ => hsub _ (hfA ⟨r, h⟩)
  have hgOB : ∀ x ∈ gO, x ∈ B := fun x ⟨r, _, h⟩ => hsubB _ (hgB ⟨r, h⟩)
  set P₀ := (A ∩ X) \ fO with hP₀
  set Q₀ := (B ∩ X) \ gO with hQ₀
  set P := P₀ ∪ Y with hP
  set Q := Q₀ ∪ Y with hQ
  have hPA : P ⊆ A := by
    rintro x (hx | hx)
    · exact hx.1.1
    · exact hFA hx.1.1
  have hQB : Q ⊆ B := by
    rintro x (hx | hx)
    · exact hx.1.1
    · exact hFB hx.1.1
  have hP₀fin : P₀.Finite := hXfin.subset fun x hx => hx.1.2
  have hQ₀fin : Q₀.Finite := hXfin.subset fun x hx => hx.1.2
  let val₁ : A → N.D := Subtype.val
  let val₂ : B → N.D := Subtype.val
  have hPimg : val₁ '' (val₁ ⁻¹' P) = P := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hPA]
  have hQimg : val₂ '' (val₂ ⁻¹' Q) = Q := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hQB]
  have hPcard : (α '' (val₁ ⁻¹' P)).ncard = P.ncard := by
    rw [ncard_image_of_injective _ hiα, ← hPimg,
      ncard_image_of_injective _ Subtype.val_injective]
    rw [hPimg]
  have hQcard : (β '' (val₂ ⁻¹' Q)).ncard = Q.ncard := by
    rw [ncard_image_of_injective _ hiβ, ← hQimg,
      ncard_image_of_injective _ Subtype.val_injective]
    rw [hQimg]
  have hX' : bd M.D ∩ M.φ ⁻¹' V = α '' (val₁ ⁻¹' P) ∪ β '' (val₂ ⁻¹' Q) :=
    N.separated_boundary_contacts M i hsbd htbd hAd hBd α β hT hαbd hβbd hφA hφB V hYbd
  -- The two parts of the new boundary meet at the ends of the pair in `V`.
  set O := ({N.f i 0, N.f i 1} : Set N.D) ∩ N.φ ⁻¹' V with hO
  have hOA : O ⊆ A := by
    rintro _ ⟨rfl | h, -⟩
    · exact hsub _ (hfA ⟨0, rfl⟩)
    · exact (mem_singleton_iff.mp h) ▸ hsub _ (hfA ⟨1, rfl⟩)
  have hcap : α '' (val₁ ⁻¹' P) ∩ β '' (val₂ ⁻¹' Q) = α '' (val₁ ⁻¹' O) :=
    N.separated_boundary_overlap M i hfA hgB α β hcross V hYbd
  have hOimg : val₁ '' (val₁ ⁻¹' O) = O := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hOA]
  have hOcard : (α '' (val₁ ⁻¹' O)).ncard = O.ncard := by
    rw [ncard_image_of_injective _ hiα, ← hOimg,
      ncard_image_of_injective _ Subtype.val_injective]
    rw [hOimg]
  have hOfin : O.Finite := (N.finite_preimage_of_finite hV).subset inter_subset_right
  -- A singleton term for a point of `N.D`.
  have hind : ∀ z : N.D, ({z} ∩ N.φ ⁻¹' V).ncard = ({N.φ z} ∩ V).ncard := by
    intro z
    by_cases hz : N.φ z ∈ V
    · rw [inter_eq_left.mpr (singleton_subset_iff.mpr hz),
        inter_eq_left.mpr (singleton_subset_iff.mpr (show z ∈ N.φ ⁻¹' V from hz)),
        ncard_singleton, ncard_singleton]
    · have h₁ : ({N.φ z} ∩ V) = ∅ := by
        ext w
        simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        rintro rfl
        exact hz
      have h₂ : ({z} ∩ N.φ ⁻¹' V) = ∅ := by
        ext w
        simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        rintro rfl
        exact hz
      rw [h₁, h₂, ncard_empty, ncard_empty]
  have hpair : ∀ a b : N.D, a ≠ b → (({a, b} : Set N.D) ∩ N.φ ⁻¹' V).ncard =
      ({N.φ a} ∩ V).ncard + ({N.φ b} ∩ V).ncard := by
    intro a b hab
    rw [← hind, ← hind, show ({a, b} : Set N.D) = {a} ∪ {b} from rfl, union_inter_distrib_right]
    refine ncard_union_eq ?_ ((finite_singleton _).inter_of_left _)
      ((finite_singleton _).inter_of_left _)
    refine disjoint_left.mpr ?_
    rintro x ⟨h₁, -⟩ ⟨h₂, -⟩
    exact hab ((mem_singleton_iff.mp h₁).symm.trans (mem_singleton_iff.mp h₂))
  have hne01 : (0 : unitInterval) ≠ 1 := zero_ne_one
  have hOsum : O.ncard = ({N.φ (N.f i 0)} ∩ V).ncard + ({N.φ (N.f i 1)} ∩ V).ncard :=
    hpair _ _ (fun h => hne01 (N.injective_f i h))
  have hEsum := hpair s t hst
  -- The old boundary count.
  have hP₀Y : Disjoint P₀ Y := disjoint_left.mpr fun x hx hy => hYbd x hy hx.1.2.1
  have hQ₀Y : Disjoint Q₀ Y := disjoint_left.mpr fun x hx hy => hYbd x hy hx.1.2.1
  have hPc : P.ncard = P₀.ncard + Y.ncard := ncard_union_eq hP₀Y hP₀fin hYfin
  have hQc : Q.ncard = Q₀.ncard + Y.ncard := ncard_union_eq hQ₀Y hQ₀fin hYfin
  have hunion : P₀ ∪ Q₀ = X \ (fO ∪ gO) := by
    ext x
    constructor
    · rintro (hx | hx)
      · refine ⟨hx.1.2, ?_⟩
        rintro (h | h)
        · exact hx.2 h
        · refine hgOF x h (hI ▸ ⟨hx.1.1, hgOB x h⟩)
      · refine ⟨hx.1.2, ?_⟩
        rintro (h | h)
        · exact hfOF x h (hI ▸ ⟨hfOA x h, hx.1.1⟩)
        · exact hx.2 h
    · rintro ⟨hx, hn⟩
      rcases hAB.symm ▸ mem_univ x with h | h
      · exact Or.inl ⟨⟨h, hx⟩, fun h' => hn (Or.inl h')⟩
      · exact Or.inr ⟨⟨h, hx⟩, fun h' => hn (Or.inr h')⟩
  have hinter : P₀ ∩ Q₀ = ({s, t} : Set N.D) ∩ N.φ ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      have : x ∈ F := hI ▸ ⟨hx.1.1, hy.1.1⟩
      exact ⟨hFbd.subset ⟨this, hx.1.2.1⟩, hx.1.2.2⟩
    · rintro ⟨hxe, hxV⟩
      have hxF : x ∈ F := by
        rcases hxe with h | h
        · exact h ▸ hsF
        · exact (mem_singleton_iff.mp h) ▸ htF
      have hxb : x ∈ bd N.D := by
        rcases hxe with h | h
        · exact h ▸ hsbd
        · exact (mem_singleton_iff.mp h) ▸ htbd
      exact ⟨⟨⟨hFA hxF, hxb, hxV⟩, fun h => hfOF x h hxF⟩,
        ⟨⟨hFB hxF, hxb, hxV⟩, fun h => hgOF x h hxF⟩⟩
  have hcount₁ := ncard_union_add_ncard_inter P₀ Q₀ hP₀fin hQ₀fin
  rw [hunion, hinter] at hcount₁
  -- The contacts on the two open sides.
  have hfgO : Disjoint fO gO := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨r, hr, rfl⟩ ⟨q, -, h⟩
    exact N.internally_disjoint_fg i i r hr ⟨q, h⟩
  have himg : N.φ '' gO = N.φ '' fO := by
    ext z
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨_, ⟨r, hr, rfl⟩, N.pasting_eq i r⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨_, ⟨r, hr, rfl⟩, (N.pasting_eq i r).symm⟩
  have hside : ∀ W : Set N.D, W ⊆ bd N.D → InjOn N.φ W →
      (X ∩ W).ncard = (N.φ '' W ∩ V).ncard := by
    intro W hW hinj
    have : N.φ '' W ∩ V = N.φ '' (X ∩ W) := by
      ext z
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, ⟨⟨hW hx, hz⟩, hx⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxW⟩, rfl⟩
        exact ⟨⟨x, hxW, rfl⟩, hx.2⟩
    rw [this, (hinj.mono inter_subset_right).ncard_image]
  have hcf := hside fO hfObd (N.injOn_image_open_side i)
  have hcg := hside gO hgObd (N.injOn_image_open_side_g i)
  rw [himg] at hcg
  have hsplit : (X ∩ fO).ncard + (X ∩ gO).ncard + (X \ (fO ∪ gO)).ncard = X.ncard := by
    have h₁ : X ∩ (fO ∪ gO) = (X ∩ fO) ∪ (X ∩ gO) := inter_union_distrib_left _ _ _
    have h₂ := ncard_inter_add_ncard_sdiff_eq_ncard X (fO ∪ gO) hXfin
    rw [h₁, ncard_union_eq (hfgO.mono inter_subset_right inter_subset_right)
      (hXfin.subset inter_subset_left) (hXfin.subset inter_subset_left)] at h₂
    exact h₂
  have hYc : Y.ncard = (N.φ '' (F \ {s, t}) ∩ V).ncard := by
    have : N.φ '' (F \ {s, t}) ∩ V = N.φ '' Y := by
      ext z
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, ⟨hx, hz⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hz⟩
    rw [this, ((N.injOn_line_interior hFbd).mono inter_subset_left).ncard_image]
  have hPf : (α '' (val₁ ⁻¹' P)).Finite :=
    ((hP₀fin.union hYfin).preimage Subtype.val_injective.injOn).image α
  have hQf : (β '' (val₂ ⁻¹' Q)).Finite :=
    ((hQ₀fin.union hYfin).preimage Subtype.val_injective.injOn).image β
  have hX'c := ncard_union_add_ncard_inter (α '' (val₁ ⁻¹' P)) (β '' (val₂ ⁻¹' Q)) hPf hQf
  rw [← hX', hcap, hOcard, hPcard, hQcard] at hX'c
  change _ + 2 * (N.φ '' fO ∩ V).ncard + _ + _ = X.ncard + 2 * _ + _ + _
  rw [← hYc]
  omega

end GraphMinor.GM07
