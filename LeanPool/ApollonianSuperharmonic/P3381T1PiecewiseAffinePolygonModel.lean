/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3381T1AffineTriangleMap
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangulationBoundary
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Set.Card

-- [TABLET NODE: P3381T1PiecewiseAffinePolygonModel]

/-!
# P3381T1PiecewiseAffinePolygonModel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PiecewiseAffineProof

private theorem hull_formula :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (u : Fin (n + 3) → Real × Real),
            ∀ (v : Fin (n + 3) → Real × Real), ∀ (A : Fin t.count → (Real × Real) ≃ₜ (Real ×
            Real)), (∀ k, ∀ (w : Fin 3 → Real), (∑ i, w i) = 1 → A k (∑ i, w i • u (t.face k i))
            = ∑ i, w i •
        v (t.face k i)) → ∀ (S : Set (Fin (n + 3))), ∀ (x : Real × Real), x ∈ convexHull Real (u
        '' S) → ∃ y ∈ convexHull Real (v '' S), ∀ k, S ⊆ Set.range (t.face k) → A k x = y := by
  classical
  intro n p X K t u v A hA S x hx
  obtain ⟨ι, inst, w, z, hw₀, hw₁, hz, hx⟩ :=
    mem_convexHull_iff_exists_fintype.mp hx
  let _ := inst
  choose j hj hz using hz
  refine ⟨∑ r, w r • v (j r), ?_, ?_⟩
  · exact mem_convexHull_of_exists_fintype w (fun r => v (j r)) hw₀ hw₁
      (fun r => Set.mem_image_of_mem v (hj r)) rfl
  · intro k hk
    have hjk : ∀ r, ∃ i, t.face k i = j r := fun r => hk (hj r)
    choose c hc using hjk
    let W : Fin 3 → Real := fun i => ∑ r, if c r = i then w r else 0
    have hW : (∑ i, W i) = 1 := by
      simpa [W, Finset.sum_comm] using hw₁
    have sum_eq : ∀ f : Fin (n + 3) → Real × Real,
        (∑ i, W i • f (t.face k i)) = ∑ r, w r • f (j r) := by
      intro f
      simp [W, Finset.sum_smul, Finset.sum_comm, ite_smul, hc]
    rw [← hx]
    simp_rw [← hz]
    calc
      A k (∑ r, w r • u (j r)) = A k (∑ i, W i • u (t.face k i)) :=
        congrArg (A k) (sum_eq u).symm
      _ = ∑ i, W i • v (t.face k i) := hA k W hW
      _ = ∑ r, w r • v (j r) := sum_eq v

private theorem paste :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (a : Fin t.count → ℝ × ℝ ≃ₜ ℝ ×
        ℝ), (∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ i : Fin (3 : ℕ), w i = (1 : ℝ) → (a
        k : ℝ × ℝ → ℝ × ℝ) (∑ i : Fin (3 : ℕ), w i • p.vertex (t.face k i)) = ∑ i : Fin (3 : ℕ),
        w i • t.target (t.face k i)) → ((∀ (u : Fin (n + 3) → Real × Real), ∀ (v : Fin (n + 3) →
        Real × Real), ∀ (A : Fin t.count → (Real × Real) ≃ₜ (Real × Real)), (∀ k, ∀ (w : Fin 3 →
        Real), (∑ i, w i) = 1 → A k (∑ i, w i • u (t.face k i)) = ∑ i, w i • v (t.face k i)) → ∀
            (S : Set (Fin (n + 3))), ∀ (x : Real × Real), x ∈ convexHull Real (u '' S) → ∃ y ∈
        convexHull Real (v '' S), ∀ k, S ⊆ Set.range (t.face k) → A k x = y) → ((∀ k, ∀ (w : Fin
        3 → Real), (∑ i, w i) = 1 → (a k).symm (∑ i, w i • t.target (t.face k i)) = ∑ i, w i •
        p.vertex (t.face k i)) → (∃ h : X ≃ₜ K, ∀ k, ∀ (x : X), (x : Real × Real) ∈ convexHull
        Real (Set.range (p.vertex ∘ t.face k)) → (h x : Real × Real) = a k x))) := by
  classical
  intro n p X K t a ha hull_formula hai
  let D := fun k => convexHull Real (Set.range (p.vertex ∘ t.face k))
  let E := fun k => convexHull Real (Set.range (t.target ∘ t.face k))
  have map_hull : ∀ (u v : Fin (n + 3) → Real × Real)
      (A : Fin t.count → (Real × Real) ≃ₜ (Real × Real)),
      (∀ k (w : Fin 3 → Real), (∑ i, w i) = 1 →
        A k (∑ i, w i • u (t.face k i)) = ∑ i, w i • v (t.face k i)) →
      ∀ k x, x ∈ convexHull Real (Set.range (u ∘ t.face k)) →
        A k x ∈ convexHull Real (Set.range (v ∘ t.face k)) := by
    intro u v A hA k x hx
    rw [Set.range_comp] at hx ⊢
    obtain ⟨y, hy, heq⟩ := hull_formula u v A hA (Set.range (t.face k)) x hx
    rwa [heq k (Set.Subset.refl _)]
  have forward : ∀ k x, x ∈ D k → a k x ∈ E k :=
    map_hull p.vertex t.target a ha
  have backward : ∀ k y, y ∈ E k → (a k).symm y ∈ D k :=
    map_hull t.target p.vertex (fun k => (a k).symm) hai
  have agree : ∀ k l x, x ∈ D k → x ∈ D l → a k x = a l x := by
    intro k l x hxk hxl
    have hx : x ∈ convexHull Real
        (p.vertex '' (Set.range (t.face k) ∩ Set.range (t.face l))) := by
      rw [← t.source_intersection]
      exact ⟨hxk, hxl⟩
    obtain ⟨y, _, heq⟩ := hull_formula p.vertex t.target a ha _ x hx
    exact (heq k Set.inter_subset_left).trans (heq l Set.inter_subset_right).symm
  have agree_inv : ∀ k l y, y ∈ E k → y ∈ E l →
      (a k).symm y = (a l).symm y := by
    intro k l y hyk hyl
    have hy : y ∈ convexHull Real
        (t.target '' (Set.range (t.face k) ∩ Set.range (t.face l))) := by
      rw [← t.target_intersection]
      exact ⟨hyk, hyl⟩
    obtain ⟨x, _, heq⟩ := hull_formula t.target p.vertex
      (fun k => (a k).symm) hai _ y hy
    exact (heq k Set.inter_subset_left).trans (heq l Set.inter_subset_right).symm
  have pick_source : ∀ x : X, ∃ k, (x : Real × Real) ∈ D k := by
    intro x
    exact Set.mem_iUnion.mp (t.source_cover ▸ x.property)
  have pick_target : ∀ y : K, ∃ k, (y : Real × Real) ∈ E k := by
    intro y
    exact Set.mem_iUnion.mp (t.target_cover ▸ y.property)
  choose ks hks using pick_source
  choose kt hkt using pick_target
  let f : X → K := fun x => ⟨a (ks x) x, by
    rw [t.target_cover]
    exact Set.mem_iUnion.mpr ⟨ks x, forward (ks x) x (hks x)⟩⟩
  let g : K → X := fun y => ⟨(a (kt y)).symm y, by
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨kt y, backward (kt y) y (hkt y)⟩⟩
  have hf : ∀ k (x : X), (x : Real × Real) ∈ D k →
      (f x : Real × Real) = a k x := by
    intro k x hx
    exact agree (ks x) k x (hks x) hx
  have hg : ∀ k (y : K), (y : Real × Real) ∈ E k →
      (g y : Real × Real) = (a k).symm y := by
    intro k y hy
    exact agree_inv (kt y) k y (hkt y) hy
  have hgf : ∀ x, g (f x) = x := by
    intro x
    apply Subtype.ext
    rw [hg (ks x) (f x) (forward (ks x) x (hks x))]
    exact (a (ks x)).symm_apply_apply x
  have hfg : ∀ y, f (g y) = y := by
    intro y
    apply Subtype.ext
    rw [hf (kt y) (g y) (backward (kt y) y (hkt y))]
    exact (a (kt y)).apply_symm_apply y
  -- Closed preimages are finite unions of the local closed preimages.
  have continuous_glue : ∀ (Y : Set (Real × Real))
      (C : Fin t.count → Set (Real × Real))
      (A : Fin t.count → (Real × Real) ≃ₜ (Real × Real)),
      Y = ⋃ k, C k → (∀ k, IsClosed (C k)) →
      ∀ F : Y → Real × Real,
        (∀ k (x : Y), (x : Real × Real) ∈ C k → F x = A k x) →
        Continuous F := by
    intro Y C A hcover hclosed F hF
    apply continuous_iff_isClosed.mpr
    intro B hB
    have heq : F ⁻¹' B = ⋃ k,
        (Subtype.val ⁻¹' C k) ∩ ((A k) ∘ Subtype.val) ⁻¹' B := by
      ext x
      constructor
      · intro hx
        have hxY : (x : Real × Real) ∈ ⋃ k, C k :=
          (Set.ext_iff.mp hcover x).mp x.property
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxY
        refine Set.mem_iUnion.mpr ⟨k, hk, ?_⟩
        change A k x ∈ B
        change F x ∈ B at hx
        rwa [← hF k x hk]
      · intro hx
        obtain ⟨k, hk, hx⟩ := Set.mem_iUnion.mp hx
        change A k x ∈ B at hx
        change F x ∈ B
        rwa [hF k x hk]
    rw [heq]
    exact isClosed_iUnion_of_finite fun k =>
      ((hclosed k).preimage continuous_subtype_val).inter
        (hB.preimage ((A k).continuous.comp continuous_subtype_val))
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_glue X D a t.source_cover
      (fun k => ((Set.finite_range (p.vertex ∘ t.face k)).isCompact_convexHull
        Real).isClosed) (fun x => (f x : Real × Real)) hf
  have hgcont : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_glue K E (fun k => (a k).symm) t.target_cover
      (fun k => ((Set.finite_range (t.target ∘ t.face k)).isCompact_convexHull
        Real).isClosed) (fun y => (g y : Real × Real)) hg
  exact ⟨{ toFun := f
           invFun := g
           left_inv := hgf
           right_inv := hfg
           continuous_toFun := hfcont
           continuous_invFun := hgcont }, hf⟩

private theorem edge_used :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ i : Fin (n + 3), ∃ k, i ∈
        Set.range (t.face k) ∧ i + 1 ∈ Set.range (t.face k) := by
  classical
  intro n p X K t i
  have hne : i ≠ i + 1 := by
    intro hi
    have hzero : (0 : Fin (n + 3)) = 1 :=
      add_left_cancel (show i + 0 = i + 1 by simp at hi)
    exact Fin.zero_ne_one hzero
  have he := t.edge_count i (i + 1) hne
  simp only [true_or, ite_true] at he
  have hn : 0 < Set.ncard {k : Fin t.count |
      i ∈ Set.range (t.face k) ∧ i + 1 ∈ Set.range (t.face k)} := by
    rw [he]
    exact Nat.zero_lt_one
  exact (Set.ncard_pos (Set.toFinite _)).mp hn

private theorem edge_transport :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (a : Fin t.count → ℝ × ℝ ≃ₜ ℝ ×
        ℝ), (∀ (k : Fin t.count), ∀ (w : Fin (3 : ℕ) → ℝ), ∑ i : Fin (3 : ℕ), w i = (1 : ℝ) → (a
        k : ℝ × ℝ → ℝ × ℝ) (∑ i : Fin (3 : ℕ), w i • p.vertex (t.face k i)) = ∑ i : Fin (3 : ℕ),
        w i • t.target (t.face k i)) → ((∀ (u : Fin (n + 3) → Real × Real), ∀ (v : Fin (n + 3) →
        Real × Real), ∀ (A : Fin t.count → (Real × Real) ≃ₜ (Real × Real)), (∀ k, ∀ (w : Fin 3 →
        Real), (∑ i, w i) = 1 → A k (∑ i, w i • u (t.face k i)) = ∑ i, w i • v (t.face k i)) → ∀
            (S : Set (Fin (n + 3))), ∀ (x : Real × Real), x ∈ convexHull Real (u '' S) → ∃ y ∈
        convexHull Real (v '' S), ∀ k, S ⊆ Set.range (t.face k) → A k x = y) → ((∀ k, ∀ (w : Fin
        3 → Real), (∑ i, w i) = 1 → (a k).symm (∑ i, w i • t.target (t.face k i)) = ∑ i, w i •
        p.vertex (t.face k i)) → (∀ (h : (↑X : Type) ≃ₜ (↑K : Type)), (∀ (k : Fin t.count), ∀ (x
            : (↑X : Type)), (↑x : ℝ × ℝ) ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range
        (p.vertex ∘ t.face k)) → (↑((h : (↑X : Type) → (↑K : Type)) x) : ℝ × ℝ) = (a k : ℝ × ℝ →
        ℝ × ℝ) (↑x : ℝ × ℝ)) → ((∀ i : Fin (n + 3), ∃ k, i ∈ Set.range (t.face k) ∧ i + 1 ∈
        Set.range (t.face k)) → ((∀ (u : Fin (n + 3) → Real × Real), ∀ i, convexHull Real (u ''
        {i, i + 1}) = segment Real (u i) (u (i + 1))) → (∀ i, ∀ (x : X), (x : Real × Real) ∈
        segment Real (p.vertex i) (p.vertex (i + 1)) ↔ (h x : Real × Real) ∈ segment Real
        (t.target i) (t.target (i + 1)))))))) := by
  classical
  intro n p X K t a ha hull_formula hai h hh edge_used pair_hull i x
  obtain ⟨k, hki, hkj⟩ := edge_used i
  have hs : ({i, i + 1} : Set (Fin (n + 3))) ⊆ Set.range (t.face k) :=
    Set.pair_subset hki hkj
  have source_subset : segment Real (p.vertex i) (p.vertex (i + 1)) ⊆
      convexHull Real (Set.range (p.vertex ∘ t.face k)) := by
    rw [← pair_hull p.vertex i, Set.range_comp]
    exact convexHull_mono (Set.image_mono hs)
  constructor
  · intro hx
    have hx' : (x : Real × Real) ∈ convexHull Real (p.vertex '' {i, i + 1}) := by
      rwa [pair_hull]
    obtain ⟨y, hy, heq⟩ := hull_formula p.vertex t.target a ha _ x hx'
    rw [hh k x (source_subset hx), heq k hs]
    rwa [pair_hull] at hy
  · intro hy
    have hy' : (h x : Real × Real) ∈ convexHull Real
        (t.target '' {i, i + 1}) := by
      rwa [pair_hull]
    obtain ⟨z, hz, heq⟩ := hull_formula t.target p.vertex
      (fun k => (a k).symm) hai _ (h x) hy'
    have hzseg : z ∈ segment Real (p.vertex i) (p.vertex (i + 1)) := by
      rwa [pair_hull] at hz
    have hztriangle := source_subset hzseg
    have hzX : z ∈ X := by
      rw [t.source_cover]
      exact Set.mem_iUnion.mpr ⟨k, hztriangle⟩
    let zX : X := ⟨z, hzX⟩
    have hzx : h zX = h x := by
      apply Subtype.ext
      rw [hh k zX hztriangle]
      change a k z = (h x : Real × Real)
      rw [← heq k hs]
      exact (a k).apply_symm_apply (h x)
    have hz_eq : z = (x : Real × Real) :=
      congrArg Subtype.val (h.injective hzx)
    rwa [← hz_eq]

end PiecewiseAffineProof

theorem P3381T1PiecewiseAffinePolygonModel {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    (t : P3381T1PairedTriangulation p X K) :
    ∃ h : X ≃ₜ K,
      (∀ x : X, (x : Real × Real) ∈ frontier X ↔
        (h x : Real × Real) ∈ frontier K) ∧
      ∀ k (x : X),
        (x : Real × Real) ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) →
        ∀ w : Fin 3 → Real, (∑ i, w i) = 1 →
          (x : Real × Real) = ∑ i, w i • p.vertex (t.face k i) →
          (h x : Real × Real) = ∑ i, w i • t.target (t.face k i) := by
-- BODY
  classical
  have local_maps : ∀ k, ∃ a : (Real × Real) ≃ₜ (Real × Real),
      ∀ w : Fin 3 → Real, (∑ i, w i) = 1 →
        a (∑ i, w i • p.vertex (t.face k i)) =
          ∑ i, w i • t.target (t.face k i) := by
    intro k
    exact P3381T1AffineTriangleMap (p.vertex ∘ t.face k)
      (t.target ∘ t.face k) (t.source_nondegenerate k) (t.target_nondegenerate k)
  choose a ha using local_maps
  -- Aggregate any finite convex combination into the three triangle weights.
  have hull_formula : ∀ (u v : Fin (n + 3) → Real × Real)
      (A : Fin t.count → (Real × Real) ≃ₜ (Real × Real)),
      (∀ k (w : Fin 3 → Real), (∑ i, w i) = 1 →
        A k (∑ i, w i • u (t.face k i)) = ∑ i, w i • v (t.face k i)) →
      ∀ (S : Set (Fin (n + 3))) (x : Real × Real),
        x ∈ convexHull Real (u '' S) →
        ∃ y ∈ convexHull Real (v '' S),
          ∀ k, S ⊆ Set.range (t.face k) → A k x = y := PiecewiseAffineProof.hull_formula n p X K t
  have hai : ∀ k (w : Fin 3 → Real), (∑ i, w i) = 1 →
      (a k).symm (∑ i, w i • t.target (t.face k i)) =
        ∑ i, w i • p.vertex (t.face k i) := by
    intro k w hw
    rw [← ha k w hw, (a k).symm_apply_apply]
  have paste : ∃ h : X ≃ₜ K, ∀ k (x : X),
      (x : Real × Real) ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) →
      (h x : Real × Real) = a k x := PiecewiseAffineProof.paste n p X K t a ha hull_formula hai
  obtain ⟨h, hh⟩ := paste
  refine ⟨h, ?_, ?_⟩
  · have hb := (P3381T1TriangulationBoundary p X K t).2.2.1
    have edge_used : ∀ i : Fin (n + 3),
        ∃ k, i ∈ Set.range (t.face k) ∧ i + 1 ∈ Set.range (t.face k) :=
            PiecewiseAffineProof.edge_used n p X K t
    have pair_hull : ∀ (u : Fin (n + 3) → Real × Real) i,
        convexHull Real (u '' {i, i + 1}) = segment Real (u i) (u (i + 1)) := by
      intro u i
      rw [Set.image_pair, convexHull_pair]
    have edge_transport : ∀ i (x : X),
        (x : Real × Real) ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ↔
          (h x : Real × Real) ∈ segment Real (t.target i) (t.target (i + 1)) :=
              PiecewiseAffineProof.edge_transport n p X K t a ha hull_formula hai h hh edge_used
              pair_hull
    intro x
    rw [hb, t.target_frontier]
    simp only [Set.mem_iUnion]
    exact exists_congr fun i => edge_transport i x
  · intro k x hx w hw hxw
    rw [hh k x hx, hxw]
    exact ha k w hw

end ApollonianSuperharmonic

end
