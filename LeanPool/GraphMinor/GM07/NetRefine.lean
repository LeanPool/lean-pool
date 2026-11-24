/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.GM07.NetRefineArcs
import LeanPool.GraphMinor.GM07.Section2MinVal

/-!
# Subdividing a paired side of a net

The refined seam graph in VII (2.5) and (2.6), pages 217–218,
adds the images of the cutting endpoints as vertices. On the source
disc this subdivides both members of a paired side at the same
parameter. The two smaller paired arcs generate exactly the same
identifications as the original pair.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- Subdividing both members of a paired side leaves the associated
surjection's fibers unchanged. This justifies the paired subarc
identifications for the refined seam graph in VII (2.6), page 218. -/
theorem Net.eqvGen_split_pair
    {S : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r) (w : unitInterval)
    (x y : N.D) : N.φ x = N.φ y ↔ Relation.EqvGen
      (fun a b : N.D =>
        (∃ (j : Fin N.r), j ≠ i ∧ ∃ t, a = N.f j t ∧ b = N.g j t) ∨
        (∃ t, a = pieceA (N.f i) 0 w.val t ∧ b = pieceA (N.g i) 0 w.val t) ∨
        (∃ t, a = pieceA (N.f i) w.val 1 t ∧ b = pieceA (N.g i) w.val 1 t)) x y := by
  constructor
  · intro hxy
    have h := (N.bd_eq_iff x y).mp hxy
    clear hxy
    induction h with
    | rel a b hab =>
      obtain ⟨j, t, rfl, rfl⟩ := hab
      apply Relation.EqvGen.rel
      by_cases hji : j = i
      · subst j
        rcases le_total t w with htw | hwt
        · obtain ⟨r, hfr, hgr⟩ := exists_pieceA_common_parameter (N.f i) (N.g i)
            0 w t ⟨unitInterval.nonneg t, htw⟩
          exact Or.inr (Or.inl ⟨r, hfr.symm, hgr.symm⟩)
        · obtain ⟨r, hfr, hgr⟩ := exists_pieceA_common_parameter (N.f i) (N.g i)
            w 1 t ⟨hwt, unitInterval.le_one t⟩
          exact Or.inr (Or.inr ⟨r, hfr.symm, hgr.symm⟩)
      · exact Or.inl ⟨j, hji, t, rfl, rfl⟩
    | refl a => exact .refl _
    | symm a b _ ih => exact .symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab with ⟨j, _, t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
      · exact N.pasting_eq j t
      · obtain ⟨s, _, hfs, hgs⟩ := pieceA_common_parameter (N.f i) (N.g i) 0 w
          (unitInterval.nonneg w) t
        exact (congrArg N.φ hfs).trans ((N.pasting_eq i s).trans (congrArg N.φ hgs).symm)
      · obtain ⟨s, _, hfs, hgs⟩ := pieceA_common_parameter (N.f i) (N.g i) w 1
          (unitInterval.le_one w) t
        exact (congrArg N.φ hfs).trans ((N.pasting_eq i s).trans (congrArg N.φ hgs).symm)
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- A point above a seam vertex cannot lie in an open paired side.
This verifies the cutting endpoint condition after subdividing at
its image in the refined seam graph of VII (2.6), page 218. -/
theorem Net.paired_interiors_ne_of_image_mem_seamV
    {S : Type*} [TopologicalSpace S] (N : Net S) {x : N.D}
    (hx : N.φ x ∈ N.seamV) :
    ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ x ∧ N.g j r ≠ x := by
  intro j r hr
  constructor
  · intro hfx
    exact N.notMem_seamV_of_mem_Ioo j hr ((congrArg N.φ hfx).symm ▸ hx)
  · intro hgx
    have hfx : N.φ (N.f j r) = N.φ x := (N.pasting_eq j r).trans (congrArg N.φ hgx)
    exact N.notMem_seamV_of_mem_Ioo j hr (hfx.symm ▸ hx)

/-- Subdividing a paired side gives a genuine net with the same source
disc and associated surjection. Its first minimized quantity is
unchanged. This is the source-disc refinement corresponding to adding
a seam vertex in VII (2.6), page 218. -/
theorem Net.exists_refine_pair
    {S : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    (w : unitInterval) (hw0 : 0 < w) (hw1 : w < 1) :
    ∃ M : Net S, ∃ e : N.D ≃ₜ M.D,
      M.r = N.r + 1 ∧ M.φ ∘ e = N.φ ∧ M.seamU = N.seamU ∧
      M.seamV = N.seamV ∪ {N.φ (N.f i w)} ∧
      (∀ G : Drawing S, M.bdVertexPreimageCard G = N.bdVertexPreimageCard G) ∧
      ∀ x : N.D, (∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ x ∧ N.g j r ≠ x) →
        ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → M.f j r ≠ e x ∧ M.g j r ≠ e x := by
  classical
  let f := splitCurveFamily N.f i w
  let g := splitCurveFamily N.g i w
  have hpair : ∀ j t, N.φ (f j t) = N.φ (g j t) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro t
      simpa only [f, g, splitCurveFamily, Fin.lastCases_last, sidePiece, ContinuousMap.coe_mk,
        Function.comp_apply] using
        N.pasting_eq i (Icc.convexComb w 1 t)
    · by_cases hj : j = i
      · subst j
        simp only [f, g, splitCurveFamily, Fin.lastCases_castSucc, ite_true, sidePiece,
          ContinuousMap.coe_mk, Function.comp_apply]
        exact fun t => N.pasting_eq i (Icc.convexComb 0 w t)
      · simpa only [f, g, splitCurveFamily, Fin.lastCases_castSucc,
          ite_eq_right hj] using N.pasting_eq j
  have hGen : ∀ j t, Relation.EqvGen
      (fun a b : N.D => ∃ (k : Fin (N.r + 1)) (r : unitInterval), a = f k r ∧ b = g k r)
      (N.f j t) (N.g j t) := by
    intro j t
    apply Relation.EqvGen.rel
    by_cases hj : j = i
    · subst j
      rcases le_total t w with htw | hwt
      · obtain ⟨r, hfr, hgr⟩ := exists_pieceA_common_parameter (N.f i) (N.g i)
          0 w t ⟨unitInterval.nonneg t, htw⟩
        refine ⟨i.castSucc, r, ?_, ?_⟩
        · simpa only [f, splitCurveFamily, Fin.lastCases_castSucc, ite_true,
            sidePiece_eq_pieceA] using hfr.symm
        · simpa only [g, splitCurveFamily, Fin.lastCases_castSucc, ite_true,
            sidePiece_eq_pieceA] using hgr.symm
      · obtain ⟨r, hfr, hgr⟩ := exists_pieceA_common_parameter (N.f i) (N.g i)
          w 1 t ⟨hwt, unitInterval.le_one t⟩
        refine ⟨Fin.last N.r, r, ?_, ?_⟩
        · simpa only [f, splitCurveFamily, Fin.lastCases_last, sidePiece_eq_pieceA] using hfr.symm
        · simpa only [g, splitCurveFamily, Fin.lastCases_last, sidePiece_eq_pieceA] using hgr.symm
    · refine ⟨j.castSucc, t, ?_, ?_⟩
      · simp only [f, splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hj]
      · simp only [g, splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hj]
  have hEquiv : ∀ x y, N.φ x = N.φ y ↔ Relation.EqvGen
      (fun a b : N.D => ∃ (k : Fin (N.r + 1)) (r : unitInterval), a = f k r ∧ b = g k r) x y := by
    intro x y
    constructor
    · intro hxy
      have h := (N.bd_eq_iff x y).mp hxy
      clear hxy
      induction h with
      | rel a b hab =>
        obtain ⟨j, t, rfl, rfl⟩ := hab
        exact hGen j t
      | refl a => exact .refl _
      | symm a b _ ih => exact .symm _ _ ih
      | trans a b c _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
    · intro h
      induction h with
      | rel a b hab =>
        obtain ⟨j, t, rfl, rfl⟩ := hab
        exact hpair j t
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hfbd : ∀ j, range (f j) ⊆ bd N.D := by
    intro j
    obtain ⟨k, hk, _⟩ := splitCurveFamily_range_subset N.f i hw0 hw1 j
    exact hk.trans (N.range_f_subset_bd k)
  have hgbd : ∀ j, range (g j) ⊆ bd N.D := by
    intro j
    obtain ⟨k, hk, _⟩ := splitCurveFamily_range_subset N.g i hw0 hw1 j
    exact hk.trans (N.range_g_subset_bd k)
  let M : Net S :=
    { D := N.D
      topD := N.topD
      isSurface_D := N.isSurface_D
      isClosedDisc_D := N.isClosedDisc_D
      r := N.r + 1
      f := f
      g := g
      φ := N.φ
      injective_f := splitCurveFamily_injective N.f N.injective_f i hw0 hw1
      injective_g := splitCurveFamily_injective N.g N.injective_g i hw0 hw1
      range_f_subset_bd := hfbd
      range_g_subset_bd := hgbd
      internally_disjoint_ff := splitCurveFamily_internally_disjoint N.f N.injective_f
        N.internally_disjoint_ff i hw0 hw1
      internally_disjoint_gg := splitCurveFamily_internally_disjoint N.g N.injective_g
        N.internally_disjoint_gg i hw0 hw1
      internally_disjoint_fg := splitCurveFamilies_internally_disjoint N.f N.g
        N.internally_disjoint_fg i hw0 hw1
      internally_disjoint_gf := splitCurveFamilies_internally_disjoint N.g N.f
        N.internally_disjoint_gf i hw0 hw1
      quotientMap_φ := N.quotientMap_φ
      pasting_eq := hpair
      interior_inj := N.interior_inj
      bd_eq_iff := hEquiv }
  refine ⟨M, Homeomorph.refl N.D, rfl, rfl, rfl,
    splitCurveFamily_endpoint_images N.f i w N.φ, fun _ => rfl, ?_⟩
  intro x hx j r hr
  constructor
  · intro hfx
    obtain ⟨j₀, _, hj₀⟩ := splitCurveFamily_range_subset N.f i hw0 hw1 j
    obtain ⟨v, hv, hvj⟩ := hj₀ ⟨r, hr, rfl⟩
    exact (hx j₀ v hv).1 (hvj.trans hfx)
  · intro hgx
    obtain ⟨j₀, _, hj₀⟩ := splitCurveFamily_range_subset N.g i hw0 hw1 j
    obtain ⟨v, hv, hvj⟩ := hj₀ ⟨r, hr, rfl⟩
    exact (hx j₀ v hv).2 (hvj.trans hgx)

/-- Adding a seam vertex by paired subdivision preserves normality
and the boundary contact count. It adds one pair and exactly the new
vertex image, as required for the refined seam graph in VII (2.6),
page 218. -/
theorem Net.exists_refine_pair_normal
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) (N : Net S)
    (i : Fin N.r) (w : unitInterval) (hw0 : 0 < w) (hw1 : w < 1)
    {G : Drawing S} (hN : N.IsNormalFor G) :
    ∃ M : Net S, M.IsNormalFor G ∧ M.r = N.r + 1 ∧ M.seamU = N.seamU ∧
      M.seamV = N.seamV ∪ {N.φ (N.f i w)} ∧
      M.bdVertexPreimageCard G = N.bdVertexPreimageCard G := by
  obtain ⟨M, _, hr, _, hU, hV, hCount, _⟩ := N.exists_refine_pair i w hw0 hw1
  have hNorm := ((N.isNormalFor_iff hS G).mp hN).2
  have hM : M.IsNormalFor G := (M.isNormalFor_iff hS G).mpr
    ⟨by rw [hr]; exact Nat.zero_lt_succ _, hU.symm ▸ hNorm⟩
  exact ⟨M, hM, hr, hU, hV, hCount G⟩

end GraphMinor.GM07
