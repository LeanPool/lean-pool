/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

/-!
# Regular points read in a chart

For a chart `e` of a complex manifold `M`, a subset `B` of the model space and
`S = e.source ∩ e⁻¹ B`, a point `y ∈ e.source` is a regular point of `S` of dimension `k`
exactly when `e y` is a regular point of `B ∩ e.target`, the model space being regarded as
a complex manifold with its identity chart (`regularAtDim_chart_iff`).

Both directions precompose a flattening with a chart transition, which is biholomorphic
on its domain (`LocalHolomorphicEquivAt.precomp`).
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.Pending.RegularAtDimChart

open FirstPass RegularPatchNeighborhood

noncomputable section

variable {n : ℕ}

/-- Precomposition of a local holomorphic equivalence centred at `T c` with a biholomorphic
partial homeomorphism `T`. -/
def precomp (T : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n))
    (hT : DifferentiableOn ℂ T T.source) (hTs : DifferentiableOn ℂ T.symm T.target)
    {c q : ComplexModel n} (hc : c ∈ T.source) (hq : T c = q)
    (Φ : LocalHolomorphicEquivAt (n := n) q) :
    LocalHolomorphicEquivAt (n := n) c where
  source := T.source ∩ T ⁻¹' Φ.source
  target := Φ.target ∩ Φ.invFun ⁻¹' T.target
  isOpen_source := T.isOpen_inter_preimage Φ.isOpen_source
  isOpen_target :=
    Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target T.open_target
  center_mem_source := ⟨hc, by rw [mem_preimage, hq]; exact Φ.center_mem_source⟩
  toFun := fun z => Φ.toFun (T z)
  invFun := fun v => T.symm (Φ.invFun v)
  toFun_holomorphic := Φ.toFun_holomorphic.comp (hT.mono inter_subset_left) fun z hz => hz.2
  invFun_holomorphic := hTs.comp (Φ.invFun_holomorphic.mono inter_subset_left) fun v hv => hv.2
  mapsTo_toFun := fun z hz => ⟨Φ.mapsTo_toFun hz.2, by
    simpa only [mem_preimage, Φ.left_inv _ hz.2] using T.map_source hz.1⟩
  mapsTo_invFun := fun v hv => ⟨T.map_target hv.2, by
    simpa only [mem_preimage, T.right_inv hv.2] using Φ.mapsTo_invFun hv.1⟩
  left_inv := fun z hz => by
    simp only [Φ.left_inv _ hz.2]
    exact T.left_inv hz.1
  right_inv := fun v hv => by
    simp only [T.right_inv hv.2]
    exact Φ.right_inv _ hv.1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Regularity in a chart.**  For a chart `e` of `M`, `y ∈ e.source` is a regular point of
`e.source ∩ e⁻¹ B` of dimension `k` iff `e y` is a regular point of `B ∩ e.target` of
dimension `k` in the model space. -/
theorem regularAtDim_chart_iff (e : ComplexChart n M) (B : Set (ComplexModel n)) {y : M}
    (hy : y ∈ e.val.source) {k : ℕ} :
    RegularAtDim (n := n) (e.val.source ∩ e.val ⁻¹' B) y k ↔
      RegularAtDim (n := n) (M := ComplexModel n) (B ∩ e.val.target) (e.val y) k := by
  set f := complexChartAt (n := n) y with hf
  have hyf : y ∈ f.val.source := mem_complexChartAt_source y
  constructor
  · rintro ⟨hk, hyS, Φ, -, hΦ0, hflat⟩
    set T := chartTransition e f with hT
    have hTsrc : T.source = e.val.target ∩ e.val.symm ⁻¹' f.val.source := by
      simp [hT, chartTransition]
    have hTapp : ∀ z, T z = f.val (e.val.symm z) := fun z => rfl
    have hc : e.val y ∈ T.source := by
      rw [hTsrc]
      exact ⟨e.val.map_source hy, by simpa [e.val.left_inv hy] using hyf⟩
    have hTc : T (e.val y) = f.val y := by rw [hTapp, e.val.left_inv hy]
    refine ⟨hk, ⟨hyS.2, e.val.map_source hy⟩,
      precomp T (differentiableOn_chartTransition e f)
        (differentiableOn_chartTransition_symm e f) hc hTc Φ, subset_univ _, ?_, ?_⟩
    · change Φ.toFun (T (e.val y)) = 0
      rw [hTc]
      exact hΦ0
    · intro z _ hz
      change z ∈ T.source ∩ T ⁻¹' Φ.source at hz
      change z ∈ B ∩ e.val.target ↔ Φ.toFun (T z) ∈ complexCoordinatePlane n k
      have hzsrc := hz.1
      rw [hTsrc] at hzsrc
      have hz1 : e.val.symm z ∈ f.val.source := hzsrc.2
      have hz2 : f.val (e.val.symm z) ∈ Φ.source := by
        have := hz.2
        rwa [mem_preimage, hTapp] at this
      rw [hTapp, ← hflat hz1 hz2]
      have hze : e.val.symm z ∈ e.val.source := e.val.map_target hzsrc.1
      simp only [mem_inter_iff, mem_preimage, e.val.right_inv hzsrc.1, hze, true_and]
      exact ⟨fun h => h.1, fun h => ⟨h, hzsrc.1⟩⟩
  · rintro ⟨hk, hyB, Ψ, -, hΨ0, hflat⟩
    set T := chartTransition f e with hT
    have hTsrc : T.source = f.val.target ∩ f.val.symm ⁻¹' e.val.source := by
      simp [hT, chartTransition]
    have hTapp : ∀ z, T z = e.val (f.val.symm z) := fun z => rfl
    have hc : f.val y ∈ T.source := by
      rw [hTsrc]
      exact ⟨f.val.map_source hyf, by simpa [f.val.left_inv hyf] using hy⟩
    have hTc : T (f.val y) = e.val y := by rw [hTapp, f.val.left_inv hyf]
    refine ⟨hk, ⟨hy, hyB.1⟩,
      precomp T (differentiableOn_chartTransition f e)
        (differentiableOn_chartTransition_symm f e) hc hTc Ψ, ?_, ?_, ?_⟩
    · intro z hz
      have := hz.1
      rw [hTsrc] at this
      exact this.1
    · change Ψ.toFun (T (f.val y)) = 0
      rw [hTc]
      exact hΨ0
    · intro y' hy' hy'src
      change f.val y' ∈ T.source ∩ T ⁻¹' Ψ.source at hy'src
      change y' ∈ e.val.source ∩ e.val ⁻¹' B ↔
        Ψ.toFun (T (f.val y')) ∈ complexCoordinatePlane n k
      have hsrc := hy'src.1
      rw [hTsrc] at hsrc
      have hy'e : y' ∈ e.val.source := by simpa [f.val.left_inv hy'] using hsrc.2
      have hTy' : T (f.val y') = e.val y' := by rw [hTapp, f.val.left_inv hy']
      have hΨsrc : e.val y' ∈ Ψ.source := by
        have := hy'src.2
        rwa [mem_preimage, hTy'] at this
      rw [hTy']
      refine Iff.trans ?_ (hflat (y := e.val y') (mem_univ _) hΨsrc)
      simp only [mem_inter_iff, mem_preimage, hy'e, e.val.map_source hy'e, true_and, and_true]

end

end RegularAtDimChart
end Pending
end Analysis
end Foundations
end SGPT
