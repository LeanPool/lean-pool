/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Riemannian density of an arbitrary chart

`chartDensity Ξ w = √det(⟨dΞ⁻¹ eᵢ, dΞ⁻¹ eⱼ⟩)`, generalizing `chartVolumeDensity` (the case `Ξ =
    chartAt x₀`).
It is `LinearMap.normDet` of the differential of `Ξ.symm`, hence multiplies by `|det|` under
change of chart.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

section Linear

variable {F W : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- `√det` of the Gram matrix of the image of the standard orthonormal basis. -/
noncomputable def gramDens (L : F →ₗ[ℝ] W) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j =>
    inner ℝ (L (stdOrthonormalBasis ℝ F i)) (L (stdOrthonormalBasis ℝ F j))))

theorem gramDens_eq_normDet (L : F →ₗ[ℝ] W) : gramDens L = L.normDet := by
  have h := L.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ F)
  unfold gramDens
  have h' : (Matrix.of fun i j =>
      inner ℝ (L (stdOrthonormalBasis ℝ F i)) (L (stdOrthonormalBasis ℝ F j))) =
      Matrix.gram ℝ (fun x => L (stdOrthonormalBasis ℝ F x)) := by
    ext i j; simp [Matrix.gram]
  rw [h']
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [← h, Real.sqrt_sq L.normDet_nonneg]

theorem gramDens_comp (L : F →ₗ[ℝ] W) (D : F →ₗ[ℝ] F) :
    gramDens (L ∘ₗ D) = gramDens L * |LinearMap.det D| := by
  rw [gramDens_eq_normDet, gramDens_eq_normDet,
    LinearMap.normDet_comp_of_finrank_eq _ _ rfl, LinearMap.normDet_eq_abs_det]

end Linear

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- The Riemannian volume density of an arbitrary chart `Ξ`, at the chart point `w`. -/
noncomputable def chartDensity (Ξ : OpenPartialHomeomorph M F) (w : F) : ℝ :=
  gramDens (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) (Ξ.symm w) from
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ.symm w).toLinearMap)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsManifold 𝓘(ℝ, F) ∞ M] in
theorem chartVolumeDensity_eq_chartDensity (x₀ : M) (z : F) :
    chartVolumeDensity F x₀ z = chartDensity (chartAt F x₀) z := by
  unfold chartVolumeDensity chartDensity gramDens
  rfl


omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsManifold 𝓘(ℝ, F) ∞ M] in
theorem gramDens_cast {x y : M} (h : x = y) (L : F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) x)
    (L' : F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) y) (hLL' : ∀ v, (L' v : F) = (L v : F)) :
    gramDens L' = gramDens L := by
  subst h
  have : L' = L := LinearMap.ext hLL'
  rw [this]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsManifold 𝓘(ℝ, F) ∞ M] in
theorem gramDens_chain {x y : M} (h : y = x) (A : F →L[ℝ] TangentSpace 𝓘(ℝ, F) x)
    (L1 : F →L[ℝ] TangentSpace 𝓘(ℝ, F) y) (D : F →L[ℝ] F)
    (hA : ∀ v, (A v : F) = (L1 (D v) : F)) :
    gramDens (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) x from A.toLinearMap) =
      gramDens (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) y from L1.toLinearMap) *
        |LinearMap.det D.toLinearMap| := by
  have h1 := gramDens_comp (W := TangentSpace 𝓘(ℝ, F) y)
    (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) y from L1.toLinearMap) D.toLinearMap
  refine Eq.trans ?_ h1
  refine gramDens_cast h _ _ fun v => ?_
  exact hA v

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem differentiableAt_transition (φ Ξ : OpenPartialHomeomorph M F)
    (hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    {z : F} (hz : z ∈ φ.target) (hx : φ.symm z ∈ Ξ.source) :
    DifferentiableAt ℝ (fun z => Ξ (φ.symm z)) z := by
  have hφd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) φ.symm z :=
    (hφ'.mdifferentiableOn (by simp) z hz).mdifferentiableAt (φ.open_target.mem_nhds hz)
  have hΞd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ (φ.symm z) :=
    (hΞ.mdifferentiableOn (by simp) _ hx).mdifferentiableAt (Ξ.open_source.mem_nhds hx)
  exact (mdifferentiableAt_iff_differentiableAt).1 (hΞd.comp z hφd)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsManifold 𝓘(ℝ, F) ∞ M] in
/-- **Transition of the Riemannian density**: `ρ_φ(z) = ρ_Ξ(T z) |det DT(z)|`, `T = Ξ ∘ φ⁻¹`. -/
theorem chartDensity_transition (φ Ξ : OpenPartialHomeomorph M F)
    (hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    (hΞ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target)
    {z : F} (hz : z ∈ φ.target) (hx : φ.symm z ∈ Ξ.source) :
    chartDensity φ z = chartDensity Ξ (Ξ (φ.symm z)) *
      |(fderiv ℝ (fun z => Ξ (φ.symm z)) z).det| := by
  set T : F → F := fun z => Ξ (φ.symm z) with hT
  have hTz : T z ∈ Ξ.target := Ξ.map_source hx
  have hφd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) φ.symm z :=
    (hφ'.mdifferentiableOn (by simp) z hz).mdifferentiableAt (φ.open_target.mem_nhds hz)
  have hΞd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ (φ.symm z) :=
    (hΞ.mdifferentiableOn (by simp) _ hx).mdifferentiableAt (Ξ.open_source.mem_nhds hx)
  have hΞd' : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ.symm (T z) :=
    (hΞ'.mdifferentiableOn (by simp) _ hTz).mdifferentiableAt (Ξ.open_target.mem_nhds hTz)
  have hTd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) T z := hΞd.comp z hφd
  have hev : φ.symm =ᶠ[𝓝 z] Ξ.symm ∘ T := by
    have h1 : φ.symm ⁻¹' Ξ.source ∈ 𝓝 z :=
      (φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds hz)).preimage_mem_nhds
        (Ξ.open_source.mem_nhds hx)
    filter_upwards [h1] with w hw
    exact (Ξ.left_inv hw).symm
  have hchain := mfderiv_comp z hΞd' hTd
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F)) hev
  have hpt : Ξ.symm (T z) = φ.symm z := Ξ.left_inv hx
  have hTf : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) T z = fderiv ℝ T z := mfderiv_eq_fderiv
  unfold chartDensity
  refine gramDens_chain hpt _ _ (fderiv ℝ T z) fun v => ?_
  have := congrArg (fun A => A v) hmf
  rw [hchain, hTf] at this
  exact this

end CutCur
