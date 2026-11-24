/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

/-! # Regular points: locality and uniqueness of dimension

Blueprint `lag:regular-point-basics`.

* `regularAtDim_of_inter_eq`: if `A ∩ W = B ∩ W` for an open `W ∋ x`, then `A` regular of
  dimension `k` at `x` implies the same for `B`.  Proof: restrict the flattening to the
  chart-preimage of `W`.
* `eq_of_regularAtDim`: a point is not regular of two different dimensions.  Proof: for
  flattenings `Φ` (dimension `k`) and `Ψ` (dimension `j`) the transition `Ψ ∘ Φ⁻¹` is
  holomorphic at `0` with a holomorphic left inverse, so its derivative is injective; it maps
  the `k`-plane into the `j`-plane near `0`, hence so does its derivative, forcing `k ≤ j`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RegularPointDimension

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Regularity is local: sets agreeing on an open neighbourhood have the same regular points. -/
theorem regularAtDim_of_inter_eq {A B W : Set M} (hW : IsOpen W) {x : M} (hxW : x ∈ W)
    (hAB : A ∩ W = B ∩ W) {k : ℕ} (h : RegularAtDim (n := n) A x k) :
    RegularAtDim (n := n) B x k := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨hk, hxA, Φ, hsub, hzero, hflat⟩ := h
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  have hs : IsOpen (e.target ∩ e.symm ⁻¹' W) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hW
  have hq : e x ∈ Φ.source ∩ (e.target ∩ e.symm ⁻¹' W) :=
    ⟨Φ.center_mem_source, e.map_source hxs, by simpa [mem_preimage, e.left_inv hxs] using hxW⟩
  have hxB : x ∈ B ∩ W := hAB ▸ ⟨hxA, hxW⟩
  let Φ' : LocalHolomorphicEquivAt (n := n) (e x) :=
    { source := Φ.source ∩ (e.target ∩ e.symm ⁻¹' W)
      target := Φ.target ∩ Φ.invFun ⁻¹' (e.target ∩ e.symm ⁻¹' W)
      isOpen_source := Φ.isOpen_source.inter hs
      isOpen_target :=
        Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target hs
      center_mem_source := hq
      toFun := Φ.toFun
      invFun := Φ.invFun
      toFun_holomorphic := Φ.toFun_holomorphic.mono inter_subset_left
      invFun_holomorphic := Φ.invFun_holomorphic.mono inter_subset_left
      mapsTo_toFun := fun z hz => ⟨Φ.mapsTo_toFun hz.1, by
        simpa only [mem_preimage, Φ.left_inv z hz.1] using hz.2⟩
      mapsTo_invFun := fun w hw => ⟨Φ.mapsTo_invFun hw.1, hw.2⟩
      left_inv := fun z hz => Φ.left_inv z hz.1
      right_inv := fun w hw => Φ.right_inv w hw.1 }
  refine ⟨hk, hxB.1, Φ', fun z hz => hsub hz.1, hzero, ?_⟩
  intro y hy hyΦ
  have hyW : y ∈ W := by
    have h' : e.symm (e y) ∈ W := hyΦ.2.2
    rwa [e.left_inv hy] at h'
  have hAB' : y ∈ A ↔ y ∈ B := by
    constructor
    · intro hyA
      have : y ∈ B ∩ W := hAB ▸ ⟨hyA, hyW⟩
      exact this.1
    · intro hyB
      have : y ∈ A ∩ W := hAB.symm ▸ ⟨hyB, hyW⟩
      exact this.1
  rw [← hAB']
  exact hflat hy hyΦ.1

/-- A holomorphic map sending the `k`-plane into the `j`-plane near `0` has derivative at `0`
sending the `k`-plane into the `j`-plane. -/
theorem fderiv_mem_complexCoordinatePlane {H : ComplexModel n → ComplexModel n} {k j : ℕ}
    (hH : DifferentiableAt ℂ H 0)
    (hplane : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      w ∈ complexCoordinatePlane n k → H w ∈ complexCoordinatePlane n j)
    {v : ComplexModel n} (hv : v ∈ complexCoordinatePlane n k) :
    fderiv ℂ H 0 v ∈ complexCoordinatePlane n j := by
  intro i hi
  have hline : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
    simpa using hc.tendsto 0
  have hev : (fun t : ℂ => (H (t • v)) i) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hline.eventually hplane] with t ht
    exact ht (fun l hl => by simp [hv l hl]) i hi
  have hd : HasDerivAt (fun t : ℂ => (H (t • v)) i) (fderiv ℂ H 0 v i) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    have h2 : HasFDerivAt H (fderiv ℂ H 0) ((0 : ℂ) • v) := by
      simpa using hH.hasFDerivAt
    have h3 := (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp_hasDerivAt
      (0 : ℂ) (h2.comp_hasDerivAt (0 : ℂ) h1)
    exact h3
  exact hd.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)

/-- An injective linear map sending the `k`-plane into the `j`-plane forces `k ≤ j`. -/
theorem le_of_injective_mapsTo_complexCoordinatePlane {k j : ℕ} (hk : k ≤ n)
    (D : ComplexModel n →ₗ[ℂ] ComplexModel n) (hD : Function.Injective D)
    (hmaps : ∀ v ∈ complexCoordinatePlane n k, D v ∈ complexCoordinatePlane n j) : k ≤ j := by
  rcases lt_or_ge n j with hjn | hjn
  · omega
  let ι : (Fin k → ℂ) →ₗ[ℂ] ComplexModel n :=
    { toFun := fun a => WithLp.toLp 2 (fun i : Fin n => if h : i.1 < k then a ⟨i, h⟩ else 0)
      map_add' := by
        intro a b
        ext i
        by_cases h : i.1 < k <;> simp [h]
      map_smul' := by
        intro c a
        ext i
        by_cases h : i.1 < k <;> simp [h] }
  let π : ComplexModel n →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun z i => z ⟨i, lt_of_lt_of_le i.2 hjn⟩
      map_add' := by
        intro a b
        ext i
        simp
      map_smul' := by
        intro c a
        ext i
        simp }
  have hιk : ∀ a, ι a ∈ complexCoordinatePlane n k := by
    intro a i hi
    simp [ι, not_lt.mpr hi]
  have hinj : Function.Injective (π ∘ₗ D ∘ₗ ι) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hDa : D (ι a) = 0 := by
      ext i
      by_cases h : i.1 < j
      · have := congrFun ha ⟨i, h⟩
        simpa [π] using this
      · simpa using hmaps _ (hιk a) i (not_lt.mp h)
    have hιa : ι a = 0 := hD (by rw [hDa, map_zero])
    funext l
    have := congrArg (fun z : ComplexModel n => z ⟨l, lt_of_lt_of_le l.2 hk⟩) hιa
    simpa [ι] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

omit [IsComplexManifold n M] in
/-- If `A` is regular of dimensions `k` and `j` at `x`, then `k ≤ j`. -/
theorem le_of_regularAtDim {A : Set M} {x : M} {k j : ℕ}
    (hk : RegularAtDim (n := n) A x k) (hj : RegularAtDim (n := n) A x j) : k ≤ j := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨hkn, -, Φ, hΦsub, hΦ0, hΦflat⟩ := hk
  obtain ⟨-, -, Ψ, -, hΨ0, hΨflat⟩ := hj
  have h0Φ : (0 : ComplexModel n) ∈ Φ.target := hΦ0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have h0Ψ : (0 : ComplexModel n) ∈ Ψ.target := hΨ0 ▸ Ψ.mapsTo_toFun Ψ.center_mem_source
  have hΦinv0 : Φ.invFun 0 = e x := by rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have hΨinv0 : Ψ.invFun 0 = e x := by rw [← hΨ0, Ψ.left_inv _ Ψ.center_mem_source]
  have hΦinv : DifferentiableAt ℂ Φ.invFun 0 :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0Φ)
  have hΨinv : DifferentiableAt ℂ Ψ.invFun 0 :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds h0Ψ)
  have hΦto : DifferentiableAt ℂ Φ.toFun (Ψ.invFun 0) := by
    rw [hΨinv0]
    exact Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hΨto : DifferentiableAt ℂ Ψ.toFun (Φ.invFun 0) := by
    rw [hΦinv0]
    exact Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds Ψ.center_mem_source)
  set H := Ψ.toFun ∘ Φ.invFun with hHdef
  set G := Φ.toFun ∘ Ψ.invFun with hGdef
  have hH : DifferentiableAt ℂ H 0 := hΨto.comp (0 : ComplexModel n) hΦinv
  have hG : DifferentiableAt ℂ G 0 := hΦto.comp (0 : ComplexModel n) hΨinv
  have hH0 : H 0 = 0 := by
    simp only [H, Function.comp_apply, hΦinv0]
    exact hΨ0
  have hU : Φ.target ∩ Φ.invFun ⁻¹' Ψ.source ∈ 𝓝 (0 : ComplexModel n) :=
    inter_mem (Φ.isOpen_target.mem_nhds h0Φ) (hΦinv.continuousAt.preimage_mem_nhds
      (by rw [hΦinv0]; exact Ψ.isOpen_source.mem_nhds Ψ.center_mem_source))
  have hGH : G ∘ H =ᶠ[𝓝 (0 : ComplexModel n)] id := by
    filter_upwards [hU] with w hw
    simp [G, H, Ψ.left_inv _ hw.2, Φ.right_inv _ hw.1]
  have hcomp : (fderiv ℂ G 0).comp (fderiv ℂ H 0) = ContinuousLinearMap.id ℂ _ := by
    have hG' : DifferentiableAt ℂ G (H 0) := by rw [hH0]; exact hG
    have := fderiv_comp (0 : ComplexModel n) hG' hH
    rw [hGH.fderiv_eq, fderiv_id, hH0] at this
    exact this.symm
  have hinj : Function.Injective (fderiv ℂ H 0) := by
    intro a b hab
    have := congrArg (fderiv ℂ G 0) hab
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using this
  have hplane : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      w ∈ complexCoordinatePlane n k → H w ∈ complexCoordinatePlane n j := by
    filter_upwards [hU] with w hw hwk
    have hwt : Φ.invFun w ∈ e.target := hΦsub (Φ.mapsTo_invFun hw.1)
    have hy : e.symm (Φ.invFun w) ∈ e.source := e.map_target hwt
    have hey : e (e.symm (Φ.invFun w)) = Φ.invFun w := e.right_inv hwt
    have hyΦ : e (e.symm (Φ.invFun w)) ∈ Φ.source := by
      rw [hey]; exact Φ.mapsTo_invFun hw.1
    have hyΨ : e (e.symm (Φ.invFun w)) ∈ Ψ.source := by
      rw [hey]; exact hw.2
    have hA : e.symm (Φ.invFun w) ∈ A :=
      (hΦflat hy hyΦ).mpr (by rw [hey, Φ.right_inv w hw.1]; exact hwk)
    have hmem := (hΨflat hy hyΨ).mp hA
    rw [hey] at hmem
    exact hmem
  exact le_of_injective_mapsTo_complexCoordinatePlane hkn (fderiv ℂ H 0).toLinearMap hinj
    (fun v hv => fderiv_mem_complexCoordinatePlane hH hplane hv)

omit [IsComplexManifold n M] in
/-- A point is not a regular point of two different dimensions. -/
theorem eq_of_regularAtDim {A : Set M} {x : M} {k j : ℕ}
    (hk : RegularAtDim (n := n) A x k) (hj : RegularAtDim (n := n) A x j) : k = j :=
  le_antisymm (le_of_regularAtDim hk hj) (le_of_regularAtDim hj hk)

end SGPT.Foundations.Analysis.Pending.RegularPointDimension
