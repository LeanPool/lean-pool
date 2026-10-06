/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolev

/-!
# Derivatives of compactly supported space-time mollifications

The local weak-derivative identities identify derivatives of the mollification with the
mollifications of the zero-extended weak data near the original support (`lem:carleman-sobolev` of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open scoped Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem spaceTimeMollify_eq_of_eq_on_ball
    {f g : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hfg : ∀ y ∈ Metric.closedBall z δ, f y = g y) :
    spaceTimeMollify f δ hδ z = spaceTimeMollify g δ hδ z := by
  rw [spaceTimeMollify, spaceTimeMollify, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hkernel : spaceTimeMollifier δ hδ t = 0
  · simp [hkernel]
  · have ht : t ∈ Metric.ball (0 : Vec3 × ℝ) δ := by
      rw [← spaceTimeMollifier_support hδ, Function.mem_support]
      exact hkernel
    have htNorm : ‖t‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using ht
    have hdist : dist (z - t) z ≤ δ := by
      rw [dist_eq_norm]
      calc
        ‖z - t - z‖ = ‖-t‖ := by congr 1; abel
        _ = ‖t‖ := norm_neg _
        _ ≤ δ := htNorm.le
    rw [hfg (z - t) (Metric.mem_closedBall.mpr hdist)]

/-- The product-coordinate support of a component is contained in the transported vector support
(`lem:carleman-sobolev`, ESS). -/
theorem product_component_tsupport_subset
    {w : ParabolicPoint → Vec3}
    (hcompact : HasCompactSupport w) (i : Fin 3) :
    tsupport (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) ⊆
      parabolicHomeomorph '' tsupport w := by
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hsupport : Function.support
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) ⊆ K := by
    intro q hq
    have hne : w (parabolicHomeomorph.symm q) i ≠ 0 := by
      simpa [Function.mem_support] using hq
    have hvec : w (parabolicHomeomorph.symm q) ≠ 0 := by
      intro hz
      exact hne (congrArg (fun v : Vec3 => v i) hz)
    exact ⟨parabolicHomeomorph.symm q,
      subset_tsupport w (Function.mem_support.mpr hvec),
      parabolicHomeomorph.apply_symm_apply q⟩
  change closure (Function.support
    (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i)) ⊆ K
  exact closure_minimal hsupport hKcompact.isClosed

/-- A compactly supported parabolic field remains compactly supported in product coordinates
(`lem:carleman-sobolev`, ESS). -/
theorem product_field_hasCompactSupport
    {w : ParabolicPoint → Vec3} (hcompact : HasCompactSupport w) :
    HasCompactSupport (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact)
  intro q hq
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, w (parabolicHomeomorph.symm q) i ≠ 0 := by
    by_contra h
    apply hq
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hvec : w (parabolicHomeomorph.symm q) ≠ 0 := by
    intro hz
    exact hi (congrArg (fun v : Vec3 => v i) hz)
  exact ⟨parabolicHomeomorph.symm q,
    subset_tsupport w (Function.mem_support.mpr hvec),
    parabolicHomeomorph.apply_symm_apply q⟩

private theorem spatialPartial_eq_zero_of_not_mem_tsupport_product
    {f : Vec3 × ℝ → ℝ} {j : Fin 3} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport f) :
    spatialPartial (fun q : ParabolicPoint => f q) j (z : ParabolicPoint) = 0 := by
  have hzero : (fun q : Vec3 × ℝ => f q) =ᶠ[𝓝 z] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hz
  have hslice : (fun x : Vec3 => f (x, z.2)) =ᶠ[𝓝 z.1] 0 := by
    exact hzero.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hnot : z.1 ∉ tsupport (fun x : Vec3 => f (x, z.2)) :=
    notMem_tsupport_iff_eventuallyEq.mpr hslice
  simp [spatialPartial, fderiv_of_notMem_tsupport ℝ hnot]

private theorem timePartial_eq_zero_of_not_mem_tsupport_product
    {f : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport f) :
    timePartial (fun q : ParabolicPoint => f q) (z : ParabolicPoint) = 0 := by
  have hzero : (fun q : Vec3 × ℝ => f q) =ᶠ[𝓝 z] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hz
  have hslice : (fun t : ℝ => f (z.1, t)) =ᶠ[𝓝 z.2] 0 := by
    exact hzero.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hnot : z.2 ∉ tsupport (fun t : ℝ => f (z.1, t)) :=
    notMem_tsupport_iff_eventuallyEq.mpr hslice
  simp [timePartial, fderiv_of_notMem_tsupport ℝ hnot]

/-- A spatial derivative of a smooth compactly supported scalar field is supported where the
field is supported (`lem:carleman-sobolev`, ESS). -/
theorem spatialPartial_tsupport_subset_product
    {f : Vec3 × ℝ → ℝ} (j : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialPartial (fun q => f q) j z) ⊆
      tsupport f := by
  apply closure_minimal
  · intro z hz
    by_contra hnot
    have hzero := spatialPartial_eq_zero_of_not_mem_tsupport_product (j := j) hnot
    exact (Function.mem_support.mp hz) hzero
  · exact isClosed_tsupport _

/-- A second spatial derivative is supported where the underlying scalar field is supported
(`lem:carleman-sobolev`, ESS). -/
theorem spatialSecondPartial_tsupport_subset_product
    {f : Vec3 × ℝ → ℝ} (j k : Fin 3) :
    tsupport (fun z : Vec3 × ℝ =>
      spatialSecondPartial (fun q => f q) j k z) ⊆ tsupport f := by
  have hfirst := spatialPartial_tsupport_subset_product (f := f) j
  have hsecond := spatialPartial_tsupport_subset_product
    (f := fun z : Vec3 × ℝ => spatialPartial (fun q : ParabolicPoint => f q) j z) k
  exact hsecond.trans hfirst

/-- A time derivative is supported where the underlying scalar field is supported
(`lem:carleman-sobolev`, ESS). -/
theorem timePartial_tsupport_subset_product
    {f : Vec3 × ℝ → ℝ} :
    tsupport (fun z : Vec3 × ℝ => timePartial (fun q => f q) z) ⊆
      tsupport f := by
  apply closure_minimal
  · intro z hz
    by_contra hnot
    have hzero := timePartial_eq_zero_of_not_mem_tsupport_product hnot
    exact (Function.mem_support.mp hz) hzero
  · exact isClosed_tsupport _

/-- On a fixed compact neighborhood of the support, the ordinary derivatives of the
zero-extended mollification are the mollifications of the zero-extended weak data
(`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeMollify_compactSupport_weakDerivs
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    {r δ : ℝ} (hr : 0 < r) (hthick :
      Metric.cthickening r (parabolicHomeomorph '' tsupport w) ⊆ Ω ×ˢ I)
    (hδ : 0 < δ) (hδsmall : 4 * δ ≤ r / 2)
    {z : Vec3 × ℝ}
    (hz : z ∈ Metric.closedBall (0 : Vec3 × ℝ) (r / 4) +
      (parabolicHomeomorph '' tsupport w)) :
    (∀ i j : Fin 3,
      spatialPartial (fun q : ParabolicPoint =>
        spaceTimeMollify
          (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i) δ hδ q) j z =
        spaceTimeMollify
          (zeroExtendField (Ω ×ˢ I)
            (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j)) δ hδ z) ∧
    (∀ i j k : Fin 3,
      spatialSecondPartial (fun q : ParabolicPoint =>
        spaceTimeMollify
          (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i) δ hδ q) j k z =
        spaceTimeMollify
          (zeroExtendField (Ω ×ˢ I)
            (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k)) δ hδ z) ∧
    (∀ i : Fin 3,
      timePartial (fun q : ParabolicPoint =>
        spaceTimeMollify
          (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i) δ hδ q) z =
        spaceTimeMollify
          (zeroExtendField (Ω ×ˢ I)
            (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i)) δ hδ z) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  have hU : IsOpen U := hΩ.prod hI
  have hKU : K ⊆ U := by
    rintro q ⟨p, hp, rfl⟩
    exact htsupport hp
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  have huNorm : ‖u‖ ≤ r / 4 := by simpa using hu
  have hzv : dist (u + v) v ≤ r / 4 := by
    rw [dist_eq_norm]
    simpa using hu
  have hsafe (x : Vec3 × ℝ) (hx : dist x (u + v) ≤ 4 * δ) : x ∈ U := by
    apply hthick
    apply Metric.mem_cthickening_of_dist_le x v r K hv
    calc
      dist x v ≤ dist x (u + v) + dist (u + v) v := dist_triangle x (u + v) v
      _ ≤ 4 * δ + r / 4 := add_le_add hx hzv
      _ = r / 4 + 4 * δ := by ring
      _ ≤ r / 4 + r / 2 := add_le_add_right hδsmall (r / 4)
      _ = r / 2 + r / 4 := by ring
      _ ≤ r := by nlinarith only [hr]
  have hsafe4 : Metric.closedBall (u + v) (4 * δ) ⊆ U := by
    intro x hx
    exact hsafe x (Metric.mem_closedBall.mp hx)
  have hsafeδ (x : Vec3 × ℝ) (hx : dist x (u + v) ≤ δ) : x ∈ U :=
    hsafe x (le_trans hx (by nlinarith only [hδ]))
  have hresult := spaceTimeMollify_weak_derivatives hΩ hI hderiv hδ hsafe4
  have hcompareDw (i j : Fin 3) :
      spaceTimeMollify (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j)
          δ hδ (u + v) =
        spaceTimeMollify
          (zeroExtendField U
            (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j)) δ hδ (u + v) := by
    apply spaceTimeMollify_eq_of_eq_on_ball hδ
    intro y hy
    have hyU : y ∈ U := by
      apply hsafeδ y
      have hdist : dist y (u + v) ≤ δ := Metric.mem_closedBall.mp hy
      exact hdist
    simp [zeroExtendField, U, hyU]
  have hcompareD2 (i j k : Fin 3) :
      spaceTimeMollify (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k)
          δ hδ (u + v) =
        spaceTimeMollify
          (zeroExtendField U
            (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k)) δ hδ (u + v) := by
    apply spaceTimeMollify_eq_of_eq_on_ball hδ
    intro y hy
    have hyU : y ∈ U := by
      apply hsafeδ y
      exact Metric.mem_closedBall.mp hy
    simp [zeroExtendField, U, hyU]
  have hcompareDtw (i : Fin 3) :
      spaceTimeMollify (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i)
          δ hδ (u + v) =
        spaceTimeMollify
          (zeroExtendField U
            (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i)) δ hδ (u + v) := by
    apply spaceTimeMollify_eq_of_eq_on_ball hδ
    intro y hy
    have hyU : y ∈ U := by
      apply hsafeδ y
      exact Metric.mem_closedBall.mp hy
    simp [zeroExtendField, U, hyU]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simpa [U] using (hresult.1 i j).trans (hcompareDw i j)
  · intro i j k
    simpa [U] using (hresult.2.1 i j k).trans (hcompareD2 i j k)
  · intro i
    simpa [U] using (hresult.2.2 i).trans (hcompareDtw i)

end CKN
