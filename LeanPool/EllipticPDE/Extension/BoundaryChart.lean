/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.ShearWeakGrad
public import LeanPool.EllipticPDE.Extension.EvenReflection


/-!
# Extension across a `C¹` boundary chart

Near a boundary point a domain with `C¹` boundary is, after relabelling the coordinates, the
region above the graph of a `C¹` function `γ` of the remaining ones. This file extends a
Sobolev class across that graph, which is the local half of Guo's extension operator.

The route is the composite of the three maps the chapter has built. The shear `S y = y + γ(y)eⱼ`
inverts the flattening, so the flattening `T = S⁻¹` sends the region above the graph onto the
half space; the class travels the other way, through `S`, and picks up the transpose of the
shear's derivative on its gradient. The flattened class is then reflected across the interface,
and the reflection returns through `T`.

## Main declarations

* `EllipticPdes.Extension.aboveGraph`: the region above the graph of a chart.
* `EllipticPdes.Extension.preimage_shear_aboveGraph`: the shear pulls that region back to the
  half space.
* `EllipticPdes.Extension.chartExt` and `EllipticPdes.Extension.chartExtGrad`: the extension
  and its gradient.
* `EllipticPdes.Extension.hasWeakGradOn_chartExt`: the extension has that weak gradient on the
  whole space.
* `EllipticPdes.Extension.chartExt_eq_of_mem`: the extension agrees with the class on the
  region it extends.
* `EllipticPdes.Extension.eLpNorm_chartExt_le` and
  `EllipticPdes.Extension.eLpNorm_chartExtGrad_le`: the extension and its gradient, bounded in
  every `Lᵖ` seminorm.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem III.2.2
steps 1 and 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1
and §C.1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The region above a graph -/

/-- **Region above the graph of a chart**, in the `j`-th coordinate. -/
def aboveGraph (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := {y | γ y < y j}

theorem isOpen_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    IsOpen (aboveGraph j γ) :=
  isOpen_lt hγ (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous

/-- The `j`-th coordinate of a sheared point. -/
theorem shear_coord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (y : EuclideanSpace ℝ (Fin d)) : (shear j γ y) j = y j + γ y := by
  simp [shear]

/-- **Pull-back of the half space through the flattening.** -/
theorem aboveGraph_eq_preimage {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} :
    aboveGraph j γ = shear j (fun z => -γ z) ⁻¹' halfSpace j := by
  ext y
  have hc : (shear j (fun z => -γ z) y) j = y j - γ y := by
    rw [shear_coord]; ring
  simp only [aboveGraph, Set.mem_preimage, halfSpace, Set.mem_ofPred_eq, hc]
  constructor <;> intro h <;> linarith

/-- **Pull-back of the region above the graph through the shear.** -/
theorem preimage_shear_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) : shear j γ ⁻¹' aboveGraph j γ = halfSpace j := by
  ext x
  have hγS : γ (shear j γ x) = γ x := hind x (γ x)
  simp only [Set.mem_preimage, aboveGraph, halfSpace, Set.mem_ofPred_eq, shear_coord, hγS]
  constructor <;> intro h <;> linarith

/-! ### The extension -/

/-- **Gradient of a class pulled back through the shear**, the transpose of the shear's
derivative applied to the gradient. -/
def shearGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => g k (shear j γ x) + g j (shear j γ x) * partialD k γ x

/-- **Extension across a `C¹` boundary chart.** The chart is flattened by the shear, the
flattened class is reflected across the interface, and the reflection returns through the
inverse shear. -/
def chartExt (j : Fin d) (γ u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => evenExt j (fun x => u (shear j γ x)) (shear j (fun z => -γ z) y)

/-- **Gradient of the extension across a `C¹` boundary chart.** The second term is the shear's
own contribution, with the sign of the inverse chart. -/
def chartExtGrad (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun y => evenExtGrad j (shearGrad j γ g) k (shear j (fun z => -γ z) y)
    - evenExtGrad j (shearGrad j γ g) j (shear j (fun z => -γ z) y) * partialD k γ y

/-- The partial derivative of a negated chart. -/
theorem partialD_neg {γ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : partialD k (fun z => -γ z) y = -partialD k γ y := by
  simp only [partialD, fderiv_fun_neg, _root_.neg_apply]

/-- **Weak gradient of the extension across a `C¹` boundary chart**, on the whole space. The
class travels through the shear onto the half space, the reflection extends it across the
interface, and the inverse shear returns it, each of the three steps supplying its own half of
the gradient. -/
theorem hasWeakGradOn_chartExt {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (aboveGraph j γ) volume)
    (hgi : ∀ k, IntegrableOn (g k) (aboveGraph j γ) volume)
    (hwg : HasWeakGradOn (aboveGraph j γ) u g) :
    HasWeakGradOn Set.univ (chartExt j γ u) (chartExtGrad j γ g) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hnegC1 : ContDiff ℝ 1 fun z => -γ z := hγ.neg
  have hnegd : Differentiable ℝ fun z => -γ z := hγd.neg
  have hckc : ∀ k : Fin d, Continuous (partialD k γ) := fun _ =>
    (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hnegb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k (fun z => -γ z) y‖ ≤ M := by
    intro k y
    rw [partialD_neg, norm_neg]
    exact hγb k y
  -- the class and its gradient, moved onto the half space
  have hmpS : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγd hind
  have hmeS : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγd.continuous hind
  have htrans : ∀ w : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn w (aboveGraph j γ) volume →
      IntegrableOn (fun x => w (shear j γ x)) (halfSpace j) volume := by
    intro w hw
    have h := (hmpS.integrableOn_comp_preimage hmeS (f := w) (s := aboveGraph j γ)).mpr hw
    rwa [preimage_shear_aboveGraph hind] at h
  have hgS : ∀ k, IntegrableOn (shearGrad j γ g k) (halfSpace j) volume := by
    intro k
    exact (htrans (g k) (hgi k)).add
      (integrableOn_mul_bounded (htrans (g j) (hgi j)) (hckc k) (hγb k))
  have hS : HasWeakGradOn (halfSpace j) (fun x => u (shear j γ x)) (shearGrad j γ g) := by
    have h := hasWeakGradOn_comp_shear (isOpen_aboveGraph hγd.continuous) hu hgi hwg hγ hind hγb
    rwa [preimage_shear_aboveGraph hind] at h
  -- reflected across the interface
  have hEven : HasWeakGradOn Set.univ (evenExt j fun x => u (shear j γ x))
      (evenExtGrad j (shearGrad j γ g)) :=
    hasWeakGradOn_evenExt (htrans u hu) hgS hS
  -- returned through the inverse shear
  have hFinal := hasWeakGradOn_comp_shear (B := Set.univ) isOpen_univ
    (integrable_evenExt (htrans u hu)).integrableOn
    (fun k => (integrable_evenExtGrad k (hgS k)).integrableOn)
    hEven hnegC1 hind.neg hnegb
  rw [Set.preimage_univ] at hFinal
  have hgrad : chartExtGrad j γ g
      = fun k y => evenExtGrad j (shearGrad j γ g) k (shear j (fun z => -γ z) y)
        + evenExtGrad j (shearGrad j γ g) j (shear j (fun z => -γ z) y)
          * partialD k (fun z => -γ z) y := by
    funext k y
    simp only [chartExtGrad, partialD_neg]
    ring
  rw [hgrad]
  exact hFinal

/-- **Agreement of the extension with the class on the region it extends.** -/
theorem chartExt_eq_of_mem {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j γ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ aboveGraph j γ) : chartExt j γ u y = u y := by
  have hmem : shear j (fun z => -γ z) y ∈ halfSpace j := by
    rw [aboveGraph_eq_preimage] at hy
    exact hy
  have h0 : (0 : ℝ) ≤ (shear j (fun z => -γ z) y) j := le_of_lt hmem
  simp only [chartExt, evenExt]
  rw [ite_eq_left h0, shear_neg_shear hind y]

/-- **Bound on the extension in every `Lᵖ` seminorm.** Both shears preserve measure and the
reflection doubles, so the extension over the whole space is bounded by twice the seminorm over
the region above the graph. -/
theorem eLpNorm_chartExt_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (aboveGraph j γ))) :
    eLpNorm (chartExt j γ u) p volume
      ≤ 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by
  have hnegd : Differentiable ℝ fun z => -γ z := hγ.neg
  have hmpS : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγ hind
  have hmeS : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγ.continuous hind
  -- the flattened class, on the half space
  have hres : MeasurePreserving (shear j γ) (volume.restrict (halfSpace j))
      (volume.restrict (aboveGraph j γ)) := by
    have h := hmpS.restrict_preimage_emb hmeS (aboveGraph j γ)
    rwa [preimage_shear_aboveGraph hind] at h
  have hvm : AEStronglyMeasurable (fun x => u (shear j γ x))
      (volume.restrict (halfSpace j)) := hu.comp_measurePreserving hres
  have hveq : eLpNorm (fun x => u (shear j γ x)) p (volume.restrict (halfSpace j))
      = eLpNorm u p (volume.restrict (aboveGraph j γ)) :=
    eLpNorm_comp_measurePreserving hu hres
  -- the reflection, returned through the inverse shear
  have hem : AEStronglyMeasurable (evenExt j fun x => u (shear j γ x)) volume :=
    aestronglyMeasurable_evenExt hvm
  have hback : eLpNorm (chartExt j γ u) p volume
      = eLpNorm (evenExt j fun x => u (shear j γ x)) p volume :=
    eLpNorm_comp_measurePreserving hem (measurePreserving_shear hnegd hind.neg)
  calc eLpNorm (chartExt j γ u) p volume
      = eLpNorm (evenExt j fun x => u (shear j γ x)) p volume := hback
    _ ≤ 2 * eLpNorm (fun x => u (shear j γ x)) p (volume.restrict (halfSpace j)) :=
        eLpNorm_evenExt_le hp hvm
    _ = 2 * eLpNorm u p (volume.restrict (aboveGraph j γ)) := by rw [hveq]

/-! ### The gradient's bound -/

/-- **Restriction of the shear to the half space**, preserving measure onto the region above
the graph. -/
theorem measurePreserving_shear_halfSpace {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) :
    MeasurePreserving (shear j γ) (volume.restrict (halfSpace j))
      (volume.restrict (aboveGraph j γ)) := by
  have h := (measurePreserving_shear hγ hind).restrict_preimage_emb
    (measurableEmbedding_shear hγ.continuous hind) (aboveGraph j γ)
  rwa [preimage_shear_aboveGraph hind] at h

/-- **Normal component of the gradient through the shear**, untouched, the chart having no
partial derivative in the direction it is a graph in. -/
theorem shearGrad_normal {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    shearGrad j γ g j = fun x => g j (shear j γ x) := by
  funext x
  have hz : partialD j γ x = 0 := partialD_eq_zero_of_indepCoord hγ hind x
  simp only [shearGrad, hz, mul_zero, add_zero]

/-- **Scaling of an `Lᵖ` seminorm by a bounded factor.** -/
theorem eLpNorm'_mul_bounded_le {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {f h : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖h x‖ ≤ C)
    {p : ℝ} (hp : 0 < p) : eLpNorm' (fun x => f x * h x) p μ ≤ ENNReal.ofReal C * eLpNorm' f p
        μ := by
  have hnorm : ‖C‖ₑ = ENNReal.ofReal C := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC0]
  have h1 : eLpNorm' (fun x => f x * h x) p μ ≤ eLpNorm' (C • f) p μ := by
    refine eLpNorm'_mono_ae hp.le (Filter.Eventually.of_forall fun x => ?_)
    have hs : ‖(C • f) x‖ = C * ‖f x‖ := by
      simp [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hC0]
    rw [norm_mul, hs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [eLpNorm'_const_smul _ hp, hnorm]

/-- **Scaling of an `Lᵖ` seminorm by a bounded factor.** -/
theorem eLpNorm_mul_bounded_le {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {f h : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖h x‖ ≤ C)
    {p : ℝ≥0∞} (hfh : AEStronglyMeasurable (fun x => f x * h x) μ) : eLpNorm (fun x => f x * h
        x) p μ ≤ ENNReal.ofReal C * eLpNorm f p μ := by
  have hnorm : ‖C‖ₑ = ENNReal.ofReal C := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC0]
  have h1 : eLpNorm (fun x => f x * h x) p μ ≤ eLpNorm (C • f) p μ := by
    refine eLpNorm_mono_ae hfh (Filter.Eventually.of_forall fun x => ?_)
    have hs : ‖(C • f) x‖ = C * ‖f x‖ := by
      simp [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hC0]
    rw [norm_mul, hs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [eLpNorm_const_smul, hnorm]

/-- **Bound on the transported gradient**, componentwise. The shear contributes the chart's
bound against the normal component. -/
theorem eLpNorm_shearGrad_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ} (hM0 : 0 ≤ M)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgm : ∀ k, AEStronglyMeasurable (g k) (volume.restrict (aboveGraph j γ))) (k : Fin d) :
    eLpNorm (shearGrad j γ g k) p (volume.restrict (halfSpace j))
      ≤ eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hres := measurePreserving_shear_halfSpace hγd hind
  have hckc : Continuous (partialD k γ) :=
    (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp : ∀ i, AEStronglyMeasurable (fun x => g i (shear j γ x))
      (volume.restrict (halfSpace j)) := fun i => (hgm i).comp_measurePreserving hres
  have heq : ∀ i, eLpNorm (fun x => g i (shear j γ x)) p (volume.restrict (halfSpace j))
      = eLpNorm (g i) p (volume.restrict (aboveGraph j γ)) := fun i =>
    eLpNorm_comp_measurePreserving (hgm i) hres
  calc eLpNorm (shearGrad j γ g k) p (volume.restrict (halfSpace j))
      ≤ eLpNorm (fun x => g k (shear j γ x)) p (volume.restrict (halfSpace j))
        + eLpNorm (fun x => g j (shear j γ x) * partialD k γ x) p
            (volume.restrict (halfSpace j)) :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
        rw [heq k, ← heq j]
        exact add_le_add le_rfl (eLpNorm_mul_bounded_le hM0 (hγb k)
          ((hcomp j).mul hckc.aestronglyMeasurable))

/-- **Bound on the gradient of the extension across a `C¹` boundary chart.** Each of the three
maps plays its part: the shear contributes the chart's bound against the normal component, the
reflection doubles, and the inverse shear contributes the bound again. -/
theorem eLpNorm_chartExtGrad_le {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ} (hM0 : 0 ≤ M)
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgm : ∀ k, AEStronglyMeasurable (g k) (volume.restrict (aboveGraph j γ))) (k : Fin d) :
    eLpNorm (chartExtGrad j γ g k) p volume
      ≤ 2 * eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + 4 * ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hnegd : Differentiable ℝ fun z => -γ z := hγd.neg
  have hres := measurePreserving_shear_halfSpace hγd hind
  have hckc : Continuous (partialD k γ) :=
    (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp : ∀ i, AEStronglyMeasurable (fun x => g i (shear j γ x))
      (volume.restrict (halfSpace j)) := fun i => (hgm i).comp_measurePreserving hres
  have hsgm : ∀ i, AEStronglyMeasurable (shearGrad j γ g i)
      (volume.restrict (halfSpace j)) := by
    intro i
    have hci : Continuous (partialD i γ) :=
      (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hcomp i).add ((hcomp j).mul hci.aestronglyMeasurable)
  -- the extended gradient, and its bound on the half space
  have hHm : ∀ i, AEStronglyMeasurable (evenExtGrad j (shearGrad j γ g) i) volume := fun i =>
    aestronglyMeasurable_evenExtGrad i (hsgm i)
  have hH : ∀ i, eLpNorm (evenExtGrad j (shearGrad j γ g) i) p volume
      ≤ 2 * eLpNorm (shearGrad j γ g i) p (volume.restrict (halfSpace j)) := fun i =>
    eLpNorm_evenExtGrad_le i hp (hsgm i)
  -- the inverse shear preserves the seminorm
  have hmpT : MeasurePreserving (shear j fun z => -γ z) volume volume :=
    measurePreserving_shear hnegd hind.neg
  have hback : ∀ i, eLpNorm (evenExtGrad j (shearGrad j γ g) i ∘ shear j fun z => -γ z)
      p volume = eLpNorm (evenExtGrad j (shearGrad j γ g) i) p volume := fun i =>
    eLpNorm_comp_measurePreserving (hHm i) hmpT
  have hTm : ∀ i, AEStronglyMeasurable
      (evenExtGrad j (shearGrad j γ g) i ∘ shear j fun z => -γ z) volume := fun i =>
    (hHm i).comp_measurePreserving hmpT
  -- the normal component travels untouched, so its bound has no chart factor
  have hjbound : eLpNorm (shearGrad j γ g j) p (volume.restrict (halfSpace j))
      = eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
    rw [shearGrad_normal hγd hind g]
    exact eLpNorm_comp_measurePreserving (hgm j) hres
  have hsplit : chartExtGrad j γ g k
      = (evenExtGrad j (shearGrad j γ g) k ∘ shear j fun z => -γ z)
        - fun y => (evenExtGrad j (shearGrad j γ g) j ∘ shear j fun z => -γ z) y
            * partialD k γ y := rfl
  rw [hsplit]
  calc eLpNorm ((evenExtGrad j (shearGrad j γ g) k ∘ shear j fun z => -γ z)
        - fun y => (evenExtGrad j (shearGrad j γ g) j ∘ shear j fun z => -γ z) y
            * partialD k γ y) p volume
      ≤ eLpNorm (evenExtGrad j (shearGrad j γ g) k ∘ shear j fun z => -γ z) p volume
        + eLpNorm (fun y => (evenExtGrad j (shearGrad j γ g) j ∘ shear j fun z => -γ z) y
            * partialD k γ y) p volume :=
        eLpNorm_sub_le hp
    _ ≤ 2 * (eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
          + ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)))
        + ENNReal.ofReal M * (2 * eLpNorm (g j) p (volume.restrict (aboveGraph j γ))) := by
        refine add_le_add ?_ ?_
        · refine ((hback k).le.trans (hH k)).trans ?_
          exact mul_le_mul_right (eLpNorm_shearGrad_le hγ hind hM0 hγb hp hgm k) 2
        · refine (eLpNorm_mul_bounded_le hM0 (hγb k)
            ((hTm j).mul hckc.aestronglyMeasurable)).trans ?_
          refine mul_le_mul_right (((hback j).le.trans (hH j)).trans ?_) _
          exact le_of_eq (by rw [hjbound])
    _ = 2 * eLpNorm (g k) p (volume.restrict (aboveGraph j γ))
        + 4 * ENNReal.ofReal M * eLpNorm (g j) p (volume.restrict (aboveGraph j γ)) := by
        ring

end EllipticPdes.Extension
