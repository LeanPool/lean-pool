/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.HalfSpace


/-!
# Extension across a flat boundary by reflection

A Sobolev class on the half space extends across the interface by reflecting it: the value at a
point below the interface is the value at its mirror image. The gradient extends the same way,
with a sign in the normal direction, and the extended pair is a weak gradient on the whole
space.

The identity is tested against an arbitrary test function of the whole space. Splitting the
integral at the interface and reflecting the lower half turns it into an integral over the half
space, tested against `φ + s (φ ∘ R)` with `s` the sign of the direction. In the normal
direction that combination is odd, so it vanishes on the interface, which is exactly the
hypothesis under which the boundary term of `EllipticPdes.Extension.integral_partialD_of_eq`
disappears.

## Main declarations

* `EllipticPdes.Extension.evenExt`: the reflected extension of a function.
* `EllipticPdes.Extension.evenExtGrad`: the reflected extension of its gradient.
* `EllipticPdes.Extension.integral_split_interface`: an integral splits at the interface.
* `EllipticPdes.Extension.hasWeakGradOn_evenExt`: the weak gradient of the extension.
* `EllipticPdes.Extension.eLpNorm_evenExt_le`: its bound in every `Lᵖ` seminorm.
* `EllipticPdes.Extension.aestronglyMeasurable_evenExt`: the extension is measurable.
* `EllipticPdes.Extension.eLpNorm_evenExtGrad_le`: the gradient's bound in every `Lᵖ` seminorm.
* `EllipticPdes.Extension.integrable_evenExt` and
  `EllipticPdes.Extension.integrable_evenExtGrad`: the extension and its gradient are
  integrable on the whole space whenever the class is integrable on the half space.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)
open EllipticPdes.Embedding (HasWeakGradOn)

variable {d : ℕ}

/-- The open half space below the interface. -/
def halfSpaceNeg (j : Fin d) : Set (EuclideanSpace ℝ (Fin d)) := {x | x j < 0}

theorem measurableSet_halfSpaceNeg (j : Fin d) : MeasurableSet (halfSpaceNeg j) :=
  (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const).measurableSet

theorem disjoint_halfSpace (j : Fin d) : Disjoint (halfSpace j) (halfSpaceNeg j) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : 0 < x j := hx
  have h2 : x j < 0 := hx'
  linarith

/-- Up to the null interface, the whole space is the union of the two open half spaces. -/
theorem univ_ae_eq_union (j : Fin d) :
    (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      =ᵐ[volume] ((halfSpace j ∪ halfSpaceNeg j : Set (EuclideanSpace ℝ (Fin d)))) := by
  have hdiff : (Set.univ : Set (EuclideanSpace ℝ (Fin d))) \ (halfSpace j ∪ halfSpaceNeg j)
      = {x : EuclideanSpace ℝ (Fin d) | x j = 0} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_union, halfSpace, halfSpaceNeg,
      Set.mem_ofPred_eq, not_or, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · rintro h; exact ⟨by linarith, by linarith⟩
  refine (MeasureTheory.ae_eq_set).mpr ⟨?_, ?_⟩
  · rw [hdiff]; exact volume_interface j
  · have : (halfSpace j ∪ halfSpaceNeg j) \ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) = ∅ := by
      simp
    rw [this]
    simp

/-- **Splitting of an integral over the whole space at the interface.** -/
theorem integral_split_interface {j : Fin d} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h1 : IntegrableOn f (halfSpace j) volume) (h2 : IntegrableOn f (halfSpaceNeg j) volume) :
    ∫ x, f x = (∫ x in halfSpace j, f x) + ∫ x in halfSpaceNeg j, f x := by
  rw [← setIntegral_univ, setIntegral_congr_set (univ_ae_eq_union j),
    setIntegral_union (disjoint_halfSpace j) (measurableSet_halfSpaceNeg j) h1 h2]

/-! ### The reflected extension -/

/-- **Reflected extension of a function**: below the interface it takes the value at the
mirror image. -/
def evenExt (j : Fin d) (u : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => if 0 ≤ x j then u x else u (reflectLI j x)

/-- **Reflected extension of a gradient**, with a sign in the normal direction. -/
def evenExtGrad (j : Fin d) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => if 0 ≤ x j then g k x else reflectSign j k * g k (reflectLI j x)

theorem preimage_reflectLI_halfSpaceNeg (j : Fin d) :
    reflectLI j ⁻¹' halfSpaceNeg j = halfSpace j := by
  ext x
  have h : reflectLI j x j = -(x j) := by
    rw [reflectLI_apply, reflectSign, ite_eq_left rfl]; ring
  simp only [Set.mem_preimage, halfSpaceNeg, halfSpace, Set.mem_ofPred_eq, h, neg_lt_zero]

/-- **Integral over the lower half space as the reflected integral over the upper one.** -/
theorem setIntegral_halfSpaceNeg (j : Fin d) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ x in halfSpaceNeg j, f x = ∫ y in halfSpace j, f (reflectLI j y) := by
  have h := (measurePreserving_reflectLI j).setIntegral_preimage_emb
    (measurableEmbedding_reflectLI j) f (halfSpaceNeg j)
  rw [preimage_reflectLI_halfSpaceNeg] at h
  exact h.symm

/-- The partial derivative is additive. -/
theorem partialD_add {f h : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    {x : EuclideanSpace ℝ (Fin d)} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    partialD k (fun y => f y + h y) x = partialD k f x + partialD k h x := by
  have hfd : HasFDerivAt (fun y => f y + h y) (fderiv ℝ f x + fderiv ℝ h x) x :=
    hf.hasFDerivAt.add hh.hasFDerivAt
  rw [partialD, hfd.fderiv]
  simp [partialD]

/-- The partial derivative commutes with a constant multiple. -/
theorem partialD_const_mul {f : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hf : DifferentiableAt ℝ f x) :
    partialD k (fun y => c * f y) x = c * partialD k f x := by
  have hfd : HasFDerivAt (fun y => c * f y) (c • fderiv ℝ f x) x :=
    hf.hasFDerivAt.const_mul c
  rw [partialD, hfd.fderiv]
  simp [partialD]

/-- The reflection fixes the interface. -/
theorem reflectLI_eq_self_of_interface {j : Fin d} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x j = 0) : reflectLI j x = x := by
  ext m
  rw [reflectLI_apply, reflectSign]
  by_cases hm : m = j
  · subst hm; rw [ite_eq_left rfl, hx]; ring
  · rw [ite_eq_right hm]; ring

/-- **Weak gradient of the reflected extension on the whole space.** Splitting the integral
at the interface and reflecting the lower half tests the class against `φ + s (φ ∘ R)`, which in
the normal direction is odd and so vanishes on the interface. That is the hypothesis under which
no boundary term survives. -/
theorem hasWeakGradOn_evenExt {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (halfSpace j) volume)
    (hg : ∀ k, IntegrableOn (g k) (halfSpace j) volume)
    (hwg : HasWeakGradOn (halfSpace j) u g) :
    HasWeakGradOn Set.univ (evenExt j u) (evenExtGrad j g) := by
  intro φ hφ hφcs _hsupp k
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set s : ℝ := reflectSign j k with hs
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => φ x + s * φ (reflectLI j x) with hψdef
  have hφR : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (reflectLI j y)) := contDiff_comp_reflect hφ j
  have hφRd : Differentiable ℝ (fun y => φ (reflectLI j y)) := hφR.differentiable (by simp)
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.add (contDiff_const.mul hφR)
  have hψcs : HasCompactSupport ψ :=
    hφcs.add ((hasCompactSupport_comp_reflect hφcs j).mul_left)
  -- The derivative of the combination, and the reflected derivative.
  have hpartial : ∀ x, partialD k ψ x
      = partialD k φ x + s * partialD k (fun z => φ (reflectLI j z)) x := by
    intro x
    rw [hψdef, partialD_add k (hφd x) ((hφRd x).const_mul s),
      partialD_const_mul k s (hφRd x)]
  have hrefl : ∀ y, partialD k φ (reflectLI j y)
      = s * partialD k (fun z => φ (reflectLI j z)) y := by
    intro y
    rw [partialD_comp_reflect hφd j k y, ← mul_assoc, hs, reflectSign_mul_self, one_mul]
  -- The two halves of the extension.
  have hExtPos : ∀ x ∈ halfSpace j, evenExt j u x = u x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x j := le_of_lt hx
    change (if 0 ≤ x j then u x else u (reflectLI j x)) = u x
    rw [ite_eq_left hx0]
  have hExtNeg : ∀ y ∈ halfSpace j, evenExt j u (reflectLI j y) = u y := by
    intro y hy
    have hyj : 0 < y j := hy
    have hRy : reflectLI j y j = -(y j) := by
      rw [reflectLI_apply, reflectSign, ite_eq_left rfl]; ring
    have hneg : ¬ (0 : ℝ) ≤ reflectLI j y j := by rw [hRy]; linarith
    change (if 0 ≤ reflectLI j y j then u (reflectLI j y)
      else u (reflectLI j (reflectLI j y))) = u y
    rw [ite_eq_right hneg, reflectLI_involutive]
  have hGradPos : ∀ x ∈ halfSpace j, evenExtGrad j g k x = g k x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x j := le_of_lt hx
    change (if 0 ≤ x j then g k x else reflectSign j k * g k (reflectLI j x)) = g k x
    rw [ite_eq_left hx0]
  have hGradNeg : ∀ y ∈ halfSpace j, evenExtGrad j g k (reflectLI j y) = s * g k y := by
    intro y hy
    have hyj : 0 < y j := hy
    have hRy : reflectLI j y j = -(y j) := by
      rw [reflectLI_apply, reflectSign, ite_eq_left rfl]; ring
    have hneg : ¬ (0 : ℝ) ≤ reflectLI j y j := by rw [hRy]; linarith
    change (if 0 ≤ reflectLI j y j then g k (reflectLI j y)
      else reflectSign j k * g k (reflectLI j (reflectLI j y))) = s * g k y
    rw [ite_eq_right hneg, reflectLI_involutive, hs]
  -- Bounds, for the integrability side conditions.
  obtain ⟨N, hN⟩ := (hφcs.fderiv ℝ).comp_left
    (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => T (EuclideanSpace.single k (1 : ℝ)))
    (by simp) |>.exists_bound_of_continuous
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨P, hP⟩ := hφcs.exists_bound_of_continuous hφ.continuous
  have hdφc : Continuous (partialD k φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφRc : Continuous (partialD k (fun z => φ (reflectLI j z))) :=
    (hφR.continuous_fderiv (by simp)).clm_apply continuous_const
  have habs : |s| = 1 := by
    rw [hs, reflectSign]
    split <;> norm_num
  -- Integrability of the four pieces on the half space.
  have hi1 : IntegrableOn (fun x => u x * partialD k φ x) (halfSpace j) volume :=
    hu.mul_bdd hdφc.aestronglyMeasurable (Filter.Eventually.of_forall hN)
  have hi2 : IntegrableOn (fun y => u y * (s * partialD k (fun z => φ (reflectLI j z)) y))
      (halfSpace j) volume := by
    refine hu.mul_bdd (c := N) ((continuous_const.mul hdφRc)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, habs, one_mul]
    have : partialD k (fun z => φ (reflectLI j z)) y = s * partialD k φ (reflectLI j y) := by
      rw [partialD_comp_reflect hφd j k y, hs]
    rw [this, norm_mul, Real.norm_eq_abs, habs, one_mul]
    exact hN _
  have hi3 : IntegrableOn (fun x => g k x * φ x) (halfSpace j) volume :=
    (hg k).mul_bdd hφ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hP)
  have hi4 : IntegrableOn (fun y => g k y * (s * φ (reflectLI j y))) (halfSpace j) volume := by
    refine (hg k).mul_bdd (c := P) ((continuous_const.mul (hφ.continuous.comp
      (reflectLI j).continuous))).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, habs, one_mul]
    exact hP _
  -- The left-hand side, moved onto the half space.
  have hLHS : ∫ x in Set.univ, evenExt j u x * partialD k φ x
      = ∫ y in halfSpace j, u y * partialD k ψ y := by
    have hj1 : IntegrableOn (fun x => evenExt j u x * partialD k φ x) (halfSpace j) volume :=
      hi1.congr_fun (fun x hx => by rw [hExtPos x hx]) (measurableSet_halfSpace j)
    have hj2 : IntegrableOn (fun x => evenExt j u x * partialD k φ x)
        (halfSpaceNeg j) volume := by
      rw [← (measurePreserving_reflectLI j).integrableOn_comp_preimage
        (measurableEmbedding_reflectLI j), preimage_reflectLI_halfSpaceNeg]
      refine hi2.congr_fun (fun y hy => ?_) (measurableSet_halfSpace j)
      change u y * (s * partialD k (fun z => φ (reflectLI j z)) y)
        = evenExt j u (reflectLI j y) * partialD k φ (reflectLI j y)
      rw [hExtNeg y hy, hrefl y]
    rw [setIntegral_univ, integral_split_interface hj1 hj2, setIntegral_halfSpaceNeg]
    have hsecond : ∫ y in halfSpace j,
        evenExt j u (reflectLI j y) * partialD k φ (reflectLI j y)
        = ∫ y in halfSpace j, u y * (s * partialD k (fun z => φ (reflectLI j z)) y) := by
      refine setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => ?_
      rw [hExtNeg y hy, hrefl y]
    rw [hsecond, ← integral_add hj1 hi2]
    refine setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => ?_
    change evenExt j u y * partialD k φ y
        + u y * (s * partialD k (fun z => φ (reflectLI j z)) y)
      = u y * partialD k ψ y
    rw [hExtPos y hy, hpartial y]
    ring
  -- The right-hand side, the same way.
  have hRHS : ∫ x in Set.univ, evenExtGrad j g k x * φ x
      = ∫ y in halfSpace j, g k y * ψ y := by
    have hj3 : IntegrableOn (fun x => evenExtGrad j g k x * φ x) (halfSpace j) volume :=
      hi3.congr_fun (fun x hx => by rw [hGradPos x hx]) (measurableSet_halfSpace j)
    have hj4 : IntegrableOn (fun x => evenExtGrad j g k x * φ x) (halfSpaceNeg j) volume := by
      rw [← (measurePreserving_reflectLI j).integrableOn_comp_preimage
        (measurableEmbedding_reflectLI j), preimage_reflectLI_halfSpaceNeg]
      refine hi4.congr_fun (fun y hy => ?_) (measurableSet_halfSpace j)
      change g k y * (s * φ (reflectLI j y))
        = evenExtGrad j g k (reflectLI j y) * φ (reflectLI j y)
      rw [hGradNeg y hy]
      ring
    rw [setIntegral_univ, integral_split_interface hj3 hj4, setIntegral_halfSpaceNeg]
    have hsecond : ∫ y in halfSpace j, evenExtGrad j g k (reflectLI j y) * φ (reflectLI j y)
        = ∫ y in halfSpace j, g k y * (s * φ (reflectLI j y)) := by
      refine setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => ?_
      rw [hGradNeg y hy]
      ring
    rw [hsecond, ← integral_add hj3 hi4]
    refine setIntegral_congr_fun (measurableSet_halfSpace j) fun y hy => ?_
    change evenExtGrad j g k y * φ y + g k y * (s * φ (reflectLI j y)) = g k y * ψ y
    rw [hGradPos y hy, hψdef]
    ring
  rw [hLHS, hRHS]
  by_cases hk : k = j
  · subst hk
    refine integral_partialD_of_eq hu (hg k) hwg hψsmooth hψcs (fun z hz => ?_)
    rw [hψdef]
    simp only
    rw [reflectLI_eq_self_of_interface hz, hs, reflectSign, ite_eq_left rfl]
    ring
  · exact integral_partialD_of_ne hk hu (hg k) hwg hψsmooth hψcs

/-! ### The bound -/

/-- The extension is, almost everywhere, the sum of the class and its reflection, each on its
own side of the interface. -/
theorem evenExt_ae_eq (j : Fin d) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    evenExt j u =ᵐ[volume] fun x => (halfSpace j).indicator u x
      + (halfSpaceNeg j).indicator (fun y => u (reflectLI j y)) x := by
  have hnull : volume {x : EuclideanSpace ℝ (Fin d) | x j = 0} = 0 := volume_interface j
  refine (MeasureTheory.ae_iff).mpr (measure_mono_null ?_ hnull)
  intro x hx
  simp only [Set.mem_ofPred_eq]
  by_contra hne
  refine hx ?_
  rcases lt_trichotomy (x j) 0 with h | h | h
  · have h1 : ¬ (0 : ℝ) ≤ x j := by linarith
    have h2 : x ∉ halfSpace j := by
      intro hmem
      exact absurd (lt_trans hmem h) (lt_irrefl 0)
    change (if 0 ≤ x j then u x else u (reflectLI j x))
      = (halfSpace j).indicator u x + (halfSpaceNeg j).indicator (fun y => u (reflectLI j y)) x
    have hmemNeg : x ∈ halfSpaceNeg j := h
    rw [ite_eq_right h1, Set.indicator_of_notMem h2, Set.indicator_of_mem hmemNeg, zero_add]
  · exact absurd h hne
  · have h2 : x ∉ halfSpaceNeg j := by
      intro hmem
      exact absurd (lt_trans h hmem) (lt_irrefl 0)
    change (if 0 ≤ x j then u x else u (reflectLI j x))
      = (halfSpace j).indicator u x + (halfSpaceNeg j).indicator (fun y => u (reflectLI j y)) x
    have hmemPos : x ∈ halfSpace j := h
    rw [ite_eq_left h.le, Set.indicator_of_notMem h2, Set.indicator_of_mem hmemPos, add_zero]

/-- **Reflection of the lower half space onto the upper one**, preserving measure. -/
theorem measurePreserving_reflectLI_halfSpaceNeg (j : Fin d) :
    MeasurePreserving (reflectLI j) (volume.restrict (halfSpaceNeg j))
      (volume.restrict (halfSpace j)) := by
  have h := (measurePreserving_reflectLI j).restrict_preimage_emb
    (measurableEmbedding_reflectLI j) (halfSpace j)
  rwa [show reflectLI j ⁻¹' halfSpace j = halfSpaceNeg j from by
    rw [← preimage_reflectLI_halfSpaceNeg j, reflectLI_preimage_preimage]] at h

/-- **Bound for the extension in every `Lᵖ` seminorm.** The reflection preserves
measure, so each side contributes the seminorm on the half space. -/
theorem eLpNorm_evenExt_le {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hu : AEStronglyMeasurable u (volume.restrict (halfSpace j))) :
    eLpNorm (evenExt j u) p volume ≤ 2 * eLpNorm u p (volume.restrict (halfSpace j)) := by
  have hmp : MeasurePreserving (reflectLI j) (volume.restrict (halfSpaceNeg j))
      (volume.restrict (halfSpace j)) := measurePreserving_reflectLI_halfSpaceNeg j
  have hu' : AEStronglyMeasurable (fun y => u (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) := hu.comp_measurePreserving hmp
  have h1 : AEStronglyMeasurable ((halfSpace j).indicator u) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpace j)).mpr hu
  have h2 : AEStronglyMeasurable
      ((halfSpaceNeg j).indicator (fun y => u (reflectLI j y))) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpaceNeg j)).mpr hu'
  calc eLpNorm (evenExt j u) p volume
      = eLpNorm (fun x => (halfSpace j).indicator u x
          + (halfSpaceNeg j).indicator (fun y => u (reflectLI j y)) x) p volume :=
        eLpNorm_congr_ae (evenExt_ae_eq j u)
    _ ≤ eLpNorm ((halfSpace j).indicator u) p volume
        + eLpNorm ((halfSpaceNeg j).indicator (fun y => u (reflectLI j y))) p volume :=
        eLpNorm_add_le hp
    _ = eLpNorm u p (volume.restrict (halfSpace j))
        + eLpNorm u p (volume.restrict (halfSpace j)) := by
        have hcomp : eLpNorm (fun y => u (reflectLI j y)) p (volume.restrict (halfSpaceNeg j))
            = eLpNorm u p (volume.restrict (halfSpace j)) :=
          eLpNorm_comp_measurePreserving hu hmp
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpace j),
          eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpaceNeg j), hcomp]
    _ = 2 * eLpNorm u p (volume.restrict (halfSpace j)) := by
        rw [two_mul]

/-! ### Integrability of the extension -/

/-- The extended gradient is, almost everywhere, the sum of the component and its signed
reflection, each on its own side of the interface. -/
theorem evenExtGrad_ae_eq (j : Fin d) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    evenExtGrad j g k =ᵐ[volume] fun x => (halfSpace j).indicator (g k) x
      + (halfSpaceNeg j).indicator (fun y => reflectSign j k * g k (reflectLI j y)) x := by
  have hnull : volume {x : EuclideanSpace ℝ (Fin d) | x j = 0} = 0 := volume_interface j
  refine (MeasureTheory.ae_iff).mpr (measure_mono_null ?_ hnull)
  intro x hx
  simp only [Set.mem_ofPred_eq]
  by_contra hne
  refine hx ?_
  rcases lt_trichotomy (x j) 0 with h | h | h
  · have h1 : ¬ (0 : ℝ) ≤ x j := by linarith
    have h2 : x ∉ halfSpace j := by
      intro hmem
      exact absurd (lt_trans hmem h) (lt_irrefl 0)
    have hmemNeg : x ∈ halfSpaceNeg j := h
    change (if 0 ≤ x j then g k x else reflectSign j k * g k (reflectLI j x))
      = (halfSpace j).indicator (g k) x
        + (halfSpaceNeg j).indicator (fun y => reflectSign j k * g k (reflectLI j y)) x
    rw [ite_eq_right h1, Set.indicator_of_notMem h2, Set.indicator_of_mem hmemNeg, zero_add]
  · exact absurd h hne
  · have h2 : x ∉ halfSpaceNeg j := by
      intro hmem
      exact absurd (lt_trans h hmem) (lt_irrefl 0)
    have hmemPos : x ∈ halfSpace j := h
    change (if 0 ≤ x j then g k x else reflectSign j k * g k (reflectLI j x))
      = (halfSpace j).indicator (g k) x
        + (halfSpaceNeg j).indicator (fun y => reflectSign j k * g k (reflectLI j y)) x
    rw [ite_eq_left h.le, Set.indicator_of_notMem h2, Set.indicator_of_mem hmemPos, add_zero]

/-- **Measurability of the reflected extension**, from the description of it as a sum of two
indicators. -/
theorem aestronglyMeasurable_evenExt {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (halfSpace j))) :
    AEStronglyMeasurable (evenExt j u) volume := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have hu' : AEStronglyMeasurable (fun y => u (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) := hu.comp_measurePreserving hmp
  have h1 : AEStronglyMeasurable ((halfSpace j).indicator u) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpace j)).mpr hu
  have h2 : AEStronglyMeasurable ((halfSpaceNeg j).indicator fun y => u (reflectLI j y)) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpaceNeg j)).mpr hu'
  exact (h1.add h2).congr (evenExt_ae_eq j u).symm

/-- **Integrability of the reflected extension.** Each side of the interface contributes the
integral over the half space, the reflection preserving measure. -/
theorem integrable_evenExt {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u (halfSpace j) volume) : Integrable (evenExt j u) volume := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have h1 : Integrable ((halfSpace j).indicator u) volume :=
    hu.integrable_indicator (measurableSet_halfSpace j)
  have hrefl : IntegrableOn (fun y => u (reflectLI j y)) (halfSpaceNeg j) volume :=
    (hmp.integrable_comp_emb (measurableEmbedding_reflectLI j)).mpr hu
  have h2 : Integrable ((halfSpaceNeg j).indicator fun y => u (reflectLI j y)) volume :=
    hrefl.integrable_indicator (measurableSet_halfSpaceNeg j)
  exact (h1.add h2).congr (evenExt_ae_eq j u).symm

/-- **Integrability of the extended gradient**, componentwise. -/
theorem integrable_evenExtGrad {j : Fin d} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (k : Fin d) (hg : IntegrableOn (g k) (halfSpace j) volume) :
    Integrable (evenExtGrad j g k) volume := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have h1 : Integrable ((halfSpace j).indicator (g k)) volume :=
    hg.integrable_indicator (measurableSet_halfSpace j)
  have hr0 : IntegrableOn (fun y => g k (reflectLI j y)) (halfSpaceNeg j) volume :=
    (hmp.integrable_comp_emb (measurableEmbedding_reflectLI j)).mpr hg
  have hr1 : IntegrableOn (fun y => reflectSign j k * g k (reflectLI j y))
      (halfSpaceNeg j) volume := Integrable.const_mul hr0 _
  have h2 : Integrable ((halfSpaceNeg j).indicator
      fun y => reflectSign j k * g k (reflectLI j y)) volume :=
    hr1.integrable_indicator (measurableSet_halfSpaceNeg j)
  exact (h1.add h2).congr (evenExtGrad_ae_eq j g k).symm

/-! ### The gradient's bound -/

/-- The sign a reflection attaches to a direction has absolute value `1`. -/
theorem abs_reflectSign (j k : Fin d) : |reflectSign j k| = 1 := by
  rw [reflectSign]
  split_ifs <;> norm_num

/-- **Measurability of the extended gradient**, componentwise. -/
theorem aestronglyMeasurable_evenExtGrad {j : Fin d} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (k : Fin d) (hg : AEStronglyMeasurable (g k) (volume.restrict (halfSpace j))) :
    AEStronglyMeasurable (evenExtGrad j g k) volume := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have hg' : AEStronglyMeasurable (fun y => g k (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) := hg.comp_measurePreserving hmp
  have h1 : AEStronglyMeasurable ((halfSpace j).indicator (g k)) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpace j)).mpr hg
  have h2 : AEStronglyMeasurable ((halfSpaceNeg j).indicator
      fun y => reflectSign j k * g k (reflectLI j y)) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpaceNeg j)).mpr
      (hg'.const_mul (reflectSign j k))
  exact (h1.add h2).congr (evenExtGrad_ae_eq j g k).symm

/-- **Bound on the extended gradient in every `Lᵖ` seminorm.** The reflection preserves measure
and the sign has absolute value `1`, so each side contributes the seminorm on the half space. -/
theorem eLpNorm_evenExtGrad_le {j : Fin d} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (k : Fin d) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : AEStronglyMeasurable (g k) (volume.restrict (halfSpace j))) :
    eLpNorm (evenExtGrad j g k) p volume
      ≤ 2 * eLpNorm (g k) p (volume.restrict (halfSpace j)) := by
  have hmp := measurePreserving_reflectLI_halfSpaceNeg j
  have hg' : AEStronglyMeasurable (fun y => g k (reflectLI j y))
      (volume.restrict (halfSpaceNeg j)) := hg.comp_measurePreserving hmp
  have h1 : AEStronglyMeasurable ((halfSpace j).indicator (g k)) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpace j)).mpr hg
  have h2 : AEStronglyMeasurable ((halfSpaceNeg j).indicator
      fun y => reflectSign j k * g k (reflectLI j y)) volume :=
    (aestronglyMeasurable_indicator_iff (measurableSet_halfSpaceNeg j)).mpr
      (hg'.const_mul (reflectSign j k))
  have hsign : eLpNorm (fun y => reflectSign j k * g k (reflectLI j y)) p
      (volume.restrict (halfSpaceNeg j))
      ≤ eLpNorm (fun y => g k (reflectLI j y)) p (volume.restrict (halfSpaceNeg j)) := by
    refine eLpNorm_mono_ae (hg'.const_mul (reflectSign j k))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs (reflectSign j k), abs_reflectSign, one_mul]
  calc eLpNorm (evenExtGrad j g k) p volume
      = eLpNorm (fun x => (halfSpace j).indicator (g k) x
          + (halfSpaceNeg j).indicator (fun y => reflectSign j k * g k (reflectLI j y)) x)
          p volume := eLpNorm_congr_ae (evenExtGrad_ae_eq j g k)
    _ ≤ eLpNorm ((halfSpace j).indicator (g k)) p volume
        + eLpNorm ((halfSpaceNeg j).indicator
            fun y => reflectSign j k * g k (reflectLI j y)) p volume := eLpNorm_add_le hp
    _ ≤ eLpNorm (g k) p (volume.restrict (halfSpace j))
        + eLpNorm (g k) p (volume.restrict (halfSpace j)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpace j),
          eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_halfSpaceNeg j)]
        have hstep : eLpNorm (fun y => reflectSign j k * g k (reflectLI j y)) p
            (volume.restrict (halfSpaceNeg j))
            ≤ eLpNorm (g k) p (volume.restrict (halfSpace j)) :=
          hsign.trans (le_of_eq (eLpNorm_comp_measurePreserving hg hmp))
        exact add_le_add le_rfl hstep
    _ = 2 * eLpNorm (g k) p (volume.restrict (halfSpace j)) := by rw [two_mul]

end EllipticPdes.Extension
