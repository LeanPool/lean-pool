/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.CollarCover
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Summation of local Gaussian-cell estimates

Real-valued integral summation for the finite space-time covers used in
`eq:bu-gaussian-collar`.
-/

public section


open MeasureTheory Set

attribute [local instance] Classical.propDecidable
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- If a finite measurable family covers a set, its cell integrals dominate
the integral of every nonnegative function over that set. -/
theorem integral_le_sum_of_finite_cover
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α) (I : Finset ι) (U : ι → Set α)
    (f : α → ℝ) (hf : Integrable f μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hS : MeasurableSet S)
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ U i) :
    (∫ x in S, f x ∂μ) ≤ ∑ i ∈ I, ∫ x in U i, f x ∂μ := by
  classical
  let g : ι → α → ℝ := fun i x => (U i).indicator f x
  have hg (i : ι) (hi : i ∈ I) : Integrable (g i) μ :=
    hf.indicator (hU i hi)
  let G : α → ℝ := fun x => ∑ i ∈ I, g i x
  have hG : Integrable G μ := integrable_finsetSum I hg
  have hpoint : ∀ᵐ x ∂μ, x ∈ S → f x ≤ G x := by
    filter_upwards [hfn] with x hfx hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    have hnonneg (j : ι) (hj : j ∈ I) : 0 ≤ g j x := by
      by_cases hmem : x ∈ U j <;> simp [g, hmem, hfx]
    have hgi : g i x = f x := by simp [g, hxi]
    calc
      f x = g i x := hgi.symm
      _ ≤ G x := by
        dsimp [G]
        exact Finset.single_le_sum (fun j hj => hnonneg j hj) hi
  have hmono : (∫ x in S, f x ∂μ) ≤ ∫ x in S, G x ∂μ :=
    setIntegral_mono_on_ae hf.restrict hG.restrict hS hpoint
  have hGnonneg : ∀ᵐ x ∂μ, 0 ≤ G x := by
    filter_upwards [hfn] with x hx
    dsimp [G]
    apply Finset.sum_nonneg
    intro i hi
    by_cases hmem : x ∈ U i <;> simp [g, hmem, hx]
  have hglobal : (∫ x in S, G x ∂μ) ≤ ∫ x, G x ∂μ :=
    setIntegral_le_integral hG hGnonneg
  have hsum : (∫ x, G x ∂μ) = ∑ i ∈ I, ∫ x, g i x ∂μ := by
    exact integral_finsetSum I hg
  have hset (i : ι) (hi : i ∈ I) :
      ∫ x, g i x ∂μ = ∫ x in U i, f x ∂μ := by
    simpa [g] using
      (integral_indicator (μ := μ) (f := f) (s := U i) (hU i hi))
  calc
    _ ≤ ∫ x in S, G x ∂μ := hmono
    _ ≤ ∫ x, G x ∂μ := hglobal
    _ = ∑ i ∈ I, ∫ x, g i x ∂μ := hsum
    _ = ∑ i ∈ I, ∫ x in U i, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hset i hi

/-- Spatial and temporal multiplicity bounds multiply for finite product
covers of parabolic cylinders. -/
theorem integral_sum_le_of_cylinder_product_multiplicity
    {ι κ : Type*}
    (Y : Finset ι) (J : Finset κ)
    (B : ι → Set Vec3) (T : κ → Set ℝ) (N K : ℕ)
    (f : ParabolicPoint → ℝ) (hf : Integrable f volume)
    (hfn : ∀ᵐ z ∂(volume : Measure ParabolicPoint), 0 ≤ f z)
    (hB : ∀ i ∈ Y, MeasurableSet (B i))
    (hT : ∀ j ∈ J, MeasurableSet (T j))
    (hspace : ∀ y, (∑ i ∈ Y, if y ∈ B i then 1 else 0) ≤ N)
    (htime : ∀ s, (∑ j ∈ J, if s ∈ T j then 1 else 0) ≤ K) :
    (∑ p ∈ Y.product J,
      ∫ z in spaceTimeSet (B p.1) (T p.2), f z ∂volume) ≤
      ((K * N : ℕ) : ℝ) * ∫ z, f z ∂volume := by
  classical
  let F : Vec3 × ℝ → ℝ := fun q => f (parabolicHomeomorph.symm q)
  have hpres := parabolicHomeomorphSymm_measurePreserving
  have hF : Integrable F volume := by
    exact hpres.integrable_comp_of_integrable hf
  have hFn : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)), 0 ≤ F q := by
    exact hpres.quasiMeasurePreserving.ae hfn
  have hsumChange :
      (∑ p ∈ Y.product J,
        ∫ z in spaceTimeSet (B p.1) (T p.2), f z ∂volume) =
      ∑ p ∈ Y.product J, ∫ q in B p.1 ×ˢ T p.2, F q := by
    apply Finset.sum_congr rfl
    intro p hp
    exact setIntegral_parabolic_to_product
  have hglobalChange :
      ∫ z, f z ∂(volume : Measure ParabolicPoint) = ∫ q, F q ∂volume := by
    have hU : spaceTimeSet (Set.univ : Set Vec3) (Set.univ : Set ℝ) =
        (Set.univ : Set ParabolicPoint) := by
      apply Set.eq_univ_of_forall
      intro z
      change z.1 ∈ (Set.univ : Set Vec3) ∧ z.2 ∈ (Set.univ : Set ℝ)
      exact ⟨Set.mem_univ _, Set.mem_univ _⟩
    calc
      ∫ z, f z ∂(volume : Measure ParabolicPoint) =
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.univ : Set ℝ), f z ∂volume := by
            rw [hU]
            exact setIntegral_univ.symm
      _ = ∫ q in (Set.univ : Set Vec3) ×ˢ (Set.univ : Set ℝ), F q ∂volume :=
        setIntegral_parabolic_to_product
      _ = ∫ q, F q ∂volume := by simp
  rw [hsumChange, hglobalChange]
  exact integral_sum_le_of_product_multiplicity_bound
    (volume : Measure (Vec3 × ℝ)) Y J B T N K F hF hFn hB hT hspace htime

end ESS

end
