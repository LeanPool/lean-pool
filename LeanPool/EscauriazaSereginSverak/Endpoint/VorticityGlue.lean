/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed

/-!
# Gluing weak derivative identities

A weak derivative identity which holds for test functions supported in a neighbourhood of every
point of an open set holds for every test function supported in the set: a smooth partition of
unity subordinate to the neighbourhoods splits the test function into finitely many localized
pieces (used to glue the local vorticity estimates in `lem:vorticity-top-extension`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Manifold ContDiff
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The product of a locally integrable function with a continuous compactly supported function
whose support lies in the open set is integrable there. -/
theorem vorticityGlue_integrableOn_mul {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {f h : Vec3 × ℝ → ℝ} (hf : LocallyIntegrableOn f D) (hh : Continuous h)
    (hhc : HasCompactSupport h) (hhD : tsupport h ⊆ D) :
    IntegrableOn (fun y => f y * h y) D := by
  have h1 : IntegrableOn f (tsupport h) := hf.integrableOn_compact_subset hhD hhc
  have h2 : IntegrableOn (fun y => f y * h y) (tsupport h) :=
    h1.mul_continuousOn hh.continuousOn hhc
  refine h2.of_forall_sdiff_eq_zero hD.measurableSet fun y hy => ?_
  rw [image_eq_zero_of_notMem_tsupport hy.2, mul_zero]

/-- A weak derivative identity for an abstract linear derivative of the test function, glued from
neighbourhoods of the points of an open set. -/
theorem vorticityGlue_generic {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {f g : Vec3 × ℝ → ℝ} (hf : LocallyIntegrableOn f D) (hg : LocallyIntegrableOn g D)
    (L : (Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ)
    (hLc : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → Continuous (L ψ))
    (hLsupp : ∀ ψ : Vec3 × ℝ → ℝ, tsupport (L ψ) ⊆ tsupport ψ)
    (hLsum : ∀ (ι : Type) (s : Finset ι) (φ : ι → Vec3 × ℝ → ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) →
        L (fun z => ∑ k ∈ s, φ k z) = fun z => ∑ k ∈ s, L (φ k) z)
    (hloc : ∀ z ∈ D, ∃ N : Set (Vec3 × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ N →
        tsupport ψ ⊆ D → ∫ y in D, f y * L ψ y = -∫ y in D, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ y in D, f y * L ψ y = -∫ y in D, g y * ψ y := by
  intro ψ hψ hψc hψD
  choose N hNo hzN hNid using hloc
  set U : D → Set (Vec3 × ℝ) := fun z => N z.1 z.2 ∩ D with hUdef
  have hUo : ∀ i, IsOpen (U i) := fun i => (hNo i.1 i.2).inter hD
  have hKU : tsupport ψ ⊆ ⋃ i, U i := fun z hz =>
    mem_iUnion.2 ⟨⟨z, hψD hz⟩, hzN z (hψD hz), hψD hz⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Vec3 × ℝ)
    (isClosed_tsupport ψ) U hUo hKU
  have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hψc.isCompact
  set s := hfin.toFinset with hsdef
  have hρs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ρ i) := fun i => contMDiff_iff_contDiff.mp (ρ i).contMDiff
  set φ : D → Vec3 × ℝ → ℝ := fun i z => ρ i z * ψ z with hφdef
  have hφs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i) := fun i => (hρs i).mul hψ
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hψc.mul_left
  have hφU : ∀ i, tsupport (φ i) ⊆ U i := fun i =>
    (tsupport_mul_subset_left (f := ⇑(ρ i)) (g := ψ)).trans (hρ i)
  have hφD : ∀ i, tsupport (φ i) ⊆ D := fun i => (hφU i).trans inter_subset_right
  -- the decomposition of the test function
  have hdec : ψ = fun z => ∑ i ∈ s, φ i z := by
    funext z
    by_cases hz : z ∈ tsupport ψ
    · have hsupp : support (fun i => ρ i z) ⊆ (s : Set D) := by
        intro i hi
        rw [hsdef, Finite.coe_toFinset]
        exact ⟨z, hi, hz⟩
      have h1 : ∑ i ∈ s, ρ i z = 1 := by
        rw [← finsum_eq_sum_of_support_subset _ hsupp]
        exact ρ.sum_eq_one hz
      simp only [φ]
      rw [← Finset.sum_mul, h1, one_mul]
    · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp only [φ, h0, mul_zero, Finset.sum_const_zero]
  have hLψ : L ψ = fun z => ∑ i ∈ s, L (φ i) z :=
    (congrArg L hdec).trans (hLsum D s φ hφs)
  have hiL : ∀ i, IntegrableOn (fun y => f y * L (φ i) y) D := fun i =>
    vorticityGlue_integrableOn_mul hD hf (hLc _ (hφs i))
      ((hφc i).mono' ((subset_tsupport _).trans (hLsupp _))) ((hLsupp _).trans (hφD i))
  have hig : ∀ i, IntegrableOn (fun y => g y * φ i y) D := fun i =>
    vorticityGlue_integrableOn_mul hD hg (hφs i).continuous (hφc i) (hφD i)
  have e1 : ∫ y in D, f y * L ψ y = ∑ i ∈ s, ∫ y in D, f y * L (φ i) y := by
    rw [← integral_finsetSum _ fun i _ => hiL i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hLψ, Finset.mul_sum]
  have e2 : ∫ y in D, g y * ψ y = ∑ i ∈ s, ∫ y in D, g y * φ i y := by
    rw [← integral_finsetSum _ fun i _ => hig i]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hy : ψ y = ∑ i ∈ s, φ i y := congrFun hdec y
    change g y * ψ y = ∑ i ∈ s, g y * φ i y
    rw [hy, Finset.mul_sum]
  rw [e1, e2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hNid i.1 i.2 (φ i) (hφs i) (hφc i) ((hφU i).trans inter_subset_left) (hφD i)

/-- The spatial partial derivative of a finite sum of smooth functions. -/
theorem vorticityGlue_spatialPartial_sum {ι : Type} (s : Finset ι) (φ : ι → Vec3 × ℝ → ℝ)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (j : Fin 3) :
    (fun z => spatialPartial (fun y : Vec3 × ℝ => ∑ k ∈ s, φ k y) j z) =
      fun z => ∑ k ∈ s, spatialPartial (φ k) j z := by
  funext z
  have hd : ∀ k, DifferentiableAt ℝ (φ k) z := fun k =>
    (hφ k).differentiable (by simp) z
  have hs : DifferentiableAt ℝ (fun y : Vec3 × ℝ => ∑ k ∈ s, φ k y) z :=
    DifferentiableAt.fun_sum fun k _ => hd k
  rw [spatialPartial_eq_product_fderiv hs, fderiv_fun_sum fun k _ => hd k,
    sum_apply]
  exact Finset.sum_congr rfl fun k _ => (spatialPartial_eq_product_fderiv (hd k) j).symm

/-- The time partial derivative of a finite sum of smooth functions. -/
theorem vorticityGlue_timePartial_sum {ι : Type} (s : Finset ι) (φ : ι → Vec3 × ℝ → ℝ)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) :
    (fun z => timePartial (fun y : Vec3 × ℝ => ∑ k ∈ s, φ k y) z) =
      fun z => ∑ k ∈ s, timePartial (φ k) z := by
  funext z
  have hd : ∀ k, DifferentiableAt ℝ (φ k) z := fun k =>
    (hφ k).differentiable (by simp) z
  have hs : DifferentiableAt ℝ (fun y : Vec3 × ℝ => ∑ k ∈ s, φ k y) z :=
    DifferentiableAt.fun_sum fun k _ => hd k
  rw [timePartial_eq_product_fderiv hs, fderiv_fun_sum fun k _ => hd k,
    sum_apply]
  exact Finset.sum_congr rfl fun k _ => (timePartial_eq_product_fderiv (hd k)).symm

/-- Gluing of weak derivative identities from local neighbourhoods. -/
theorem vorticity_weak_glue_spatial {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {f g : Vec3 × ℝ → ℝ} (hf : LocallyIntegrableOn f D) (hg : LocallyIntegrableOn g D)
    (j : Fin 3)
    (hloc : ∀ z ∈ D, ∃ N : Set (Vec3 × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ N →
        tsupport ψ ⊆ D → ∫ y in D, f y * spatialPartial ψ j y = -∫ y in D, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ y in D, f y * spatialPartial ψ j y = -∫ y in D, g y * ψ y :=
  vorticityGlue_generic hD hf hg (fun ψ z => spatialPartial ψ j z)
    (fun _ hψ => (CKN.spatialPartial_contDiff hψ j).continuous)
    (fun _ => CKN.tsupport_spatialPartial_subset j)
    (fun _ s φ hφ => vorticityGlue_spatialPartial_sum s φ hφ j) hloc

/-- Gluing of weak time derivative identities from local neighbourhoods. -/
theorem vorticity_weak_glue_time {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {f g : Vec3 × ℝ → ℝ} (hf : LocallyIntegrableOn f D) (hg : LocallyIntegrableOn g D)
    (hloc : ∀ z ∈ D, ∃ N : Set (Vec3 × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ N →
        tsupport ψ ⊆ D → ∫ y in D, f y * timePartial ψ y = -∫ y in D, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ y in D, f y * timePartial ψ y = -∫ y in D, g y * ψ y :=
  vorticityGlue_generic hD hf hg (fun ψ z => timePartial ψ z)
    (fun _ hψ => (CKN.contDiff_timePartial hψ).continuous)
    (fun ψ => CKN.tsupport_timePartial_subset ψ)
    (fun _ s φ hφ => vorticityGlue_timePartial_sum s φ hφ) hloc

end ESS
