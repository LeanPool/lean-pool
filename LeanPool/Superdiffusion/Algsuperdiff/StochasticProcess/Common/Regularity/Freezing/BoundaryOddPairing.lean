/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryWeakTests
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionGlue

/-!
# BoundaryOddPairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Folding a tested pairing across one coordinate face

Let `U` be invariant under the reflection in `{y i = c}` and let `H` be one of
the two open halves it cuts.  A flux field and a scalar source on `H` extend
oddly across the face.  Testing the extended data on `U` against a smooth
compactly supported function is the same as testing the original data on `H`
against the odd fold of that function.  This is the pairing identity behind the
reflection of a divergence-form weak solution; only measure-preservation of the
reflection and the vanishing of the odd fold on the face are used.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport Filter
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

private theorem integrableOn_vecDot_coords {W : Set (Vec d)} {A B : Vec d → Vec d}
    (hA : ∀ j, MemLp (fun y => A y j) 2 (volume.restrict W))
    (hB : ∀ j, MemLp (fun y => B y j) 2 (volume.restrict W)) :
    IntegrableOn (fun y => vecDot (A y) (B y)) W volume := by
  have hsum : (fun y => vecDot (A y) (B y)) = fun y => ∑ j : Fin d, A y j * B y j := by
    funext y
    rw [vecDot]
  rw [IntegrableOn, hsum]
  exact integrable_finsetSum _ fun j _ => (hA j).integrable_mul (hB j)

private theorem vecDot_sub_left_local (A B C : Vec d) :
    vecDot (A - B) C = vecDot A C - vecDot B C := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem vecDot_sub_right_local (A B C : Vec d) :
    vecDot A (B - C) = vecDot A B - vecDot A C := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-! ## 1. The gradient leg -/

/-- The odd extension of a flux field, tested on the symmetric domain, is the
original flux tested on the half against the odd fold. -/
theorem integral_vecDot_oddFaceExtendGrad_eq
    {U : Set (Vec d)} (hUopen : IsOpen U) {i : Fin d} {c sigma : ℝ}
    (hUsymm : ∀ y : Vec d, coordFaceReflection c i y ∈ U ↔ y ∈ U)
    {F : Vec d → Vec d}
    (hF : ∀ j, MemLp (fun y => zeroExtendGrad (faceHalf U i c sigma) F y j) 2
      (volume : Measure (Vec d)))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ y in U, vecDot (oddFaceExtendGrad c i
          (zeroExtendGrad (faceHalf U i c sigma) F) y)
        (euclideanGradient φ y) ∂volume =
      ∫ y in faceHalf U i c sigma, vecDot (F y)
        (euclideanGradient (fun z => φ z - φ (coordFaceReflection c i z)) y) ∂volume := by
  classical
  set H : Set (Vec d) := faceHalf U i c sigma with hHdef
  set G : Vec d → Vec d := zeroExtendGrad H F with hGdef
  have hHopen : IsOpen H := isOpen_faceHalf hUopen i c sigma
  have hHmeas : MeasurableSet H := hHopen.measurableSet
  have hHsub : H ⊆ U := faceHalf_subset U i c sigma
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hGrL2 : ∀ j : Fin d,
      MemLp (fun y => G (coordFaceReflection c i y) j) 2 (volume : Measure (Vec d)) :=
    fun j => (hF j).comp_measurePreserving (measurePreserving_coordFaceReflection c i)
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection c i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection c i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection c i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc c i
  have hDφL2 : ∀ j : Fin d,
      MemLp (fun y => euclideanGradient φ y j) 2 (volume : Measure (Vec d)) := by
    intro j
    have h := memLp_two_fderiv_apply_restrict (W := (Set.univ : Set (Vec d))) hφ hφc j
    rwa [Measure.restrict_univ] at h
  have hDφrL2 : ∀ j : Fin d,
      MemLp (fun y => euclideanGradient (fun z => φ (coordFaceReflection c i z)) y j) 2
        (volume : Measure (Vec d)) := by
    intro j
    have h := memLp_two_fderiv_apply_restrict (W := (Set.univ : Set (Vec d))) hφr hφrc j
    rwa [Measure.restrict_univ] at h
  have hgradcomp : ∀ y : Vec d,
      euclideanGradient (fun z => φ (coordFaceReflection c i z)) y =
        coordReflectionLinear i (euclideanGradient φ (coordFaceReflection c i y)) :=
    fun y => euclideanGradient_comp_coordFaceReflection hφ c i y
  have hgradψ : ∀ y : Vec d,
      euclideanGradient (fun z => φ z - φ (coordFaceReflection c i z)) y =
        euclideanGradient φ y -
          euclideanGradient (fun z => φ (coordFaceReflection c i z)) y := by
    intro y
    funext j
    change (fderiv ℝ (fun z => φ z - φ (coordFaceReflection c i z)) y) (basisVec j) =
      (fderiv ℝ φ y) (basisVec j) -
        (fderiv ℝ (fun z => φ (coordFaceReflection c i z)) y) (basisVec j)
    rw [fderiv_fun_sub (hφ.differentiable (by simp) y) (hφr.differentiable (by simp) y)]
    simp
  have hcollapse : ∀ K : Vec d → Vec d,
      (∀ j, MemLp (fun y => K y j) 2 (volume : Measure (Vec d))) →
      ∫ y in U, vecDot (G y) (K y) ∂volume =
        ∫ y in H, vecDot (F y) (K y) ∂volume := by
    intro K _hK
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hHsub ?_]
    · refine setIntegral_congr_fun hHmeas fun y hy => ?_
      rw [hGdef, zeroExtendGrad_of_mem _ hy]
    · intro y hy
      rw [hGdef, zeroExtendGrad_of_notMem _ hy.2]
      simp [vecDot]
  have hK1int : IntegrableOn (fun y => vecDot (G y) (euclideanGradient φ y)) U volume :=
    integrableOn_vecDot_coords (fun j => (hF j).restrict U) (fun j => (hDφL2 j).restrict U)
  have hK2int : IntegrableOn
      (fun y => vecDot (coordReflectionLinear i (G (coordFaceReflection c i y)))
        (euclideanGradient φ y)) U volume := by
    refine integrableOn_vecDot_coords (fun j => ?_) (fun j => (hDφL2 j).restrict U)
    have hj : (fun y => coordReflectionLinear i (G (coordFaceReflection c i y)) j) =
        fun y => (if j = i then (-1 : ℝ) else 1) * G (coordFaceReflection c i y) j := by
      funext y
      rw [coordReflectionLinear_apply_coord]
    rw [hj]
    exact ((hGrL2 j).const_mul _).restrict U
  have hsplit : ∫ y in U, vecDot (oddFaceExtendGrad c i G y)
        (euclideanGradient φ y) ∂volume =
      (∫ y in U, vecDot (G y) (euclideanGradient φ y) ∂volume) -
        ∫ y in U, vecDot (coordReflectionLinear i (G (coordFaceReflection c i y)))
          (euclideanGradient φ y) ∂volume := by
    rw [← integral_sub hK1int hK2int]
    refine setIntegral_congr_fun hUmeas fun y _ => ?_
    exact vecDot_sub_left_local _ _ _
  have hpre : coordFaceReflection c i ⁻¹' U = U := by
    ext z
    exact hUsymm z
  have hcov : ∫ y in U, vecDot (coordReflectionLinear i (G (coordFaceReflection c i y)))
        (euclideanGradient φ y) ∂volume =
      ∫ y in U, vecDot (G y)
        (euclideanGradient (fun z => φ (coordFaceReflection c i z)) y) ∂volume := by
    have h := (measurePreserving_coordFaceReflection c i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection c i)
      (fun y => vecDot (coordReflectionLinear i (G y))
        (euclideanGradient φ (coordFaceReflection c i y))) U
    rw [hpre] at h
    calc ∫ y in U, vecDot (coordReflectionLinear i (G (coordFaceReflection c i y)))
          (euclideanGradient φ y) ∂volume
        = ∫ y in U, vecDot (coordReflectionLinear i (G (coordFaceReflection c i y)))
            (euclideanGradient φ (coordFaceReflection c i
              (coordFaceReflection c i y))) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [coordFaceReflection_involutive]
      _ = ∫ y in U, vecDot (coordReflectionLinear i (G y))
            (euclideanGradient φ (coordFaceReflection c i y)) ∂volume := h
      _ = ∫ y in U, vecDot (G y)
            (euclideanGradient (fun z => φ (coordFaceReflection c i z)) y) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [vecDot_coordReflectionLinear_left, ← hgradcomp y]
  have hHint1 : IntegrableOn (fun y => vecDot (F y) (euclideanGradient φ y)) H volume := by
    refine integrableOn_vecDot_coords (fun j => ?_) (fun j => (hDφL2 j).restrict H)
    have hj : (fun y => F y j) =ᵐ[volume.restrict H] fun y => G y j := by
      filter_upwards [ae_restrict_mem hHmeas] with y hy
      rw [hGdef, zeroExtendGrad_of_mem _ hy]
    exact ((hF j).restrict H).ae_eq hj.symm
  have hHint2 : IntegrableOn (fun y => vecDot (F y)
      (euclideanGradient (fun z => φ (coordFaceReflection c i z)) y)) H volume := by
    refine integrableOn_vecDot_coords (fun j => ?_) (fun j => (hDφrL2 j).restrict H)
    have hj : (fun y => F y j) =ᵐ[volume.restrict H] fun y => G y j := by
      filter_upwards [ae_restrict_mem hHmeas] with y hy
      rw [hGdef, zeroExtendGrad_of_mem _ hy]
    exact ((hF j).restrict H).ae_eq hj.symm
  have hfold : (∫ y in H, vecDot (F y) (euclideanGradient φ y) ∂volume) -
      ∫ y in H, vecDot (F y)
        (euclideanGradient (fun z => φ (coordFaceReflection c i z)) y) ∂volume =
      ∫ y in H, vecDot (F y)
        (euclideanGradient (fun z => φ z - φ (coordFaceReflection c i z)) y) ∂volume := by
    rw [← integral_sub hHint1 hHint2]
    refine setIntegral_congr_fun hHmeas fun y _ => ?_
    rw [hgradψ y, vecDot_sub_right_local]
  rw [hsplit, hcov, hcollapse _ hDφL2, hcollapse _ hDφrL2, hfold]

/-! ## 2. The scalar leg -/

/-- The odd extension of a scalar source, tested on the symmetric domain, is
the original source tested on the half against the odd fold. -/
theorem integral_mul_oddFaceExtend_eq
    {U : Set (Vec d)} (hUopen : IsOpen U) {i : Fin d} {c sigma : ℝ}
    (hUsymm : ∀ y : Vec d, coordFaceReflection c i y ∈ U ↔ y ∈ U)
    {h : Vec d → ℝ}
    (hh : MemLp (zeroExtend (faceHalf U i c sigma) h) 2 (volume : Measure (Vec d)))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ y in U, oddFaceExtend c i (zeroExtend (faceHalf U i c sigma) h) y * φ y ∂volume =
      ∫ y in faceHalf U i c sigma,
        h y * (φ y - φ (coordFaceReflection c i y)) ∂volume := by
  classical
  set H : Set (Vec d) := faceHalf U i c sigma with hHdef
  set Z : Vec d → ℝ := zeroExtend H h with hZdef
  have hHopen : IsOpen H := isOpen_faceHalf hUopen i c sigma
  have hHmeas : MeasurableSet H := hHopen.measurableSet
  have hHsub : H ⊆ U := faceHalf_subset U i c sigma
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hZrL2 : MemLp (fun y => Z (coordFaceReflection c i y)) 2
      (volume : Measure (Vec d)) :=
    hh.comp_measurePreserving (measurePreserving_coordFaceReflection c i)
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection c i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection c i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection c i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc c i
  have hφL2 : MemLp φ 2 (volume : Measure (Vec d)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hφrL2 : MemLp (fun z => φ (coordFaceReflection c i z)) 2
      (volume : Measure (Vec d)) :=
    hφr.continuous.memLp_of_hasCompactSupport hφrc
  have hint1 : IntegrableOn (fun y => Z y * φ y) U volume :=
    ((hh.restrict U).integrable_mul (hφL2.restrict U))
  have hint2 : IntegrableOn (fun y => Z (coordFaceReflection c i y) * φ y) U volume :=
    ((hZrL2.restrict U).integrable_mul (hφL2.restrict U))
  have hsplit : ∫ y in U, oddFaceExtend c i Z y * φ y ∂volume =
      (∫ y in U, Z y * φ y ∂volume) -
        ∫ y in U, Z (coordFaceReflection c i y) * φ y ∂volume := by
    rw [← integral_sub hint1 hint2]
    refine setIntegral_congr_fun hUmeas fun y _ => ?_
    rw [oddFaceExtend]
    ring
  have hcollapse : ∀ K : Vec d → ℝ,
      ∫ y in U, Z y * K y ∂volume = ∫ y in H, h y * K y ∂volume := by
    intro K
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hHsub ?_]
    · refine setIntegral_congr_fun hHmeas fun y hy => ?_
      rw [hZdef, zeroExtend_of_mem _ hy]
    · intro y hy
      rw [hZdef, zeroExtend_of_notMem _ hy.2, zero_mul]
  have hpre : coordFaceReflection c i ⁻¹' U = U := by
    ext z
    exact hUsymm z
  have hcov : ∫ y in U, Z (coordFaceReflection c i y) * φ y ∂volume =
      ∫ y in U, Z y * φ (coordFaceReflection c i y) ∂volume := by
    have hmp := (measurePreserving_coordFaceReflection c i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection c i)
      (fun y => Z y * φ (coordFaceReflection c i y)) U
    rw [hpre] at hmp
    calc ∫ y in U, Z (coordFaceReflection c i y) * φ y ∂volume
        = ∫ y in U, Z (coordFaceReflection c i y) *
            φ (coordFaceReflection c i (coordFaceReflection c i y)) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [coordFaceReflection_involutive]
      _ = ∫ y in U, Z y * φ (coordFaceReflection c i y) ∂volume := hmp
  have hHint1 : IntegrableOn (fun y => h y * φ y) H volume := by
    have hj : (fun y => h y) =ᵐ[volume.restrict H] fun y => Z y := by
      filter_upwards [ae_restrict_mem hHmeas] with y hy
      rw [hZdef, zeroExtend_of_mem _ hy]
    exact (((hh.restrict H).ae_eq hj.symm).integrable_mul (hφL2.restrict H))
  have hHint2 : IntegrableOn
      (fun y => h y * φ (coordFaceReflection c i y)) H volume := by
    have hj : (fun y => h y) =ᵐ[volume.restrict H] fun y => Z y := by
      filter_upwards [ae_restrict_mem hHmeas] with y hy
      rw [hZdef, zeroExtend_of_mem _ hy]
    exact (((hh.restrict H).ae_eq hj.symm).integrable_mul (hφrL2.restrict H))
  have hfold : (∫ y in H, h y * φ y ∂volume) -
      ∫ y in H, h y * φ (coordFaceReflection c i y) ∂volume =
      ∫ y in H, h y * (φ y - φ (coordFaceReflection c i y)) ∂volume := by
    rw [← integral_sub hHint1 hHint2]
    refine setIntegral_congr_fun hHmeas fun y _ => ?_
    ring
  rw [hsplit, hcov, hcollapse φ, hcollapse (fun z => φ (coordFaceReflection c i z)), hfold]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
