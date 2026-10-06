/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffFull
public import LeanPool.EscauriazaSereginSverak.Linear.UCWeakProduct
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Weak multiplication on the short-time half-space cylinder

Smooth scalar factors obey the spatial, second spatial, and time weak product
identities on the cylinder used in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The positive spatial half-space for the short-time backward uniqueness argument. -/
abbrev buShortΩ : Set Vec3 := {x : Vec3 | 0 < x 2}
/-- The terminal half of the normalized short time interval. -/
abbrev buShortI : Set ℝ := Ioo (1 / 2 : ℝ) 1

private theorem bu_integrable_mul_test
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ spaceTimeSet buShortΩ buShortI) :
    IntegrableOn (fun z : ParabolicPoint => f z * ψ (parabolicHomeomorph z))
      (spaceTimeSet buShortΩ buShortI) volume := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  let U : Set ParabolicPoint := spaceTimeSet buShortΩ buShortI
  let K : Set ParabolicPoint := parabolicHomeomorph.symm '' tsupport ψ
  have hUopen : IsOpen U := isOpen_spaceTimeSet buShortΩ buShortI hΩ hI
  have hψpar : Continuous (fun z : ParabolicPoint =>
      ψ (parabolicHomeomorph z)) :=
    hψ.continuous.comp parabolicHomeomorph.continuous
  have hloc : LocallyIntegrableOn
      (fun z : ParabolicPoint => f z * ψ (parabolicHomeomorph z)) U volume :=
    hf.mul_continuousOn hψpar.continuousOn hUopen.isLocallyClosed
  have hKcompact : IsCompact K :=
    parabolicHomeomorph.symm.isCompact_image.mpr hψc.isCompact
  have hKU : K ⊆ U := by
    rintro z ⟨q, hq, rfl⟩
    exact hψU hq
  have hKint := hloc.integrableOn_compact_subset hKU hKcompact
  have hoff (z : ParabolicPoint) (hz : z ∉ K) :
      f z * ψ (parabolicHomeomorph z) = 0 := by
    have hψzero : ψ (parabolicHomeomorph z) = 0 := by
      by_contra hne
      have hqs : parabolicHomeomorph z ∈ tsupport ψ :=
        subset_tsupport ψ (Function.mem_support.mpr hne)
      exact hz ⟨parabolicHomeomorph z, hqs, by cases z; rfl⟩
    rw [hψzero, mul_zero]
  exact (hKint.integrable_of_forall_notMem_eq_zero hoff).integrableOn

private theorem bu_locallyIntegrableOn_mul_smooth
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    LocallyIntegrableOn
      (fun z : ParabolicPoint => f z * χ (parabolicHomeomorph z))
      (spaceTimeSet buShortΩ buShortI) volume := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact hf.mul_continuousOn
    (hχ.continuous.comp parabolicHomeomorph.continuous).continuousOn
    (isOpen_spaceTimeSet buShortΩ buShortI hΩ hI).isLocallyClosed

private theorem bu_locallyIntegrableOn_smooth_mul
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    LocallyIntegrableOn
      (fun z : ParabolicPoint => χ (parabolicHomeomorph z) * f z)
      (spaceTimeSet buShortΩ buShortI) volume := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact hf.continuousOn_mul
    (hχ.continuous.comp parabolicHomeomorph.continuous).continuousOn
    (isOpen_spaceTimeSet buShortΩ buShortI hΩ hI).isLocallyClosed

private theorem bu_locallyIntegrableOn_pi
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    {f : ParabolicPoint → ι → E}
    (hf : ∀ i : ι, LocallyIntegrableOn (fun z => f z i)
      (spaceTimeSet buShortΩ buShortI) volume) :
    LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  apply (locallyIntegrableOn_iff
    (isOpen_spaceTimeSet buShortΩ buShortI hΩ hI).isLocallyClosed).2
  intro K hKU hK
  exact Integrable.of_eval (fun i => (hf i).integrableOn_compact_subset hKU hK)

private theorem bu_weak_spatial_product
    {f g : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume)
    (hg : LocallyIntegrableOn g (spaceTimeSet buShortΩ buShortI) volume)
    (j : Fin 3)
    (hweak : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI →
      ∫ z in spaceTimeSet buShortΩ buShortI, f z * spatialPartial φ j z =
        -∫ z in spaceTimeSet buShortΩ buShortI, g z * φ z)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI) :
    (∫ z in spaceTimeSet buShortΩ buShortI,
      (f z * χ (parabolicHomeomorph z)) * spatialPartial φ j z) =
    -∫ z in spaceTimeSet buShortΩ buShortI,
      (g z * χ (parabolicHomeomorph z) +
        f z * spatialPartial χ j (parabolicHomeomorph z)) * φ z := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => spatialPartial ψ j q
  let dχ : Vec3 × ℝ → ℝ := fun q => spatialPartial χ j q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet buShortΩ buShortI := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := spatialPartial_contDiff hψd j
  have hdψc : HasCompactSupport dψ := hasCompactSupport_spatialPartial hψc j
  have hdψU : tsupport dψ ⊆ spaceTimeSet buShortΩ buShortI :=
    (tsupport_spatialPartial_subset j).trans hψU
  have hdχd : ContDiff ℝ (⊤ : ℕ∞) dχ := spatialPartial_contDiff hχ j
  have htest :
      (fun q : Vec3 × ℝ => ψ q * χ q) ∈
        spaceTimeTestFunction (V := ℝ) buShortΩ buShortI :=
    spaceTimeTestFunction_mul_smooth hφ hχ
  have hA : IntegrableOn
      (fun z : ParabolicPoint => f z * (χ (parabolicHomeomorph z) *
        dψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hf (hχ.mul hdψd)
      hdψc.mul_left
      ((tsupport_mul_subset_right (f := χ) (g := dψ)).trans hdψU)
  have hB : IntegrableOn
      (fun z : ParabolicPoint => f z * (dχ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hf (hdχd.mul hψd)
      hψc.mul_left
      ((tsupport_mul_subset_right (f := dχ) (g := ψ)).trans hψU)
  have hC : IntegrableOn
      (fun z : ParabolicPoint => g z * (ψ (parabolicHomeomorph z) *
        χ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hg (hψd.mul hχ)
      hψc.mul_right
      ((tsupport_mul_subset_left (f := ψ) (g := χ)).trans hψU)
  have hD : IntegrableOn
      (fun z : ParabolicPoint => g z * (χ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume := by
    convert hC using 1
    ext z
    ring
  have hprod := hweak (fun z : ParabolicPoint => ψ z * χ z) htest
  have hderiv (z : ParabolicPoint) :
      spatialPartial (fun q : ParabolicPoint => ψ q * χ q) j z =
      dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
        ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z) := by
    exact CKN.Core.Step3.spatialPartial_mul_full hψd hχ j
      (parabolicHomeomorph z)
  simp only [hderiv] at hprod
  have hsum :
      (∫ z in spaceTimeSet buShortΩ buShortI,
        f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z))) +
      (∫ z in spaceTimeSet buShortΩ buShortI,
        f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) =
      -∫ z in spaceTimeSet buShortΩ buShortI,
        g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
    calc
      _ = ∫ z in spaceTimeSet buShortΩ buShortI,
          (f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) +
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) :=
            (integral_add hA hB).symm
      _ = ∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
            ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z)) := by
            congr 1
            ext z
            ring
      _ = -∫ z in spaceTimeSet buShortΩ buShortI, g z * (ψ z * χ z) := hprod
      _ = -∫ z in spaceTimeSet buShortΩ buShortI,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
            congr 2
            ext z
            rcases z with ⟨x, s⟩
            change g (x, s) * (φ (x, s) * χ (x, s)) =
              g (x, s) * (χ (x, s) * φ (x, s))
            ring
  calc
    (∫ z in spaceTimeSet buShortΩ buShortI,
        (f z * χ (parabolicHomeomorph z)) * spatialPartial φ j z) =
        ∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) := by
          congr 1
          ext z
          rcases z with ⟨x, s⟩
          change f (x, s) * χ (x, s) * spatialPartial φ j (x, s) =
            f (x, s) * (χ (x, s) * spatialPartial φ j (x, s))
          ring
    _ = -((∫ z in spaceTimeSet buShortΩ buShortI,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) +
        (∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)))) := by
          linarith only [hsum]
    _ = -∫ z in spaceTimeSet buShortΩ buShortI,
          (g z * χ (parabolicHomeomorph z) +
            f z * spatialPartial χ j (parabolicHomeomorph z)) * φ z := by
          rw [← integral_add hD hB]
          congr 2
          ext z
          rcases z with ⟨x, s⟩
          change g (x, s) * (χ (x, s) * φ (x, s)) +
              f (x, s) * (spatialPartial χ j (x, s) * φ (x, s)) =
            (g (x, s) * χ (x, s) +
              f (x, s) * spatialPartial χ j (x, s)) * φ (x, s)
          ring

private theorem bu_weak_time_product
    {f g : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet buShortΩ buShortI) volume)
    (hg : LocallyIntegrableOn g (spaceTimeSet buShortΩ buShortI) volume)
    (hweak : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI →
      ∫ z in spaceTimeSet buShortΩ buShortI, f z * timePartial φ z =
        -∫ z in spaceTimeSet buShortΩ buShortI, g z * φ z)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI) :
    (∫ z in spaceTimeSet buShortΩ buShortI,
      (f z * χ (parabolicHomeomorph z)) * timePartial φ z) =
    -∫ z in spaceTimeSet buShortΩ buShortI,
      (g z * χ (parabolicHomeomorph z) +
        f z * timePartial χ (parabolicHomeomorph z)) * φ z := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => timePartial ψ q
  let dχ : Vec3 × ℝ → ℝ := fun q => timePartial χ q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet buShortΩ buShortI := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := contDiff_timePartial hψd
  have hdψc : HasCompactSupport dψ := hasCompactSupport_timePartial hψc
  have hdψU : tsupport dψ ⊆ spaceTimeSet buShortΩ buShortI :=
    (tsupport_timePartial_subset ψ).trans hψU
  have hdχd : ContDiff ℝ (⊤ : ℕ∞) dχ := contDiff_timePartial hχ
  have htest :
      (fun q : Vec3 × ℝ => ψ q * χ q) ∈
        spaceTimeTestFunction (V := ℝ) buShortΩ buShortI :=
    spaceTimeTestFunction_mul_smooth hφ hχ
  have hA : IntegrableOn
      (fun z : ParabolicPoint => f z * (χ (parabolicHomeomorph z) *
        dψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hf (hχ.mul hdψd)
      hdψc.mul_left
      ((tsupport_mul_subset_right (f := χ) (g := dψ)).trans hdψU)
  have hB : IntegrableOn
      (fun z : ParabolicPoint => f z * (dχ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hf (hdχd.mul hψd)
      hψc.mul_left
      ((tsupport_mul_subset_right (f := dχ) (g := ψ)).trans hψU)
  have hC : IntegrableOn
      (fun z : ParabolicPoint => g z * (ψ (parabolicHomeomorph z) *
        χ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume :=
    bu_integrable_mul_test hg (hψd.mul hχ)
      hψc.mul_right
      ((tsupport_mul_subset_left (f := ψ) (g := χ)).trans hψU)
  have hD : IntegrableOn
      (fun z : ParabolicPoint => g z * (χ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet buShortΩ buShortI) volume := by
    convert hC using 1
    ext z
    ring
  have hprod := hweak (fun z : ParabolicPoint => ψ z * χ z) htest
  have hderiv (z : ParabolicPoint) :
      timePartial (fun q : ParabolicPoint => ψ q * χ q) z =
      dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
        ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z) := by
    exact CKN.Core.Step3.timePartial_mul_full hψd hχ
      (parabolicHomeomorph z)
  simp only [hderiv] at hprod
  have hsum :
      (∫ z in spaceTimeSet buShortΩ buShortI,
        f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z))) +
      (∫ z in spaceTimeSet buShortΩ buShortI,
        f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) =
      -∫ z in spaceTimeSet buShortΩ buShortI,
        g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
    calc
      _ = ∫ z in spaceTimeSet buShortΩ buShortI,
          (f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) +
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) :=
            (integral_add hA hB).symm
      _ = ∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
            ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z)) := by
            congr 1
            ext z
            ring
      _ = -∫ z in spaceTimeSet buShortΩ buShortI, g z * (ψ z * χ z) := hprod
      _ = -∫ z in spaceTimeSet buShortΩ buShortI,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
            congr 2
            ext z
            rcases z with ⟨x, s⟩
            change g (x, s) * (φ (x, s) * χ (x, s)) =
              g (x, s) * (χ (x, s) * φ (x, s))
            ring
  calc
    (∫ z in spaceTimeSet buShortΩ buShortI,
        (f z * χ (parabolicHomeomorph z)) * timePartial φ z) =
        ∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) := by
          congr 1
          ext z
          rcases z with ⟨x, s⟩
          change f (x, s) * χ (x, s) * timePartial φ (x, s) =
            f (x, s) * (χ (x, s) * timePartial φ (x, s))
          ring
    _ = -((∫ z in spaceTimeSet buShortΩ buShortI,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) +
        (∫ z in spaceTimeSet buShortΩ buShortI,
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)))) := by
          linarith only [hsum]
    _ = -∫ z in spaceTimeSet buShortΩ buShortI,
          (g z * χ (parabolicHomeomorph z) +
            f z * timePartial χ (parabolicHomeomorph z)) * φ z := by
          rw [← integral_add hD hB]
          congr 2
          ext z
          rcases z with ⟨x, s⟩
          change g (x, s) * (χ (x, s) * φ (x, s)) +
              f (x, s) * (timePartial χ (x, s) * φ (x, s)) =
            (g (x, s) * χ (x, s) +
              f (x, s) * timePartial χ (x, s)) * φ (x, s)
          ring


private theorem bu_weak_spatial_add
    {f₁ f₂ g₁ g₂ : ParabolicPoint → ℝ}
    (hf₁ : LocallyIntegrableOn f₁ (spaceTimeSet buShortΩ buShortI) volume)
    (hf₂ : LocallyIntegrableOn f₂ (spaceTimeSet buShortΩ buShortI) volume)
    (hg₁ : LocallyIntegrableOn g₁ (spaceTimeSet buShortΩ buShortI) volume)
    (hg₂ : LocallyIntegrableOn g₂ (spaceTimeSet buShortΩ buShortI) volume)
    (j : Fin 3)
    (h₁ : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI →
      ∫ z in spaceTimeSet buShortΩ buShortI, f₁ z * spatialPartial φ j z =
        -∫ z in spaceTimeSet buShortΩ buShortI, g₁ z * φ z)
    (h₂ : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI →
      ∫ z in spaceTimeSet buShortΩ buShortI, f₂ z * spatialPartial φ j z =
        -∫ z in spaceTimeSet buShortΩ buShortI, g₂ z * φ z)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI) :
    ∫ z in spaceTimeSet buShortΩ buShortI,
      (f₁ z + f₂ z) * spatialPartial φ j z =
        -∫ z in spaceTimeSet buShortΩ buShortI, (g₁ z + g₂ z) * φ z := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => spatialPartial ψ j q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet buShortΩ buShortI := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := spatialPartial_contDiff hψd j
  have hdψc : HasCompactSupport dψ := hasCompactSupport_spatialPartial hψc j
  have hdψU : tsupport dψ ⊆ spaceTimeSet buShortΩ buShortI :=
    (tsupport_spatialPartial_subset j).trans hψU
  have hA₁ := bu_integrable_mul_test hf₁ hdψd hdψc hdψU
  have hA₂ := bu_integrable_mul_test hf₂ hdψd hdψc hdψU
  have hB₁ := bu_integrable_mul_test hg₁ hψd hψc hψU
  have hB₂ := bu_integrable_mul_test hg₂ hψd hψc hψU
  have hA₁' : IntegrableOn
      (fun z : ParabolicPoint => f₁ z * spatialPartial φ j z)
      (spaceTimeSet buShortΩ buShortI) volume := by
    convert hA₁ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hA₂' : IntegrableOn
      (fun z : ParabolicPoint => f₂ z * spatialPartial φ j z)
      (spaceTimeSet buShortΩ buShortI) volume := by
    convert hA₂ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hB₁' : IntegrableOn
      (fun z : ParabolicPoint => g₁ z * φ z)
      (spaceTimeSet buShortΩ buShortI) volume := by
    convert hB₁ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hB₂' : IntegrableOn
      (fun z : ParabolicPoint => g₂ z * φ z)
      (spaceTimeSet buShortΩ buShortI) volume := by
    convert hB₂ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  calc
    (∫ z in spaceTimeSet buShortΩ buShortI, (f₁ z + f₂ z) * spatialPartial φ j z) =
        (∫ z in spaceTimeSet buShortΩ buShortI, f₁ z * spatialPartial φ j z) +
          (∫ z in spaceTimeSet buShortΩ buShortI, f₂ z * spatialPartial φ j z) := by
          rw [← integral_add hA₁' hA₂']
          congr 1
          ext z
          ring
    _ = -((∫ z in spaceTimeSet buShortΩ buShortI, g₁ z * φ z) +
          (∫ z in spaceTimeSet buShortΩ buShortI, g₂ z * φ z)) := by
          rw [h₁ φ hφ, h₂ φ hφ]
          ring
    _ = -∫ z in spaceTimeSet buShortΩ buShortI, (g₁ z + g₂ z) * φ z := by
          rw [← integral_add hB₁' hB₂']
          congr 2
          ext z
          ring


/-- A smooth scalar factor evaluated in parabolic coordinates. -/
@[expose] def buCutScalar (κ : Vec3 × ℝ → ℝ) (z : ParabolicPoint) : ℝ :=
  κ (parabolicHomeomorph z)

/-- The cut-off vector field. -/
@[expose] def buCutField (κ : Vec3 × ℝ → ℝ) (w : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 := fun z => buCutScalar κ z • w z

/-- First spatial weak derivative data for the cut-off field. -/
@[expose] def buCutDw (κ : Vec3 × ℝ → ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j => buCutScalar κ z * Dw z i j +
    w z i * spatialPartial (buCutScalar κ) j z

/-- Second spatial weak derivative data for the cut-off field. -/
@[expose] def buCutD2 (κ : Vec3 × ℝ → ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (z : ParabolicPoint) : Fin 3 → Fin 3 → Vec3 :=
  fun i j k => buCutScalar κ z * D2w z i j k +
    spatialPartial (buCutScalar κ) k z * Dw z i j +
    spatialPartial (buCutScalar κ) j z * Dw z i k +
    w z i * spatialSecondPartial (buCutScalar κ) j k z

/-- Weak time derivative data for the cut-off field. -/
@[expose] def buCutDt (κ : Vec3 × ℝ → ℝ) (w Dtw : ParabolicPoint → Vec3)
    (z : ParabolicPoint) : Vec3 :=
  fun i => buCutScalar κ z * Dtw z i + w z i * timePartial (buCutScalar κ) z

/-- Smooth scalar multiplication preserves weak spatial and time derivatives
on the shifted half-space cylinder. -/
theorem buCut_hasSpaceTimeWeakDerivs
    (κ : Vec3 × ℝ → ℝ)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) κ)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hw : HasSpaceTimeWeakDerivs buShortΩ buShortI w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs buShortΩ buShortI
      (buCutField κ w)
      (buCutDw κ w Dw)
      (buCutD2 κ w Dw D2w)
      (buCutDt κ w Dtw) := by
  have hΩ : IsOpen buShortΩ := (isOpen_lt continuous_const (continuous_apply 2))
  have hI : IsOpen buShortI := isOpen_Ioo
  let ξ : Vec3 × ℝ → ℝ := κ
  have hξsmooth : ContDiff ℝ (⊤ : ℕ∞) ξ := hξ
  have hξj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial ξ j z) :=
    spatialPartial_contDiff hξsmooth j
  have hξjk (j k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial ξ j k z) := by
    exact spatialPartial_contDiff (hξj j) k
  have hξt : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial ξ z) :=
    contDiff_timePartial hξsmooth
  have hξpoint (z : ParabolicPoint) :
      ξ (parabolicHomeomorph z) = buCutScalar κ z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξsp (j : Fin 3) (z : ParabolicPoint) :
      spatialPartial ξ j (parabolicHomeomorph z) =
        spatialPartial (buCutScalar κ) j z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξtime (z : ParabolicPoint) :
      timePartial ξ (parabolicHomeomorph z) =
        timePartial (buCutScalar κ) z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξsecond (j k : Fin 3) (z : ParabolicPoint) :
      spatialSecondPartial ξ j k (parabolicHomeomorph z) =
        spatialSecondPartial (buCutScalar κ) j k z := by
    rcases z with ⟨x, s⟩
    rfl
  rcases hw with ⟨hwl, hDwl, hD2wl, hDtwl, hweak⟩
  have hwi (i : Fin 3) : LocallyIntegrableOn (fun z => w z i)
      (spaceTimeSet buShortΩ buShortI) volume := locallyIntegrableOn_pi_eval hwl i
  have hDwij (i j : Fin 3) : LocallyIntegrableOn (fun z => Dw z i j)
      (spaceTimeSet buShortΩ buShortI) volume := by
    have hi : LocallyIntegrableOn (fun z => Dw z i)
        (spaceTimeSet buShortΩ buShortI) volume := locallyIntegrableOn_pi_eval hDwl i
    exact locallyIntegrableOn_pi_eval hi j
  have hD2wijk (i j k : Fin 3) : LocallyIntegrableOn (fun z => D2w z i j k)
      (spaceTimeSet buShortΩ buShortI) volume := by
    have hi : LocallyIntegrableOn (fun z => D2w z i)
        (spaceTimeSet buShortΩ buShortI) volume := locallyIntegrableOn_pi_eval hD2wl i
    have hij : LocallyIntegrableOn (fun z => D2w z i j)
        (spaceTimeSet buShortΩ buShortI) volume := locallyIntegrableOn_pi_eval hi j
    exact locallyIntegrableOn_pi_eval hij k
  have hDtwi (i : Fin 3) : LocallyIntegrableOn (fun z => Dtw z i)
      (spaceTimeSet buShortΩ buShortI) volume := locallyIntegrableOn_pi_eval hDtwl i
  have hcutw : LocallyIntegrableOn (buCutField κ w)
      (spaceTimeSet buShortΩ buShortI) volume := by
    apply bu_locallyIntegrableOn_pi
    intro i
    convert bu_locallyIntegrableOn_smooth_mul (hwi i) hξsmooth using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutDw : LocallyIntegrableOn (buCutDw κ w Dw)
      (spaceTimeSet buShortΩ buShortI) volume := by
    apply bu_locallyIntegrableOn_pi
    intro i
    apply bu_locallyIntegrableOn_pi
    intro j
    have hA := bu_locallyIntegrableOn_smooth_mul (hDwij i j) hξsmooth
    have hB := bu_locallyIntegrableOn_mul_smooth (hwi i) (hξj j)
    convert hA.add hB using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutD2 : LocallyIntegrableOn (buCutD2 κ w Dw D2w)
      (spaceTimeSet buShortΩ buShortI) volume := by
    apply bu_locallyIntegrableOn_pi
    intro i
    apply bu_locallyIntegrableOn_pi
    intro j
    apply bu_locallyIntegrableOn_pi
    intro k
    have hA := bu_locallyIntegrableOn_smooth_mul
      (hD2wijk i j k) hξsmooth
    have hB := bu_locallyIntegrableOn_smooth_mul
      (hDwij i j) (hξj k)
    have hC := bu_locallyIntegrableOn_smooth_mul
      (hDwij i k) (hξj j)
    have hD := bu_locallyIntegrableOn_mul_smooth
      (hwi i) (hξjk j k)
    convert ((hA.add hB).add hC).add hD using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutDt : LocallyIntegrableOn (buCutDt κ w Dtw)
      (spaceTimeSet buShortΩ buShortI) volume := by
    apply bu_locallyIntegrableOn_pi
    intro i
    have hA := bu_locallyIntegrableOn_smooth_mul (hDtwi i) hξsmooth
    have hB := bu_locallyIntegrableOn_mul_smooth (hwi i) hξt
    convert hA.add hB using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  refine ⟨hcutw, hcutDw, hcutD2, hcutDt, ?_⟩
  intro φ hφ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hp := bu_weak_spatial_product (hwi i) (hDwij i j) j
      (fun ψ hψ => (hweak ψ hψ).1 i j) hξsmooth φ hφ
    simpa only [buCutField, buCutDw, ξ, Pi.smul_apply, smul_eq_mul,
      hξpoint, hξsp, mul_comm] using hp
  · intro i j k
    have hA : LocallyIntegrableOn
        (fun z : ParabolicPoint => Dw z i j * ξ (parabolicHomeomorph z))
        (spaceTimeSet buShortΩ buShortI) volume :=
      bu_locallyIntegrableOn_mul_smooth (hDwij i j) hξsmooth
    have hB : LocallyIntegrableOn
        (fun z : ParabolicPoint => w z i *
          spatialPartial ξ j (parabolicHomeomorph z))
        (spaceTimeSet buShortΩ buShortI) volume :=
      bu_locallyIntegrableOn_mul_smooth (hwi i) (hξj j)
    have hG₁ : LocallyIntegrableOn
        (fun z : ParabolicPoint =>
          D2w z i j k * ξ (parabolicHomeomorph z) +
            Dw z i j * spatialPartial ξ k (parabolicHomeomorph z))
        (spaceTimeSet buShortΩ buShortI) volume :=
      (bu_locallyIntegrableOn_mul_smooth (hD2wijk i j k) hξsmooth).add
        (bu_locallyIntegrableOn_mul_smooth (hDwij i j) (hξj k))
    have hG₂ : LocallyIntegrableOn
        (fun z : ParabolicPoint =>
          Dw z i k * spatialPartial ξ j (parabolicHomeomorph z) +
            w z i * spatialSecondPartial ξ j k (parabolicHomeomorph z))
        (spaceTimeSet buShortΩ buShortI) volume :=
      (bu_locallyIntegrableOn_mul_smooth (hDwij i k) (hξj j)).add
        (bu_locallyIntegrableOn_mul_smooth (hwi i) (hξjk j k))
    have hp₁ (ψ : ParabolicPoint → ℝ)
        (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI) :=
      bu_weak_spatial_product (hDwij i j) (hD2wijk i j k) k
        (fun ϕ hϕ => (hweak ϕ hϕ).2.1 i j k) hξsmooth ψ hψ
    have hp₂ (ψ : ParabolicPoint → ℝ)
        (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) buShortΩ buShortI) :=
      bu_weak_spatial_product (hwi i) (hDwij i k) k
        (fun ϕ hϕ => (hweak ϕ hϕ).1 i k) (hξj j) ψ hψ
    have hsum := bu_weak_spatial_add hA hB hG₁ hG₂ k hp₁ hp₂ φ hφ
    have hleft (z : ParabolicPoint) :
        buCutDw κ w Dw z i j =
          Dw z i j * ξ (parabolicHomeomorph z) +
            w z i * spatialPartial ξ j (parabolicHomeomorph z) := by
      rw [hξpoint, hξsp]
      simp only [buCutDw]
      ring
    have hright (z : ParabolicPoint) :
        buCutD2 κ w Dw D2w z i j k =
          D2w z i j k * ξ (parabolicHomeomorph z) +
            Dw z i j * spatialPartial ξ k (parabolicHomeomorph z) +
            (Dw z i k * spatialPartial ξ j (parabolicHomeomorph z) +
              w z i * spatialSecondPartial ξ j k (parabolicHomeomorph z)) := by
      rw [hξpoint, hξsp, hξsp, hξsecond]
      simp only [buCutD2]
      ring
    simpa only [hleft, hright] using hsum
  · intro i
    have hp := bu_weak_time_product (hwi i) (hDtwi i)
      (fun ψ hψ => (hweak ψ hψ).2.2 i) hξsmooth φ hφ
    simpa only [buCutField, buCutDt, ξ, Pi.smul_apply, smul_eq_mul,
      hξpoint, hξtime, mul_comm] using hp


end ESS
