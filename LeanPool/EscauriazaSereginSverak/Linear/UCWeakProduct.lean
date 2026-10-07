/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Weak product rule for the Gaussian cutoff

Smooth compactly supported factors preserve the weak integration-by-parts
identities used in `lem:uc-gaussian`.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem uc_integrable_mul_test
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z : ParabolicPoint => f z * ψ (parabolicHomeomorph z))
      (spaceTimeSet Ω I) volume := by
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  let U : Set ParabolicPoint := spaceTimeSet Ω I
  let K : Set ParabolicPoint := parabolicHomeomorph.symm '' tsupport ψ
  have hUopen : IsOpen U := isOpen_spaceTimeSet Ω I hΩ hI
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

private theorem uc_locallyIntegrableOn_mul_smooth
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    LocallyIntegrableOn
      (fun z : ParabolicPoint => f z * χ (parabolicHomeomorph z))
      (spaceTimeSet Ω I) volume := by
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact hf.mul_continuousOn
    (hχ.continuous.comp parabolicHomeomorph.continuous).continuousOn
    (isOpen_spaceTimeSet Ω I hΩ hI).isLocallyClosed

private theorem uc_locallyIntegrableOn_smooth_mul
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    LocallyIntegrableOn
      (fun z : ParabolicPoint => χ (parabolicHomeomorph z) * f z)
      (spaceTimeSet Ω I) volume := by
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact hf.continuousOn_mul
    (hχ.continuous.comp parabolicHomeomorph.continuous).continuousOn
    (isOpen_spaceTimeSet Ω I hΩ hI).isLocallyClosed

private theorem uc_locallyIntegrableOn_pi_eval
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set Vec3} {I : Set ℝ}
    {f : ParabolicPoint → ι → E}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume) (i : ι) :
    LocallyIntegrableOn (fun z => f z i) (spaceTimeSet Ω I) volume := by
  simpa [Function.comp_def, ContinuousLinearMap.proj] using
    (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).locallyIntegrableOn_comp hf

private theorem uc_locallyIntegrableOn_pi
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : ParabolicPoint → ι → E}
    (hf : ∀ i : ι, LocallyIntegrableOn (fun z => f z i)
      (spaceTimeSet Ω I) volume) :
    LocallyIntegrableOn f (spaceTimeSet Ω I) volume := by
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isClosedEmbedding.locallyCompactSpace
  apply (locallyIntegrableOn_iff
    (isOpen_spaceTimeSet Ω I hΩ hI).isLocallyClosed).2
  intro K hKU hK
  exact Integrable.of_eval (fun i => (hf i).integrableOn_compact_subset hKU hK)

private theorem uc_weak_spatial_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f g : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume)
    (hg : LocallyIntegrableOn g (spaceTimeSet Ω I) volume)
    (j : Fin 3)
    (hweak : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, f z * spatialPartial φ j z =
        -∫ z in spaceTimeSet Ω I, g z * φ z)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ z in spaceTimeSet Ω I,
      (f z * χ (parabolicHomeomorph z)) * spatialPartial φ j z) =
    -∫ z in spaceTimeSet Ω I,
      (g z * χ (parabolicHomeomorph z) +
        f z * spatialPartial χ j (parabolicHomeomorph z)) * φ z := by
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => spatialPartial ψ j q
  let dχ : Vec3 × ℝ → ℝ := fun q => spatialPartial χ j q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet Ω I := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := spatialPartial_contDiff hψd j
  have hdψc : HasCompactSupport dψ := hasCompactSupport_spatialPartial hψc j
  have hdψU : tsupport dψ ⊆ spaceTimeSet Ω I :=
    (tsupport_spatialPartial_subset j).trans hψU
  have hdχd : ContDiff ℝ (⊤ : ℕ∞) dχ := spatialPartial_contDiff hχ j
  have htest :
      (fun q : Vec3 × ℝ => ψ q * χ q) ∈
        spaceTimeTestFunction (V := ℝ) Ω I :=
    spaceTimeTestFunction_mul_smooth hφ hχ
  have hA : IntegrableOn
      (fun z : ParabolicPoint => f z * (χ (parabolicHomeomorph z) *
        dψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hf (hχ.mul hdψd)
      hdψc.mul_left
      ((tsupport_mul_subset_right (f := χ) (g := dψ)).trans hdψU)
  have hB : IntegrableOn
      (fun z : ParabolicPoint => f z * (dχ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hf (hdχd.mul hψd)
      hψc.mul_left
      ((tsupport_mul_subset_right (f := dχ) (g := ψ)).trans hψU)
  have hC : IntegrableOn
      (fun z : ParabolicPoint => g z * (ψ (parabolicHomeomorph z) *
        χ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hg (hψd.mul hχ)
      hψc.mul_right
      ((tsupport_mul_subset_left (f := ψ) (g := χ)).trans hψU)
  have hD : IntegrableOn
      (fun z : ParabolicPoint => g z * (χ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume := by
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
      (∫ z in spaceTimeSet Ω I,
        f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z))) +
      (∫ z in spaceTimeSet Ω I,
        f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) =
      -∫ z in spaceTimeSet Ω I,
        g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
    calc
      _ = ∫ z in spaceTimeSet Ω I,
          (f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) +
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) :=
            (integral_add hA hB).symm
      _ = ∫ z in spaceTimeSet Ω I,
          f z * (dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
            ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z)) := by
            congr 1
            ext z
            ring
      _ = -∫ z in spaceTimeSet Ω I, g z * (ψ z * χ z) := hprod
      _ = -∫ z in spaceTimeSet Ω I,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
            congr 2
            ext z
            rcases z with ⟨x, s⟩
            change g (x, s) * (φ (x, s) * χ (x, s)) =
              g (x, s) * (χ (x, s) * φ (x, s))
            ring
  calc
    (∫ z in spaceTimeSet Ω I,
        (f z * χ (parabolicHomeomorph z)) * spatialPartial φ j z) =
        ∫ z in spaceTimeSet Ω I,
          f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) := by
          congr 1
          ext z
          rcases z with ⟨x, s⟩
          change f (x, s) * χ (x, s) * spatialPartial φ j (x, s) =
            f (x, s) * (χ (x, s) * spatialPartial φ j (x, s))
          ring
    _ = -((∫ z in spaceTimeSet Ω I,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) +
        (∫ z in spaceTimeSet Ω I,
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)))) := by
          linarith only [hsum]
    _ = -∫ z in spaceTimeSet Ω I,
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

private theorem uc_weak_time_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f g : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) volume)
    (hg : LocallyIntegrableOn g (spaceTimeSet Ω I) volume)
    (hweak : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, f z * timePartial φ z =
        -∫ z in spaceTimeSet Ω I, g z * φ z)
    {χ : Vec3 × ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ z in spaceTimeSet Ω I,
      (f z * χ (parabolicHomeomorph z)) * timePartial φ z) =
    -∫ z in spaceTimeSet Ω I,
      (g z * χ (parabolicHomeomorph z) +
        f z * timePartial χ (parabolicHomeomorph z)) * φ z := by
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => timePartial ψ q
  let dχ : Vec3 × ℝ → ℝ := fun q => timePartial χ q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet Ω I := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := contDiff_timePartial hψd
  have hdψc : HasCompactSupport dψ := hasCompactSupport_timePartial hψc
  have hdψU : tsupport dψ ⊆ spaceTimeSet Ω I :=
    (tsupport_timePartial_subset ψ).trans hψU
  have hdχd : ContDiff ℝ (⊤ : ℕ∞) dχ := contDiff_timePartial hχ
  have htest :
      (fun q : Vec3 × ℝ => ψ q * χ q) ∈
        spaceTimeTestFunction (V := ℝ) Ω I :=
    spaceTimeTestFunction_mul_smooth hφ hχ
  have hA : IntegrableOn
      (fun z : ParabolicPoint => f z * (χ (parabolicHomeomorph z) *
        dψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hf (hχ.mul hdψd)
      hdψc.mul_left
      ((tsupport_mul_subset_right (f := χ) (g := dψ)).trans hdψU)
  have hB : IntegrableOn
      (fun z : ParabolicPoint => f z * (dχ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hf (hdχd.mul hψd)
      hψc.mul_left
      ((tsupport_mul_subset_right (f := dχ) (g := ψ)).trans hψU)
  have hC : IntegrableOn
      (fun z : ParabolicPoint => g z * (ψ (parabolicHomeomorph z) *
        χ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume :=
    uc_integrable_mul_test hΩ hI hg (hψd.mul hχ)
      hψc.mul_right
      ((tsupport_mul_subset_left (f := ψ) (g := χ)).trans hψU)
  have hD : IntegrableOn
      (fun z : ParabolicPoint => g z * (χ (parabolicHomeomorph z) *
        ψ (parabolicHomeomorph z))) (spaceTimeSet Ω I) volume := by
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
      (∫ z in spaceTimeSet Ω I,
        f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z))) +
      (∫ z in spaceTimeSet Ω I,
        f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) =
      -∫ z in spaceTimeSet Ω I,
        g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
    calc
      _ = ∫ z in spaceTimeSet Ω I,
          (f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) +
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) :=
            (integral_add hA hB).symm
      _ = ∫ z in spaceTimeSet Ω I,
          f z * (dψ (parabolicHomeomorph z) * χ (parabolicHomeomorph z) +
            ψ (parabolicHomeomorph z) * dχ (parabolicHomeomorph z)) := by
            congr 1
            ext z
            ring
      _ = -∫ z in spaceTimeSet Ω I, g z * (ψ z * χ z) := hprod
      _ = -∫ z in spaceTimeSet Ω I,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)) := by
            congr 2
            ext z
            rcases z with ⟨x, s⟩
            change g (x, s) * (φ (x, s) * χ (x, s)) =
              g (x, s) * (χ (x, s) * φ (x, s))
            ring
  calc
    (∫ z in spaceTimeSet Ω I,
        (f z * χ (parabolicHomeomorph z)) * timePartial φ z) =
        ∫ z in spaceTimeSet Ω I,
          f z * (χ (parabolicHomeomorph z) * dψ (parabolicHomeomorph z)) := by
          congr 1
          ext z
          rcases z with ⟨x, s⟩
          change f (x, s) * χ (x, s) * timePartial φ (x, s) =
            f (x, s) * (χ (x, s) * timePartial φ (x, s))
          ring
    _ = -((∫ z in spaceTimeSet Ω I,
          g z * (χ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z))) +
        (∫ z in spaceTimeSet Ω I,
          f z * (dχ (parabolicHomeomorph z) * ψ (parabolicHomeomorph z)))) := by
          linarith only [hsum]
    _ = -∫ z in spaceTimeSet Ω I,
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


private theorem uc_weak_spatial_add
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f₁ f₂ g₁ g₂ : ParabolicPoint → ℝ}
    (hf₁ : LocallyIntegrableOn f₁ (spaceTimeSet Ω I) volume)
    (hf₂ : LocallyIntegrableOn f₂ (spaceTimeSet Ω I) volume)
    (hg₁ : LocallyIntegrableOn g₁ (spaceTimeSet Ω I) volume)
    (hg₂ : LocallyIntegrableOn g₂ (spaceTimeSet Ω I) volume)
    (j : Fin 3)
    (h₁ : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, f₁ z * spatialPartial φ j z =
        -∫ z in spaceTimeSet Ω I, g₁ z * φ z)
    (h₂ : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, f₂ z * spatialPartial φ j z =
        -∫ z in spaceTimeSet Ω I, g₂ z * φ z)
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    ∫ z in spaceTimeSet Ω I,
      (f₁ z + f₂ z) * spatialPartial φ j z =
        -∫ z in spaceTimeSet Ω I, (g₁ z + g₂ z) * φ z := by
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  let dψ : Vec3 × ℝ → ℝ := fun q => spatialPartial ψ j q
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψc : HasCompactSupport ψ := hφ.2.1
  have hψU : tsupport ψ ⊆ spaceTimeSet Ω I := hφ.2.2
  have hdψd : ContDiff ℝ (⊤ : ℕ∞) dψ := spatialPartial_contDiff hψd j
  have hdψc : HasCompactSupport dψ := hasCompactSupport_spatialPartial hψc j
  have hdψU : tsupport dψ ⊆ spaceTimeSet Ω I :=
    (tsupport_spatialPartial_subset j).trans hψU
  have hA₁ := uc_integrable_mul_test hΩ hI hf₁ hdψd hdψc hdψU
  have hA₂ := uc_integrable_mul_test hΩ hI hf₂ hdψd hdψc hdψU
  have hB₁ := uc_integrable_mul_test hΩ hI hg₁ hψd hψc hψU
  have hB₂ := uc_integrable_mul_test hΩ hI hg₂ hψd hψc hψU
  have hA₁' : IntegrableOn
      (fun z : ParabolicPoint => f₁ z * spatialPartial φ j z)
      (spaceTimeSet Ω I) volume := by
    convert hA₁ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hA₂' : IntegrableOn
      (fun z : ParabolicPoint => f₂ z * spatialPartial φ j z)
      (spaceTimeSet Ω I) volume := by
    convert hA₂ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hB₁' : IntegrableOn
      (fun z : ParabolicPoint => g₁ z * φ z)
      (spaceTimeSet Ω I) volume := by
    convert hB₁ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hB₂' : IntegrableOn
      (fun z : ParabolicPoint => g₂ z * φ z)
      (spaceTimeSet Ω I) volume := by
    convert hB₂ using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  calc
    (∫ z in spaceTimeSet Ω I, (f₁ z + f₂ z) * spatialPartial φ j z) =
        (∫ z in spaceTimeSet Ω I, f₁ z * spatialPartial φ j z) +
          (∫ z in spaceTimeSet Ω I, f₂ z * spatialPartial φ j z) := by
          rw [← integral_add hA₁' hA₂']
          congr 1
          ext z
          ring
    _ = -((∫ z in spaceTimeSet Ω I, g₁ z * φ z) +
          (∫ z in spaceTimeSet Ω I, g₂ z * φ z)) := by
          rw [h₁ φ hφ, h₂ φ hφ]
          ring
    _ = -∫ z in spaceTimeSet Ω I, (g₁ z + g₂ z) * φ z := by
          rw [← integral_add hB₁' hB₂']
          congr 2
          ext z
          ring

/-- Smooth scalar multiplication preserves the space-time weak derivative
structure, with the usual first, second, and time product rules. -/
theorem ucCutoff_hasSpaceTimeWeakDerivs
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (θ : Vec3 → ℝ) (η χ : ℝ → ℝ)
    (hξ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ucCutoffScalar θ η χ z))
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hw : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω I
      (ucCutoffField θ η χ w)
      (ucCutoffDw θ η χ w Dw)
      (ucCutoffD2 θ η χ w Dw D2w)
      (ucCutoffDt θ η χ w Dtw) := by
  let ξ : Vec3 × ℝ → ℝ := fun z => ucCutoffScalar θ η χ z
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
      ξ (parabolicHomeomorph z) = ucCutoffScalar θ η χ z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξsp (j : Fin 3) (z : ParabolicPoint) :
      spatialPartial ξ j (parabolicHomeomorph z) =
        spatialPartial (ucCutoffScalar θ η χ) j z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξtime (z : ParabolicPoint) :
      timePartial ξ (parabolicHomeomorph z) =
        timePartial (ucCutoffScalar θ η χ) z := by
    rcases z with ⟨x, s⟩
    rfl
  have hξsecond (j k : Fin 3) (z : ParabolicPoint) :
      spatialSecondPartial ξ j k (parabolicHomeomorph z) =
        spatialSecondPartial (ucCutoffScalar θ η χ) j k z := by
    rcases z with ⟨x, s⟩
    rfl
  rcases hw with ⟨hwl, hDwl, hD2wl, hDtwl, hweak⟩
  have hwi (i : Fin 3) : LocallyIntegrableOn (fun z => w z i)
      (spaceTimeSet Ω I) volume := uc_locallyIntegrableOn_pi_eval hwl i
  have hDwij (i j : Fin 3) : LocallyIntegrableOn (fun z => Dw z i j)
      (spaceTimeSet Ω I) volume := by
    have hi : LocallyIntegrableOn (fun z => Dw z i)
        (spaceTimeSet Ω I) volume := uc_locallyIntegrableOn_pi_eval hDwl i
    exact uc_locallyIntegrableOn_pi_eval hi j
  have hD2wijk (i j k : Fin 3) : LocallyIntegrableOn (fun z => D2w z i j k)
      (spaceTimeSet Ω I) volume := by
    have hi : LocallyIntegrableOn (fun z => D2w z i)
        (spaceTimeSet Ω I) volume := uc_locallyIntegrableOn_pi_eval hD2wl i
    have hij : LocallyIntegrableOn (fun z => D2w z i j)
        (spaceTimeSet Ω I) volume := uc_locallyIntegrableOn_pi_eval hi j
    exact uc_locallyIntegrableOn_pi_eval hij k
  have hDtwi (i : Fin 3) : LocallyIntegrableOn (fun z => Dtw z i)
      (spaceTimeSet Ω I) volume := uc_locallyIntegrableOn_pi_eval hDtwl i
  have hcutw : LocallyIntegrableOn (ucCutoffField θ η χ w)
      (spaceTimeSet Ω I) volume := by
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro i
    convert uc_locallyIntegrableOn_smooth_mul hΩ hI (hwi i) hξsmooth using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutDw : LocallyIntegrableOn (ucCutoffDw θ η χ w Dw)
      (spaceTimeSet Ω I) volume := by
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro i
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro j
    have hA := uc_locallyIntegrableOn_smooth_mul hΩ hI (hDwij i j) hξsmooth
    have hB := uc_locallyIntegrableOn_mul_smooth hΩ hI (hwi i) (hξj j)
    convert hA.add hB using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutD2 : LocallyIntegrableOn (ucCutoffD2 θ η χ w Dw D2w)
      (spaceTimeSet Ω I) volume := by
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro i
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro j
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro k
    have hA := uc_locallyIntegrableOn_smooth_mul hΩ hI
      (hD2wijk i j k) hξsmooth
    have hB := uc_locallyIntegrableOn_smooth_mul hΩ hI
      (hDwij i j) (hξj k)
    have hC := uc_locallyIntegrableOn_smooth_mul hΩ hI
      (hDwij i k) (hξj j)
    have hD := uc_locallyIntegrableOn_mul_smooth hΩ hI
      (hwi i) (hξjk j k)
    convert ((hA.add hB).add hC).add hD using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  have hcutDt : LocallyIntegrableOn (ucCutoffDt θ η χ w Dtw)
      (spaceTimeSet Ω I) volume := by
    apply uc_locallyIntegrableOn_pi hΩ hI
    intro i
    have hA := uc_locallyIntegrableOn_smooth_mul hΩ hI (hDtwi i) hξsmooth
    have hB := uc_locallyIntegrableOn_mul_smooth hΩ hI (hwi i) hξt
    convert hA.add hB using 1
    ext z
    rcases z with ⟨x, s⟩
    rfl
  refine ⟨hcutw, hcutDw, hcutD2, hcutDt, ?_⟩
  intro φ hφ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hp := uc_weak_spatial_product hΩ hI (hwi i) (hDwij i j) j
      (fun ψ hψ => (hweak ψ hψ).1 i j) hξsmooth φ hφ
    simpa only [ucCutoffField, ucCutoffDw, ξ, Pi.smul_apply, smul_eq_mul,
      hξpoint, hξsp, mul_comm] using hp
  · intro i j k
    have hA : LocallyIntegrableOn
        (fun z : ParabolicPoint => Dw z i j * ξ (parabolicHomeomorph z))
        (spaceTimeSet Ω I) volume :=
      uc_locallyIntegrableOn_mul_smooth hΩ hI (hDwij i j) hξsmooth
    have hB : LocallyIntegrableOn
        (fun z : ParabolicPoint => w z i *
          spatialPartial ξ j (parabolicHomeomorph z))
        (spaceTimeSet Ω I) volume :=
      uc_locallyIntegrableOn_mul_smooth hΩ hI (hwi i) (hξj j)
    have hG₁ : LocallyIntegrableOn
        (fun z : ParabolicPoint =>
          D2w z i j k * ξ (parabolicHomeomorph z) +
            Dw z i j * spatialPartial ξ k (parabolicHomeomorph z))
        (spaceTimeSet Ω I) volume :=
      (uc_locallyIntegrableOn_mul_smooth hΩ hI (hD2wijk i j k) hξsmooth).add
        (uc_locallyIntegrableOn_mul_smooth hΩ hI (hDwij i j) (hξj k))
    have hG₂ : LocallyIntegrableOn
        (fun z : ParabolicPoint =>
          Dw z i k * spatialPartial ξ j (parabolicHomeomorph z) +
            w z i * spatialSecondPartial ξ j k (parabolicHomeomorph z))
        (spaceTimeSet Ω I) volume :=
      (uc_locallyIntegrableOn_mul_smooth hΩ hI (hDwij i k) (hξj j)).add
        (uc_locallyIntegrableOn_mul_smooth hΩ hI (hwi i) (hξjk j k))
    have hp₁ (ψ : ParabolicPoint → ℝ)
        (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :=
      uc_weak_spatial_product hΩ hI (hDwij i j) (hD2wijk i j k) k
        (fun ϕ hϕ => (hweak ϕ hϕ).2.1 i j k) hξsmooth ψ hψ
    have hp₂ (ψ : ParabolicPoint → ℝ)
        (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :=
      uc_weak_spatial_product hΩ hI (hwi i) (hDwij i k) k
        (fun ϕ hϕ => (hweak ϕ hϕ).1 i k) (hξj j) ψ hψ
    have hsum := uc_weak_spatial_add hΩ hI hA hB hG₁ hG₂ k hp₁ hp₂ φ hφ
    have hleft (z : ParabolicPoint) :
        ucCutoffDw θ η χ w Dw z i j =
          Dw z i j * ξ (parabolicHomeomorph z) +
            w z i * spatialPartial ξ j (parabolicHomeomorph z) := by
      rw [hξpoint, hξsp]
      simp only [ucCutoffDw]
      ring
    have hright (z : ParabolicPoint) :
        ucCutoffD2 θ η χ w Dw D2w z i j k =
          D2w z i j k * ξ (parabolicHomeomorph z) +
            Dw z i j * spatialPartial ξ k (parabolicHomeomorph z) +
            (Dw z i k * spatialPartial ξ j (parabolicHomeomorph z) +
              w z i * spatialSecondPartial ξ j k (parabolicHomeomorph z)) := by
      rw [hξpoint, hξsp, hξsp, hξsecond]
      simp only [ucCutoffD2]
      ring
    simpa only [hleft, hright] using hsum
  · intro i
    have hp := uc_weak_time_product hΩ hI (hwi i) (hDtwi i)
      (fun ψ hψ => (hweak ψ hψ).2.2 i) hξsmooth φ hφ
    simpa only [ucCutoffField, ucCutoffDt, ξ, Pi.smul_apply, smul_eq_mul,
      hξpoint, hξtime, mul_comm] using hp
end ESS
