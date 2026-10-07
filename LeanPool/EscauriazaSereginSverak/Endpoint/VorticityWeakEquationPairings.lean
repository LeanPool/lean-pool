/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityPairing
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestOperators
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Local integrability and convection pairings for vorticity

The suitable solution supplies the integrability and spatial pairing needed
for the weak vorticity identity (manuscript `lem:vorticity-weak-eq`).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

private theorem suitableWeakConvectionPairings_integrable
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    {u ω : ParabolicPoint → Vec3} {ψ : Vec3 × ℝ → Vec3}
    (hcurl : vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I)
    (hu : ∀ i : Fin 3, MemLp (fun z : ParabolicPoint => u z i) 2
      (volume.restrict (CKN.spaceTimeSet Ω' J)))
    (hω : ∀ i : Fin 3, MemLp (fun z : ParabolicPoint => ω z i) 2
      (volume.restrict (CKN.spaceTimeSet Ω' J))) :
    IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume ∧
    IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialCross (u z) (ω z) i * vorticityTestCurl ψ z i)
      (CKN.spaceTimeSet Ω' J) volume := by
  have hleftTerm (i j : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => u z i * u z j * CKN.spatialPartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume := by
    have hpair := (hu i).integrable_mul (hu j)
    have hcurli := CKN.component_mem_spaceTimeTestFunction hcurl i
    obtain ⟨C, hC⟩ := CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcurli j
    exact hpair.mul_bdd (c := C)
      (g := fun z => CKN.spatialPartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spatialPartial_contDiff hcurli.1 j).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  have hleft : IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hleftTerm i j
  have hcrossProduct (i j : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => u z i * ω z j)
      (CKN.spaceTimeSet Ω' J) volume := (hu i).integrable_mul (hω j)
  have hcrossComponent (i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => spatialCross (u z) (ω z) i)
      (CKN.spaceTimeSet Ω' J) volume := by
    fin_cases i
    · change IntegrableOn (fun z => u z 1 * ω z 2 - u z 2 * ω z 1)
        (CKN.spaceTimeSet Ω' J) volume
      exact (hcrossProduct 1 2).sub (hcrossProduct 2 1)
    · change IntegrableOn (fun z => u z 2 * ω z 0 - u z 0 * ω z 2)
        (CKN.spaceTimeSet Ω' J) volume
      exact (hcrossProduct 2 0).sub (hcrossProduct 0 2)
    · change IntegrableOn (fun z => u z 0 * ω z 1 - u z 1 * ω z 0)
        (CKN.spaceTimeSet Ω' J) volume
      exact (hcrossProduct 0 1).sub (hcrossProduct 1 0)
  have hrightTerm (i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => spatialCross (u z) (ω z) i * vorticityTestCurl ψ z i)
      (CKN.spaceTimeSet Ω' J) volume := by
    have hcurli := CKN.component_mem_spaceTimeTestFunction hcurl i
    obtain ⟨C, hC⟩ := CKN.exists_bound_of_mem_spaceTimeTestFunction hcurli
    exact (hcrossComponent i).mul_bdd (c := C)
      (g := fun z => vorticityTestCurl ψ z i)
      hcurli.1.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  have hright : IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialCross (u z) (ω z) i * vorticityTestCurl ψ z i)
      (CKN.spaceTimeSet Ω' J) volume :=
    integrable_finsetSum _ fun i _ => hrightTerm i
  exact ⟨hleft, hright⟩

noncomputable section

private theorem vorticityFlux_entry_memLp
    {K : Set ParabolicPoint} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : MemLp Du 2 (volume.restrict K)) (i : Fin 3) :
    MemLp (fun z => weakVorticity Du z i) 2 (volume.restrict K) := by
  have hentry (i j : Fin 3) : MemLp (fun z => Du z i j) 2
      (volume.restrict K) :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
  fin_cases i
  · change MemLp (fun z => Du z 2 1 - Du z 1 2) 2 (volume.restrict K)
    exact (hentry 2 1).sub (hentry 1 2)
  · change MemLp (fun z => Du z 0 2 - Du z 2 0) 2 (volume.restrict K)
    exact (hentry 0 2).sub (hentry 2 0)
  · change MemLp (fun z => Du z 1 0 - Du z 0 1) 2 (volume.restrict K)
    exact (hentry 1 0).sub (hentry 0 1)

private theorem spatialWeakVorticity_entry_memLp
    {K : Set Vec3} {Dv : Vec3 → Fin 3 → Vec3}
    (hDv : MemLp Dv 2 (volume.restrict K)) (i : Fin 3) :
    MemLp (fun x => spatialWeakVorticity Dv x i) 2 (volume.restrict K) := by
  have hentry (i j : Fin 3) : MemLp (fun x => Dv x i j) 2
      (volume.restrict K) :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDv) i)) j
  fin_cases i
  · change MemLp (fun x => Dv x 2 1 - Dv x 1 2) 2 (volume.restrict K)
    exact (hentry 2 1).sub (hentry 1 2)
  · change MemLp (fun x => Dv x 0 2 - Dv x 2 0) 2 (volume.restrict K)
    exact (hentry 0 2).sub (hentry 2 0)
  · change MemLp (fun x => Dv x 1 0 - Dv x 0 1) 2 (volume.restrict K)
    exact (hentry 1 0).sub (hentry 0 1)

/-- Each weak-vorticity component paired with a compact test component is
integrable on a local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakVorticityTestComponentIntegrableOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) (i : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => weakVorticity Du z i * φ z i)
      (CKN.spaceTimeSet Ω' J) volume := by
  have hφi := CKN.component_mem_spaceTimeTestFunction hφ i
  fin_cases i
  · change IntegrableOn (fun z : ParabolicPoint =>
      (Du z 2 1 - Du z 1 2) * φ z 0) (CKN.spaceTimeSet Ω' J) volume
    have h21 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 2 1
    have h12 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 1 2
    have heq : (fun z : ParabolicPoint =>
        Du z 2 1 * φ z 0 - Du z 1 2 * φ z 0) =ᵐ[
        volume.restrict (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 2 1 - Du z 1 2) * φ z 0) := by
      filter_upwards [] with z
      ring
    exact (h21.sub h12).congr heq
  · change IntegrableOn (fun z : ParabolicPoint =>
      (Du z 0 2 - Du z 2 0) * φ z 1) (CKN.spaceTimeSet Ω' J) volume
    have h02 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 0 2
    have h20 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 2 0
    have heq : (fun z : ParabolicPoint =>
        Du z 0 2 * φ z 1 - Du z 2 0 * φ z 1) =ᵐ[
        volume.restrict (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 0 2 - Du z 2 0) * φ z 1) := by
      filter_upwards [] with z
      ring
    exact (h02.sub h20).congr heq
  · change IntegrableOn (fun z : ParabolicPoint =>
      (Du z 1 0 - Du z 0 1) * φ z 2) (CKN.spaceTimeSet Ω' J) volume
    have h10 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 1 0
    have h01 := suitableWeakGradientTestIntegrableOnBox hdata hbox hφi 0 1
    have heq : (fun z : ParabolicPoint =>
        Du z 1 0 * φ z 2 - Du z 0 1 * φ z 2) =ᵐ[
        volume.restrict (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 1 0 - Du z 0 1) * φ z 2) := by
      filter_upwards [] with z
      ring
    exact (h10.sub h01).congr heq

/-- The weak-vorticity flux paired with a spatial derivative of a compact
field is integrable on a local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakVorticityFluxTestIntegrableOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I)
    (hψbox : tsupport (show ParabolicPoint → Vec3 from ψ) ⊆
      CKN.spaceTimeSet Ω' J) :
    IntegrableOn (fun z : ParabolicPoint =>
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume := by
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) :=
    (CKN.isSuitableWeakSolution_iff_integrable.mp h).toData
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from ψ)
  have hK : IsCompact K := CKN.isCompact_tsupport_parabolic hψ.2.1
  have hKΩ : K ⊆ CKN.spaceTimeSet Ω I :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  have hKS : K ⊆ CKN.spaceTimeSet Ω' J := hψbox
  have hu : MemLp u 2 (volume.restrict K) :=
    CKN.velocity_memLp_two_on_compact_of_data hdata hK hKΩ
  have hDu : MemLp Du 2 (volume.restrict K) :=
    CKN.gradient_memLp_two_on_compact_of_data hdata hK hKΩ
  have hω (i : Fin 3) : MemLp (fun z : ParabolicPoint => weakVorticity Du z i)
      2 (volume.restrict K) := vorticityFlux_entry_memLp hDu i
  have hterm (j i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint =>
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z) K volume := by
    have huEntry : MemLp (fun z : ParabolicPoint => u z j) 2
        (volume.restrict K) :=
      hu.continuousLinearMap_comp (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
    have hprod : IntegrableOn
        (fun z : ParabolicPoint => u z j * weakVorticity Du z i -
          weakVorticity Du z j * u z i) K volume := by
      have h₁ := huEntry.integrable_mul (hω i)
      have h₂ := (hω j).integrable_mul
        (hu.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))
      exact h₁.sub h₂
    have hψi := CKN.component_mem_spaceTimeTestFunction hψ i
    obtain ⟨C, hC⟩ := CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψi j
    have hflux : IntegrableOn (fun z : ParabolicPoint => vorticityFlux u Du z j i)
        K volume := by
      simpa only [vorticityFlux] using hprod
    exact hflux.mul_bdd (c := C)
      (g := fun z => CKN.spatialPartial (fun w : Vec3 × ℝ => ψ w i) j z)
      (CKN.spatialPartial_contDiff hψi.1 j).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  have hKint : IntegrableOn (fun z : ParabolicPoint =>
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z) K volume := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact integrable_finsetSum _ fun i _ => hterm j i
  have hzero (z : ParabolicPoint) (hz : z ∉ K) :
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z = 0 := by
    have hzψ : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
      intro hmem
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from ψ)
      rw [CKN.tsupport_parabolic_eq]
      exact hmem
    have hderiv (i j : Fin 3) : CKN.spatialPartial
        (fun w : Vec3 × ℝ => ψ w i) j z = 0 := by
      have hcomp : (show Vec3 × ℝ from z) ∉
          tsupport (fun w : Vec3 × ℝ => ψ w i) := by
        intro hi
        exact hzψ ((CKN.tsupport_component_subset (ι := Fin 3)
          ψ i (by intro y hy; simp [hy])) hi)
      exact CKN.spatialPartial_eq_zero_off_tsupport hcomp j
    simp [hderiv]
  apply hKint.of_ae_sdiff_eq_zero (localBox_spaceTimeSet_nullMeasurable hbox)
  filter_upwards [] with z hz
  exact hzero z hz.2

/-- The nonlinear momentum pairing against the curl of a test equals the
space-time pairing with velocity crossed with weak vorticity. -/
theorem suitableWeakConvectionPairingOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I)
    (hψbox : tsupport (show ParabolicPoint → Vec3 from ψ) ⊆
      CKN.spaceTimeSet Ω' J) :
    ∫ z in CKN.spaceTimeSet Ω' J,
      ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
    ∫ z in CKN.spaceTimeSet Ω' J,
      ∑ i : Fin 3,
        spatialCross (u z) (weakVorticity Du z) i * vorticityTestCurl ψ z i := by
  have hInt : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ => 0) :=
    CKN.isSuitableWeakSolution_iff_integrable.mp h
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) := hInt.toData
  have hcurl : vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I :=
    vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hS := localBox_spaceTimeSet_nullMeasurable hbox
  have hboxLp := CKN.Core.Step3.local_memLp_two_of_energy
    (hu := hdata.aestronglyMeasurable_velocity hbox)
    (hDu := hdata.aestronglyMeasurable_gradient hbox)
    (henergy := hdata.energy_lintegral_lt_top hbox)
  have hu (i : Fin 3) : MemLp (fun z : ParabolicPoint => u z i) 2
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    hboxLp.1.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hDuMem : MemLp Du 2 (volume.restrict (CKN.spaceTimeSet Ω' J)) := hboxLp.2
  have hωMem : MemLp (fun z : ParabolicPoint => weakVorticity Du z) 2
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    memLp_pi_iff.mpr (fun i => vorticityFlux_entry_memLp hDuMem i)
  have hω (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => weakVorticity Du z i) 2
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    hωMem.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have ⟨hleft, hright⟩ := suitableWeakConvectionPairings_integrable hcurl hu hω
  have hleftIter := vorticity_integral_on_box_eq_iterated hleft
  have hrightIter := vorticity_integral_on_box_eq_iterated hright
  have hmem := CKN.slice_memLp_ae_of_sws hInt hbox
  have hweak := suitableWeakGradientOnSlices h Ω' J hbox
  have hweakAE : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn Ω' (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
    rw [ae_all_iff]
    exact hweak
  have htrace := suitableWeakGradientTraceZeroOnBox h Ω' J hbox
  have hψbox' : tsupport ψ ⊆ Ω' ×ˢ J := by
    intro z hz
    have hzP : (show ParabolicPoint from z) ∈
        tsupport (show ParabolicPoint → Vec3 from ψ) := by
      rw [CKN.tsupport_parabolic_eq]
      exact hz
    exact hψbox hzP
  have hcurlBox : tsupport (vorticityTestCurl ψ) ⊆ Ω' ×ˢ J :=
    vorticityTestCurl_tsupport_subset.trans hψbox'
  have hcurlComponent (i : Fin 3) :
      (fun z : Vec3 × ℝ => vorticityTestCurl ψ z i) ∈
        CKN.spaceTimeTestFunction (V := ℝ) Ω I :=
    CKN.component_mem_spaceTimeTestFunction hcurl i
  have hcurlComponentBox (i : Fin 3) :
      tsupport (fun z : Vec3 × ℝ => vorticityTestCurl ψ z i) ⊆ Ω' ×ˢ J := by
    exact (CKN.tsupport_component_subset (ι := Fin 3)
      (vorticityTestCurl ψ) i (by intro z hz; simp [hz])).trans hcurlBox
  have hsliceEq : ∀ᵐ t ∂(volume.restrict J),
      (∫ x in Ω', ∑ i : Fin 3, ∑ j : Fin 3,
        u (x, t) i * u (x, t) j * CKN.spatialDeriv
          (fun y : Vec3 => vorticityTestCurl ψ (y, t) i) j x) =
      (∫ x in Ω', ∑ i : Fin 3,
        spatialCross (u (x, t)) (spatialWeakVorticity (fun x => Du (x, t)) x) i *
          vorticityTestCurl ψ (x, t) i) := by
    filter_upwards [hmem, hweakAE, htrace] with t ht hwt hdiv
    let Φ : Vec3 → Vec3 := fun x => vorticityTestCurl ψ (x, t)
    have hΦsmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => Φ x i) :=
      (CKN.slice_testFunction (hcurlComponent i).1 (hcurlComponent i).2.1
        (hcurlComponentBox i) t).1
    have hΦcompact (i : Fin 3) : HasCompactSupport (fun x : Vec3 => Φ x i) :=
      (CKN.slice_testFunction (hcurlComponent i).1 (hcurlComponent i).2.1
        (hcurlComponentBox i) t).2.1
    have hΦΩ (i : Fin 3) : tsupport (fun x : Vec3 => Φ x i) ⊆ Ω' :=
      (CKN.slice_testFunction (hcurlComponent i).1 (hcurlComponent i).2.1
        (hcurlComponentBox i) t).2.2
    have hdivΦ (x : Vec3) : ∑ i : Fin 3,
        CKN.spatialDeriv (fun y : Vec3 => Φ y i) i x = 0 := by
      have hd := vorticityTestCurl_divergence hψ.1 (x, t)
      simpa [Φ, CKN.spatialDeriv, vorticityTestPartial] using hd
    have hpair := suitableWeakConvectionPairingDivergenceFree
      hbox.1
      (by
        have hle : (volume : Measure Vec3) Ω' ≤ volume (closure Ω') :=
          measure_mono subset_closure
        have hlt : (volume : Measure Vec3) (closure Ω') < ⊤ :=
          hbox.2.1.measure_lt_top
        change (volume.restrict Ω') Set.univ < ⊤
        simpa [Measure.restrict_apply_univ, hbox.1.measurableSet] using
          lt_of_le_of_lt hle hlt)
      (fun i => (memLp_pi_iff.mp ht.1) i) ht.2
      hwt hdiv
      hΦsmooth hΦcompact hΦΩ hdivΦ
    have hleftIntegrable (i j : Fin 3) : IntegrableOn
        (fun x : Vec3 => u (x, t) i * u (x, t) j *
          CKN.spatialDeriv (fun y : Vec3 => Φ y i) j x) Ω' volume := by
      have hu_i : MemLp (fun x : Vec3 => u (x, t) i) 2 (volume.restrict Ω') :=
        (memLp_pi_iff.mp ht.1) i
      have hu_j : MemLp (fun x : Vec3 => u (x, t) j) 2 (volume.restrict Ω') :=
        (memLp_pi_iff.mp ht.1) j
      have hprod := hu_i.integrable_mul hu_j
      obtain ⟨C, hC⟩ := CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
        (hcurlComponent i) j
      exact hprod.mul_bdd (c := C)
        (g := fun x => CKN.spatialDeriv (fun y : Vec3 => Φ y i) j x)
        (CKN.contDiff_spatialDeriv_smooth (hΦsmooth i) j).continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          have hbound := hC (x, t)
          simpa [Φ, CKN.spatialPartial, CKN.spatialDeriv] using hbound)
    have hleftIntegrableSum (i : Fin 3) : IntegrableOn
        (fun x : Vec3 => ∑ j : Fin 3,
          u (x, t) i * u (x, t) j *
            CKN.spatialDeriv (fun y : Vec3 => Φ y i) j x) Ω' volume :=
      integrable_finsetSum _ fun j _ => hleftIntegrable i j
    have hrightProduct (i j : Fin 3) : IntegrableOn
        (fun x : Vec3 => u (x, t) i * spatialWeakVorticity (fun y => Du (y, t)) x j)
        Ω' volume := by
      exact ((memLp_pi_iff.mp ht.1) i).integrable_mul
        (spatialWeakVorticity_entry_memLp ht.2 j)
    have hrightComponent (i : Fin 3) : IntegrableOn
        (fun x : Vec3 => spatialCross (u (x, t))
          (spatialWeakVorticity (fun y => Du (y, t)) x) i) Ω' volume := by
      fin_cases i
      · change IntegrableOn (fun x =>
          u (x, t) 1 * spatialWeakVorticity (fun y => Du (y, t)) x 2 -
          u (x, t) 2 * spatialWeakVorticity (fun y => Du (y, t)) x 1) Ω' volume
        exact (hrightProduct 1 2).sub (hrightProduct 2 1)
      · change IntegrableOn (fun x =>
          u (x, t) 2 * spatialWeakVorticity (fun y => Du (y, t)) x 0 -
          u (x, t) 0 * spatialWeakVorticity (fun y => Du (y, t)) x 2) Ω' volume
        exact (hrightProduct 2 0).sub (hrightProduct 0 2)
      · change IntegrableOn (fun x =>
          u (x, t) 0 * spatialWeakVorticity (fun y => Du (y, t)) x 1 -
          u (x, t) 1 * spatialWeakVorticity (fun y => Du (y, t)) x 0) Ω' volume
        exact (hrightProduct 0 1).sub (hrightProduct 1 0)
    have hrightIntegrable (i : Fin 3) : IntegrableOn
        (fun x : Vec3 => spatialCross (u (x, t))
          (spatialWeakVorticity (fun y => Du (y, t)) x) i * Φ x i) Ω' volume := by
      obtain ⟨C, hC⟩ := CKN.exists_bound_of_mem_spaceTimeTestFunction (hcurlComponent i)
      exact (hrightComponent i).mul_bdd (c := C) (g := fun x => Φ x i)
        (hΦsmooth i).continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          have hbound := hC (x, t)
          simpa [Φ] using hbound)
    have hleftSum :
        (∫ x in Ω', ∑ i : Fin 3, ∑ j : Fin 3,
          u (x, t) i * u (x, t) j *
            CKN.spatialDeriv (fun y : Vec3 => Φ y i) j x) =
        ∑ i : Fin 3, ∫ x in Ω', ∑ j : Fin 3,
          u (x, t) i * u (x, t) j *
            CKN.spatialDeriv (fun y : Vec3 => Φ y i) j x := by
      rw [integral_finsetSum _ (fun i _ => hleftIntegrableSum i)]
    have hrightSum :
        (∫ x in Ω', ∑ i : Fin 3,
          spatialCross (u (x, t)) (spatialWeakVorticity (fun y => Du (y, t)) x) i *
            Φ x i) =
        ∑ i : Fin 3, ∫ x in Ω',
          spatialCross (u (x, t)) (spatialWeakVorticity (fun y => Du (y, t)) x) i *
            Φ x i := by
      rw [integral_finsetSum _ (fun i _ => hrightIntegrable i)]
    rw [← hleftSum, ← hrightSum] at hpair
    exact hpair
  calc
    (∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z j * CKN.spatialPartial
            (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z) =
      ∫ t in J, ∫ x in Ω',
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (x, t) i * u (x, t) j * CKN.spatialPartial
            (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j (x, t) := hleftIter
    _ = ∫ t in J, ∫ x in Ω',
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (x, t) i * u (x, t) j * CKN.spatialDeriv
            (fun y : Vec3 => vorticityTestCurl ψ (y, t) i) j x := by
              apply integral_congr_ae
              filter_upwards [] with t
              apply integral_congr_ae
              filter_upwards [] with x
              rfl
    _ = ∫ t in J, ∫ x in Ω',
        ∑ i : Fin 3,
          spatialCross (u (x, t))
            (spatialWeakVorticity (fun y => Du (y, t)) x) i *
            vorticityTestCurl ψ (x, t) i := by
              apply integral_congr_ae
              exact hsliceEq
    _ = ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3,
          spatialCross (u z) (weakVorticity Du z) i * vorticityTestCurl ψ z i :=
            hrightIter.symm


end

end ESS
