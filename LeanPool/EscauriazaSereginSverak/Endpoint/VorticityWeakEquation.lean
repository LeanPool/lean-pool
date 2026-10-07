/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityPairing
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEquationPairings
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestOperators
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Distributional vorticity equation

The curl of the suitable momentum identity gives the local weak equation for
vorticity (manuscript `lem:vorticity-weak-eq`).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section


private theorem vorticityFlux_spaceTimeTestCurl_pairing
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {ψ : Vec3 × ℝ → Vec3} (z : ParabolicPoint) :
    (∑ j : Fin 3, ∑ i : Fin 3,
      vorticityFlux u Du z j i * CKN.spatialPartial
        (fun w : Vec3 × ℝ => ψ w i) j z) =
      ∑ i : Fin 3,
        spatialCross (u z) (weakVorticity Du z) i * vorticityTestCurl ψ z i := by
  rcases z with ⟨x, t⟩
  let ψt : Vec3 → Vec3 := fun y => ψ (y, t)
  have hstatic := vorticityFlux_spatialTestCurl_pairing
    (u (x, t)) (spatialWeakVorticity (fun y => Du (y, t)) x) ψt x
  have hω : spatialWeakVorticity (fun y => Du (y, t)) x =
      weakVorticity Du (x, t) := by
    funext i
    fin_cases i <;> rfl
  rw [hω] at hstatic
  simpa [ψt, vorticityFlux, weakVorticity, spatialWeakVorticity,
    vorticityTestCurl, vorticityTestPartial, CKN.spatialPartial,
    spatialTestCurl, CKN.spatialDeriv] using hstatic

/-- The divergence-free momentum test's viscous term is the negative weak
vorticity pairing against the Laplacian of the test curl. -/
private theorem suitableWeakViscousCurlPairingOnBox
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
        Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
      -∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3,
          u z i * vorticityTestLaplacian (vorticityTestCurl ψ)
            (show Vec3 × ℝ from z) i := by
  have hInt : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ => 0) :=
    CKN.isSuitableWeakSolution_iff_integrable.mp h
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) := hInt.toData
  have hcurl : vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I :=
    vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hcurlBoxOrd : tsupport (vorticityTestCurl ψ) ⊆ Ω' ×ˢ J := by
    have hψbox' : tsupport ψ ⊆ Ω' ×ˢ J := by
      intro z hz
      have hzP : (show ParabolicPoint from z) ∈
          tsupport (show ParabolicPoint → Vec3 from ψ) := by
        rw [CKN.tsupport_parabolic_eq]
        exact hz
      exact hψbox hzP
    exact vorticityTestCurl_tsupport_subset.trans hψbox'
  have hcurlComp (i : Fin 3) :
      (fun z : Vec3 × ℝ => vorticityTestCurl ψ z i) ∈
        CKN.spaceTimeTestFunction (V := ℝ) Ω I :=
    CKN.component_mem_spaceTimeTestFunction hcurl i
  have hcurlCompBox (i : Fin 3) :
      tsupport (fun z : Vec3 × ℝ => vorticityTestCurl ψ z i) ⊆ Ω' ×ˢ J := by
    exact (CKN.tsupport_component_subset (ι := Fin 3)
      (vorticityTestCurl ψ) i (by intro z hz; simp [hz])).trans hcurlBoxOrd
  have hcurlLap := vorticityTestLaplacian_mem_spaceTimeTestFunction hcurl
  have hL (i j : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => Du z i j * CKN.spatialPartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume :=
    suitableWeakGradientTestIntegrableOnBox hdata hbox
      (vorticitySpatialPartialTest (hcurlComp i) j) i j
  have hR (i j : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => u z i * CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z)
      (CKN.spaceTimeSet Ω' J) volume := by
    have hpartialTest := vorticitySpatialPartialTest (hcurlComp i) j
    exact suitableWeakVelocityTestIntegrableOnBox hdata hbox
      (vorticitySpatialPartialTest hpartialTest j) i
  have hLsum (i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => ∑ j : Fin 3,
        Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume :=
    integrable_finsetSum _ fun j _ => hL i j
  have hRsum (i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => ∑ j : Fin 3,
        u z i * CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z)
      (CKN.spaceTimeSet Ω' J) volume :=
    integrable_finsetSum _ fun j _ => hR i j
  have hRlap (i : Fin 3) : IntegrableOn
      (fun z : ParabolicPoint => u z i * vorticityTestLaplacian
        (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i)
      (CKN.spaceTimeSet Ω' J) volume := by
    have heq : (fun z : ParabolicPoint => ∑ j : Fin 3,
        u z i * CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z) =ᵐ[
        volume.restrict (CKN.spaceTimeSet Ω' J)]
        (fun z : ParabolicPoint => u z i * vorticityTestLaplacian
          (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i) := by
      filter_upwards [] with z
      simp [vorticityTestLaplacian, CKN.spatialSecondPartial, ← Finset.mul_sum]
    exact (hRsum i).congr heq
  have hPair (i j : Fin 3) :
      ∫ z in CKN.spaceTimeSet Ω' J,
        Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
      -∫ z in CKN.spaceTimeSet Ω' J,
        u z i * CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z := by
    let φ : Vec3 × ℝ → ℝ := fun w => CKN.spatialPartial
      (fun y : Vec3 × ℝ => vorticityTestCurl ψ y i) j w
    have hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I :=
      vorticitySpatialPartialTest (hcurlComp i) j
    have hφbox : tsupport φ ⊆ Ω' ×ˢ J := by
      exact (CKN.tsupport_spatialPartial_subset j).trans (hcurlCompBox i)
    have hweak := suitableWeakSpatialIntegrationByParts h Ω' J hbox
      hφ.1 hφ.2.1 hφbox i j
    have hDuInt := suitableWeakGradientTestIntegrableOnBox hdata hbox hφ i j
    have hpartialφTest := vorticitySpatialPartialTest hφ j
    have hUInt := suitableWeakVelocityTestIntegrableOnBox hdata hbox hpartialφTest i
    have hDuIter := vorticity_integral_on_box_eq_iterated hDuInt
    have hUIter := vorticity_integral_on_box_eq_iterated hUInt
    calc
      ∫ z in CKN.spaceTimeSet Ω' J,
          Du z i j * CKN.spatialPartial
            (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
        ∫ t in J, ∫ x in Ω', Du (x, t) i j * φ (x, t) := by
          simpa only [φ] using hDuIter
      _ = -∫ t in J, ∫ x in Ω',
          u (x, t) i * CKN.spatialPartial φ j (x, t) := hweak
      _ = -∫ z in CKN.spaceTimeSet Ω' J,
          u z i * CKN.spatialSecondPartial
            (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z := by
          rw [← hUIter]
          congr 1
  have hPairSum (i : Fin 3) :
      ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ j : Fin 3, Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
      -∫ z in CKN.spaceTimeSet Ω' J,
        ∑ j : Fin 3, u z i * CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z := by
    rw [integral_finsetSum _ (fun j _ => hL i j),
      integral_finsetSum _ (fun j _ => hR i j)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hPair i j
  have htotalLeft : IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z)
      (CKN.spaceTimeSet Ω' J) volume :=
    integrable_finsetSum _ fun i _ => hLsum i
  have htotalRight : IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, u z i * vorticityTestLaplacian
        (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i)
      (CKN.spaceTimeSet Ω' J) volume := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact suitableWeakVelocityTestIntegrableOnBox hdata hbox
      (CKN.component_mem_spaceTimeTestFunction hcurlLap i) i
  calc
    (∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Du z i j * CKN.spatialPartial
            (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z) =
      ∑ i : Fin 3, ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ j : Fin 3, Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z := by
            rw [integral_finsetSum _ (fun i _ => hLsum i)]
    _ = -∑ i : Fin 3, ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ j : Fin 3, u z i * CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => vorticityTestCurl ψ w i) j j z := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            exact hPairSum i
    _ = -∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, u z i * vorticityTestLaplacian
          (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i := by
            congr 1
            rw [integral_finsetSum _ (fun i _ => hRlap i)]
            apply Finset.sum_congr rfl
            intro i hi
            apply integral_congr_ae
            filter_upwards [] with z
            simp [vorticityTestLaplacian, CKN.spatialSecondPartial,
              ← Finset.mul_sum]

private theorem vorticityTestCurl_partials_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → Vec3}
    (_hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I)
    (z : ParabolicPoint)
    (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from vorticityTestCurl ψ)) :
    (∀ i : Fin 3, CKN.timePartial
      (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z = 0) ∧
    (∀ i j : Fin 3, CKN.spatialPartial
      (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z = 0) := by
  have hnot (i : Fin 3) : (show Vec3 × ℝ from z) ∉
      tsupport (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) := by
    intro hi
    apply hz
    rw [CKN.tsupport_parabolic_eq]
    exact (CKN.tsupport_component_subset (ι := Fin 3)
      (vorticityTestCurl ψ) i (by intro w hw; simp [hw])) hi
  constructor
  · intro i
    apply CKN.timePartial_eq_zero_off_tsupport
    exact hnot i
  · intro i j
    apply CKN.spatialPartial_eq_zero_off_tsupport
    exact hnot i

private theorem suitableWeakVorticityViscousIdentityOnBox
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
        Du z i j * CKN.spatialPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z =
    -∫ z in CKN.spaceTimeSet Ω' J,
      ∑ i : Fin 3, weakVorticity Du z i *
        vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i := by
  have hψboxOrd : tsupport ψ ⊆ Ω' ×ˢ J := by
    intro z hz
    have hzP : (show ParabolicPoint from z) ∈
        tsupport (show ParabolicPoint → Vec3 from ψ) := by
      rw [CKN.tsupport_parabolic_eq]
      exact hz
    exact hψbox hzP
  have hlapTest := vorticityTestLaplacian_mem_spaceTimeTestFunction hψ
  have hlapBoxOrd : tsupport (vorticityTestLaplacian ψ) ⊆ Ω' ×ˢ J :=
    (vorticityTestLaplacian_tsupport).trans hψboxOrd
  have hlapBox : tsupport
      (show ParabolicPoint → Vec3 from vorticityTestLaplacian ψ) ⊆
        CKN.spaceTimeSet Ω' J := by
    rw [CKN.tsupport_parabolic_eq]
    exact hlapBoxOrd
  have hlapPair := suitableWeakVorticityPairingOnBox h hbox hlapTest hlapBox
  have hlapCurlComm (z : ParabolicPoint) (i : Fin 3) :
      vorticityTestCurl (vorticityTestLaplacian ψ)
          (show Vec3 × ℝ from z) i =
        vorticityTestLaplacian (vorticityTestCurl ψ)
          (show Vec3 × ℝ from z) i :=
    vorticityTestCurl_laplacian_commute hψ.1 i (show Vec3 × ℝ from z)
  calc
    _ = -∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, u z i * vorticityTestLaplacian
          (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i :=
      suitableWeakViscousCurlPairingOnBox h hbox hψ hψbox
    _ = -∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, weakVorticity Du z i *
          vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i := by
      congr 1
      calc
        (∫ z in CKN.spaceTimeSet Ω' J,
            ∑ i : Fin 3, u z i * vorticityTestLaplacian
              (vorticityTestCurl ψ) (show Vec3 × ℝ from z) i) =
          ∫ z in CKN.spaceTimeSet Ω' J,
            ∑ i : Fin 3, u z i * vorticityTestCurl
              (vorticityTestLaplacian ψ) (show Vec3 × ℝ from z) i := by
                apply integral_congr_ae
                filter_upwards [] with z
                apply Finset.sum_congr rfl
                intro i hi
                rw [hlapCurlComm]
        _ = ∫ z in CKN.spaceTimeSet Ω' J,
            ∑ i : Fin 3, weakVorticity Du z i *
              vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i := by
                simpa using hlapPair.symm

private theorem suitableWeakVorticityTimeIdentityOnBox
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
      ∑ i : Fin 3, u z i * CKN.timePartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z =
    ∫ z in CKN.spaceTimeSet Ω' J,
      ∑ i : Fin 3, weakVorticity Du z i *
        vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) i := by
  have hψboxOrd : tsupport ψ ⊆ Ω' ×ˢ J := by
    intro z hz
    have hzP : (show ParabolicPoint from z) ∈
        tsupport (show ParabolicPoint → Vec3 from ψ) := by
      rw [CKN.tsupport_parabolic_eq]
      exact hz
    exact hψbox hzP
  have htimeTest := vorticityTestTimeDerivative_mem_spaceTimeTestFunction hψ
  have htimeBoxOrd : tsupport (vorticityTestTimeDerivative ψ) ⊆ Ω' ×ˢ J :=
    (vorticityTestTimeDerivative_tsupport).trans hψboxOrd
  have htimeBox : tsupport
      (show ParabolicPoint → Vec3 from vorticityTestTimeDerivative ψ) ⊆
        CKN.spaceTimeSet Ω' J := by
    rw [CKN.tsupport_parabolic_eq]
    exact htimeBoxOrd
  have htimePair := suitableWeakVorticityPairingOnBox h hbox htimeTest htimeBox
  have htimeComm (z : ParabolicPoint) (i : Fin 3) :
      CKN.timePartial (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z =
        vorticityTestCurl (vorticityTestTimeDerivative ψ)
          (show Vec3 × ℝ from z) i := by
    change vorticityTestTimePartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z =
      vorticityTestCurl
        (fun w => fun k => vorticityTestTimePartial (fun y => ψ y k) w) z i
    exact vorticityTestCurl_timePartial hψ.1 i z
  calc
    _ = ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, u z i * vorticityTestCurl
          (vorticityTestTimeDerivative ψ) (show Vec3 × ℝ from z) i := by
            apply integral_congr_ae
            filter_upwards [] with z
            apply Finset.sum_congr rfl
            intro i hi
            rw [htimeComm]
    _ = _ := by simpa using htimePair.symm

private theorem suitableWeakVorticityNonlinearIdentityOnBox
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
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z := by
  have hconvection := suitableWeakConvectionPairingOnBox h hbox hψ hψbox
  have hfluxPair (z : ParabolicPoint) :
      (∑ i : Fin 3,
        spatialCross (u z) (weakVorticity Du z) i *
          vorticityTestCurl ψ (show Vec3 × ℝ from z) i) =
        ∑ j : Fin 3, ∑ i : Fin 3,
          vorticityFlux u Du z j i * CKN.spatialPartial
            (fun w : Vec3 × ℝ => ψ w i) j z := by
    exact (vorticityFlux_spaceTimeTestCurl_pairing (u := u) (Du := Du)
      (ψ := ψ) z).symm
  calc
    _ = ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3,
          spatialCross (u z) (weakVorticity Du z) i *
            vorticityTestCurl ψ (show Vec3 × ℝ from z) i := by
              simpa using hconvection
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfluxPair

/-- The weak vorticity equation holds on any local box containing the support
of the test field (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakVorticityEquationOnBox
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
      (-(∑ i : Fin 3, weakVorticity Du z i *
          vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) i)
        - ∑ i : Fin 3, weakVorticity Du z i *
          vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i) =
    ∫ z in CKN.spaceTimeSet Ω' J,
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z := by
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) :=
    (CKN.isSuitableWeakSolution_iff_integrable.mp h).toData
  have hψboxOrd : tsupport ψ ⊆ Ω' ×ˢ J := by
    intro w hw
    have hwP : (show ParabolicPoint from w) ∈
        tsupport (show ParabolicPoint → Vec3 from ψ) := by
      rw [CKN.tsupport_parabolic_eq]
      exact hw
    exact hψbox hwP
  have htimeTest := vorticityTestTimeDerivative_mem_spaceTimeTestFunction hψ
  have hlapTest := vorticityTestLaplacian_mem_spaceTimeTestFunction hψ
  have htimeBoxOrd : tsupport (vorticityTestTimeDerivative ψ) ⊆ Ω' ×ˢ J :=
    (vorticityTestTimeDerivative_tsupport).trans hψboxOrd
  have hlapBoxOrd : tsupport (vorticityTestLaplacian ψ) ⊆ Ω' ×ˢ J :=
    (vorticityTestLaplacian_tsupport).trans hψboxOrd
  have htimeBox : tsupport
      (show ParabolicPoint → Vec3 from vorticityTestTimeDerivative ψ) ⊆
        CKN.spaceTimeSet Ω' J := by
    rw [CKN.tsupport_parabolic_eq]
    exact htimeBoxOrd
  have hlapBox : tsupport
      (show ParabolicPoint → Vec3 from vorticityTestLaplacian ψ) ⊆
        CKN.spaceTimeSet Ω' J := by
    rw [CKN.tsupport_parabolic_eq]
    exact hlapBoxOrd
  have hcurl : vorticityTestCurl ψ ∈
      CKN.spaceTimeTestFunction (V := Vec3) Ω I :=
    vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hcurlBoxOrd : tsupport (vorticityTestCurl ψ) ⊆ Ω' ×ˢ J :=
    vorticityTestCurl_tsupport_subset.trans hψboxOrd
  have hcurlBox : tsupport
      (show ParabolicPoint → Vec3 from vorticityTestCurl ψ) ⊆
        CKN.spaceTimeSet Ω' J := by
    rw [CKN.tsupport_parabolic_eq]
    exact hcurlBoxOrd
  let K : Set ParabolicPoint :=
    tsupport (show ParabolicPoint → Vec3 from vorticityTestCurl ψ)
  have hKcompact : IsCompact K := CKN.isCompact_tsupport_parabolic hcurl.2.1
  have hKΩ : K ⊆ CKN.spaceTimeSet Ω I :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hcurl
  have hKbox : K ⊆ CKN.spaceTimeSet Ω' J := hcurlBox
  let timeTerm : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, u z i * CKN.timePartial
      (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z
  let nonlinearTerm : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * CKN.spatialPartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
  let viscousTerm : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * CKN.spatialPartial
        (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
  let momentumTerm : ParabolicPoint → ℝ := fun z =>
    -timeTerm z - nonlinearTerm z + viscousTerm z
  let omegaTimeTerm : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, weakVorticity Du z i *
      vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) i
  let omegaLaplacianTerm : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, weakVorticity Du z i *
      vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i
  let fluxTerm : ParabolicPoint → ℝ := fun z =>
    ∑ j : Fin 3, ∑ i : Fin 3,
      vorticityFlux u Du z j i * CKN.spatialPartial
        (fun w : Vec3 × ℝ => ψ w i) j z
  have htimeZero (z : ParabolicPoint) (hz : z ∉ K) :
      timeTerm z = 0 := by
    have hpartial := vorticityTestCurl_partials_zero_off_support hψ z hz
    simp [timeTerm, hpartial.1]
  have hnonlinearZero (z : ParabolicPoint) (hz : z ∉ K) :
      nonlinearTerm z = 0 := by
    have hpartial := vorticityTestCurl_partials_zero_off_support hψ z hz
    simp [nonlinearTerm, hpartial.2]
  have hviscousZero (z : ParabolicPoint) (hz : z ∉ K) :
      viscousTerm z = 0 := by
    have hpartial := vorticityTestCurl_partials_zero_off_support hψ z hz
    simp [viscousTerm, hpartial.2]
  have hmomentumSupport := suitableWeakMomentumTestCurlOnSupport h hψ
  have hmomentumSupport' : ∫ z in K, momentumTerm z = 0 := by
    simpa [K, momentumTerm] using hmomentumSupport
  have hmomentumBox : ∫ z in CKN.spaceTimeSet Ω' J, momentumTerm z = 0 := by
    calc
      ∫ z in CKN.spaceTimeSet Ω' J, momentumTerm z = ∫ z in K, momentumTerm z :=
        integralOn_eq_of_subset_of_zero_off hKbox
          (by intro z hz; simp [momentumTerm, htimeZero z hz,
            hnonlinearZero z hz, hviscousZero z hz])
      _ = 0 := hmomentumSupport'
  have htimeCompact := CKN.momentum_timeTerm_integrableOn_of_data
    hdata hKcompact hKΩ hcurl
  have hnonlinearCompact := CKN.momentum_nonlinearTerm_integrableOn_of_data
    hdata hKcompact hKΩ hcurl
  have hviscousCompact := CKN.momentum_viscousTerm_integrableOn_of_data
    hdata hKcompact hKΩ hcurl
  have htimeInt : IntegrableOn timeTerm (CKN.spaceTimeSet Ω' J) volume := by
    apply htimeCompact.of_ae_sdiff_eq_zero (localBox_spaceTimeSet_nullMeasurable hbox)
    filter_upwards [] with z hz
    exact htimeZero z hz.2
  have hnonlinearInt : IntegrableOn nonlinearTerm
      (CKN.spaceTimeSet Ω' J) volume := by
    apply hnonlinearCompact.of_ae_sdiff_eq_zero
      (localBox_spaceTimeSet_nullMeasurable hbox)
    filter_upwards [] with z hz
    exact hnonlinearZero z hz.2
  have hviscousInt : IntegrableOn viscousTerm
      (CKN.spaceTimeSet Ω' J) volume := by
    apply hviscousCompact.of_ae_sdiff_eq_zero
      (localBox_spaceTimeSet_nullMeasurable hbox)
    filter_upwards [] with z hz
    exact hviscousZero z hz.2
  have htimeSubtract :
      (∫ z in CKN.spaceTimeSet Ω' J, -timeTerm z - nonlinearTerm z) =
        (∫ z in CKN.spaceTimeSet Ω' J, -timeTerm z)
          - ∫ z in CKN.spaceTimeSet Ω' J, nonlinearTerm z :=
    integral_sub htimeInt.neg hnonlinearInt
  have hmomentumSplit :
      (∫ z in CKN.spaceTimeSet Ω' J, momentumTerm z) =
        (-(∫ z in CKN.spaceTimeSet Ω' J, timeTerm z))
          - (∫ z in CKN.spaceTimeSet Ω' J, nonlinearTerm z)
          + (∫ z in CKN.spaceTimeSet Ω' J, viscousTerm z) := by
    change (∫ z in CKN.spaceTimeSet Ω' J,
        (-timeTerm z - nonlinearTerm z) + viscousTerm z) = _
    calc
      _ = (∫ z in CKN.spaceTimeSet Ω' J, -timeTerm z - nonlinearTerm z)
          + ∫ z in CKN.spaceTimeSet Ω' J, viscousTerm z :=
        integral_add (htimeInt.neg.sub hnonlinearInt) hviscousInt
      _ = (-(∫ z in CKN.spaceTimeSet Ω' J, timeTerm z)
          - ∫ z in CKN.spaceTimeSet Ω' J, nonlinearTerm z)
          + ∫ z in CKN.spaceTimeSet Ω' J, viscousTerm z := by
        rw [htimeSubtract, integral_neg]
  have htimeOmegaInt : IntegrableOn omegaTimeTerm
      (CKN.spaceTimeSet Ω' J) volume := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact suitableWeakVorticityTestComponentIntegrableOnBox hdata hbox htimeTest i
  have hlapOmegaInt : IntegrableOn omegaLaplacianTerm
      (CKN.spaceTimeSet Ω' J) volume := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact suitableWeakVorticityTestComponentIntegrableOnBox hdata hbox hlapTest i
  have hfluxInt : IntegrableOn fluxTerm
      (CKN.spaceTimeSet Ω' J) volume := by
    simpa [fluxTerm] using suitableWeakVorticityFluxTestIntegrableOnBox
      h hbox hψ hψbox
  have htimeId :
      ∫ z in CKN.spaceTimeSet Ω' J, timeTerm z =
        ∫ z in CKN.spaceTimeSet Ω' J, omegaTimeTerm z := by
    simpa [timeTerm, omegaTimeTerm] using
      suitableWeakVorticityTimeIdentityOnBox h hbox hψ hψbox
  have hviscousId :
      ∫ z in CKN.spaceTimeSet Ω' J, viscousTerm z =
        -∫ z in CKN.spaceTimeSet Ω' J, omegaLaplacianTerm z := by
    simpa [viscousTerm, omegaLaplacianTerm] using
      suitableWeakVorticityViscousIdentityOnBox h hbox hψ hψbox
  have hnonlinearId :
      ∫ z in CKN.spaceTimeSet Ω' J, nonlinearTerm z =
        ∫ z in CKN.spaceTimeSet Ω' J, fluxTerm z := by
    simpa [nonlinearTerm, fluxTerm] using
      suitableWeakVorticityNonlinearIdentityOnBox h hbox hψ hψbox
  let A : ℝ := ∫ z in CKN.spaceTimeSet Ω' J, omegaTimeTerm z
  let B : ℝ := ∫ z in CKN.spaceTimeSet Ω' J, fluxTerm z
  let C : ℝ := ∫ z in CKN.spaceTimeSet Ω' J, omegaLaplacianTerm z
  have hscalar : -A - B - C = 0 := by
    calc
      -A - B - C =
          (-(∫ z in CKN.spaceTimeSet Ω' J, timeTerm z))
            - (∫ z in CKN.spaceTimeSet Ω' J, nonlinearTerm z)
            + (∫ z in CKN.spaceTimeSet Ω' J, viscousTerm z) := by
        dsimp [A, B, C]
        rw [← htimeId, ← hnonlinearId, hviscousId]
        ring
      _ = ∫ z in CKN.spaceTimeSet Ω' J, momentumTerm z := hmomentumSplit.symm
      _ = 0 := hmomentumBox
  calc
    ∫ z in CKN.spaceTimeSet Ω' J,
        (-(omegaTimeTerm z) - omegaLaplacianTerm z) = -A - C := by
          calc
            _ = (∫ z in CKN.spaceTimeSet Ω' J, -omegaTimeTerm z)
                - ∫ z in CKN.spaceTimeSet Ω' J, omegaLaplacianTerm z := by
              exact integral_sub htimeOmegaInt.neg hlapOmegaInt
            _ = _ := by dsimp [A, C]; rw [integral_neg]
    _ = B := by
      linarith only [hscalar]
    _ = ∫ z in CKN.spaceTimeSet Ω' J, fluxTerm z := by rfl

/-- The distributional vorticity identity holds for every compact test on an
open cylinder (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakVorticityEquation
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : I.OrdConnected)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    ∫ z in CKN.spaceTimeSet Ω I,
      (-(∑ i : Fin 3, weakVorticity Du z i *
          vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) i)
        - ∑ i : Fin 3, weakVorticity Du z i *
          vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i) =
    ∫ z in CKN.spaceTimeSet Ω I,
      ∑ j : Fin 3, ∑ i : Fin 3,
        vorticityFlux u Du z j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z := by
  let K : Set ParabolicPoint :=
    tsupport (show ParabolicPoint → Vec3 from ψ)
  have hKcompact : IsCompact K := CKN.isCompact_tsupport_parabolic hψ.2.1
  have hKglobal : K ⊆ CKN.spaceTimeSet Ω I :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    CKN.caccioppoli_localBox_of_compact_subset hΩ hI hIord hKcompact hKglobal
  have hlocal := suitableWeakVorticityEquationOnBox h hbox hψ hKbox
  let lhsTerm : ParabolicPoint → ℝ := fun z =>
    -(∑ i : Fin 3, weakVorticity Du z i *
      vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) i)
      - ∑ i : Fin 3, weakVorticity Du z i *
        vorticityTestLaplacian ψ (show Vec3 × ℝ from z) i
  let rhsTerm : ParabolicPoint → ℝ := fun z =>
    ∑ j : Fin 3, ∑ i : Fin 3,
      vorticityFlux u Du z j i * CKN.spatialPartial
        (fun w : Vec3 × ℝ => ψ w i) j z
  have htimeZero (z : ParabolicPoint) (hz : z ∉ K) :
      vorticityTestTimeDerivative ψ (show Vec3 × ℝ from z) = 0 := by
    have hzOrd : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
      intro hw
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from ψ)
      rw [CKN.tsupport_parabolic_eq]
      exact hw
    have hnot : (show Vec3 × ℝ from z) ∉
        tsupport (vorticityTestTimeDerivative ψ) := by
      intro ht
      exact hzOrd (vorticityTestTimeDerivative_tsupport ht)
    exact image_eq_zero_of_notMem_tsupport hnot
  have hlapZero (z : ParabolicPoint) (hz : z ∉ K) :
      vorticityTestLaplacian ψ (show Vec3 × ℝ from z) = 0 := by
    have hzOrd : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
      intro hw
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from ψ)
      rw [CKN.tsupport_parabolic_eq]
      exact hw
    have hnot : (show Vec3 × ℝ from z) ∉
        tsupport (vorticityTestLaplacian ψ) := by
      intro hlap
      exact hzOrd (vorticityTestLaplacian_tsupport hlap)
    exact image_eq_zero_of_notMem_tsupport hnot
  have hleftZero (z : ParabolicPoint) (hz : z ∉ K) : lhsTerm z = 0 := by
    simp [lhsTerm, htimeZero z hz, hlapZero z hz]
  have hrightZero (z : ParabolicPoint) (hz : z ∉ K) : rhsTerm z = 0 := by
    have hzOrd : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
      intro hw
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from ψ)
      rw [CKN.tsupport_parabolic_eq]
      exact hw
    have hcomp (i : Fin 3) : (show Vec3 × ℝ from z) ∉
        tsupport (fun w : Vec3 × ℝ => ψ w i) := by
      intro hi
      exact hzOrd ((CKN.tsupport_component_subset (ι := Fin 3)
        ψ i (by intro w hw; simp [hw])) hi)
    have hpartial (i j : Fin 3) :
        CKN.spatialPartial
          (fun w : Vec3 × ℝ => ψ w i) j z = 0 := by
      change CKN.spatialPartial
        (fun w : Vec3 × ℝ => ψ w i) j (show Vec3 × ℝ from z) = 0
      exact CKN.spatialPartial_eq_zero_off_tsupport (hcomp i) j
    simp [rhsTerm, hpartial]
  calc
    ∫ z in CKN.spaceTimeSet Ω I, lhsTerm z = ∫ z in K, lhsTerm z :=
      integralOn_eq_of_subset_of_zero_off hKglobal
        (by intro z hz; exact hleftZero z hz)
    _ = ∫ z in CKN.spaceTimeSet Ω' J, lhsTerm z := by
      symm
      exact integralOn_eq_of_subset_of_zero_off hKbox
        (by intro z hz; exact hleftZero z hz)
    _ = ∫ z in CKN.spaceTimeSet Ω' J, rhsTerm z := by
      simpa [lhsTerm, rhsTerm] using hlocal
    _ = ∫ z in K, rhsTerm z := integralOn_eq_of_subset_of_zero_off hKbox
      (by intro z hz; exact hrightZero z hz)
    _ = ∫ z in CKN.spaceTimeSet Ω I, rhsTerm z := by
      symm
      exact integralOn_eq_of_subset_of_zero_off hKglobal
        (by intro z hz; exact hrightZero z hz)

end

end ESS
