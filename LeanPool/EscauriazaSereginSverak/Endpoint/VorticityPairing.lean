/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEqSpacetime
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityDefinitions
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Space-time pairings for weak vorticity

Spatial weak integration by parts identifies the distributional curl pairing
on a local space-time box.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

private theorem vorticityScalarTest_of_localBox
    {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I := by
  refine ⟨hφ, hφc, ?_⟩
  rintro ⟨x, t⟩ hφz
  have hz := hφbox hφz
  exact ⟨(subset_closure.trans hbox.2.2.1) hz.1,
    (subset_closure.trans hbox.2.2.2.2.2) hz.2⟩

private theorem suitableWeakGradientTestPairingOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (i j : Fin 3) :
    ∫ z in CKN.spaceTimeSet Ω' J, Du z i j * φ z =
      -∫ z in CKN.spaceTimeSet Ω' J,
        u z i * CKN.spatialPartial φ j z := by
  have hInt : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ => 0) :=
    CKN.isSuitableWeakSolution_iff_integrable.mp h
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) :=
    hInt.toData
  have htest := vorticityScalarTest_of_localBox hbox hφ hφc hφbox
  have hpartial := vorticitySpatialPartialTest htest j
  have hDint := suitableWeakGradientTestIntegrableOnBox hdata hbox htest i j
  have hUint := suitableWeakVelocityTestIntegrableOnBox hdata hbox hpartial i
  rw [vorticity_integral_on_box_eq_iterated hDint,
    vorticity_integral_on_box_eq_iterated hUint]
  exact suitableWeakSpatialIntegrationByParts h Ω' J hbox hφ hφc hφbox i j

private theorem vorticityTestPartial_at_parabolicHomeomorph
    (φ : Vec3 × ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    vorticityTestPartial φ i (parabolicHomeomorph z) =
      CKN.spatialPartial (show ParabolicPoint → ℝ from φ) i z := by
  rw [vorticityTestPartial_eq_spatialPartial]
  rfl

private theorem weakVorticity_test_integrable_of_gradient_products
    {Ω' : Set Vec3} {J : Set ℝ}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (ψ : ParabolicPoint → Vec3)
    (hgrad : ∀ k i j : Fin 3, IntegrableOn
      (fun z : ParabolicPoint => Du z i j * ψ z k)
      (CKN.spaceTimeSet Ω' J) volume)
    (i : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => weakVorticity Du z i * ψ z i)
      (CKN.spaceTimeSet Ω' J) volume := by
  fin_cases i
  · change IntegrableOn
      (fun z : ParabolicPoint => (Du z 2 1 - Du z 1 2) * ψ z 0)
      (CKN.spaceTimeSet Ω' J) volume
    have hsub := (hgrad 0 2 1).sub (hgrad 0 1 2)
    have heq :
        ((fun z : ParabolicPoint => Du z 2 1 * ψ z 0) -
          fun z => Du z 1 2 * ψ z 0) =ᵐ[volume.restrict
            (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 2 1 - Du z 1 2) * ψ z 0) := by
      filter_upwards [] with z
      simp only [Pi.sub_apply]
      ring
    exact hsub.congr heq
  · change IntegrableOn
      (fun z : ParabolicPoint => (Du z 0 2 - Du z 2 0) * ψ z 1)
      (CKN.spaceTimeSet Ω' J) volume
    have hsub := (hgrad 1 0 2).sub (hgrad 1 2 0)
    have heq :
        ((fun z : ParabolicPoint => Du z 0 2 * ψ z 1) -
          fun z => Du z 2 0 * ψ z 1) =ᵐ[volume.restrict
            (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 0 2 - Du z 2 0) * ψ z 1) := by
      filter_upwards [] with z
      simp only [Pi.sub_apply]
      ring
    exact hsub.congr heq
  · change IntegrableOn
      (fun z : ParabolicPoint => (Du z 1 0 - Du z 0 1) * ψ z 2)
      (CKN.spaceTimeSet Ω' J) volume
    have hsub := (hgrad 2 1 0).sub (hgrad 2 0 1)
    have heq :
        ((fun z : ParabolicPoint => Du z 1 0 * ψ z 2) -
          fun z => Du z 0 1 * ψ z 2) =ᵐ[volume.restrict
            (CKN.spaceTimeSet Ω' J)]
        (fun z => (Du z 1 0 - Du z 0 1) * ψ z 2) := by
      filter_upwards [] with z
      simp only [Pi.sub_apply]
      ring
    exact hsub.congr heq

/-- Pairing weak vorticity against a smooth compact field is the velocity
pairing against its curl on every local box (manuscript
`lem:vorticity-weak-eq`). -/
theorem suitableWeakVorticityPairingOnBox
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
      ∑ i : Fin 3, weakVorticity Du z i * (show ParabolicPoint → Vec3 from ψ) z i =
    ∫ z in CKN.spaceTimeSet Ω' J,
      ∑ i : Fin 3,
        u z i * (show ParabolicPoint → Vec3 from vorticityTestCurl ψ) z i := by
  have hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) := by
    exact (CKN.isSuitableWeakSolution_iff_integrable.mp h).toData
  have hψbox' : tsupport ψ ⊆ Ω' ×ˢ J := by
    intro z hz
    have hz' : (show ParabolicPoint from z) ∈
        tsupport (show ParabolicPoint → Vec3 from ψ) := by
      rw [CKN.tsupport_parabolic_eq]
      exact hz
    have hzb := hψbox hz'
    change z.1 ∈ Ω' ∧ z.2 ∈ J at hzb
    exact hzb
  let ψP : ParabolicPoint → Vec3 := show ParabolicPoint → Vec3 from ψ
  let curlP : ParabolicPoint → Vec3 :=
    fun z => vorticityTestCurl ψ (parabolicHomeomorph z)
  have hcomponentTest (i : Fin 3) :
      (fun z : Vec3 × ℝ => ψ z i) ∈
        CKN.spaceTimeTestFunction (V := ℝ) Ω I :=
    CKN.component_mem_spaceTimeTestFunction hψ i
  have hcomponentBox (i : Fin 3) :
      tsupport (fun z : Vec3 × ℝ => ψ z i) ⊆ Ω' ×ˢ J := by
    exact (CKN.tsupport_component_subset (ι := Fin 3) ψ i
      (by intro z hz; simp [hz])).trans hψbox'
  have hcurl : vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction
      (V := Vec3) Ω I := vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hgrad (k i j : Fin 3) :
      ∫ z in CKN.spaceTimeSet Ω' J,
        Du z i j * ψP z k =
      -∫ z in CKN.spaceTimeSet Ω' J,
        u z i * CKN.spatialPartial (fun w : Vec3 × ℝ => ψ w k) j z := by
    simpa only [ψP] using suitableWeakGradientTestPairingOnBox h hbox
      (hcomponentTest k).1 (hcomponentTest k).2.1 (hcomponentBox k) i j
  have hgradIntegrable (k i j : Fin 3) :
      IntegrableOn (fun z : ParabolicPoint => Du z i j * ψP z k)
        (CKN.spaceTimeSet Ω' J) volume := by
    simpa only [ψP] using suitableWeakGradientTestIntegrableOnBox hdata hbox
      (hcomponentTest k) i j
  have hvelocityCurlIntegrable (i : Fin 3) :
      IntegrableOn (fun z : ParabolicPoint =>
        u z i * curlP z i)
        (CKN.spaceTimeSet Ω' J) volume := by
    have hraw := suitableWeakVelocityTestIntegrableOnBox hdata hbox
      (CKN.component_mem_spaceTimeTestFunction hcurl i) i
    have hpoint (z : ParabolicPoint) (j : Fin 3) :
        vorticityTestCurl ψ z j =
          vorticityTestCurl ψ (parabolicHomeomorph z) j := by
      change vorticityTestCurl ψ z j =
        vorticityTestCurl ψ (z.1, z.2) j
      rfl
    have hcast : (show ParabolicPoint → Vec3 from vorticityTestCurl ψ) = curlP := by
      funext z j
      exact hpoint z j
    have heq :
        (fun z : ParabolicPoint =>
          u z i * (show ParabolicPoint → Vec3 from vorticityTestCurl ψ) z i) =ᵐ[
            volume.restrict (CKN.spaceTimeSet Ω' J)]
          (fun z => u z i * curlP z i) := by
      filter_upwards [] with z
      rw [hcast]
    exact hraw.congr heq
  have hvelocityPartialIntegrable (k i j : Fin 3) :
      IntegrableOn (fun z : ParabolicPoint =>
        u z i * CKN.spatialPartial (fun w : Vec3 × ℝ => ψ w k) j z)
        (CKN.spaceTimeSet Ω' J) volume := by
    exact suitableWeakVelocityTestIntegrableOnBox hdata hbox
      (vorticitySpatialPartialTest (hcomponentTest k) j) i
  have homegaIntegrable (i : Fin 3) :
      IntegrableOn (fun z : ParabolicPoint => weakVorticity Du z i * ψP z i)
        (CKN.spaceTimeSet Ω' J) volume := by
    exact weakVorticity_test_integrable_of_gradient_products ψP hgradIntegrable i
  have hcomponent0 :
      ∫ z in CKN.spaceTimeSet Ω' J, weakVorticity Du z 0 * ψP z 0 =
        (∫ z in CKN.spaceTimeSet Ω' J, Du z 2 1 * ψP z 0) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 1 2 * ψP z 0 := by
    change ∫ z in CKN.spaceTimeSet Ω' J,
        (Du z 2 1 - Du z 1 2) * ψP z 0 = _
    calc
      ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 2 1 - Du z 1 2) * ψP z 0 =
        ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 2 1 * ψP z 0 - Du z 1 2 * ψP z 0) := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = _ := integral_sub (hgradIntegrable 0 2 1) (hgradIntegrable 0 1 2)
  have hcomponent1 :
      ∫ z in CKN.spaceTimeSet Ω' J, weakVorticity Du z 1 * ψP z 1 =
        (∫ z in CKN.spaceTimeSet Ω' J, Du z 0 2 * ψP z 1) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 2 0 * ψP z 1 := by
    change ∫ z in CKN.spaceTimeSet Ω' J,
        (Du z 0 2 - Du z 2 0) * ψP z 1 = _
    calc
      ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 0 2 - Du z 2 0) * ψP z 1 =
        ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 0 2 * ψP z 1 - Du z 2 0 * ψP z 1) := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = _ := integral_sub (hgradIntegrable 1 0 2) (hgradIntegrable 1 2 0)
  have hcomponent2 :
      ∫ z in CKN.spaceTimeSet Ω' J, weakVorticity Du z 2 * ψP z 2 =
        (∫ z in CKN.spaceTimeSet Ω' J, Du z 1 0 * ψP z 2) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 0 1 * ψP z 2 := by
    change ∫ z in CKN.spaceTimeSet Ω' J,
        (Du z 1 0 - Du z 0 1) * ψP z 2 = _
    calc
      ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 1 0 - Du z 0 1) * ψP z 2 =
        ∫ z in CKN.spaceTimeSet Ω' J,
          (Du z 1 0 * ψP z 2 - Du z 0 1 * ψP z 2) := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = _ := integral_sub (hgradIntegrable 2 1 0) (hgradIntegrable 2 0 1)
  have hleftExpand :
      ∫ z in CKN.spaceTimeSet Ω' J,
          ∑ i : Fin 3, weakVorticity Du z i * ψP z i =
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 2 1 * ψP z 0) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 1 2 * ψP z 0) +
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 0 2 * ψP z 1) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 2 0 * ψP z 1) +
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 1 0 * ψP z 2) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 0 1 * ψP z 2) := by
    calc
      _ = ∑ i : Fin 3,
          ∫ z in CKN.spaceTimeSet Ω' J, weakVorticity Du z i * ψP z i :=
        integral_finsetSum _ (fun i _ => homegaIntegrable i)
      _ = _ := by
        simp only [Fin.sum_univ_three, hcomponent0, hcomponent1, hcomponent2]
  have hrightExpand :
      ∫ z in CKN.spaceTimeSet Ω' J,
          ∑ i : Fin 3, u z i * curlP z i =
        ((∫ z in CKN.spaceTimeSet Ω' J,
          u z 0 * curlP z 0) +
          ∫ z in CKN.spaceTimeSet Ω' J,
            u z 1 * curlP z 1) +
          ∫ z in CKN.spaceTimeSet Ω' J,
            u z 2 * curlP z 2 := by
    calc
      _ = ∑ i : Fin 3,
          ∫ z in CKN.spaceTimeSet Ω' J,
            u z i * curlP z i :=
        integral_finsetSum _ (fun i _ => hvelocityCurlIntegrable i)
      _ = _ := by simp only [Fin.sum_univ_three]
  calc
    ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3, weakVorticity Du z i * ψP z i =
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 2 1 * ψP z 0) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 1 2 * ψP z 0) +
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 0 2 * ψP z 1) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 2 0 * ψP z 1) +
        ((∫ z in CKN.spaceTimeSet Ω' J, Du z 1 0 * ψP z 2) -
          ∫ z in CKN.spaceTimeSet Ω' J, Du z 0 1 * ψP z 2) := hleftExpand
    _ = ∫ z in CKN.spaceTimeSet Ω' J,
        ∑ i : Fin 3,
          u z i * curlP z i := by
          rw [hrightExpand]
          rw [hgrad 0 2 1, hgrad 0 1 2, hgrad 1 0 2, hgrad 1 2 0,
            hgrad 2 1 0, hgrad 2 0 1]
          simp only [curlP, vorticityTestCurl_zero, vorticityTestCurl_one,
            vorticityTestCurl_two, vorticityTestPartial_at_parabolicHomeomorph]
          simp_rw [mul_sub]
          rw [integral_sub (hvelocityPartialIntegrable 2 0 1)
              (hvelocityPartialIntegrable 1 0 2),
            integral_sub (hvelocityPartialIntegrable 0 1 2)
              (hvelocityPartialIntegrable 2 1 0),
            integral_sub (hvelocityPartialIntegrable 1 2 0)
              (hvelocityPartialIntegrable 0 2 1)]
          ring

end ESS
