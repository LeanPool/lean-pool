/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Restriction of a suitable weak solution to a smaller open subcylinder

The missing step of the printed proof of Corollary 2.3 (`cor:interior:nonanalytic`):
showing that the hypotheses of `thm:main` hold on the smaller cylinder `B(R')x(-δ',0)` with
`ρ(t)` replaced by `min{ρ(t),R'/2}` requires knowing that a suitable weak solution on the
standing cylinder is still a suitable weak solution on that smaller cylinder.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem spatialPartial_eq_zero_of_notMem_tsupport {φ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport φ) (i : Fin 3) : spatialPartial φ i z = 0 := by
  change fderiv ℝ (fun x : Vec3 => φ (x, z.2)) z.1 (basisVec i) = 0
  have hcont : Continuous (fun x : Vec3 => ((x, z.2) : Vec3 × ℝ)) :=
    continuous_id.prodMk continuous_const
  have htendsto := hcont.tendsto z.1
  have hslice : (fun x : Vec3 => φ (x, z.2)) =ᶠ[nhds z.1] (fun _ => (0:ℝ)) :=
    htendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp hz)
  have hnotmem : z.1 ∉ tsupport (fun x : Vec3 => φ (x, z.2)) :=
    notMem_tsupport_iff_eventuallyEq.mpr hslice
  rw [fderiv_of_notMem_tsupport ℝ hnotmem]
  rfl

theorem timePartial_eq_zero_of_notMem_tsupport {φ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport φ) : timePartial φ z = 0 := by
  change fderiv ℝ (fun s : ℝ => φ (z.1, s)) z.2 1 = 0
  have hcont : Continuous (fun s : ℝ => ((z.1, s) : Vec3 × ℝ)) :=
    continuous_const.prodMk continuous_id
  have htendsto := hcont.tendsto z.2
  have hslice : (fun s : ℝ => φ (z.1, s)) =ᶠ[nhds z.2] (fun _ => (0:ℝ)) :=
    htendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp hz)
  have hnotmem : z.2 ∉ tsupport (fun s : ℝ => φ (z.1, s)) :=
    notMem_tsupport_iff_eventuallyEq.mpr hslice
  rw [fderiv_of_notMem_tsupport ℝ hnotmem]
  rfl

theorem tsupport_spatialPartial_subset (φ : Vec3 × ℝ → ℝ) (i : Fin 3) :
    tsupport (fun w : Vec3 × ℝ => spatialPartial φ i w) ⊆ tsupport φ := by
  refine closure_minimal (fun w hw => ?_) (isClosed_tsupport φ)
  by_contra hc
  exact hw (spatialPartial_eq_zero_of_notMem_tsupport hc i)

theorem spatialSecondPartial_eq_zero_of_notMem_tsupport {φ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) (i j : Fin 3) :
    spatialSecondPartial φ i j z = 0 :=
  spatialPartial_eq_zero_of_notMem_tsupport (φ := fun w : Vec3 × ℝ => spatialPartial φ i w)
    (fun hmem => hz (tsupport_spatialPartial_subset φ i hmem)) j

theorem notMem_tsupport_apply_of_notMem_tsupport {φ : Vec3 × ℝ → Vec3}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) (i : Fin 3) :
    z ∉ tsupport (fun w => φ w i) := by
  rw [notMem_tsupport_iff_eventuallyEq] at hz ⊢
  filter_upwards [hz] with w hw
  simp [hw]

theorem localBox_mono {Ω Ω' : Set Vec3} {I I' : Set ℝ} (hΩ : Ω' ⊆ Ω) (hI : I' ⊆ I)
    {Ω'' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω' I' Ω'' J) : localBox Ω I Ω'' J := by
  exact ⟨hbox.1, hbox.2.1, hbox.2.2.1.trans hΩ, hbox.2.2.2.1, hbox.2.2.2.2.1,
    hbox.2.2.2.2.2.trans hI⟩

theorem setIntegral_spaceTimeSet_eq_of_support_subset {Ω Ω' : Set Vec3} {I I' : Set ℝ}
    {F : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hΩopen : IsOpen Ω) (hIopen : IsOpen I) (hΩ'sub : Ω' ⊆ Ω) (hI'sub : I' ⊆ I)
    (hSsub : S ⊆ spaceTimeSet Ω' I') (hvanish : ∀ z ∉ S, F z = 0) :
    ∫ z in spaceTimeSet Ω I, F z = ∫ z in spaceTimeSet Ω' I', F z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (hΩopen.measurableSet.prod hIopen.measurableSet) (Set.prod_mono hΩ'sub hI'sub)
  intro z hz
  exact hvanish z (fun hmem => hz.2 (hSsub hmem))

theorem isSuitableWeakSolution_restrict {Ω Ω' : Set Vec3} {I I' : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution Ω I q u Du p f)
    (hΩ'open : IsOpen Ω') (hΩ'sub : Ω' ⊆ Ω)
    (hI'open : IsOpen I') (hI'ord : I'.OrdConnected) (hI'sub : I' ⊆ I) :
    IsSuitableWeakSolution Ω' I' q u Du p f := by
  obtain ⟨hΩopen, hIopen, hIord, hq, hforceLp, hmeasEnergy, hdivfree, hmomentum, henergy⟩ := hsol
  have hΩ'I'_sub : spaceTimeSet Ω' I' ⊆ spaceTimeSet Ω I := Set.prod_mono hΩ'sub hI'sub
  refine ⟨hΩ'open, hI'open, hI'ord, hq, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω₁ J hbox
    exact hforceLp Ω₁ J (localBox_mono hΩ'sub hI'sub hbox)
  · intro Ω₁ J hbox
    exact hmeasEnergy Ω₁ J (localBox_mono hΩ'sub hI'sub hbox)
  · intro ψ hψ
    have hψΩI : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
      ⟨hψ.1, hψ.2.1, hψ.2.2.trans hΩ'I'_sub⟩
    have heq := hdivfree ψ hψΩI
    rw [← heq]
    exact (setIntegral_spaceTimeSet_eq_of_support_subset hΩopen hIopen hΩ'sub hI'sub hψ.2.2
      (fun z hz => by
        have h0 : ∀ i, spatialPartial ψ i z = 0 :=
          fun i => spatialPartial_eq_zero_of_notMem_tsupport hz i
        simp [h0])).symm
  · intro φ hφ
    have hφΩI : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans hΩ'I'_sub⟩
    have heq := hmomentum φ hφΩI
    rw [← heq]
    exact (setIntegral_spaceTimeSet_eq_of_support_subset hΩopen hIopen hΩ'sub hI'sub hφ.2.2
      (fun z hz => by
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        have h0t : ∀ i, timePartial (fun w => φ w i) z = 0 :=
          fun i => timePartial_eq_zero_of_notMem_tsupport
            (notMem_tsupport_apply_of_notMem_tsupport hz i)
        have h0s : ∀ i j, spatialPartial (fun w => φ w i) j z = 0 :=
          fun i j => spatialPartial_eq_zero_of_notMem_tsupport
            (notMem_tsupport_apply_of_notMem_tsupport hz i) j
        simp [h0t, h0s, congrFun hφz])).symm
  · intro ψ hψ hψnonneg
    have hψΩI : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
      ⟨hψ.1, hψ.2.1, hψ.2.2.trans hΩ'I'_sub⟩
    have hineq := henergy ψ hψΩI hψnonneg
    have heq1 : ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z =
        ∫ z in spaceTimeSet Ω' I', spatialGradientSq u Du z * ψ z :=
      setIntegral_spaceTimeSet_eq_of_support_subset hΩopen hIopen hΩ'sub hI'sub hψ.2.2
        (fun z hz => by
          have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          rw [hψz, mul_zero])
    have heq2 : ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 * (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) * ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z =
        ∫ z in spaceTimeSet Ω' I',
          (vec3EuclideanNorm (u z)) ^ 2 * (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) * ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z :=
      setIntegral_spaceTimeSet_eq_of_support_subset hΩopen hIopen hΩ'sub hI'sub hψ.2.2
        (fun z hz => by
          have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          have h0t : timePartial ψ z = 0 := timePartial_eq_zero_of_notMem_tsupport hz
          have h0s : ∀ i, spatialPartial ψ i z = 0 :=
            fun i => spatialPartial_eq_zero_of_notMem_tsupport hz i
          have h0s2 : ∀ i, spatialSecondPartial ψ i i z = 0 :=
            fun i => spatialSecondPartial_eq_zero_of_notMem_tsupport hz i i
          simp [hψz, h0t, h0s, h0s2])
    rw [← heq1, ← heq2]
    exact hineq

end CIV
