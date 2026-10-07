/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEq
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Distributional velocity traces for vorticity

The terminal velocity trace is expressed by its action on compactly supported
smooth spatial tests. This is the trace convention used to identify the
terminal value of a continuous vorticity representative.
-/

public section


open MeasureTheory Filter
open scoped BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

/-- A velocity has zero weak local trace at time zero if every compactly
supported smooth spatial pairing tends to zero from negative times
(manuscript `lem:vorticity-top-extension`). -/
@[expose] def HasZeroDistributionalVelocityTrace (u : Vec3 × ℝ → Vec3) : Prop :=
  ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    (∀ t < 0, Integrable (fun x : Vec3 =>
      ∑ i : Fin 3, u (x, t) i * ψ x i)) ∧
    Tendsto (fun t : ℝ => ∫ x : Vec3,
      ∑ i : Fin 3, u (x, t) i * ψ x i) (nhdsWithin 0 (Set.Iio 0)) (nhds 0)

/-- The curl of a smooth vector test is smooth. -/
theorem spatialVorticityTestCurl_contDiff
    {ψ : Vec3 → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialTestCurl ψ) := by
  have hcomponent (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ x i) :=
    (contDiff_apply ℝ ℝ i).comp hψ
  have hpartial (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => CKN.spatialDeriv (fun y => ψ y i) j x) := by
    rw [contDiff_iff_forall_nat_le]
    intro n _hn
    have hcomponent' : ContDiff ℝ (n + 1 : ℕ) (fun x : Vec3 => ψ x i) :=
      (hcomponent i).of_le (by simp)
    have hfd := hcomponent'.contDiff_fderiv_apply (m := n) (by simp)
    have hline : ContDiff ℝ n (fun x : Vec3 => (x, CKN.basisVec j)) :=
      contDiff_id.prodMk contDiff_const
    simpa only [Function.comp_def, CKN.spatialDeriv] using hfd.comp hline
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hpartial 2 1).sub (hpartial 1 2)
  · exact (hpartial 0 2).sub (hpartial 2 0)
  · exact (hpartial 1 0).sub (hpartial 0 1)

/-- The curl of a compactly supported vector test is compactly supported. -/
theorem spatialVorticityTestCurl_hasCompactSupport
    {ψ : Vec3 → Vec3} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (spatialTestCurl ψ) := by
  have hcomponent (i : Fin 3) :
      tsupport (fun x : Vec3 => ψ x i) ⊆ tsupport ψ := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      apply hx
      have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [hzero]
    · exact isClosed_tsupport ψ
  have hderiv (i j : Fin 3) (x : Vec3)
      (hx : x ∉ tsupport ψ) :
      CKN.spatialDeriv (fun y => ψ y i) j x = 0 := by
    have hxcomp : x ∉ tsupport (fun y : Vec3 => ψ y i) :=
      fun hx' => hx (hcomponent i hx')
    have hxderiv : x ∉ tsupport (CKN.spatialDeriv (fun y => ψ y i) j) :=
      fun hx' => hxcomp (CKN.tsupport_spatialDeriv_subset j hx')
    exact image_eq_zero_of_notMem_tsupport hxderiv
  have hsupp : Function.support (spatialTestCurl ψ) ⊆ tsupport ψ := by
    intro x hx
    by_contra hnot
    apply hx
    funext i
    fin_cases i
    · simp [hderiv 2 1 x hnot, hderiv 1 2 x hnot]
    · simp [hderiv 0 2 x hnot, hderiv 2 0 x hnot]
    · simp [hderiv 1 0 x hnot, hderiv 0 1 x hnot]
  exact HasCompactSupport.of_support_subset_isCompact hψ.isCompact hsupp

end

end ESS
