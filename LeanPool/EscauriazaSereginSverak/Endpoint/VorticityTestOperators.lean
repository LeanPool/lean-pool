/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestCalculus
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEqSpacetime
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Differential operators on vorticity tests

Time derivatives, Laplacians, and curls of compact smooth tests retain the
expected support and commute in the combinations used in
`lem:vorticity-weak-eq`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

/-- The time derivative of a compact vector test, in ordinary product
coordinates. -/
@[expose] def vorticityTestTimeDerivative (ψ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z i => vorticityTestTimePartial (fun w => ψ w i) (show ParabolicPoint from z)

/-- The spatial Laplacian of a compact vector test, in ordinary product
coordinates. -/
@[expose] def vorticityTestLaplacian (ψ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z i => ∑ j : Fin 3,
    CKN.spatialSecondPartial (show ParabolicPoint → ℝ from fun w => ψ w i) j j
      (show ParabolicPoint from z)

private theorem vorticityTestPartial_finsetSum
    {F : Fin 3 → Vec3 × ℝ → ℝ} (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j))
    (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestPartial (fun w => ∑ j : Fin 3, F j w) i z =
      ∑ j : Fin 3, vorticityTestPartial (F j) i z := by
  let G (j : Fin 3) : Vec3 → ℝ := fun x => F j (x, z.2)
  have hG (j : Fin 3) : DifferentiableAt ℝ (G j) z.1 := by
    exact ((hF j).differentiable (by simp)).differentiableAt.comp z.1 (by fun_prop)
  have hsum := fderiv_fun_sum (u := Finset.univ) (A := G) (x := z.1)
    (fun j hj => hG j)
  change (fderiv ℝ (fun x : Vec3 => ∑ j : Fin 3, G j x) z.1)
      (CKN.basisVec i) = _
  rw [hsum]
  simp [vorticityTestPartial, G]

@[expose] def vorticityScalarLaplacian (φ : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  fun z => ∑ j : Fin 3,
    vorticityTestPartial (fun w => vorticityTestPartial φ j w) j z

private theorem vorticityScalarLaplacian_partial_commute
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestPartial (vorticityScalarLaplacian φ) i z =
      vorticityScalarLaplacian (fun w => vorticityTestPartial φ i w) z := by
  unfold vorticityScalarLaplacian at *
  have hsecond (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => vorticityTestPartial (fun y => vorticityTestPartial φ j y) j w) := by
    exact CKN.spatialPartial_contDiff
      (CKN.spatialPartial_contDiff hφ j) j
  rw [vorticityTestPartial_finsetSum hsecond i z]
  apply Finset.sum_congr rfl
  intro j hj
  have hfirst : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => vorticityTestPartial φ j w) := by
    exact CKN.spatialPartial_contDiff hφ j
  have hinner :
      (fun w => vorticityTestPartial
        (fun y => vorticityTestPartial φ j y) i w) =
      (fun w => vorticityTestPartial
        (fun y => vorticityTestPartial φ i y) j w) := by
    funext w
    exact vorticityTestPartial_spatialPartial_commute hφ j i w
  calc
    vorticityTestPartial
        (fun w => vorticityTestPartial (fun y => vorticityTestPartial φ j y) j w)
        i z = vorticityTestPartial
          (fun w => vorticityTestPartial (fun y => vorticityTestPartial φ j y) i w)
          j z := by
            exact vorticityTestPartial_spatialPartial_commute hfirst j i z
    _ = vorticityTestPartial
          (fun w => vorticityTestPartial (fun y => vorticityTestPartial φ i y) j w)
          j z := by rw [hinner]

private theorem vorticityScalarLaplacian_sub
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    vorticityScalarLaplacian (fun w => f w - g w) z =
      vorticityScalarLaplacian f z - vorticityScalarLaplacian g z := by
  unfold vorticityScalarLaplacian
  calc
    (∑ j : Fin 3, vorticityTestPartial
      (fun w => vorticityTestPartial (fun y => f y - g y) j w) j z) =
      ∑ j : Fin 3, (vorticityTestPartial
        (fun w => vorticityTestPartial f j w) j z -
        vorticityTestPartial (fun w => vorticityTestPartial g j w) j z) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hinner : (fun w => vorticityTestPartial
              (fun y => f y - g y) j w) =
              (fun w => vorticityTestPartial f j w - vorticityTestPartial g j w) := by
            funext w
            exact vorticityTestPartial_sub_smooth hf hg j w
          rw [hinner]
          exact vorticityTestPartial_sub_smooth
            (CKN.spatialPartial_contDiff hf j) (CKN.spatialPartial_contDiff hg j) j z
    _ = (∑ j : Fin 3, vorticityTestPartial
          (fun w => vorticityTestPartial f j w) j z) -
        ∑ j : Fin 3, vorticityTestPartial
          (fun w => vorticityTestPartial g j w) j z := by
      rw [Finset.sum_sub_distrib]

private theorem vorticityTestLaplacian_component
    (ψ : Vec3 × ℝ → Vec3) (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestLaplacian ψ z i =
      vorticityScalarLaplacian (fun w => ψ w i) z := by
  simp [vorticityTestLaplacian, vorticityScalarLaplacian,
    CKN.spatialSecondPartial, vorticityTestPartial_eq_spatialPartial]
  rfl

/-- Curl and the spatial Laplacian commute on smooth vector tests. -/
theorem vorticityTestCurl_laplacian_commute
    {ψ : Vec3 × ℝ → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    vorticityTestCurl (vorticityTestLaplacian ψ) z i =
      vorticityTestLaplacian (vorticityTestCurl ψ) z i := by
  have hcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => ψ w k) :=
    (contDiff_apply ℝ ℝ k).comp hψ
  have hlapComp (k : Fin 3) :
      (fun w : Vec3 × ℝ => vorticityTestLaplacian ψ w k) =
        vorticityScalarLaplacian (fun w => ψ w k) := by
    funext w
    exact vorticityTestLaplacian_component ψ k w
  have hpartialLap (k i : Fin 3) (w : Vec3 × ℝ) :
      vorticityTestPartial
        (fun y => vorticityTestLaplacian ψ y k) i w =
      vorticityScalarLaplacian
        (fun y => vorticityTestPartial (fun x => ψ x k) i y) w := by
    rw [hlapComp k]
    exact vorticityScalarLaplacian_partial_commute (hcomp k) i w
  fin_cases i
  · change vorticityTestCurl (vorticityTestLaplacian ψ) z 0 =
      vorticityTestLaplacian (vorticityTestCurl ψ) z 0
    rw [vorticityTestCurl_zero]
    rw [hpartialLap 2 1 z, hpartialLap 1 2 z]
    rw [vorticityTestLaplacian_component]
    exact (vorticityScalarLaplacian_sub (CKN.spatialPartial_contDiff (hcomp 2) 1)
      (CKN.spatialPartial_contDiff (hcomp 1) 2) z).symm
  · change vorticityTestCurl (vorticityTestLaplacian ψ) z 1 =
      vorticityTestLaplacian (vorticityTestCurl ψ) z 1
    rw [vorticityTestCurl_one]
    rw [hpartialLap 0 2 z, hpartialLap 2 0 z]
    rw [vorticityTestLaplacian_component]
    exact (vorticityScalarLaplacian_sub (CKN.spatialPartial_contDiff (hcomp 0) 2)
      (CKN.spatialPartial_contDiff (hcomp 2) 0) z).symm
  · change vorticityTestCurl (vorticityTestLaplacian ψ) z 2 =
      vorticityTestLaplacian (vorticityTestCurl ψ) z 2
    rw [vorticityTestCurl_two]
    rw [hpartialLap 1 0 z, hpartialLap 0 1 z]
    rw [vorticityTestLaplacian_component]
    exact (vorticityScalarLaplacian_sub (CKN.spatialPartial_contDiff (hcomp 1) 0)
      (CKN.spatialPartial_contDiff (hcomp 0) 1) z).symm

/-- The time derivative of a vector test is supported in the original test
support. -/
theorem vorticityTestTimeDerivative_tsupport
    {ψ : Vec3 × ℝ → Vec3} :
    tsupport (vorticityTestTimeDerivative ψ) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hnot
  apply hz
  apply funext
  intro i
  have hcomp : (show Vec3 × ℝ from z) ∉
      tsupport (fun w : Vec3 × ℝ => ψ w i) := by
    intro hi
    have hsub := CKN.tsupport_component_subset (ι := Fin 3)
      ψ i (by intro y hy; simp [hy])
    exact hnot (hsub hi)
  have hzero := CKN.timePartial_eq_zero_off_tsupport hcomp
  change vorticityTestTimePartial (fun w => ψ w i) (show ParabolicPoint from z) = 0
  exact hzero

/-- The Laplacian of a vector test is supported in the original test support. -/
theorem vorticityTestLaplacian_tsupport
    {ψ : Vec3 × ℝ → Vec3} :
    tsupport (vorticityTestLaplacian ψ) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hnot
  apply hz
  apply funext
  intro i
  have hcomp : (show Vec3 × ℝ from z) ∉
      tsupport (fun w : Vec3 × ℝ => ψ w i) := by
    intro hi
    have hsub := CKN.tsupport_component_subset (ι := Fin 3)
      ψ i (by intro y hy; simp [hy])
    exact hnot (hsub hi)
  simp only [vorticityTestLaplacian, CKN.spatialSecondPartial]
  apply Finset.sum_eq_zero
  intro j hj
  exact CKN.spatialSecondPartial_eq_zero_off_tsupport hcomp j j

/-- Time differentiation preserves the compact CKN test class and its
support. -/
theorem vorticityTestTimeDerivative_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    vorticityTestTimeDerivative ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I := by
  have hcomponent (i : Fin 3) :
      (fun z : Vec3 × ℝ => vorticityTestTimeDerivative ψ z i) ∈
        CKN.spaceTimeTestFunction (V := ℝ) Ω I := by
    have hψi := CKN.component_mem_spaceTimeTestFunction hψ i
    have htime := vorticityTimePartialTest hψi
    have heq : (fun z : Vec3 × ℝ => vorticityTestTimeDerivative ψ z i) =
        (fun z : Vec3 × ℝ => CKN.timePartial
          (show ParabolicPoint → ℝ from fun w => ψ w i)
          (show ParabolicPoint from z)) := by
      funext z
      rfl
    rw [heq]
    exact htime
  refine ⟨contDiff_pi.2 ?_, ?_, ?_⟩
  · intro i
    exact (hcomponent i).1
  · exact hψ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _)
      vorticityTestTimeDerivative_tsupport
  · exact vorticityTestTimeDerivative_tsupport.trans hψ.2.2

/-- The spatial Laplacian preserves the compact CKN test class and its
support. -/
theorem vorticityTestLaplacian_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    vorticityTestLaplacian ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I := by
  have hcomponent (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => vorticityTestLaplacian ψ z i) := by
    apply ContDiff.sum
    intro j hj
    have hψi := CKN.component_mem_spaceTimeTestFunction hψ i
    have hsecond := CKN.Core.Step3.spatialSecondPartial_contDiff_full hψi.1 j j
    convert hsecond using 1
    rfl
  refine ⟨contDiff_pi.2 hcomponent, ?_, ?_⟩
  · exact hψ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _)
      vorticityTestLaplacian_tsupport
  · exact vorticityTestLaplacian_tsupport.trans hψ.2.2

/-- The curl of a smooth vector test is supported in the original test
support. -/
theorem vorticityTestCurl_tsupport_subset
    {ψ : Vec3 × ℝ → Vec3} :
    tsupport (vorticityTestCurl ψ) ⊆ tsupport ψ := by
  have hzero (z : Vec3 × ℝ) (hz : z ∉ tsupport ψ) :
      vorticityTestCurl ψ z = 0 := by
    apply funext
    intro i
    have hcomp (k : Fin 3) : z ∉ tsupport (fun w : Vec3 × ℝ => ψ w k) := by
      intro hk
      have hsub := CKN.tsupport_component_subset (ι := Fin 3)
        ψ k (by intro y hy; simp [hy])
      exact hz (hsub hk)
    have hpartial (k l : Fin 3) : vorticityTestPartial
        (fun w : Vec3 × ℝ => ψ w k) l z = 0 := by
      rw [vorticityTestPartial_eq_spatialPartial]
      exact CKN.spatialPartial_eq_zero_off_tsupport (hcomp k) l
    fin_cases i
    · change vorticityTestCurl ψ z 0 = (0 : ℝ)
      rw [vorticityTestCurl_zero, hpartial 2 1, hpartial 1 2]
      ring
    · change vorticityTestCurl ψ z 1 = (0 : ℝ)
      rw [vorticityTestCurl_one, hpartial 0 2, hpartial 2 0]
      ring
    · change vorticityTestCurl ψ z 2 = (0 : ℝ)
      rw [vorticityTestCurl_two, hpartial 1 0, hpartial 0 1]
      ring
  have hfun : Function.support (vorticityTestCurl ψ) ⊆ tsupport ψ := by
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot)
  exact closure_minimal hfun (isClosed_tsupport ψ)

end

end ESS
