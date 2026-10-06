/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureHelmholtzIdentity
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialCutoff

/-!
# Assoc Pressure Solenoidal Cutoff

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatially cut off vector potential used to test the Leray--Hopf
equation in the proof of `lem:helmholtz-test`. -/
@[expose]
def associatedPressureHelmholtzCutoffVectorPotential
    (φ : Vec3 × ℝ → Vec3) (n : ℕ) : Vec3 × ℝ → Vec3 :=
  fun z => rieszPressurePotentialCutoff n z.1 •
    associatedPressureHelmholtzVectorPotential φ z

private theorem associatedPressureHelmholtzVectorPotential_zero_off_time_support
    {φ : Vec3 × ℝ → Vec3}
    {t : ℝ} (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
    associatedPressureHelmholtzVectorPotential φ (x, t) = 0 := by
  have hnot : (x, t) ∉ tsupport φ := by
    intro hz
    exact ht ⟨(x, t), hz, rfl⟩
  have hslice (i : Fin 3) : (fun y : Vec3 => φ (y, t) i) = 0 := by
    funext y
    have hnoty : (y, t) ∉ tsupport φ := by
      intro hz
      exact ht ⟨(y, t), hz, rfl⟩
    have hy : φ (y, t) = 0 := image_eq_zero_of_notMem_tsupport hnoty
    exact congrArg (fun v : Vec3 => v i) hy
  have hpartial (i j : Fin 3) (y : Vec3) :
      CKN.spatialPartialProd (fun q : Vec3 × ℝ => φ q i) j (y, t) = 0 := by
    change (fderiv ℝ (fun q : Vec3 => φ (q, t) i) y) (CKN.basisVec j) = 0
    rw [hslice i]
    simp
  have hsource (j : Fin 3) (y : Vec3) :
      associatedPressureTestCurlComponent φ j (y, t) = 0 := by
    fin_cases j <;>
      simp [associatedPressureTestCurlComponent, hpartial]
  funext j
  change -associatedPressureNewtonianPotential
    (associatedPressureTestCurlComponent φ j) (x, t) = 0
  have hsourceSlice :
      (fun y : Vec3 => associatedPressureTestCurlComponent φ j (y, t)) = 0 := by
    funext y
    exact hsource j y
  rw [associatedPressureNewtonianPotential]
  change -CKN.pressureNewtonianPotential (fun y : Vec3 =>
      associatedPressureTestCurlComponent φ j (y, t)) x = 0
  rw [hsourceSlice]
  simp [CKN.pressureNewtonianPotential]

/-- The vector-potential cutoff belongs to the compact test class on the
original time slab. -/
theorem associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    associatedPressureHelmholtzCutoffVectorPotential φ n ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  let K : Set ℝ := (tsupport φ).image Prod.snd
  let R : ℝ := 3 * rieszPressurePotentialCutoffRadius n / 4
  let B : Set Vec3 := CKN.euclideanClosedBall 0 R
  let S : Set (Vec3 × ℝ) := B ×ˢ K
  have hK : IsCompact K := hφ.2.1.isCompact.image continuous_snd
  have hKsubset : K ⊆ Ioo 0 T := by
    rintro t ⟨z, hz, rfl⟩
    exact hφ.2.2 hz |>.2
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (mul_pos (by norm_num)
      (rieszPressurePotentialCutoffRadius_pos n)) (by norm_num)
  have hB : IsCompact B := by
    dsimp [B, R]
    exact CKN.isCompact_euclideanClosedBall 0 hR.le
  have hS : IsCompact S := hB.prod hK
  have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => rieszPressurePotentialCutoff n z.1) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadius_pos n)).comp contDiff_fst
  have hpotentialSmooth := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotential φ n) := by
    apply contDiff_pi.2
    intro j
    exact hcutSmooth.mul
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).contDiff.comp hpotentialSmooth)
  have hKzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0 := by
    intro t ht x
    exact associatedPressureHelmholtzVectorPotential_zero_off_time_support ht x
  have hpointzero : ∀ z, z ∉ S →
      associatedPressureHelmholtzCutoffVectorPotential φ n z = 0 := by
    intro z hz
    by_cases ht : z.2 ∈ K
    · have hx : z.1 ∉ B := by
        intro hx
        exact hz ⟨hx, ht⟩
      have houter : z.1 ∉
          CKN.euclideanBall 0 (3 * rieszPressurePotentialCutoffRadius n / 4) := by
        intro hy
        apply hx
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        have hy' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hy
        simpa [B, R] using hy'.le
      have hnot : z.1 ∉ tsupport (rieszPressurePotentialCutoff n) := by
        intro hy
        have hy' := CKN.mollifiedBallCutoff_tsupport_subset_outer 0
          (rieszPressurePotentialCutoffRadius_pos n) hy
        exact houter (by simpa [R] using hy')
      have hcut : rieszPressurePotentialCutoff n z.1 = 0 :=
        image_eq_zero_of_notMem_tsupport hnot
      simp [associatedPressureHelmholtzCutoffVectorPotential, hcut]
    · simp [associatedPressureHelmholtzCutoffVectorPotential,
        hKzero z.2 ht z.1]
  have hcompact : HasCompactSupport
      (associatedPressureHelmholtzCutoffVectorPotential φ n) :=
    HasCompactSupport.intro hS hpointzero
  have htsub : tsupport (associatedPressureHelmholtzCutoffVectorPotential φ n) ⊆ S := by
    change closure (Function.support
      (associatedPressureHelmholtzCutoffVectorPotential φ n)) ⊆ S
    apply closure_minimal
    · intro z hz
      by_contra hnot
      exact hz (hpointzero z hnot)
    · exact hS.isClosed
  refine ⟨hcont, hcompact, ?_⟩
  have hsub : S ⊆ spaceTimeSet Set.univ (Ioo 0 T) := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    exact ⟨Set.mem_univ _, hKsubset ht⟩
  exact htsub.trans hsub

/-- The curl of the cut off vector potential is a solenoidal test in the
Leray--Hopf equation. -/
theorem associatedPressureHelmholtzCutoffCurl_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n) ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) :=
  associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n)

/-- The solenoidal cutoff tests give zero in the Leray--Hopf momentum
identity. -/
theorem associatedPressureHelmholtzCutoffCurl_momentum_zero
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∫ z in spaceTimeSet Set.univ (Ioo 0 T),
      (-(∑ i : Fin 3, u z i * timePartial
          (fun y => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n)
            (parabolicHomeomorph y) i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial
              (fun y => associatedPressureTestCurl
                (associatedPressureHelmholtzCutoffVectorPotential φ n)
                (parabolicHomeomorph y) i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial
              (fun y => associatedPressureTestCurl
                (associatedPressureHelmholtzCutoffVectorPotential φ n)
                (parabolicHomeomorph y) i) j z = 0 := by
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let w : ParabolicPoint → Vec3 := fun y =>
    associatedPressureTestCurl
      (associatedPressureHelmholtzCutoffVectorPotential φ n)
      (parabolicHomeomorph y)
  have hw : w ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
    change (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) ∈ _
    simpa [w] using associatedPressureHelmholtzCutoffCurl_mem_spaceTimeTestFunction hφ n
  have htest := associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n
  have hdiv : ∀ z : ParabolicPoint,
      ∑ i : Fin 3, spatialPartial (fun y => w y i) i z = 0 := by
    intro z
    change ∑ i : Fin 3, associatedPressureTestPartial
      (fun y : Vec3 × ℝ =>
        associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n) y i)
      i (parabolicHomeomorph z) = 0
    exact associatedPressureTestCurl_divergence htest.1 (parabolicHomeomorph z)
  exact hMomentum w hw hdiv

end CKN.Leray

end
