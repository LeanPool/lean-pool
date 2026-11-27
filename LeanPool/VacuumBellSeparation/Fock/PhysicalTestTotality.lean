/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.StandardTensorTotality
public import LeanPool.VacuumBellSeparation.Fock.RealExponentialCoefficients
public import LeanPool.VacuumBellSeparation.Fock.WeylFockEquivalence
public import LeanPool.VacuumBellSeparation.FreeField.WedgeTimeSlice
public import LeanPool.VacuumBellSeparation.FreeField.WedgeSourceStandardness

/-!
# Totality for the original compact spacetime test labels

Real rescaling of compact tests recovers every tensor coefficient. The
actual wedge time-slice closure and the proved standard one-particle
wedge space then give totality in the literal full Fock space. No
abstract density or cyclicity assumption is added.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open MeasureTheory
open scoped InnerProductSpace

/-- The real scalar action on a symmetric tensor sector, restricted from complex scalars. -/
local instance physicalTotalitySectorRealModule (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :
    Module ℝ (SymmetricTensorPower E n) :=
  Module.complexToReal (SymmetricTensorPower E n)

/-- Completeness of each closed symmetric tensor sector. -/
local instance physicalTotalitySectorComplete (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :
    CompleteSpace (SymmetricTensorPower E n) :=
  (isClosed_symmetricTensorSubmodule E n).isComplete.completeSpace_coe

/-- Completeness of the square-summable sum of the symmetric tensor sectors. -/
local instance physicalTotalityFockComplete (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    CompleteSpace (SymmetricFockSpace E) := lp.completeSpace

/-- The complex norm on the square-summable sum of the symmetric tensor sectors. -/
local instance physicalTotalityFockComplexNormedSpace (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    NormedSpace ℂ (SymmetricFockSpace E) := lp.instNormedSpace

variable {m : ℝ} (hm : 0 < m)

/-- Literal real rescaling of an original compact spacetime test. -/
def scaleTest (t : ℝ) (F : RealTestFunction) : RealTestFunction :=
  ⟨fun x => t • F.1 x, F.2.1.const_smul t,
    F.2.2.smul_left (f := fun _ : Spacetime => t)⟩

theorem oneParticle_scaleTest (t : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (scaleTest t F) p = (t : ℂ) * oneParticle m F p := by
  unfold oneParticle scaleTest
  simp only [smul_eq_mul, Complex.ofReal_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem oneParticleL2_scaleTest (t : ℝ) (F : RealTestFunction) :
    oneParticleL2 hm (scaleTest t F) = t • oneParticleL2 hm F := by
  apply Lp.ext
  filter_upwards [coeFn_oneParticleL2 hm (scaleTest t F),
    Lp.coeFn_smul t (oneParticleL2 hm F), coeFn_oneParticleL2 hm F] with p h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃, oneParticle_scaleTest, Complex.real_smul]

theorem physicalFock_eq_zero_of_test_exponential_orthogonal
    (x : SymmetricFockSpace (Lp ℂ 2 (oneParticleMeasure m)))
    (hx : ∀ F : RealTestFunction,
      inner ℂ x (exponentialVector _ (oneParticleL2 hm F)) = 0) : x = 0 := by
  let H := Lp ℂ 2 (oneParticleMeasure m)
  have hc (F : RealTestFunction) (n : ℕ) :
      inner ℂ (x n) (pureSymmetricTensor H n (oneParticleL2 hm F)) = 0 := by
    apply inner_pureTensor_zero_of_real_exponential_zero H x (oneParticleL2 hm F)
    intro t
    -- The coefficient theorem uses restriction of complex scalars on H;
    -- establish the same Lp equality directly in its complex scalar action.
    have hscale : oneParticleL2 hm (scaleTest t F) = (t : ℂ) • oneParticleL2 hm F := by
      apply Lp.ext
      filter_upwards [coeFn_oneParticleL2 hm (scaleTest t F),
        Lp.coeFn_smul (t : ℂ) (oneParticleL2 hm F), coeFn_oneParticleL2 hm F] with p h₁ h₂ h₃
      rw [h₁, h₂, Pi.smul_apply, h₃, oneParticle_scaleTest, smul_eq_mul]
    change inner ℂ x (exponentialVector H ((t : ℂ) • oneParticleL2 hm F)) = 0
    rw [← hscale]
    exact hx (scaleTest t F)
  apply lp.ext
  funext n
  apply symmetricTensor_eq_zero_of_standard_diagonal (leftWedgeSourceStandardSubspace hm 0) n
  intro v
  let M := symmetricTensorScalarForm H n (x n)
  have hcont : Continuous (fun y : H => M (fun _ => y)) :=
    M.cont.comp (continuous_pi fun _ => continuous_id)
  have hz : closure (wedgeSpacetimeTestVectors hm 0) ⊆
      {y : H | M (fun _ => y) = 0} := by
    apply closure_minimal ?_ (isClosed_eq hcont continuous_const)
    rintro _ ⟨F, hF, rfl⟩
    exact hc F n
  apply hz
  rw [closure_wedgeSpacetimeTestVectors]
  exact v.property

theorem physical_coherentVector_dense_span :
    (Submodule.span ℂ (Set.range fun F : RealTestFunction =>
      coherentVector (Lp ℂ 2 (oneParticleMeasure m))
        (oneParticleL2 hm F))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range fun F : RealTestFunction =>
    coherentVector (Lp ℂ 2 (oneParticleMeasure m)) (oneParticleL2 hm F))
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply physicalFock_eq_zero_of_test_exponential_orthogonal hm x
    intro F
    have h : inner ℂ x (coherentVector (Lp ℂ 2 (oneParticleMeasure m))
        (oneParticleL2 hm F)) = 0 :=
      K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨F, rfl⟩) hx
    change inner ℂ x
      (Complex.exp ((-(‖oneParticleL2 hm F‖ ^ 2 / 2) : ℝ) : ℂ) •
        exponentialVector (Lp ℂ 2 (oneParticleMeasure m)) (oneParticleL2 hm F)) = 0 at h
    rw [inner_smul_right] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  let : CompleteSpace K.topologicalClosure :=
    K.isClosed_topologicalClosure.isComplete.completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

end VacuumBellSeparation.Fock
