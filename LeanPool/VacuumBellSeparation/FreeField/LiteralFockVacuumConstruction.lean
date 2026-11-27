/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LiteralFockVacuumNorm
public import LeanPool.VacuumBellSeparation.Fock.PhysicalTestTotality
public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness

/-!
# Construction of the original cyclic free-field vacuum on literal Fock space

This construction is separated from its later specification proofs.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

/-- The normed additive group of the square-summable Fock sectors. -/
local instance literalFockConstructionNormedGroup (m : ℝ) :
    NormedAddCommGroup (LiteralFockSpace (m := m)) :=
  lp.normedAddCommGroup

/-- The complex normed space of square-summable Fock sectors. -/
local instance literalFockConstructionNormedSpace (m : ℝ) :
    NormedSpace ℂ (LiteralFockSpace (m := m)) :=
  physicalTotalityFockComplexNormedSpace (Lp ℂ 2 (oneParticleMeasure m))

/-- The sectorwise inner product summed over particle numbers. -/
local instance literalFockConstructionInnerProduct (m : ℝ) :
    InnerProductSpace ℂ (LiteralFockSpace (m := m)) :=
  lp.instInnerProductSpace

/-- Completeness of the literal Fock space obtained from its complete sectors. -/
local instance literalFockConstructionComplete (m : ℝ) :
    CompleteSpace (LiteralFockSpace (m := m)) :=
  physicalTotalityFockComplete (Lp ℂ 2 (oneParticleMeasure m))

variable {m : ℝ} (hm : 0 < m)

theorem literalFockWeyl_vacuum (v : Lp ℂ 2 (oneParticleMeasure m)) :
    fockWeyl _ v (literalFockVacuumVector (m := m)) = coherentVector _ v := by
  rw [literalFockVacuumVector, fockWeyl_coherentVector,
    weylPhase_zero_right _ (fun _ _ => rfl), one_smul, add_zero]

/-- The Weyl operator of a real spacetime test function on literal Fock space. -/
def literalTestWeyl (F : RealTestFunction) :
    LiteralFockSpace (m := m) →L[ℂ] LiteralFockSpace (m := m) :=
  fockWeyl (Lp ℂ 2 (oneParticleMeasure m)) (oneParticleL2 hm F)

/-- Construct a free-field vacuum from additive labels preserving the one-particle form
whose coherent vectors are total in symmetric Fock space. -/
def fockVacuumOfLabel (m : ℝ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (label : RealTestFunction → K)
    (hadd : ∀ F G, label (F + G) = label F + label G)
    (hinner : ∀ F G, inner ℂ (label F) (label G) = oneParticleInner m F G)
    (htotal : (Submodule.span ℂ
      (Set.range fun F => coherentVector K (label F))).topologicalClosure = ⊤) :
    FreeFieldVacuum m (SymmetricFockSpace K) where
  weyl F := fockWeyl K (label F)
  vacuum := coherentVector K 0
  weyl_mem_unitary F := fockWeyl_mem_unitary K (label F)
  weyl_mul F G := by
    rw [fockWeyl_mul, ← hadd]
    simp only [weylPhase, id_eq, hinner]
  vacuum_norm := by
    rw [← weylFockEquiv_weylVec, LinearIsometryEquiv.norm_map]
    exact norm_weylVec_zero _ (fun _ _ => rfl)
  vacuum_weyl F := by
    rw [fockWeyl_coherentVector, weylPhase_zero_right _ (fun _ _ => rfl),
      one_smul, add_zero, inner_coherentVector]
    have hn : ‖label F‖ ^ 2 = (oneParticleInner m F F).re := by
      rw [@norm_sq_eq_re_inner ℂ, hinner]
      rfl
    simp only [weylKernel, id_eq, norm_zero, zero_pow two_ne_zero, neg_zero, zero_div,
      zero_sub, inner_zero_left, add_zero, Complex.ofReal_exp, hn]
  cyclic := fockWeyl_cyclic_of_dense_coherentVector K label htotal

/-- The cyclic vacuum system on the Fock space of the massive one-particle representation. -/
def literalFockVacuum : FreeFieldVacuum m (LiteralFockSpace (m := m)) :=
  fockVacuumOfLabel m (Lp ℂ 2 (oneParticleMeasure m)) (oneParticleL2 hm)
    (oneParticleL2_add hm) (inner_oneParticleL2 hm) (physical_coherentVector_dense_span hm)

end VacuumBellSeparation
