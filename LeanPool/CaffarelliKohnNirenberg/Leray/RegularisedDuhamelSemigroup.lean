/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildDefinition
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Semigroup identities for the regularized mild equation

These identities express restarting the Fourier heat evolution and its
projected divergence term at an intermediate time.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private instance : ENNReal.HolderTriple (∞ : ℝ≥0∞) 2 2 := by
  constructor
  simp

theorem lpMultiplier_add (m : Lp (α := L2Vec3) ℂ ∞)
    (f g : ComplexVectorL2) : m • (f + g) = m • f + m • g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) m (f + g), Lp.coeFn_add f g,
    Lp.coeFn_lpSMul (r := 2) m f, Lp.coeFn_lpSMul (r := 2) m g,
    Lp.coeFn_add (m • f) (m • g)] with ξ hL hfg hF hG hsum
  calc
    (m • (f + g)) ξ = m ξ • (f + g) ξ := hL
    _ = m ξ • (f ξ + g ξ) := by
      rw [hfg]
      simp only [Pi.add_apply]
    _ = m ξ • f ξ + m ξ • g ξ := by simp
    _ = (m • f) ξ + (m • g) ξ := by
      rw [hF, hG]
      rfl
    _ = (m • f + m • g) ξ := hsum.symm

theorem lpMultiplier_smul (m : Lp (α := L2Vec3) ℂ ∞)
    (c : ℂ) (f : ComplexVectorL2) : m • (c • f) = c • (m • f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) m (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_lpSMul (r := 2) m f, Lp.coeFn_smul c (m • f)] with ξ hL hcf hF hR
  calc
    (m • (c • f)) ξ = m ξ • (c • f) ξ := hL
    _ = m ξ • (c • f ξ) := by
      rw [hcf]
      simp only [Pi.smul_apply]
    _ = (m ξ * c) • f ξ := by rw [smul_smul]
    _ = (c * m ξ) • f ξ := by rw [mul_comm]
    _ = c • (m ξ • f ξ) := by rw [smul_smul]
    _ = c • (m • f) ξ := congrArg (fun x => c • x) hF.symm
    _ = (c • (m • f)) ξ := hR.symm

/-- The spatial `L²` class of a Schwartz vector field. -/
@[expose]
def complexSchwartzToL2
    (g : SchwartzMap L2Vec3 ComplexVec3) : ComplexVectorL2 := g.toLp 2

/-- The complex heat evolution as a bounded linear operator on spatial `L²`. -/
@[expose]
noncomputable def heatSemigroupCLM (t : ℝ) (ht : 0 ≤ t) :
    ComplexVectorL2 →L[ℂ] ComplexVectorL2 := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  let L : ComplexVectorL2 →ₗ[ℂ] ComplexVectorL2 := {
    toFun := heatSemigroup t ht
    map_add' := by
      intro f g
      change ℱ.symm (heatMultiplier t ht • ℱ (f + g)) =
        ℱ.symm (heatMultiplier t ht • ℱ f) +
          ℱ.symm (heatMultiplier t ht • ℱ g)
      rw [ℱ.map_add, lpMultiplier_add, ℱ.symm.map_add]
    map_smul' := by
      intro c f
      change ℱ.symm (heatMultiplier t ht • ℱ (c • f)) =
        c • ℱ.symm (heatMultiplier t ht • ℱ f)
      rw [ℱ.map_smul, lpMultiplier_smul, ℱ.symm.map_smul]
  }
  exact L.mkContinuous 1 (by
    intro f
    calc
      ‖L f‖ = ‖heatSemigroup t ht f‖ := by rfl
      _ ≤ ‖f‖ := heatSemigroup_norm_le t ht f
      _ = 1 * ‖f‖ := by ring)

@[simp]
theorem heatSemigroupCLM_apply (t : ℝ) (ht : 0 ≤ t)
    (f : ComplexVectorL2) : heatSemigroupCLM t ht f = heatSemigroup t ht f := by
  simp [heatSemigroupCLM, LinearMap.mkContinuous_apply]

end CKN.Leray

end
