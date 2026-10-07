/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDuhamelStokes
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pairings for the regularized Duhamel formula

The real mild equation is paired against complex Fourier test fields by
taking the real part after complexification.
-/

public section

open MeasureTheory
open Filter Set
open scoped ENNReal FourierTransform
open scoped Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Complexify a real-valued Schwartz vector field pointwise. -/
@[expose]
def complexifyRealSchwartz
    (φ : SchwartzMap L2Vec3 L2Vec3) : SchwartzMap L2Vec3 ComplexVec3 :=
  SchwartzMap.postcompCLM complexifyValue φ

/-- Complexification of the L² class of a real Schwartz function agrees
with the L² class of its pointwise complexification. -/
theorem complexify_toLp_realSchwartz
    (φ : SchwartzMap L2Vec3 L2Vec3) :
    complexifyVectorL2 (φ.toLp 2) = complexSchwartzToL2 (complexifyRealSchwartz φ) := by
  apply Lp.ext
  filter_upwards [complexifyValue.coeFn_compLpL (φ.toLp 2),
    φ.coeFn_toLp 2 volume, (complexifyRealSchwartz φ).coeFn_toLp 2 volume]
    with x hcomp hφ hg
  change ((complexifyValue.compLpL 2 volume) (φ.toLp 2)) x = _
  change ((complexifyValue.compLpL 2 volume) (φ.toLp 2)) x = _ at hcomp
  rw [hcomp, hφ]
  change complexifyValue (φ x) = ((complexifyRealSchwartz φ).toLp 2) x
  rw [hg]
  rfl

end CKN.Leray

end
