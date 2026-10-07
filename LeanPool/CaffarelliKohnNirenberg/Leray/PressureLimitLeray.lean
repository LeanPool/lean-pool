/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.PressureLimit

/-!
# Pressure convergence in the Leray limit

The regularized transport tensor converges in `L^(3/2)` when both velocity
factors converge strongly in `L³`, and the space-time Riesz pressure preserves
that convergence on every finite slab (`prop:leray-pressure-limit`).
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Leray

/-- The product-coordinate space-time region corresponding to the interval
`(0,T)` in the Leray pressure limit (`prop:leray-pressure-limit`). -/
@[expose]
def lerayPressureLimitSlab (T : ℝ) : Set (Vec3 × ℝ) :=
  Set.univ ×ˢ Set.Ioo (0 : ℝ) T

/-- The canonical space-time Riesz pressure on a finite slab, formed from the
product of two `L³` velocity fields. -/
@[expose]
def lerayProductPressureOnSlab
    (T : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T))) : Vec3 × ℝ → ℝ :=
  rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
    (fun i j => (lerayPressureLimitSlab T).indicator (fun z => v z i * w z j))
    (rieszPressureSpaceTime_product_memLp_of_slab
      (MeasurableSet.univ.prod measurableSet_Ioo) v w
      (fun i => hv.eval i) (fun j => hw.eval j))

/-- The regularized Leray pressures converge strongly in `L^(3/2)` on each
finite time slab under the exact strong `L³` velocity convergences in
`prop:leray-limit`. -/
theorem lerayPressureLimit_Lthree
    (T : ℝ)
    (Jseq useq : ℕ → Vec3 × ℝ → Vec3)
    (u : Vec3 × ℝ → Vec3)
    (hJseq : ∀ n, MemLp (Jseq n) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (huseq : ∀ n, MemLp (useq n) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hu : MemLp u 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hJconv : Tendsto (fun n => eLpNorm (Jseq n - u) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
      atTop (𝓝 0))
    (huconv : Tendsto (fun n => eLpNorm (useq n - u) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (lerayProductPressureOnSlab T (Jseq n) (useq n) (hJseq n) (huseq n) -
        lerayProductPressureOnSlab T u u hu hu)
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
      atTop (𝓝 0) := by
  exact rieszPressureSpaceTime_product_tendsto_of_Lthree
    (MeasurableSet.univ.prod measurableSet_Ioo)
    Jseq useq u u hJseq huseq hu hu hJconv huconv

end CKN.Leray

end
