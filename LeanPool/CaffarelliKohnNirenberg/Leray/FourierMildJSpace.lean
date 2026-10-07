/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalJRange
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The closed `J` carrier for the regularized mild equation

The continuous mild flow is formulated in the closed divergence-free
subspace of real velocity `L²`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Real velocity `L²` data whose coordinate representative belongs to the
closed divergence-free space `J`. -/
@[expose]
def RegularizedMildJData (u : RealVectorL2) : Prop :=
  CKN.IsInJ (realVectorL2Representative u)

private theorem realVectorL2Representative_add_ae
    (u v : RealVectorL2) :
    realVectorL2Representative (u + v) =ᵐ[volume]
      realVectorL2Representative u + realVectorL2Representative v := by
  have hLp : (fun x : L2Vec3 => (u + v) x) =ᵐ[volume]
      fun x => u x + v x := Lp.coeFn_add u v
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
  filter_upwards [htransport] with x hx
  change l2Vec3Equiv ((u + v) (WithLp.toLp 2 x)) =
    l2Vec3Equiv (u (WithLp.toLp 2 x)) + l2Vec3Equiv (v (WithLp.toLp 2 x))
  rw [hx, map_add]

private theorem realVectorL2Representative_smul_ae
    (c : ℝ) (u : RealVectorL2) :
    realVectorL2Representative (c • u) =ᵐ[volume]
      c • realVectorL2Representative u := by
  have hLp : (fun x : L2Vec3 => (c • u) x) =ᵐ[volume]
      fun x => c • u x := Lp.coeFn_smul c u
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
  filter_upwards [htransport] with x hx
  change l2Vec3Equiv ((c • u) (WithLp.toLp 2 x)) =
    c • l2Vec3Equiv (u (WithLp.toLp 2 x))
  rw [hx, map_smul]

end CKN.Leray

end
