/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatConvolution

/-!
# Heat Orbit

The componentwise Gaussian convolution of a vector field at a fixed time.
-/

public section

open CKN.Foundation.Heat CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The componentwise Gaussian convolution of a vector field at a fixed time. -/
@[expose] def heatConvVec3 (t : ℝ) (b : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  fun i => heatConv t (fun y => b y i) x

/-- The heat orbit in `sec:pv-trace`, represented by CKN's Gaussian kernel. -/
@[expose] def heatOrbit (b : Vec3 → Vec3) (z : ParabolicPoint) : Vec3 :=
  heatConvVec3 z.2 b z.1

end ESS

end
