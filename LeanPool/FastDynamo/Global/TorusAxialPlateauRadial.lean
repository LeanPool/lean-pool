/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusAxialVelocityConcrete

/-!
# The radial form of the fixed axial plateau

The cut-off `ϑ` of `eq:axial-offset` is a function of the Euclidean radius
`|y - p_n| / R_n` alone.  `Global/TorusAxialVelocityConcrete.lean` builds it that way; this
leaf records the consequences that `prop:particle-flow` needs and that no
other part of the velocity layer uses: the radial profile `ϑ_rad : ℝ → ℝ` with its
plateau, support, range, smoothness and Lipschitz bounds, the invariance of `ϑ` under
every linear isometry of the plane, and the two identities in the paper's form

`ϑ((y - p_n)/R_n) = ϑ_rad (|y - p_n| / R_n)`,
`u_n^ax(y) = a_n ϑ_rad (|y - p_n| / R_n) e₃`.

`eq:explicit-particle-flow` — the axial displacement along a circular
trajectory is exactly `t * g_n(r)` — is available only because of this radial form.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-- The paper's radial profile `ϑ : [0, ∞) → ℝ` of `eq:axial-offset`. -/
def axialPlateauRadial (t : ℝ) : ℝ :=
  axialPlateauSq (t ^ 2)

/-- The plateau is radial in the Euclidean norm: `ϑ(y) = ϑ_rad (|y|)`.  This is the
identity `prop:particle-flow` needs. -/
theorem axialPlateau_eq_axialPlateauRadial (y : ℝ × ℝ) :
    axialPlateauBump y = axialPlateauRadial ‖pairToWholePlane y‖ := by
  rw [axialPlateauRadial, axialPlateau_eq_axialPlateauSq]

/-- The scaled cut-off in the paper's form `ϑ(|y - p_n| / R_n)` (`eq:axial-offset`). -/
theorem axialCellCutoff_eq_axialPlateauRadial
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) (x : ℝ × ℝ) :
    P.axialCellCutoff n x =
      axialPlateauRadial
        (pairEuclideanDist x (P.scaleFamily.cellCenter n) /
          P.scaleFamily.bufferRadius n) := by
  rw [axialCellCutoff, axialPlateau_eq_axialPlateauRadial,
    P.norm_pairToWholePlane_axialBufferCoordinate n x]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
