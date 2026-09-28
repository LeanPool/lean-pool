/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch002
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Foundation.Batch004
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Semantics.Batch002
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Semantics.Batch001
public import Mathlib.Data.Nat.Find
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.Definitions`.
* `KernelOnly.PartB.Parameters`.
* `KernelOnly.PartB.CellSemanticsCore`.
* `KernelOnly.PartB.Phase1Semantics`.
* `KernelOnly.PartB.Phase2Semantics`.
* `KernelOnly.PartB.Phase3Semantics`.
* `KernelOnly.PartB.Phase4Semantics`.
* `KernelOnly.PartB.Phase5Semantics`.
* `KernelOnly.PartB.CellSemantics`.
* `KernelOnly.PartB.CellCover`.
* `KernelOnly.PartB.Continuum`.
-/

@[expose] public section

noncomputable section


section

/-!
# Part B semantic definitions

The numerical layer from Part A is frozen.  This file names the certified
parameter vector and the two real support functions whose continuum lower
bounds are established by the exact cell certificate.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

/-- The unique direct-system parameter vector certified in Part A. -/
def params : Romik.Params :=
  Romik.coordEquiv.symm PartALeanCert.fullRoot

/-- The physical parameter interval. -/
def physicalInterval : Set ℝ := Set.Icc (0 : ℝ) (Real.pi / 2)

/-- The two global support functions used in the manuscript's grid lemma. -/
def Gu (s t : ℝ) : ℝ :=
  1 + dot (Romik.path params s - Romik.path params t) (u s)

/-- The vertical support slack between two path positions in the frame at `s`. -/
def Gv (s t : ℝ) : ℝ :=
  1 + dot (Romik.path params s - Romik.path params t) (v s)

/-- The real version of the exact rational target. -/
def target : ℝ := (targetQ : ℝ)

/-- Physical mesh node `iπ/128`. -/
def nodeTime (i : Nat) : ℝ := (nodeCoeff i : ℝ) * Real.pi

/-- Physical closed cell. -/
def cellSet (i : Cell) : Set ℝ :=
  Set.Icc (nodeTime i.1) (nodeTime (i.1 + 1))

/-- Semantic containment in a planar interval box. -/
def PointContains (z : RatInterval × RatInterval) (p : Point) : Prop :=
  RatInterval.Contains z.1 p.1 ∧ RatInterval.Contains z.2 p.2

end PartB
end GerverSofa

end

end

end

section

/-!
# Part B parameter, matching and regularity certificate

Every theorem in this file is a direct consequence of the concrete Part A
unique zero.  No numerical computation is repeated.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

/-- The certified parameter vector lies in the direct Romik box. -/
theorem params_mem : params ∈ Romik.box := by
  simpa [params, Romik.vectorBox] using PartALeanCert.fullRoot_mem

/-- The certified parameter vector satisfies all 22 direct equations. -/
theorem params_equations : Romik.Equations params := by
  simpa [params, Romik.Equations, Romik.vectorSystem] using
    PartALeanCert.fullRoot_zero

/-- The four physical switches are correctly ordered. -/
theorem params_switchOrder : Romik.SwitchOrder params :=
  Romik.switchOrder_of_mem_box params_mem

/-- Positional matching at `φ`. -/
theorem match12 : Romik.path1 params params.phi = Romik.path2 params params.phi :=
  Romik.match_path12_of_equations params_equations

/-- Positional matching at `θ`. -/
theorem match23 : Romik.path2 params params.theta = Romik.path3 params params.theta :=
  Romik.match_path23_of_equations params_equations

/-- Positional matching at `π/2-θ`. -/
theorem match34 :
    Romik.path3 params (Real.pi / 2 - params.theta) =
      Romik.path4 params (Real.pi / 2 - params.theta) :=
  Romik.match_path34_of_equations params_equations

/-- Positional matching at `π/2-φ`. -/
theorem match45 :
    Romik.path4 params (Real.pi / 2 - params.phi) =
      Romik.path5 params (Real.pi / 2 - params.phi) :=
  Romik.match_path45_of_equations params_equations

/-- Global continuity of the literal five-phase path. -/
theorem continuous_path : Continuous (Romik.path params) :=
  Romik.continuous_path_of_mem_box_and_equations params_mem params_equations

/-- Global continuity of the associated rigid frame. -/
theorem continuous_frame : SE2.ContinuousPath (Romik.frame params) :=
  Romik.continuousPath_frame_of_path params continuous_path

/-- Exact initial normalization. -/
theorem path_zero : Romik.path params 0 = (0, 0) :=
  Romik.path_zero_of_mem_box_and_equations params_mem params_equations

/-- Clean exact bounds for the two independent switching angles. -/
theorem phi_bounds :
    ((1958868239504182093160893749 : ℝ) /
      50000000000000000000000000000) ≤ params.phi ∧
    params.phi ≤
      ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) := by
  have hp := params_mem
  dsimp [params, Romik.vectorBox, Romik.box, qR] at hp ⊢
  aesop

theorem theta_bounds :
    ((34065075469136244723692787727 : ℝ) /
      50000000000000000000000000000) ≤ params.theta ∧
    params.theta ≤
      ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) := by
  have hp := params_mem
  dsimp [params, Romik.vectorBox, Romik.box, qR] at hp ⊢
  aesop

end PartB
end GerverSofa

end

end

end

section

/-!
# Core semantic infrastructure for the Part B cell certificate

Hull, time-cell, certified-root-coordinate and trigonometric containment lemmas
are isolated here so the five analytic phases can be compiled and diagnosed
independently.
-/

/-! ## Hull and time-cell semantics -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem contains_intervalHull_left {a b : RatInterval} {x : ℝ}
    (hx : Contains a x) : Contains (intervalHull a b) x := by
  constructor
  · have hmin : min a.lo b.lo ≤ a.lo := min_le_left _ _
    exact le_trans (by exact_mod_cast hmin) hx.1
  · have hmax : a.hi ≤ max a.hi b.hi := le_max_left _ _
    exact le_trans hx.2 (by exact_mod_cast hmax)

theorem contains_intervalHull_right {a b : RatInterval} {x : ℝ}
    (hx : Contains b x) : Contains (intervalHull a b) x := by
  constructor
  · have hmin : min a.lo b.lo ≤ b.lo := min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) hx.1
  · have hmax : b.hi ≤ max a.hi b.hi := le_max_right _ _
    exact le_trans hx.2 (by exact_mod_cast hmax)

theorem pointContains_hull_left {a b : RatInterval × RatInterval} {x : Point}
    (hx : PointContains a x) : PointContains (pointHull a b) x := by
  exact ⟨contains_intervalHull_left hx.1,
    contains_intervalHull_left hx.2⟩

theorem pointContains_hull_right {a b : RatInterval × RatInterval} {x : Point}
    (hx : PointContains b x) : PointContains (pointHull a b) x := by
  exact ⟨contains_intervalHull_right hx.1,
    contains_intervalHull_right hx.2⟩

theorem nodeTime_mono {i j : Nat} (hij : i ≤ j) :
    nodeTime i ≤ nodeTime j := by
  unfold nodeTime nodeCoeff
  apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
  norm_num
  have hijR : (i : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hij
  exact div_le_div_of_nonneg_right hijR (by norm_num)

theorem cellTimeInterval_contains_start (i : Cell) :
    Contains (cellTimeInterval i) (nodeTime i.1) := by
  apply contains_intervalHull_left
  simpa [nodeTime, nodeCoeff, ExactReplay.scale] using
    (RatInterval.contains_scale (a := nodeCoeff i.1)
      ExactReplay.piI_contains_pi)

theorem cellTimeInterval_contains_end (i : Cell) :
    Contains (cellTimeInterval i) (nodeTime (i.1 + 1)) := by
  apply contains_intervalHull_right
  simpa [nodeTime, nodeCoeff, ExactReplay.scale] using
    (RatInterval.contains_scale (a := nodeCoeff (i.1 + 1))
      ExactReplay.piI_contains_pi)

theorem cellTimeInterval_contains {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) : Contains (cellTimeInterval i) t := by
  exact ⟨le_trans (cellTimeInterval_contains_start i).1 ht.1,
    le_trans ht.2 (cellTimeInterval_contains_end i).2⟩

/-! ## The Part A root is enclosed coordinatewise -/

theorem root_coord_contains (k : Fin 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox k.1)
      (PartALeanCert.fullRoot k) := by
  exact ((Romik.inputBox_exact PartALeanCert.fullRoot).1
    PartALeanCert.fullRoot_mem).2 k

theorem k11_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 0) params.k11 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 0)
    (PartALeanCert.fullRoot (0 : Fin 22))
  exact root_coord_contains (0 : Fin 22)
theorem k12_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 1) params.k12 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 1)
    (PartALeanCert.fullRoot (1 : Fin 22))
  exact root_coord_contains (1 : Fin 22)
theorem k21_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 2) params.k21 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 2)
    (PartALeanCert.fullRoot (2 : Fin 22))
  exact root_coord_contains (2 : Fin 22)
theorem k22_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 3) params.k22 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 3)
    (PartALeanCert.fullRoot (3 : Fin 22))
  exact root_coord_contains (3 : Fin 22)
theorem k31_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 4) params.k31 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 4)
    (PartALeanCert.fullRoot (4 : Fin 22))
  exact root_coord_contains (4 : Fin 22)
theorem k32_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 5) params.k32 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 5)
    (PartALeanCert.fullRoot (5 : Fin 22))
  exact root_coord_contains (5 : Fin 22)
theorem k41_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 6) params.k41 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 6)
    (PartALeanCert.fullRoot (6 : Fin 22))
  exact root_coord_contains (6 : Fin 22)
theorem k42_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 7) params.k42 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 7)
    (PartALeanCert.fullRoot (7 : Fin 22))
  exact root_coord_contains (7 : Fin 22)
theorem k51_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 8) params.k51 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 8)
    (PartALeanCert.fullRoot (8 : Fin 22))
  exact root_coord_contains (8 : Fin 22)
theorem k52_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 9) params.k52 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 9)
    (PartALeanCert.fullRoot (9 : Fin 22))
  exact root_coord_contains (9 : Fin 22)
theorem a1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 10) params.a1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 10)
    (PartALeanCert.fullRoot (10 : Fin 22))
  exact root_coord_contains (10 : Fin 22)
theorem a2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 11) params.a2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 11)
    (PartALeanCert.fullRoot (11 : Fin 22))
  exact root_coord_contains (11 : Fin 22)
theorem b1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 12) params.b1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 12)
    (PartALeanCert.fullRoot (12 : Fin 22))
  exact root_coord_contains (12 : Fin 22)
theorem b2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 13) params.b2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 13)
    (PartALeanCert.fullRoot (13 : Fin 22))
  exact root_coord_contains (13 : Fin 22)
theorem c1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 14) params.c1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 14)
    (PartALeanCert.fullRoot (14 : Fin 22))
  exact root_coord_contains (14 : Fin 22)
theorem c2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 15) params.c2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 15)
    (PartALeanCert.fullRoot (15 : Fin 22))
  exact root_coord_contains (15 : Fin 22)
theorem d1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 16) params.d1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 16)
    (PartALeanCert.fullRoot (16 : Fin 22))
  exact root_coord_contains (16 : Fin 22)
theorem d2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 17) params.d2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 17)
    (PartALeanCert.fullRoot (17 : Fin 22))
  exact root_coord_contains (17 : Fin 22)
theorem e1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 18) params.e1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 18)
    (PartALeanCert.fullRoot (18 : Fin 22))
  exact root_coord_contains (18 : Fin 22)
theorem e2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 19) params.e2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 19)
    (PartALeanCert.fullRoot (19 : Fin 22))
  exact root_coord_contains (19 : Fin 22)

theorem point_contains (q : ℚ) : Contains (RatInterval.point q) (q : ℝ) :=
  (RatInterval.contains_point_iff q (q : ℝ)).2 rfl

theorem trig_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    Contains (ExactReplay.cosineInterval (cellTimeInterval i)) (Real.cos t) ∧
    Contains (ExactReplay.sineInterval (cellTimeInterval i)) (Real.sin t) := by
  have htI := cellTimeInterval_contains htCell
  exact ⟨ExactReplay.cosI_contains htI htPhys.1 htPhys.2,
    ExactReplay.sinI_contains htI htPhys.1 htPhys.2⟩

end PartB
end GerverSofa

end

end

end

section

/-! Semantic enclosure for analytic path phase 1. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece1_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 1 i) (Romik.path1 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hz1 := RatInterval.contains_sub
    (RatInterval.contains_add (RatInterval.contains_mul a1_contains hc)
      (RatInterval.contains_mul a2_contains hs)) hone
  have hz2 := RatInterval.contains_sub
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg a2_contains) hc)
      (RatInterval.contains_mul a1_contains hs)) hhalf
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path1, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr1 k11_contains
  · simpa [cellPieceInterval, ti, Romik.path1, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr2 k12_contains

end PartB
end GerverSofa

end

end

end

section

/-! Semantic enclosure for analytic path phase 2. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece2_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 2 i) (Romik.path2 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hquarter := point_contains (1 / 4)
  have htt := RatInterval.contains_mul htI htI
  have hz1 := RatInterval.contains_add
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg hquarter) htt)
      (RatInterval.contains_mul b1_contains htI)) b2_contains
  have hz2 := RatInterval.contains_sub
    (RatInterval.contains_sub (RatInterval.contains_mul hhalf htI) b1_contains)
    hone
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path2, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr1 k21_contains
  · simpa [cellPieceInterval, ti, Romik.path2, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr2 k22_contains

end PartB
end GerverSofa

end

end

end

section

/-! Semantic enclosure for analytic path phase 3. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece3_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 3 i) (Romik.path3 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hz1 := RatInterval.contains_sub c1_contains htI
  have hz2 := RatInterval.contains_add c2_contains htI
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path3, Romik.rot, Romik.addK] using
      RatInterval.contains_add hr1 k31_contains
  · simpa [cellPieceInterval, ti, Romik.path3, Romik.rot, Romik.addK] using
      RatInterval.contains_add hr2 k32_contains

end PartB
end GerverSofa

end

end

end

section

/-! Semantic enclosure for analytic path phase 4. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece4_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 4 i) (Romik.path4 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hquarter := point_contains (1 / 4)
  have htt := RatInterval.contains_mul htI htI
  have hz1 := RatInterval.contains_sub
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg hhalf) htI)
      d1_contains) hone
  have hz2 := RatInterval.contains_add
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg hquarter) htt)
      (RatInterval.contains_mul d1_contains htI)) d2_contains
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path4, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr1 k41_contains
  · simpa [cellPieceInterval, ti, Romik.path4, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr2 k42_contains

end PartB
end GerverSofa

end

end

end

section

/-! Semantic enclosure for analytic path phase 5. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece5_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 5 i) (Romik.path5 params t) := by
  let ti := cellTimeInterval i
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hz1 := RatInterval.contains_sub
    (RatInterval.contains_add (RatInterval.contains_mul e1_contains hc)
      (RatInterval.contains_mul e2_contains hs)) hhalf
  have hz2 := RatInterval.contains_sub
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg e2_contains) hc)
      (RatInterval.contains_mul e1_contains hs)) hone
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path5, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr1 k51_contains
  · simpa [cellPieceInterval, ti, Romik.path5, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr2 k52_contains

end PartB
end GerverSofa

end

end

end

section

/-!
# Assembly of semantic soundness for the Part B cell certificate

The five phase enclosures are independent modules.  This file classifies the
four switching cells, selects the appropriate phase/hull, and proves semantic
soundness of the two product-cell support expressions.
-/

/-! ## Switches lie in exactly four mesh cells -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

private theorem node1_lt_phi : nodeTime 1 < params.phi := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := phi_bounds.1
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem phi_lt_node2 : params.phi < nodeTime 2 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := phi_bounds.2
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem node27_lt_theta : nodeTime 27 < params.theta := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := theta_bounds.1
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem theta_lt_node28 : params.theta < nodeTime 28 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := theta_bounds.2
  unfold nodeTime nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

private theorem node36_lt_eta :
    nodeTime 36 < Real.pi / 2 - params.theta := by
  have h := theta_lt_node28
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem eta_lt_node37 :
    Real.pi / 2 - params.theta < nodeTime 37 := by
  have h := node27_lt_theta
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem node62_lt_tau :
    nodeTime 62 < Real.pi / 2 - params.phi := by
  have h := phi_lt_node2
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem tau_lt_node63 :
    Real.pi / 2 - params.phi < nodeTime 63 := by
  have h := node1_lt_phi
  unfold nodeTime nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

private theorem phase1_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hphase : t ≤ params.phi) : i.1 ≤ 1 := by
  by_contra hnot
  have hi : 2 ≤ i.1 := by omega
  have h2i : nodeTime 2 ≤ nodeTime i.1 := nodeTime_mono hi
  linarith [phi_lt_node2, ht.1]

private theorem phase2_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hlo : params.phi < t)
    (hhi : t ≤ params.theta) : 1 ≤ i.1 ∧ i.1 ≤ 27 := by
  constructor
  · by_contra hnot
    have hi0 : i.1 = 0 := by omega
    have hend : t ≤ nodeTime 1 := by simpa [cellSet, hi0] using ht.2
    linarith [node1_lt_phi]
  · by_contra hnot
    have hi : 28 ≤ i.1 := by omega
    have h28i : nodeTime 28 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [theta_lt_node28, ht.1]

private theorem phase3_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) (hlo : params.theta < t)
    (hhi : t ≤ Real.pi / 2 - params.theta) :
    27 ≤ i.1 ∧ i.1 ≤ 36 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 27 := by omega
    have hend : nodeTime (i.1 + 1) ≤ nodeTime 27 := nodeTime_mono hi
    linarith [node27_lt_theta, ht.2]
  · by_contra hnot
    have hi : 37 ≤ i.1 := by omega
    have h37i : nodeTime 37 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [eta_lt_node37, ht.1]

private theorem phase4_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i)
    (hlo : Real.pi / 2 - params.theta < t)
    (hhi : t ≤ Real.pi / 2 - params.phi) :
    36 ≤ i.1 ∧ i.1 ≤ 62 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 36 := by omega
    have hend : nodeTime (i.1 + 1) ≤ nodeTime 36 := nodeTime_mono hi
    linarith [node36_lt_eta, ht.2]
  · by_contra hnot
    have hi : 63 ≤ i.1 := by omega
    have h63i : nodeTime 63 ≤ nodeTime i.1 := nodeTime_mono hi
    linarith [tau_lt_node63, ht.1]

private theorem phase5_cell {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i)
    (hlo : Real.pi / 2 - params.phi < t) : 62 ≤ i.1 := by
  by_contra hnot
  have hi : i.1 + 1 ≤ 62 := by omega
  have hend : nodeTime (i.1 + 1) ≤ nodeTime 62 := nodeTime_mono hi
  linarith [node62_lt_tau, ht.2]

/-! ## Every literal path branch is contained in the selected cell hull -/

private theorem cellPath_contains_piece1 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : i.1 ≤ 1) :
    PointContains (cellPathInterval i) (Romik.path1 params t) := by
  have h := cellPiece1_contains htCell htPhys
  by_cases h0 : i.1 = 0
  · simpa [cellPathInterval, h0] using h
  · have h1 : i.1 = 1 := by omega
    simpa [cellPathInterval, h0, h1] using pointContains_hull_left h

private theorem cellPath_contains_piece2 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 1 ≤ i.1 ∧ i.1 ≤ 27) :
    PointContains (cellPathInterval i) (Romik.path2 params t) := by
  have h := cellPiece2_contains htCell htPhys
  by_cases h1 : i.1 = 1
  · have h0 : i.1 ≠ 0 := by omega
    simpa [cellPathInterval, h0, h1] using pointContains_hull_right h
  by_cases h27 : i.1 = 27
  · have h0 : i.1 ≠ 0 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27] using pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h26 : i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26] using h

private theorem cellPath_contains_piece3 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 27 ≤ i.1 ∧ i.1 ≤ 36) :
    PointContains (cellPathInterval i) (Romik.path3 params t) := by
  have h := cellPiece3_contains htCell htPhys
  by_cases h27 : i.1 = 27
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27] using pointContains_hull_right h
  by_cases h36 : i.1 = 36
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27n : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27n, h35, h36] using
      pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27n : i.1 ≠ 27 := by omega
    have h35 : i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27n, h35] using h

private theorem cellPath_contains_piece4 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 36 ≤ i.1 ∧ i.1 ≤ 62) :
    PointContains (cellPathInterval i) (Romik.path4 params t) := by
  have h := cellPiece4_contains htCell htPhys
  by_cases h36 : i.1 = 36
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36] using
      pointContains_hull_right h
  by_cases h62 : i.1 = 62
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36n : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36n, h61, h62] using
      pointContains_hull_left h
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36n : i.1 ≠ 36 := by omega
    have h61 : i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36n, h61] using h

private theorem cellPath_contains_piece5 {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval)
    (hi : 62 ≤ i.1) :
    PointContains (cellPathInterval i) (Romik.path5 params t) := by
  have h := cellPiece5_contains htCell htPhys
  by_cases h62 : i.1 = 62
  · have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36 : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36, h61, h62] using
      pointContains_hull_right h
  · have h63 : i.1 = 63 := by omega
    have h0 : i.1 ≠ 0 := by omega
    have h1 : i.1 ≠ 1 := by omega
    have h26 : ¬ i.1 ≤ 26 := by omega
    have h27 : i.1 ≠ 27 := by omega
    have h35 : ¬ i.1 ≤ 35 := by omega
    have h36 : i.1 ≠ 36 := by omega
    have h61 : ¬ i.1 ≤ 61 := by omega
    have h62n : i.1 ≠ 62 := by omega
    simpa [cellPathInterval, h0, h1, h26, h27, h35, h36, h61, h62n,
      h63] using h

/-- The interval selected for a cell contains the literal five-phase path at
every physical time in that cell. -/
theorem cellPath_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPathInterval i) (Romik.path params t) := by
  unfold Romik.path
  by_cases h1 : t ≤ params.phi
  · rw [ite_eq_left h1]
    exact cellPath_contains_piece1 htCell htPhys (phase1_cell htCell h1)
  · rw [ite_eq_right h1]
    have h1' : params.phi < t := lt_of_not_ge h1
    by_cases h2 : t ≤ params.theta
    · rw [ite_eq_left h2]
      exact cellPath_contains_piece2 htCell htPhys
        (phase2_cell htCell h1' h2)
    · rw [ite_eq_right h2]
      have h2' : params.theta < t := lt_of_not_ge h2
      by_cases h3 : t ≤ Real.pi / 2 - params.theta
      · rw [ite_eq_left h3]
        exact cellPath_contains_piece3 htCell htPhys
          (phase3_cell htCell h2' h3)
      · rw [ite_eq_right h3]
        have h3' : Real.pi / 2 - params.theta < t := lt_of_not_ge h3
        by_cases h4 : t ≤ Real.pi / 2 - params.phi
        · rw [ite_eq_left h4]
          exact cellPath_contains_piece4 htCell htPhys
            (phase4_cell htCell h3' h4)
        · rw [ite_eq_right h4]
          have h4' : Real.pi / 2 - params.phi < t := lt_of_not_ge h4
          exact cellPath_contains_piece5 htCell htPhys
            (phase5_cell htCell h4')

/-! ## Semantic soundness of the two product-cell expressions -/

theorem guCell_contains {i j : Cell} {s t : ℝ}
    (hsCell : s ∈ cellSet i) (htCell : t ∈ cellSet j)
    (hsPhys : s ∈ physicalInterval) (htPhys : t ∈ physicalInterval) :
    Contains (guCellInterval i j) (Gu s t) := by
  have hxs := cellPath_contains hsCell hsPhys
  have hxt := cellPath_contains htCell htPhys
  have htr := trig_contains hsCell hsPhys
  have hdx := RatInterval.contains_sub hxs.1 hxt.1
  have hdy := RatInterval.contains_sub hxs.2 hxt.2
  have hone := point_contains 1
  have h := RatInterval.contains_add
    (RatInterval.contains_add hone (RatInterval.contains_mul hdx htr.1))
    (RatInterval.contains_mul hdy htr.2)
  simpa [guCellInterval, Gu, dot, u, sub_eq_add_neg, ExactReplay.oneI, add_assoc] using h

theorem gvCell_contains {i j : Cell} {s t : ℝ}
    (hsCell : s ∈ cellSet i) (htCell : t ∈ cellSet j)
    (hsPhys : s ∈ physicalInterval) (htPhys : t ∈ physicalInterval) :
    Contains (gvCellInterval i j) (Gv s t) := by
  have hxs := cellPath_contains hsCell hsPhys
  have hxt := cellPath_contains htCell htPhys
  have htr := trig_contains hsCell hsPhys
  have hdx := RatInterval.contains_sub hxs.1 hxt.1
  have hdy := RatInterval.contains_sub hxs.2 hxt.2
  have hone := point_contains 1
  have h := RatInterval.contains_add
    (RatInterval.contains_add hone
      (RatInterval.contains_mul hdx (RatInterval.contains_neg htr.2)))
    (RatInterval.contains_mul hdy htr.1)
  simpa [gvCellInterval, Gv, dot, v, sub_eq_add_neg, ExactReplay.oneI, add_assoc] using h

end PartB
end GerverSofa

end

end

end

section

/-!
# Coverage by the 64 exact mesh cells
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

/-- Every physical angle belongs to one of the 64 closed cells between the
65 nodes `iπ/128`. -/
theorem exists_cell_cover {t : ℝ} (ht : t ∈ physicalInterval) :
    ∃ i : Cell, t ∈ cellSet i := by
  let P : Nat → Prop := fun n => t ≤ nodeTime (n + 1)
  have hnode64 : nodeTime 64 = Real.pi / 2 := by
    norm_num [nodeTime, nodeCoeff]; ring
  have h63 : P 63 := by
    change t ≤ nodeTime 64
    simpa [hnode64] using ht.2
  have hex : ∃ n : Nat, P n := ⟨63, h63⟩
  let n : Nat := Nat.find hex
  have hn63 : n ≤ 63 := Nat.find_min' hex h63
  have hn64 : n < 64 := by omega
  refine ⟨⟨n, hn64⟩, ?_⟩
  constructor
  · by_cases hn0 : n = 0
    · have hnode0 : nodeTime n = 0 := by
        rw [hn0]
        norm_num [nodeTime, nodeCoeff]
      simpa [cellSet, hnode0] using ht.1
    · have hpred : n - 1 < n := Nat.sub_one_lt hn0
      have hnot : ¬ P (n - 1) := Nat.find_min hex hpred
      have hlt : nodeTime ((n - 1) + 1) < t := lt_of_not_ge hnot
      have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)
      simpa [cellSet, hsucc] using hlt.le
  · exact Nat.find_spec hex

end PartB
end GerverSofa

end

end

end

section

/-!
# Exact continuum support margins

The 64×64 cell certificate is now transported to every pair of physical
angles.  This is the semantic conclusion needed from Part B.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartB

/-- First global support inequality on the complete square. -/
theorem Gu_gt_target :
    ∀ s ∈ physicalInterval, ∀ t ∈ physicalInterval, target < Gu s t := by
  intro s hs t ht
  rcases exists_cell_cover hs with ⟨i, hsi⟩
  rcases exists_cell_cover ht with ⟨j, htj⟩
  have hsem := guCell_contains hsi htj hs ht
  have hrat := (all_cell_lower i j).1
  have hcast : (targetQ : ℝ) < ((guCellInterval i j).lo : ℝ) := by
    exact_mod_cast hrat
  simpa [target] using lt_of_lt_of_le hcast hsem.1

/-- Second global support inequality on the complete square. -/
theorem Gv_gt_target :
    ∀ s ∈ physicalInterval, ∀ t ∈ physicalInterval, target < Gv s t := by
  intro s hs t ht
  rcases exists_cell_cover hs with ⟨i, hsi⟩
  rcases exists_cell_cover ht with ⟨j, htj⟩
  have hsem := gvCell_contains hsi htj hs ht
  have hrat := (all_cell_lower i j).2
  have hcast : (targetQ : ℝ) < ((gvCellInterval i j).lo : ℝ) := by
    exact_mod_cast hrat
  simpa [target] using lt_of_lt_of_le hcast hsem.1

/-- Manuscript form of the two `0.171` inequalities. -/
theorem global_half_plane_margins :
    (∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (171 : ℝ) / 1000 < Gu s t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (171 : ℝ) / 1000 < Gv s t) := by
  constructor
  · simpa [physicalInterval, target, targetQ] using Gu_gt_target
  · simpa [physicalInterval, target, targetQ] using Gv_gt_target

end PartB
end GerverSofa

end

end

end
