/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMollifierTest

/-!
# Compactness Mollifier Lp

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Mollifying a coordinate of a spatial `L²` function is the Hilbert
pairing with the corresponding reflected mollifier test. -/
theorem mollify_lp_component_eq_inner
    (V : Lp L2Vec3 2 (volume : Measure Vec3))
    (m : ℕ) (x : Vec3) (i : Fin 3) :
    CKN.mollify (fun y : Vec3 => V y i)
      (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x =
    inner ℝ V ((memLp_reflected_mollifier_coordinate m x i).toLp
      (fun y : Vec3 =>
        (WithLp.toLp 2 (Pi.single i
          (CKN.mollifier (d := 3) (CKN.sliceRadius m)
            (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))) := by
  let f : Vec3 → Vec3 := fun y j => V y j
  have hf : MemLp (fun y => (1 : ℝ) • WithLp.toLp 2 (f y)) 2
      (volume : Measure Vec3) := by
    simpa only [one_smul, f, WithLp.toLp_ofLp] using Lp.memLp V
  have h := mollify_component_eq_cutoff_inner f (fun _ => 1) hf m x i
    (fun _ _ => rfl)
  simpa only [f, one_smul, WithLp.toLp_ofLp,
    Lp.toLp_coeFn V (Lp.memLp V)] using h

end CKN.Leray
