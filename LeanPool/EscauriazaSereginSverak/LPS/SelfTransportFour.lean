/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceTrilinear
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity

/-!
# Self-transport cancellation at the L⁴ exponent

The divergence-free transport pairing vanishes for an `H¹` slice in `L⁴`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The self-transport form of an `L⁴` slice vanishes. -/
theorem lps_slice_self_transport_four {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu : SerrinSlice u Du) (hu4 : MemLp u (ENNReal.ofReal 4) volume) :
    ∫ x : Vec3, ∑ k : Fin 3, u x k * ∑ j : Fin 3, u x j * Du x k j = 0 := by
  have hu2' : MemLp u (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.mem2
  have hDu2' : MemLp Du (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.grad2
  have hbf (j k : Fin 3) : MemLp (fun x => u x j * u x k) 2 volume := by
    rw [serrin_ofReal_two]
    exact serrin_prod_memLp (p := 4) (q := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu4.eval j) (hu4.eval k)
  have hbDf (j k : Fin 3) :
      MemLp (fun x => u x j * Du x k j) (ENNReal.ofReal (4 / 3)) volume :=
    serrin_prod_memLp (p := 4) (q := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu4.eval j) ((hDu2'.eval k).eval j)
  have _ : ENNReal.HolderTriple (ENNReal.ofReal (4 / 3)) (ENNReal.ofReal 4) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have h := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace hu.mem2 hu.grad2 hu.grad
    hu.mem2 hu.grad2 hu.grad (r := ENNReal.ofReal (4 / 3)) (s := ENNReal.ofReal 4)
    (serrin_one_le_ofReal (by norm_num)) (by simp) hbf hbDf (fun k => hu4.eval k)
  have heq : (fun x => ∑ k : Fin 3, ∑ j : Fin 3,
      u x j * (Du x k j * u x k + u x k * Du x k j)) =
      fun x => 2 * ∑ k : Fin 3, u x k * ∑ j : Fin 3, u x j * Du x k j := by
    funext x
    simp only [Fin.sum_univ_three]
    ring
  rw [heq, integral_const_mul] at h
  linarith only [h]

end ESS

end
