/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import LeanPool.CCDN.ForMathlib.Matrix

/-! Finite linear independence of formal power series survives arbitrary
field extension. A finite nonzero coefficient minor witnesses independence. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

private theorem powerSeries_linearIndependent_map
    {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Finite ι]
    (v : ι → PowerSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  classical
  let := Fintype.ofFinite ι
  let A : Matrix ℕ ι K := fun n i => PowerSeries.coeff n (v i)
  have hcols : LinearIndependent K A.col := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    apply (Fintype.linearIndependent_iff.mp hv) c _ i
    apply PowerSeries.ext
    intro n
    have h := congrFun hc n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
    change (∑ x, c x • PowerSeries.coeff n (v x)) = 0 at h
    simpa only [map_sum, PowerSeries.coeff_smul, map_zero] using h
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (linearIndependent_iff_card_eq_finrank_span.mp hcols).symm
  obtain ⟨a, c, _, _, hdet⟩ :=
    Matrix.exists_det_submatrix_ne_zero_of_le_rank A (Fintype.card ι) hrank.ge
  let B : Matrix ℕ ι L := A.map (algebraMap K L)
  have hdetB : (B.submatrix a c).det ≠ 0 := by
    have hm : (B.submatrix a c).det = algebraMap K L ((A.submatrix a c).det) := by
      rw [RingHom.map_det]
      rfl
    rw [hm]
    exact (map_ne_zero (algebraMap K L)).mpr hdet
  have hrankB : Fintype.card ι ≤ B.rank := B.le_rank_of_det_submatrix_ne_zero a c hdetB
  have hker : B.mulVecLin.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h := B.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi] at h
    change B.rank + Module.finrank L B.mulVecLin.ker = Fintype.card ι at h
    omega
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have hz : B.mulVecLin w = 0 := by
    ext n
    have h := congrArg (PowerSeries.coeff n) hw
    simpa only [B, A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map,
      Matrix.of_apply, Pi.zero_apply, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_map,
      map_zero, smul_eq_mul, mul_comm] using h
  have hmem : w ∈ B.mulVecLin.ker := hz
  rw [hker, Submodule.mem_bot] at hmem
  exact congrFun hmem i

/-- Independence survives coefficient extension even for an infinite family:
each relation involves only a finite subfamily. -/
theorem powerSeries_linearIndependent_map_of_linearIndependent
    {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (v : ι → PowerSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact powerSeries_linearIndependent_map (v ∘ (Subtype.val : s → ι))
    (hv.comp _ Subtype.val_injective)

end
end CCDN
