/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAtlasPartition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAtlasOverlap

/-!
# Matrix Schur atlas partition

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `measurableSet_matrixSchurAtlasAngularPiece`,
`matrixSchurAtlas_partition_pairwise_disjoint`, `matrixSchurAtlas_partition_cover`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The lower coordinates `x` for which `E⋆ C Q(x)` lies in `matrixUnitaryFlagSaturation n V`,
with `Q(x)` the exponential unitary frame: the overlap of the angular charts at `C` and `E`. -/
def matrixSchurAtlasAngularOverlap {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ) : Set (SchurLowerIndex n → ℂ) :=
  {x | ((star E * C * matrixSchurExponentialUnitaryFrame n x : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}

theorem matrixSchurAtlasAngularOverlap_isOpen {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) :
    IsOpen (matrixSchurAtlasAngularOverlap V C E) :=
  hopen.preimage (continuous_const.mul (matrixSchurExponentialUnitaryFrame_continuous n))

/-- The `k`-th angular piece: `V` with the overlaps with the charts at `C j`, `j < k`,
removed. -/
def matrixSchurAtlasAngularPiece {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ) (k : ℕ) : Set (SchurLowerIndex n → ℂ) :=
  V \ ⋃ j : Fin k, matrixSchurAtlasAngularOverlap V (C k) (C j.val)

theorem measurableSet_matrixSchurAtlasAngularPiece {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (hV : IsOpen V)
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) (k : ℕ) :
    MeasurableSet (matrixSchurAtlasAngularPiece V C k) :=
  hV.measurableSet.diff (MeasurableSet.iUnion fun j =>
    (matrixSchurAtlasAngularOverlap_isOpen V (C k) (C j.val) hopen).measurableSet)

theorem matrixSchurAtlas_partition_no_overlap {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (k l : ℕ) (hkl : k < l) (p q : SchurCoordinates n)
    (hp : p ∈ matrixSchurAtlasAngularPiece V C k ×ˢ matrixSchurSortedUpperDomain n)
    (hq : q ∈ matrixSchurAtlasAngularPiece V C l ×ˢ matrixSchurSortedUpperDomain n) :
    matrixSchurAtlasChart (C k) p ≠ matrixSchurAtlasChart (C l) q := by
  intro he
  have hflag := matrixSchurAtlas_overlap_flag V (C l) (C k) q p
    ⟨hq.1.1, hq.2⟩ ⟨hp.1.1, hp.2⟩ he.symm
  have hmem : q.1 ∈ matrixSchurAtlasAngularOverlap V (C l) (C k) := by
    change (((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      (C l : Matrix (Fin n) (Fin n) ℂ)) * matrixSchurExponentialFrame n q.1) ∈
        matrixUnitaryFlagSaturation n V
    rw [Matrix.mul_assoc]
    exact hflag
  exact hq.1.2 (Set.mem_iUnion.mpr ⟨⟨k, hkl⟩, hmem⟩)

theorem matrixSchurAtlas_partition_pairwise_disjoint {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ) :
    Pairwise (fun k l => Disjoint
      (matrixSchurAtlasChart (C k) '' (matrixSchurAtlasAngularPiece V C k ×ˢ
          matrixSchurSortedUpperDomain n))
      (matrixSchurAtlasChart (C l) '' (matrixSchurAtlasAngularPiece V C l ×ˢ
          matrixSchurSortedUpperDomain n))) := by
  intro k l hne
  apply Set.disjoint_left.mpr
  intro G hGk hGl
  obtain ⟨p, hp, hpk⟩ := hGk
  obtain ⟨q, hq, hql⟩ := hGl
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact matrixSchurAtlas_partition_no_overlap V C k l hkl p q hp hq (hpk.trans hql.symm)
  · exact matrixSchurAtlas_partition_no_overlap V C l k hlk q p hq hp (hql.trans hpk.symm)

/-- Choosing the first flag chart yields a genuine disjoint product-domain atlas
covering every simple matrix. -/
theorem matrixSchurAtlas_partition_cover {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
      ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
        matrixUnitaryFlagSaturation n V)
    (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) :
    ∃ k, ∃ p ∈ matrixSchurAtlasAngularPiece V C k ×ˢ matrixSchurSortedUpperDomain n,
      G = matrixSchurAtlasChart (C k) p := by
  classical
  let P : ℕ → Prop := fun k => ∃ p ∈ V ×ˢ matrixSchurSortedUpperDomain n,
    G = matrixSchurAtlasChart (C k) p
  have hP : ∃ k, P k := matrixSchurAtlas_cover_of_unitary_cover n V C hC G hs
  obtain ⟨p, hp, he⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, p, ⟨⟨hp.1, ?_⟩, hp.2⟩, he⟩
  intro hUnion
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hUnion
  have hflag : ((C j.val : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((C (Nat.find hP) : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1)) ∈
        matrixUnitaryFlagSaturation n V := by
    change p.1 ∈ matrixSchurAtlasAngularOverlap V (C (Nat.find hP)) (C j.val) at hj
    change (((C j.val : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      (C (Nat.find hP) : Matrix (Fin n) (Fin n) ℂ)) * matrixSchurExponentialFrame n p.1) ∈
        matrixUnitaryFlagSaturation n V at hj
    rw [Matrix.mul_assoc] at hj
    exact hj
  obtain ⟨q, hq, heq⟩ := matrixSchurAtlas_flag_overlap V (C (Nat.find hP)) (C j.val) p hp.2 hflag
  have hPj : P j.val := ⟨q, hq, he.trans heq⟩
  have hmin := Nat.find_min' hP hPj
  exact (Nat.not_le_of_lt j.isLt) hmin

end
end GinibrePoincare
