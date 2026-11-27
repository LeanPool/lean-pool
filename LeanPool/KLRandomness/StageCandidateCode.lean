/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageCandidate
public import LeanPool.KLRandomness.StageCodeSearch

/-!
# Computable affine output for a candidate on an actual pool

The candidate matrix is indexed by pool positions, whereas the output code
is indexed by input coordinates. Its finite truth table is computed by
pulling an input word back along the finite pool list. Certified code search
then performs the coordinate change and supplies a right inverse, with no
matrix or certificate added to the description as advice.
-/

@[expose] public section

namespace Klr.StageCandidateCode

open AffineCode SparseSearch SparseListSearch FiniteMeasure RandomMatrix
open StageCandidate
open scoped BigOperators

/-- Replace the candidate's syndrome while leaving its matrix unchanged. -/
def withSyndrome (c : Data) (y : List Bool) : Data :=
  (c.1, (rows c, (y, certificate c)))

@[simp] theorem width_withSyndrome (c : Data) (y : List Bool) :
    width (withSyndrome c y) = width c := rfl

@[simp] theorem rank_withSyndrome (c : Data) (y : List Bool) :
    rank (withSyndrome c y) = rank c := rfl

@[simp] theorem matrix_withSyndrome (c : Data) (y : List Bool) :
    matrix (withSyndrome c y) = matrix c := rfl

theorem computable_withSyndrome : Computable₂ withSyndrome := by
  exact ((Computable.fst.comp Computable.fst).pair
    ((computable_rows.comp Computable.fst).pair
      (Computable.snd.pair (computable_certificate.comp Computable.fst)))).to₂

/-- Read a finite input word at the actual pool positions. -/
def poolWord (G : List ℕ) (s : List Bool) : List Bool :=
  G.map (fun k => s.getD k false)

theorem computable_poolWord : Computable₂ poolWord := by
  exact (Primrec.list_map Primrec.fst
    ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to_comp

theorem getD_poolWord (G : List ℕ) (s : List Bool) (j : Fin G.length) :
    (poolWord G s).getD j.val false = s.getD (G.get j) false := by
  simp [poolWord, List.getD_eq_getElem?_getD, j.isLt]

/-- A computable coordinate bound for the entire concrete pool. -/
def bound (G : List ℕ) : ℕ := G.sum + 1

theorem computable_bound : Computable bound :=
  Primrec.succ.to_comp.comp (Primrec.list_sum Primrec.id).to_comp

theorem get_lt_bound (G : List ℕ) (j : Fin G.length) : G.get j < bound G :=
  Nat.lt_succ_of_le (List.le_sum_of_mem (List.get_mem G j))

/-- The truth table for the new affine constraint at actual input positions. -/
def table (G : List ℕ) (c : Data) (y s : List Bool) : Bool :=
  accepts (withSyndrome c y) (poolWord G s)

theorem computable_table : Computable
    (fun p : ((List ℕ × Data) × List Bool) × List Bool => table p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hG : Computable (fun p : ((List ℕ × Data) × List Bool) × List Bool => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hc : Computable (fun p : ((List ℕ × Data) × List Bool) × List Bool => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hy : Computable (fun p : ((List ℕ × Data) × List Bool) × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  exact computable_accepts.comp (computable_withSyndrome.comp hc hy)
    (computable_poolWord.comp hG Computable.snd)

theorem restrictedMap_eq_columnMap_of_zero {M r : ℕ}
    (C : Fin M → Fin r → ZMod 2) (T : Finset (Fin M))
    (hz : ∀ j ∉ T, C j = 0) (x : Fin M → ZMod 2) :
    restrictedMap C T (fun j => x j.val) = columnMap C x := by
  classical
  change (∑ j : T, x j.val • C j.val) = ∑ j, x j • C j
  rw [Finset.sum_coe_sort T (fun j => x j • C j)]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by rw [hz j hj, smul_zero]

/-- The embedded block computes the original candidate equations on pool bits. -/
theorem block_matrix_coordinates (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : Fin r → ZMod 2) (X : Cantor) :
    (block G.get hG.injective_get a ha y).matrix
      (coordinateValues (fun i => i.val) X) =
        columnMap (columns a G.length r) (fun j => boolEquivF2 (X (G.get j))) := by
  change restrictedMap (columns a G.length r) (SparseListWeights.support G.length a)
    (fun j => boolEquivF2 (X (G.get j.val))) = _
  exact restrictedMap_eq_columnMap_of_zero _ _ (fun j hj => columns_zero_off_support ha hj)
    (fun j => boolEquivF2 (X (G.get j)))

/-- The executable truth table describes the actual embedded affine block.
The input depth may be enlarged to cover old equations and adaptive queries. -/
theorem table_inputPrefix (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : List Bool) (n : ℕ) (hn : bound G ≤ n) (X : Cantor) :
    table G a.2 y (ScanRule.inputPrefix X n) = true ↔
      X ∈ (block G.get hG.injective_get a ha (wordVector r y)).event := by
  have hw := ha.2.2.1
  have hr := ha.2.2.2.1
  rw [table, accepts_eq_true]
  have hlen : width (withSyndrome a.2 y) ≤ (poolWord G (ScanRule.inputPrefix X n)).length := by
    simp [poolWord, hw]
  rw [and_iff_right hlen]
  have hv (i : Fin r) : boolEquivF2 (AffineCode.rowValue (withSyndrome a.2 y)
      (poolWord G (ScanRule.inputPrefix X n)) i.val) =
      columnMap (columns a G.length r) (fun j => boolEquivF2 (X (G.get j))) i := by
    change boolEquivF2 (parity (fun j => entry (rows a.2) i.val j &&
      (poolWord G (ScanRule.inputPrefix X n)).getD j false) (width a.2)) = _
    rw [hw, value_parity]
    simp only [columnMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, columns]
    apply Finset.sum_congr rfl
    intro j _
    rw [value_and, getD_poolWord G _ j,
      ScanRule.getD_inputPrefix X ((get_lt_bound G j).trans_le hn)]
    exact mul_comm _ _
  change (∀ i < rank a.2, AffineCode.rowValue (withSyndrome a.2 y)
    (poolWord G (ScanRule.inputPrefix X n)) i = y.getD i false) ↔
    (block G.get hG.injective_get a ha (wordVector r y)).matrix
      (coordinateValues (fun i => i.val) X) = wordVector r y
  rw [hr, block_matrix_coordinates G hG a ha]
  constructor
  · intro h
    funext i
    rw [← hv i, h i.val i.isLt]
    rfl
  · intro h i hi
    apply boolEquivF2.injective
    exact (hv ⟨i, hi⟩).trans (congrFun h ⟨i, hi⟩)

/-- Actual reconstruction: compare finite truth tables and search for a
certified affine output code. -/
def reconstruct (p : (List ℕ × Data) × List Bool) : Part Data :=
  StageCodeSearch.reconstruct (rank p.1.2) (bound p.1.1) (table p.1.1 p.1.2 p.2)

theorem partrec_reconstruct : Partrec reconstruct :=
  StageCodeSearch.partrec_reconstruct
    (computable_rank.comp (Computable.snd.comp Computable.fst))
    (computable_bound.comp (Computable.fst.comp Computable.fst)) computable_table.to₂

/-- Every checked candidate on a nodup actual pool is successfully recovered
with the same rank and exact event, for every supplied syndrome. -/
theorem exists_reconstructed_code (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a) (y : List Bool) :
    ∃ c ∈ reconstruct ((G, a.2), y),
      valid c = true ∧ rank c = r ∧
        event c = (block G.get hG.injective_get a ha (wordVector r y)).event := by
  have hbound : ∀ k ∈ (block G.get hG.injective_get a ha (wordVector r y)).support,
      k < bound G := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact get_lt_bound G j
  have h := StageCodeSearch.exists_reconstructed_code
    (block G.get hG.injective_get a ha (wordVector r y)) (bound G) hbound (table G a.2 y)
    (table_inputPrefix G hG a ha y (bound G) le_rfl)
  simpa only [reconstruct, ha.2.2.2.1, block_rank] using h

end Klr.StageCandidateCode
