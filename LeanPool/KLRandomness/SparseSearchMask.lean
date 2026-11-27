/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseSearchRank

/-!
# Computable rank tests after restricting the columns

A finite Boolean mask selects columns of the coded matrix. Zeroing its other
columns is a concrete computation, and the certificate-free rank checker on
this new code agrees with surjectivity of the actual restricted column map.
-/

@[expose] public section

namespace Klr.SparseSearch

open AffineCode FiniteMeasure RandomMatrix

/-- Evaluate a function at the first `n` natural numbers, retaining its
external computation parameter. -/
def tabulate {β : Type*} (f : ℕ → β) (n : ℕ) : List β := (List.range n).map f

theorem getD_tabulate {β : Type*} (f : ℕ → β) {n i : ℕ} (hi : i < n) (b : β) :
    (tabulate f n).getD i b = f i := by
  simp [tabulate, List.getD_eq_getElem?_getD, hi]

theorem computable_tabulate {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℕ → β} (hf : Computable₂ f) :
    Computable (fun p : α × ℕ => tabulate (f p.1) p.2) := by
  have hs : Computable₂ (fun (a : α × ℕ) (p : ℕ × List β) => p.2 ++ [f a.1 p.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.snd (Computable.const []) hs).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [tabulate, Nat.rec_add_one, List.range_succ, List.map_append,
      List.map_cons, List.map_nil] using congrArg (fun s => s ++ [f a.1 n]) ih

/-- Zero every column whose mask bit is false. The result is a rectangular
Boolean matrix, irrespective of missing entries in the original code. -/
def maskCode (c : Data) (d : List Bool) : Data :=
  (c.1, (tabulate (fun i => tabulate
    (fun j => entry (rows c) i j && d.getD j false) (width c)) (rank c),
      (syndrome c, certificate c)))

@[simp] theorem width_maskCode (c : Data) (d : List Bool) : width (maskCode c d) = width c := rfl
@[simp] theorem rank_maskCode (c : Data) (d : List Bool) : rank (maskCode c d) = rank c := rfl

theorem computable_maskCode : Computable₂ maskCode := by
  have hc : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hd : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hj : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.2) := Computable.snd
  have he := computable_entry.comp ((computable_rows.comp hc).pair (hi.pair hj))
  have hb := (Primrec.list_getD false).to_comp.comp hd hj
  have hrow := (computable_tabulate
    (f := fun p : (Data × List Bool) × ℕ => fun j =>
      entry (rows p.1.1) p.2 j && p.1.2.getD j false)
    (Primrec.and.to_comp.comp he hb)).comp
      (Computable.id.pair (computable_width.comp (Computable.fst.comp Computable.fst)))
  have hrows := (computable_tabulate
    (f := fun p : Data × List Bool => fun i => tabulate
      (fun j => entry (rows p.1) i j && p.2.getD j false) (width p.1)) hrow).comp
      (Computable.id.pair (computable_rank.comp Computable.fst))
  have hresult := (Computable.fst.comp Computable.fst).pair
    (hrows.pair ((computable_syndrome.comp Computable.fst).pair
      (computable_certificate.comp Computable.fst)))
  exact hresult.of_eq fun _ => rfl

theorem matrix_maskCode (c : Data) (d : List Bool) :
    matrix (maskCode c d) = fun i j => if d.getD j.val false then matrix c i j else 0 := by
  ext i j
  change Fin (rank c) at i
  change Fin (width c) at j
  change boolEquivF2 ((tabulate (fun i => tabulate
    (fun j => entry (rows c) i j && d.getD j false) (width c)) (rank c)).getD i.val []
      |>.getD j.val false) = _
  rw [getD_tabulate _ i.isLt, getD_tabulate _ j.isLt]
  cases d.getD j.val false <;> simp [matrix]

/-- The actual set of selected column indices. -/
def selectedColumns (c : Data) (d : List Bool) : Finset (Fin (width c)) :=
  Finset.univ.filter (fun j => d.getD j.val false = true)

@[simp] theorem mem_selectedColumns (c : Data) (d : List Bool) (j : Fin (width c)) :
    j ∈ selectedColumns c d ↔ d.getD j.val false = true := by simp [selectedColumns]

theorem mulVecLin_eq_columnMap {m r : ℕ}
    (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    A.mulVecLin = columnMap (fun j i => A i j) := by
  ext x i
  simp [columnMap, Matrix.mulVec, dotProduct, mul_comm]

/-- Zeroing columns and dropping them have the same surjectivity behavior. -/
theorem zero_columns_surjective_iff {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (B : ι → V) (T : Finset ι) :
    Function.Surjective (columnMap (fun i => if i ∈ T then B i else 0) (K := K)) ↔
      Function.Surjective (restrictedMap B T (K := K)) := by
  rw [← not_iff_not, not_surjective_iff_exists_annihilator,
    restricted_not_surjective_iff]
  constructor
  · rintro ⟨φ, hφ, hB⟩
    refine ⟨φ, hφ, funext fun t => ?_⟩
    simpa [t.property] using hB t.val
  · rintro ⟨φ, hφ, hB⟩
    refine ⟨φ, hφ, fun i => ?_⟩
    by_cases hi : i ∈ T
    · simpa [hi] using congrFun hB ⟨i, hi⟩
    · simp [hi]

/-- A computable check of full row rank on only the selected columns. -/
def maskedFullRank (c : Data) (d : List Bool) : Bool := fullRank (maskCode c d)

theorem computable_maskedFullRank : Computable₂ maskedFullRank :=
  (computable_fullRank.comp computable_maskCode).to₂

/-- The executable masked checker is precisely the restriction-rank predicate
needed in sparse-list verification. -/
theorem maskedFullRank_eq_true (c : Data) (d : List Bool) :
    maskedFullRank c d = true ↔ Function.Surjective
      (restrictedMap (fun j i => matrix c i j) (selectedColumns c d) (K := ZMod 2)) := by
  rw [maskedFullRank, fullRank_eq_true, mulVecLin_eq_columnMap]
  have he : (fun j i => matrix (maskCode c d) i j) =
      fun j => if j ∈ selectedColumns c d then (fun i => matrix c i j) else 0 := by
    funext j i
    change Fin (width c) at j
    change Fin (rank c) at i
    rw [matrix_maskCode]
    simp only [mem_selectedColumns]
    split_ifs <;> rfl
  rw [he]
  exact zero_columns_surjective_iff _ _

end Klr.SparseSearch
