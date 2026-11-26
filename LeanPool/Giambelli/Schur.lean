/-
Copyright (c) 2026 Paul-Olivier Dehaye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Olivier Dehaye
-/
module

public import LeanPool.Giambelli.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
public import TauCeti.Combinatorics.Young.Partitions

/-!
# Giambelli's identity for Schur polynomials

This file specialises `Giambelli.giambelli_jt'` to Tau Ceti's Schur polynomials. The complete and
elementary symmetric polynomials `TauCeti.hsymmInt`, `TauCeti.esymmInt` form an `(h, e)` pair by
Tau Ceti's `h`–`e` convolution, and Tau Ceti's Jacobi–Trudi identity
`TauCeti.diagramSchurPoly_eq_det_hsymmInt` identifies Schur polynomials with Jacobi–Trudi
determinants, for the diagram and for each hook.

## Main definitions

* `Giambelli.hookDiagram a b`: the hook `(a + 1, 1^b)`, i.e. `(a | b)` in Frobenius notation.
* `Giambelli.frobeniusRank μ`: the side of the Durfee square of `μ`.
* `Giambelli.arm μ i = μᵢ − i − 1` and `Giambelli.leg μ j = μ′ⱼ − j − 1`: the Frobenius
  coordinates of `μ`.

## Main results

* `Giambelli.diagramSchurPoly_eq_det_hook`: **Giambelli's identity**
  `s_μ = det (s_{(αᵢ | βⱼ)})_{i, j < d}` in the alphabet `Fin N`.
* `Giambelli.schurPoly_eq_det_hook`: the same identity for partitions, in any finite alphabet.
* `Giambelli.diagramSchurPoly_hookDiagram`: the hook Schur polynomial
  `s_{(a | b)} = Σ_{r ≤ a} (−1)^r h_{a−r} e_{b+1+r}`.
-/

@[expose] public section

open Finset Matrix TauCeti

namespace Giambelli

variable {R : Type*} [CommRing R]

/-- The complete and elementary symmetric polynomials of integer degree form an `(h, e)` pair. -/
theorem hePair_hsymmInt_esymmInt (σ : Type*) [Fintype σ] [DecidableEq σ] :
    HEPair (hsymmInt σ R) (esymmInt σ R) where
  h_neg _ hk := hsymmInt_of_neg hk
  e_neg _ hk := esymmInt_of_neg hk
  e_zero := esymmInt_zero
  conv N := by
    rw [← sum_range_hsymm_mul_neg_one_pow_mul_esymm (σ := σ) R N]
    refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.mp hr
    rw [show (N : ℤ) - r = ((N - r : ℕ) : ℤ) by omega, sg_natCast, hsymmInt_natCast,
      esymmInt_natCast]
    ring

/-! ## Rows, columns and Frobenius coordinates of a Young diagram -/

/-- A row length is determined by the cells of its row. -/
theorem rowLen_eq_of_forall_mem_iff {μ : YoungDiagram} {i m : ℕ}
    (h : ∀ j, (i, j) ∈ μ ↔ j < m) : μ.rowLen i = m := by
  have key : ∀ j, j < μ.rowLen i ↔ j < m := fun j => YoungDiagram.mem_iff_lt_rowLen.symm.trans (h j)
  exact le_antisymm (not_lt.mp fun hm => lt_irrefl _ ((key m).mp hm))
    (not_lt.mp fun hm => lt_irrefl _ ((key _).mpr hm))

/-- A column length is determined by the cells of its column. -/
theorem colLen_eq_of_forall_mem_iff {μ : YoungDiagram} {j m : ℕ}
    (h : ∀ i, (i, j) ∈ μ ↔ i < m) : μ.colLen j = m := by
  have key : ∀ i, i < μ.colLen j ↔ i < m := fun i => YoungDiagram.mem_iff_lt_colLen.symm.trans (h i)
  exact le_antisymm (not_lt.mp fun hm => lt_irrefl _ ((key m).mp hm))
    (not_lt.mp fun hm => lt_irrefl _ ((key _).mpr hm))

/-- The rows of a Young diagram, as an antitone function on its `μ.colLen 0` nonempty rows. -/
def rows (μ : YoungDiagram) : Fin (μ.colLen 0) → ℕ := fun i => μ.rowLen i

theorem rows_antitone (μ : YoungDiagram) : Antitone (rows μ) := fun _ _ h =>
  μ.rowLen_anti _ _ h

/-- The side of the Durfee square of `μ`: the number of rows `i` with `i < μᵢ`. -/
def frobeniusRank (μ : YoungDiagram) : ℕ := durfee (rows μ)

/-- The Frobenius arms `αᵢ = μᵢ − i − 1`. -/
def arm (μ : YoungDiagram) (i : ℕ) : ℕ := μ.rowLen i - i - 1

/-- The Frobenius legs `βⱼ = μ′ⱼ − j − 1`. -/
def leg (μ : YoungDiagram) (j : ℕ) : ℕ := μ.colLen j - j - 1

theorem rowL_rows (μ : YoungDiagram) (i : ℕ) : rowL (rows μ) i = μ.rowLen i := by
  by_cases hi : i < μ.colLen 0
  · simp [rowL, hi, rows]
  · rw [rowL, dite_eq_right hi, eq_comm, ← Nat.le_zero, ← not_lt,
      ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    exact hi

theorem colL_rows (μ : YoungDiagram) (j : ℕ) : colL (rows μ) j = μ.colLen j := by
  have hle : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti 0 j (Nat.zero_le j)
  have hiff : ∀ i : Fin (μ.colLen 0), j < rows μ i ↔ (i : ℕ) < μ.colLen j := fun i =>
    YoungDiagram.mem_iff_lt_rowLen.symm.trans YoungDiagram.mem_iff_lt_colLen
  rw [colL, filter_congr fun i _ => hiff i, Fin.card_filter_val_lt, min_eq_right hle]

theorem frobA_rows (μ : YoungDiagram) (i : ℕ) : frobA (rows μ) i = arm μ i := by
  rw [frobA, rowL_rows, arm]

theorem frobB_rows (μ : YoungDiagram) (j : ℕ) : frobB (rows μ) j = leg μ j := by
  rw [frobB, colL_rows, leg]

/-! ## Hooks -/

/-- The hook `(a + 1, 1^b)`, written `(a | b)` in Frobenius notation: the cells `(0, j)` with
`j ≤ a` and `(i, 0)` with `i ≤ b`. -/
def hookDiagram (a b : ℕ) : YoungDiagram where
  cells := range 1 ×ˢ range (a + 1) ∪ range (b + 1) ×ˢ range 1
  isLowerSet := by
    intro p q hqp hp
    simp only [coe_union, coe_product, coe_range, Set.mem_union, Set.mem_prod, Set.mem_Iio] at hp ⊢
    have h1 := hqp.1
    have h2 := hqp.2
    omega

theorem mem_hookDiagram {a b : ℕ} {c : ℕ × ℕ} :
    c ∈ hookDiagram a b ↔ (c.1 = 0 ∧ c.2 ≤ a) ∨ (c.1 ≤ b ∧ c.2 = 0) := by
  rw [← YoungDiagram.mem_cells]
  simp only [hookDiagram, mem_union, mem_product, mem_range]
  omega

theorem colLen_zero_hookDiagram (a b : ℕ) : (hookDiagram a b).colLen 0 = b + 1 :=
  colLen_eq_of_forall_mem_iff fun i => by rw [mem_hookDiagram]; omega

theorem rowLen_hookDiagram (a b : ℕ) (i : Fin (b + 1)) :
    (hookDiagram a b).rowLen i = hookShape a b i :=
  rowLen_eq_of_forall_mem_iff fun j => by
    rw [mem_hookDiagram, hookShape]
    have := i.isLt
    split_ifs <;> omega

/-- The hook Schur polynomial is the Jacobi–Trudi determinant of the hook. -/
theorem diagramSchurPoly_hookDiagram_eq_jt (N a b : ℕ) :
    diagramSchurPoly N R (hookDiagram a b) = jt (hsymmInt (Fin N) R) (hookShape a b) := by
  rw [diagramSchurPoly_eq_det_hsymmInt N (hookDiagram a b) (colLen_zero_hookDiagram a b).le, jt]
  refine congrArg det (Matrix.ext fun i j => ?_)
  rw [of_apply, of_apply, rowLen_hookDiagram]

/-- **The hook Schur polynomial**: `s_{(a | b)} = Σ_{r ≤ a} (−1)^r h_{a−r} e_{b+1+r}`. -/
theorem diagramSchurPoly_hookDiagram (N a b : ℕ) :
    diagramSchurPoly N R (hookDiagram a b) =
      ∑ r ∈ range (a + 1), (-1) ^ r * hsymmInt (Fin N) R ((a : ℤ) - r) *
        esymmInt (Fin N) R ((b : ℤ) + 1 + r) := by
  rw [diagramSchurPoly_hookDiagram_eq_jt, jt_hook (hePair_hsymmInt_esymmInt _), hookV]
  simp only [sg_natCast]

/-! ## Giambelli's identity -/

/-- **Giambelli's identity.** For a Young diagram `μ` with Durfee square of side `d` and
Frobenius coordinates `μ = (α₀, …, α_{d−1} | β₀, …, β_{d−1})`, the Schur polynomial in the
alphabet `Fin N` is the determinant of the hook Schur polynomials,
`s_μ = det (s_{(αᵢ | βⱼ)})_{i, j < d}`. -/
theorem diagramSchurPoly_eq_det_hook (N : ℕ) (μ : YoungDiagram) :
    diagramSchurPoly N R μ = det (of fun i j : Fin (frobeniusRank μ) =>
      diagramSchurPoly N R (hookDiagram (arm μ i) (leg μ j))) := by
  rw [diagramSchurPoly_eq_det_hsymmInt N μ le_rfl]
  change jt (hsymmInt (Fin N) R) (rows μ) = _
  rw [giambelli_jt' (hePair_hsymmInt_esymmInt _) (rows_antitone μ)]
  refine congrArg det (Matrix.ext fun i j => ?_)
  change _ = diagramSchurPoly N R (hookDiagram (arm μ i) (leg μ j))
  rw [of_apply, diagramSchurPoly_hookDiagram_eq_jt, frobA_rows, frobB_rows]

/-- **Giambelli's identity for partitions.** In any finite alphabet `σ`, the Schur polynomial of
a partition `μ` is `det (s_{(αᵢ | βⱼ)})_{i, j < d}`, where `d`, `α` and `β` are the Durfee size and
Frobenius coordinates of the Young diagram of `μ`, and the hooks are taken as partitions. -/
theorem schurPoly_eq_det_hook (σ : Type*) [Fintype σ] {n : ℕ}
    (μ : n.Partition) :
    schurPoly σ R μ =
      det (of fun i j : Fin (frobeniusRank (YoungDiagram.ofPartition μ)) =>
        schurPoly σ R (shapePartition (hookDiagram (arm (YoungDiagram.ofPartition μ) i)
          (leg (YoungDiagram.ofPartition μ) j)))) := by
  rw [schurPoly_eq_rename, diagramSchurPoly_eq_det_hook, AlgHom.map_det]
  refine congrArg det (Matrix.ext fun i j => ?_)
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, schurPoly_eq_rename,
    ofPartition_shapePartition]

end Giambelli
