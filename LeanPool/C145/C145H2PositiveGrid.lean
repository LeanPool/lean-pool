/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145H2NumeratorData
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! C145 DRE8 Lemma D: exact arbitrary positive H2 sampling grids.
The literal full-N denominator numerator is restricted to z=s+t. Its two
coordinate degrees are derived from the erased products, without a supplied
unisolvence, degree, rank, or kernel certificate. Symmetry/ground-zero are not
needed for interpolation, so the result restricts to the source V0. -/

@[expose] public section

noncomputable section
namespace C145.H2
open MvPolynomial C145.ThreePlane
open scoped BigOperators
variable {n : ℕ}

/-- The actual two-variable numerator after imposing the response plane. -/
def planeNumerator (rates : Fin n → ℝ) (E : Tensor n) : P2 :=
  rhoZ (numerator rates E)

private def erasedProduct (rates : Fin n → ℝ) (i : Fin n) (p : P2) : P2 :=
  ∏ h ∈ Finset.univ.erase i, (p + C (rates h))

private theorem planeNumerator_formula (rates : Fin n → ℝ) (E : Tensor n) :
    planeNumerator rates E = ∑ i, ∑ j, ∑ k,
      C (E i j k) * erasedProduct rates i (X 0) *
        erasedProduct rates j (X 1) * erasedProduct rates k (X 0 + X 1) := by
  have hrho (F : P3) : rhoZ F =
      eval₂Hom C ![(X 0 : P2) + X 1, X 0, X 1] F := rfl
  unfold planeNumerator
  rw [hrho]
  simp [numerator, L, erasedProduct]

private theorem erasedProduct_degree_le (rates : Fin n → ℝ) (i : Fin n)
    (p : P2) (c : Fin 2) :
    degreeOf c (erasedProduct rates i p) ≤ (n - 1) * degreeOf c p := by
  classical
  calc
    _ ≤ ∑ h ∈ Finset.univ.erase i, degreeOf c (p + C (rates h)) :=
      degreeOf_prod_le c _ _
    _ ≤ ∑ _h ∈ Finset.univ.erase i, degreeOf c p := by
      apply Finset.sum_le_sum
      intro h hh
      exact (degreeOf_add_le c p _).trans (by simp)
    _ = (n - 1) * degreeOf c p := by simp [Finset.card_erase_of_mem]

private theorem plane_term_degree_le (rates : Fin n → ℝ) (E : Tensor n)
    (i j k : Fin n) (c : Fin 2) :
    degreeOf c (C (E i j k) * erasedProduct rates i (X 0) *
      erasedProduct rates j (X 1) * erasedProduct rates k (X 0 + X 1)) ≤
      2 * n - 2 := by
  have h0 := erasedProduct_degree_le rates i (X 0) c
  have h1 := erasedProduct_degree_le rates j (X 1) c
  have hs := erasedProduct_degree_le rates k (X 0 + X 1) c
  have hsum : degreeOf c ((X 0 : P2) + X 1) ≤ 1 :=
    (degreeOf_add_le c _ _).trans (by fin_cases c <;> simp [degreeOf_X])
  have hdeg := degreeOf_mul_le c
    (C (E i j k) * erasedProduct rates i (X 0) * erasedProduct rates j (X 1))
    (erasedProduct rates k (X 0 + X 1))
  have hdeg' := degreeOf_mul_le c
    (C (E i j k) * erasedProduct rates i (X 0)) (erasedProduct rates j (X 1))
  have hdeg'' := degreeOf_mul_le c (C (E i j k)) (erasedProduct rates i (X 0))
  have hlast : degreeOf c (erasedProduct rates k (X 0 + X 1)) ≤ n - 1 :=
    hs.trans (by simpa using Nat.mul_le_mul_left (n - 1) hsum)
  fin_cases c <;> simp [degreeOf_X] at h0 h1 hdeg hdeg' hdeg'' hlast ⊢ <;> omega

/-- Literal denominator clearing has bidegree at most 2N-2, for every full
N-index tensor. This bound is proved, never supplied by the caller. -/
theorem planeNumerator_degree_le (rates : Fin n → ℝ) (E : Tensor n) (c : Fin 2) :
    degreeOf c (planeNumerator rates E) ≤ 2 * n - 2 := by
  classical
  rw [planeNumerator_formula]
  apply (degreeOf_sum_le c _ _).trans
  apply Finset.sup_le; intro i hi
  apply (degreeOf_sum_le c _ _).trans
  apply Finset.sup_le; intro j hj
  apply (degreeOf_sum_le c _ _).trans
  exact Finset.sup_le (fun k hk => plane_term_degree_le rates E i j k c)

private def gridSlice (e : Equiv.Perm (Fin 2)) (F : P2) (v : ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval ![v]) (finSuccEquiv ℝ 1 (rename e F))

private theorem eval_gridSlice (e : Equiv.Perm (Fin 2)) (F : P2) (v u : ℝ) :
    (gridSlice e F v).eval u = MvPolynomial.eval ((![u,v] : Fin 2 → ℝ) ∘ e) F := by
  unfold gridSlice
  rw [← MvPolynomial.eval_eq_eval_mv_eval', MvPolynomial.eval_rename]
  rfl

private theorem gridSlice_natDegree_le (e : Equiv.Perm (Fin 2)) (F : P2) (v : ℝ) :
    (gridSlice e F v).natDegree ≤ degreeOf (e.symm 0) F := by
  have he : degreeOf (0 : Fin 2) (rename e F) = degreeOf (e.symm 0) F := by
    simpa only [e.apply_symm_apply] using
      (degreeOf_rename_of_injective (p := F) e.injective (e.symm 0))
  calc
    _ ≤ (finSuccEquiv ℝ 1 (rename e F)).natDegree := Polynomial.natDegree_map_le
    _ = degreeOf (0 : Fin 2) (rename e F) := natDegree_finSuccEquiv _
    _ = degreeOf (e.symm 0) F := he

private theorem gridLine_zero {m : ℕ} (nodes : Fin m → ℝ)
    (hnodes : Function.Injective nodes) (F : P2)
    (hdegree : ∀ c : Fin 2, degreeOf c F < m)
    (e : Equiv.Perm (Fin 2)) (v : ℝ)
    (hnode : ∀ i, MvPolynomial.eval ((![nodes i,v] : Fin 2 → ℝ) ∘ e) F = 0)
    (u : ℝ) : MvPolynomial.eval ((![u,v] : Fin 2 → ℝ) ∘ e) F = 0 := by
  classical
  have hp : gridSlice e F v = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.univ : Finset (Fin m)) hnodes.injOn
    · have hn : (gridSlice e F v).natDegree < m :=
        (gridSlice_natDegree_le e F v).trans_lt (hdegree (e.symm 0))
      have hc : ((gridSlice e F v).natDegree : WithBot ℕ) < (m : WithBot ℕ) :=
        WithBot.coe_lt_coe.mpr hn
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Polynomial.degree_le_natDegree (p := gridSlice e F v)).trans_lt hc
    · intro i hi
      rw [eval_gridSlice]
      exact hnode i
  rw [← eval_gridSlice, hp, Polynomial.eval_zero]

/-- Successive univariate finite-root interpolation on any Cartesian grid.
The two axes may overlap, and diagonal samples are retained. -/
theorem bidegree_grid_eq_zero {m : ℕ} (sNodes tNodes : Fin m → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (F : P2) (hdegree : ∀ c : Fin 2, degreeOf c F < m)
    (hgrid : ∀ i j, MvPolynomial.eval ![sNodes i, tNodes j] F = 0) : F = 0 := by
  have hs (s : ℝ) (j : Fin m) : MvPolynomial.eval ![s,tNodes j] F = 0 := by
    simpa using gridLine_zero sNodes hsNodes F hdegree (Equiv.refl (Fin 2))
      (tNodes j) (fun i => by simpa using hgrid i j) s
  have hst (s t : ℝ) : MvPolynomial.eval ![s,t] F = 0 := by
    have hv (u : ℝ) : (fun x => (![u,s] : Fin 2 → ℝ) (Equiv.swap 0 1 x)) = ![s,u] := by
      funext r; fin_cases r <;> simp
    have hnode (j : Fin m) :
        MvPolynomial.eval ((![tNodes j,s] : Fin 2 → ℝ) ∘ Equiv.swap 0 1) F = 0 := by
      rw [show ((![tNodes j,s] : Fin 2 → ℝ) ∘ Equiv.swap 0 1) = ![s,tNodes j] from hv _]
      exact hs s j
    have h := gridLine_zero tNodes htNodes F hdegree (Equiv.swap 0 1) s hnode t
    simpa only [show ((![t,s] : Fin 2 → ℝ) ∘ Equiv.swap 0 1) = ![s,t] from hv _] using h
  apply MvPolynomial.funext
  intro w
  have hw : w = ![w 0,w 1] := by funext c; fin_cases c <;> rfl
  rw [hw, map_zero]
  exact hst _ _

/-- Exact source grid count, with nonvanishing positive denominators derived
from the rates and positivity. No symmetry, rate injection, or nonzero overlap
assumption is needed for this interpolation step. -/
theorem positive_grid_iff_nullPositive (hn : 0 < n) (rates : Fin n → ℝ)
    (hRates : ∀ i, 0 < rates i) (E : Tensor n)
    (sNodes tNodes : Fin (2 * n - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i) :
    (∀ i j, H rates E (sNodes i) (tNodes j) = 0) ↔ NullPositive rates E := by
  constructor
  · intro hg
    apply (positive_data_iff_plane rates hRates E).mpr
    change planeNumerator rates E = 0
    apply bidegree_grid_eq_zero sNodes tNodes hsNodes htNodes
    · intro c
      have hd := planeNumerator_degree_le rates E c
      omega
    · intro i j
      rw [planeNumerator, eval_rhoZ, clear_response_denominators rates E _ _
        (positive_regular rates hRates _ _ (hsPos i) (htPos j)), hg i j, mul_zero]
  · intro h i j
    exact h _ _ (hsPos i) (htPos j)

end C145.H2

end
