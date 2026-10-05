/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.Basic

/-!
# Tensor decomposition of the hypergraph-product (HGP) parity-check matrices

The Tillich–Zémor hypergraph product glues two classical codes $C_1, C_2$ (parity-check
matrices $H_1 : r_1 \times n_1$ and $H_2 : r_2 \times n_2$) into a quantum code on
$n_1 n_2 + r_1 r_2$ qubits, whose two families of checks take block tensor form:

$$H_X = [\,H_1 \otimes I_{n_2} \;\middle|\; I_{r_1} \otimes H_2^\top\,],\qquad
H_Z = [\,I_{n_1} \otimes H_2 \;\middle|\; H_1^\top \otimes I_{r_2}\,].$$

This module gives the **entrywise definition** of the construction (`hgpHX` / `hgpHZ`) and
the first structural theorem:

* `hgp_orthogonal`: $H_X H_Z^\top = 0$. The CSS compatibility condition holds for
  **arbitrary** inputs $H_1, H_2$, and the proof is purely algebraic (the two blocks each
  contribute $H_1 \otimes H_2^\top$, which cancel over GF(2)); it enumerates nothing.

The distance bounds are proved in `GF2/HGPCleaning` and `GF2/HGPCleaningDual`;
`GF2/HGPKunneth` supplies the rank and dimension formula. Concrete code instances from
upstream are outside this import.

## Index conventions

* Rows and columns are **product and sum types** (not flattened to `Fin`), so no relabelling
  is needed: the rows of `hgpHX` are `Fin r₁ × Fin n₂` and the rows of `hgpHZ` are
  `Fin n₁ × Fin r₂`, and both share the column space
  `(Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)`.
* Flattening to `Fin` (for the instance anchor) is left to `Matrix.reindex`.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## Construction -/

/--
**The X-type checks of the HGP** $H_X = [H_1 \otimes I_{n_2} \mid I_{r_1} \otimes H_2^\top]$.

A row is `(i, j) : r₁ × n₂`. On the left half of the columns, `(a, b) : n₁ × n₂`, the entry
is $H_1\, i\,a \cdot [j = b]$; on the right half, `(s, t) : r₁ × r₂`, it is
$[i = s] \cdot H_2\, t\, j$ (the $(j, t)$ entry of $H_2^\top$).
-/
def hgpHX (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin r₁ × Fin n₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0))
    (fun st => (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) c

/--
**The Z-type checks of the HGP** $H_Z = [I_{n_1} \otimes H_2 \mid H_1^\top \otimes I_{r_2}]$.

A row is `(a, d) : n₁ × r₂`. On the left half of the columns the entry is
$[a = a'] \cdot H_2\, d\, b$; on the right half it is $H_1\, s\, a \cdot [d = t]$.
-/
def hgpHZ (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin n₁ × Fin r₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2)
    (fun st => H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0)) c

/-- The four blocks, described entrywise (`rfl` level). -/
theorem hgpHX_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (ab : Fin n₁ × Fin n₂) :
    hgpHX H₁ H₂ x (Sum.inl ab) = H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0) := rfl

theorem hgpHX_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (st : Fin r₁ × Fin r₂) :
    hgpHX H₁ H₂ x (Sum.inr st) = (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2 := rfl

theorem hgpHZ_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (ab : Fin n₁ × Fin n₂) :
    hgpHZ H₁ H₂ x (Sum.inl ab) = (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2 := rfl

theorem hgpHZ_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (st : Fin r₁ × Fin r₂) :
    hgpHZ H₁ H₂ x (Sum.inr st) = H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0) := rfl

/-! ## The structural theorem: CSS compatibility -/

/--
**CSS compatibility of the HGP (structural theorem)**: $H_X H_Z^\top = 0$ for arbitrary
$H_1, H_2$.

The two blocks contribute $(H_1 \otimes I)(I \otimes H_2)^\top = H_1 \otimes H_2^\top$ and
$(I \otimes H_2^\top)(H_1^\top \otimes I)^\top = H_1 \otimes H_2^\top$ respectively, that is,
the same matrix added to itself, which is zero over GF(2). The two `Finset.sum_eq_single`
applications in the proof are this tensor identity at the entrywise level: each product
$H_1\, i\, a \cdot H_2\, d\, j$ is contributed exactly once, by $(a, j)$ on the left half and
by $(i, d)$ on the right half.
-/
theorem hgp_orthogonal (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    hgpHX H₁ H₂ * (hgpHZ H₁ H₂).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    hgpHX_inl, hgpHX_inr, hgpHZ_inl, hgpHZ_inr]
  have keyL : (∑ p : Fin n₁ × Fin n₂,
        (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) * ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2))
      = H₁ x.1 y.1 * H₂ y.2 x.2 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n₁ × Fin n₂)))
      (f := fun p => (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) *
        ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2)) (y.1, x.2) ?_ ?_).trans ?_
    · intro p _ hp
      by_cases h₁ : y.1 = p.1
      · by_cases h₂ : x.2 = p.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hp
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1, x.2)) h
    · simp
  have keyR : (∑ st : Fin r₁ × Fin r₂,
        ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) * (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else
          0)))
      = H₂ y.2 x.2 * H₁ x.1 y.1 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin r₁ × Fin r₂)))
      (f := fun st => ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) *
        (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else 0))) (x.1, y.2) ?_ ?_).trans ?_
    · intro st _ hst
      by_cases h₁ : x.1 = st.1
      · by_cases h₂ : y.2 = st.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hst
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1, y.2)) h
    · simp
  rw [keyL, keyR]
  have hcomm : H₂ y.2 x.2 * H₁ x.1 y.1 = H₁ x.1 y.1 * H₂ y.2 x.2 := mul_comm _ _
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _

end QECCertificates
