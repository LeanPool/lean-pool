/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.HGP

/-!
# The lifted product: HGP over a group algebra, and its degeneration to HGP

**Definitions from the literature** (with the source given in each case):

* Panteleev–Kalachev, *Asymptotically Good Quantum and Locally Testable Classical LDPC
  Codes*, STOC 2022 (arXiv:2111.03654v2), **Appendix B, Eq. (13)** (PDF page 48):
  given a finite group $G$ ($|G| = \ell$) and two seed matrices over the group algebra
  $R = \mathbb{F}_2[G]$, namely $A \in R^{m_A \times n_A}$ and $B \in R^{m_B \times n_B}$,
  replace each element $r \in R$ by its **regular-representation $\ell \times \ell$ matrix**
  and then take the block tensor of the HGP:
  $$H_X = \bigl[\,\widehat A \otimes I_{m_B} \;\bigm|\; I_{m_A} \otimes \widehat B\,\bigr],\qquad
    H_Z = \bigl[\,I_{n_A} \otimes \widehat B^{\top} \;\bigm|\; \widehat A^{\top} \otimes
      I_{n_B}\,\bigr].$$
  This is the **lifted product** $\mathrm{LP}(A, B)$; when $m_A = n_A = m_B = n_B = 1$ it
  degenerates to a **two-block group algebra code (2BGA)**, in the words of Lin–Pryadko,
  *Quantum two-block group algebra codes*, PRA **109**, 022407 (2024), **p. 6** ("2BGA codes
  are a degenerate case of LP codes with both matrices of dimension 1 x 1").

* The two regular representations of a group-algebra element $a = \sum_g a_g\, g$
  (Lin–Pryadko, ibid., **p. 5, Eq. (36)**):
  $$[L(a)]_{\sigma,\tau} = \sum_g a_g\,\delta_{g\tau,\sigma} = a(\sigma\tau^{-1}),\qquad
    [R(b)]_{\sigma,\tau} = \sum_g b_g\,\delta_{\tau g,\sigma} = b(\tau^{-1}\sigma).$$
  $L(a)$ is the matrix of "left multiplication $x \mapsto a\,x$" and $R(b)$ the matrix of
  "right multiplication $x \mapsto x\,b$"; this module writes them `leftMulMat a` and
  `rightMulMat b`.

## What this module contributes

1. **`leftMulMat_mul_rightMulMat`**: the two regular representations **commute entrywise**
   ($L(a)R(b) = R(b)L(a)$). This is the whole content of the CSS compatibility of LP: the
   `hgp_orthogonal` of HGP uses the transposed pairing of two Kronecker factors, whereas LP uses
   "the two regular representations commute". The proof is two permutation reindexings
   ($\rho \mapsto \tau^{-1}\rho$ and $\rho \mapsto \rho^{-1}\sigma$) plus one commutativity of
   multiplication.
2. **`lp_orthogonal`**: $H_X H_Z^{\top} = 0$ for general seeds (a **structure theorem**, holding
   for arbitrary $A, B$, with no enumeration). It lifts the entrywise argument of
   `hgp_orthogonal` to the level of "every block is a pair of group-algebra elements".
3. **2BGA (1 x 1 seeds)**: `lp2HX` / `lp2HZ` and `lp2_orthogonal`, that is, the `LP[a, b]` of the
   literature.
4. **The relation to HGP** (the four lemmas `lpExpandR_liftConst` and friends, plus
   `lp_trivialGroup_eq_hgp`): for a seed of **constant group-algebra elements** (that is, coming
   from $\mathbb{F}_2 \subset \mathbb{F}_2[G]$, written `liftConst M` here) one has
   $\widehat A = A \otimes I_\ell$, so the check matrices of LP are **block diagonal** in the group
   index and every block is exactly $\mathrm{HGP}(A, B^{\top})$:
   $$H^{\mathrm{LP}}_X\bigl((i,s),\gamma\bigr)\bigl((j,t),\gamma\bigr)
     = \bigl[\mathrm{HGP}(A,B^{\top})\bigr]_{(i,s)(j,t)}.$$
   Taking $\ell = 1$ (`Subsingleton G`) gives `lp_trivialGroup_eq_hgp`: **on the trivial group LP
   is HGP entrywise**. This agrees with the literature (Panteleev–Kalachev, p. 8: "for
   $R = \mathbb{F}_q$ the lifted product is equivalent to the product construction", and the
   group algebra at $\ell = 1$ is $\mathbb{F}_q$ itself).

## A note on conventions (the mirror relation with the literature)

The $H_X$ here gives the **left** multiplication matrix to the first seed and the **right**
multiplication matrix to the second (consistent with Eq. (36) of the 2BGA paper, and the anchor
instances reproduce the tables of the literature accordingly); the $\widehat A / \widehat B$ of
Panteleev–Kalachev give the right regular representation to the first seed. The two conventions are
mirror images of each other: the $\mathrm{LP}(A,B)$ here and the $\mathrm{LP}(B,A)$ of PK differ
only by **the exchange of the two qubit blocks** (a permutation), so the code parameters agree.

## Index conventions

Rows and columns are both **product types with a group index** (not flattened to `Fin`), which is
what makes the structure theorem require no relabelling:

* rows of $H_X$: `(Fin m_A x Fin m_B) x G`; rows of $H_Z$: `(Fin n_A x Fin n_B) x G`
* the columns of both are `((Fin n_A x Fin m_B) x G) (+) ((Fin m_A x Fin n_B) x G)`.

Flattening to `Fin` for an instance is left to `Matrix.reindex`.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## 1. The two regular representations of a group-algebra element -/

/-- The **left-multiplication matrix** of a group-algebra element `a : G → ZMod 2`: the matrix of
    the
linear operator `x ↦ a * x` in the basis `G`.

Entrywise: `(leftMulMat a) σ τ = a (σ * τ⁻¹)` (the `L(a)` of Lin–Pryadko Eq. (36)). -/
def leftMulMat (a : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => a (σ * τ⁻¹)

/-- The **right-multiplication matrix** of a group-algebra element `b : G → ZMod 2`: the matrix of
    the
linear operator `x ↦ x * b` in the basis `G`.

Entrywise: `(rightMulMat b) σ τ = b (τ⁻¹ * σ)` (the `R(b)` of Lin–Pryadko Eq. (36)). -/
def rightMulMat (b : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => b (τ⁻¹ * σ)

/-- The left-translation permutation `x ↦ g * x` (used for reindexing). -/
def mulLeftEquiv (g : G) : G ≃ G where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

/-- The reversed right-translation permutation `x ↦ x⁻¹ * g` (used for reindexing). -/
def invMulEquiv (g : G) : G ≃ G where
  toFun x := x⁻¹ * g
  invFun y := g * y⁻¹
  left_inv x := by simp
  right_inv y := by simp

/-- `σ * τ⁻¹ = 1 ↔ σ = τ` (shared by the two lemmas for constant seeds). -/
theorem mul_inv_eq_one_iff (σ τ : G) : σ * τ⁻¹ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : σ * τ⁻¹ * τ = 1 * τ := by rw [h]
    rwa [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h2
  · intro h; rw [h, mul_inv_cancel]

/-- `τ⁻¹ * σ = 1 ↔ σ = τ`. -/
theorem inv_mul_eq_one_iff (σ τ : G) : τ⁻¹ * σ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : τ * (τ⁻¹ * σ) = τ * 1 := by rw [h]
    rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  · intro h; rw [h, inv_mul_cancel]

/-- **The two regular representations commute entrywise**: `L(a) * R(b) = R(b) * L(a)`.

This is the whole content of the CSS compatibility of LP (`lp_orthogonal` calls nothing else).
Entrywise, both sides equal $\sum_\mu a(\sigma\mu^{-1}\tau^{-1})\,b(\mu)$: the left-hand side is
reindexed by $\rho \mapsto \tau^{-1}\rho$ and the right-hand side by $\rho \mapsto \rho^{-1}\sigma$,
and the two then differ by one commutativity of multiplication. -/
theorem leftMulMat_mul_rightMulMat [Fintype G] (a b : G → ZMod 2) :
    leftMulMat a * rightMulMat b = rightMulMat b * leftMulMat a := by
  ext σ τ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : (∑ ρ, leftMulMat a σ ρ * rightMulMat b ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (mulLeftEquiv τ).symm
      (fun ρ => leftMulMat a σ ρ * rightMulMat b ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : ((mulLeftEquiv τ).symm) x = τ⁻¹ * x := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    congr 1
    group
  have hR : (∑ ρ, rightMulMat b σ ρ * leftMulMat a ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (invMulEquiv σ)
      (fun ρ => rightMulMat b σ ρ * leftMulMat a ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : (invMulEquiv σ) x = x⁻¹ * σ := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    rw [mul_comm (b (x⁻¹ * σ)) (a (x * τ⁻¹))]
    congr 1
    group
  rw [hL, hR]

/-! ## 2. The lifted product with general seeds -/

/-- The **right regular block expansion** of a seed matrix: the `(i,j)`-th group-algebra element of
`A` is replaced by its left-multiplication matrix
(that is, the $\ell \times \ell$ block of `A` in the right regular representation). -/
def lpExpandR {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2)) :
    Matrix (Fin mA × G) (Fin nA × G) (ZMod 2) :=
  fun x y => A x.1 y.1 (x.2 * y.2⁻¹)

/-- The **left regular block expansion** of a seed matrix: the `(s,t)`-th group-algebra element of
    `B`
is replaced by its right-multiplication matrix. -/
def lpExpandL {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix (Fin mB × G) (Fin nB × G) (ZMod 2) :=
  fun x y => B x.1 y.1 (y.2⁻¹ * x.2)

theorem lpExpandR_apply {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (i : Fin mA) (σ : G) (j : Fin nA) (τ : G) :
    lpExpandR A (i, σ) (j, τ) = leftMulMat (A i j) σ τ := rfl

theorem lpExpandL_apply {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (s : Fin mB) (σ : G) (t : Fin nB) (τ : G) :
    lpExpandL B (s, σ) (t, τ) = rightMulMat (B s t) σ τ := rfl

/-- **The X-type checks of the lifted product**
$H_X = [\widehat A \otimes I_{m_B} \mid I_{m_A} \otimes \widehat B]$.

Row `((i,s),σ)`; the left half column `((j,s'),τ)` takes $\widehat A\,(i,\sigma)(j,\tau)\cdot[s=s']$
and the right half column `((i',t'),τ)` takes $[i=i']\cdot \widehat B\,(s,\sigma)(t',\tau)$. -/
def lpHX {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin mA × Fin mB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0))
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2)) c

/-- **The Z-type checks of the lifted product**
$H_Z = [I_{n_A} \otimes \widehat B^{\top} \mid \widehat A^{\top} \otimes I_{n_B}]$.

Row `((j,t),σ)`; the left half column `((j',s'),τ)` takes $[j=j']\cdot \widehat
    B\,(s',\tau)(t,\sigma)$
(that is, $\widehat B$ after the block transpose) and the right half column `((i',t'),τ)` takes
$\widehat A\,(i',\tau)(j,\sigma)\cdot[t=t']$. -/
def lpHZ {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin nA × Fin nB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2))
    (fun y => lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0)) c

/-- The entrywise description of the four blocks (at the `rfl` level). -/
theorem lpHX_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX A B x (Sum.inl y)
      = lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl

theorem lpHX_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX A B x (Sum.inr y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2) := rfl

theorem lpHZ_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ A B x (Sum.inl y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2) := rfl

theorem lpHZ_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ A B x (Sum.inr y)
      = lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl

/-! ## 3. The structure theorem: CSS compatibility of the lifted product -/

/-- **CSS compatibility of the lifted product**: $H_X H_Z^{\top} = 0$, for **any** seeds $A, B$.

Entrywise, the left and the right block each collapse to a single sum (`Finset.sum_eq_single`
    removes
the Kronecker $\delta$ factor), and the two summands are $(L(A_{ij})\cdot
    R(B_{st}))(\sigma,\sigma')$
and $(R(B_{st})\cdot L(A_{ij}))(\sigma,\sigma')$, which are equal by `leftMulMat_mul_rightMulMat`
    and
therefore add to zero over $\mathbb{F}_2$. **No enumeration is involved.** -/
theorem lp_orthogonal [Fintype G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    lpHX A B * (lpHZ A B).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lpHX_inl, lpHX_inr, lpHZ_inl, lpHZ_inr]
  have hL : (∑ p : (Fin nA × Fin mB) × G,
        (lpExpandR A (x.1.1, x.2) (p.1.1, p.2) * (if x.1.2 = p.1.2 then 1 else 0)) *
          ((if y.1.1 = p.1.1 then 1 else 0) * lpExpandL B (p.1.2, p.2) (y.1.2, y.2)))
      = ∑ τ : G, leftMulMat (A x.1.1 y.1.1) x.2 τ * rightMulMat (B x.1.2 y.1.2) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin nA × Fin mB)))
      (f := fun q : Fin nA × Fin mB =>
        (lpExpandR A (x.1.1, x.2) (q.1, τ) * (if x.1.2 = q.2 then 1 else 0)) *
          ((if y.1.1 = q.1 then 1 else 0) * lpExpandL B (q.2, τ) (y.1.2, y.2)))
      (y.1.1, x.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : y.1.1 = q.1
      · by_cases h₂ : x.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1.1, x.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  have hR : (∑ q : (Fin mA × Fin nB) × G,
        ((if x.1.1 = q.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.1.2, q.2)) *
          (lpExpandR A (q.1.1, q.2) (y.1.1, y.2) * (if y.1.2 = q.1.2 then 1 else 0)))
      = ∑ τ : G, rightMulMat (B x.1.2 y.1.2) x.2 τ * leftMulMat (A x.1.1 y.1.1) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin mA × Fin nB)))
      (f := fun q : Fin mA × Fin nB =>
        ((if x.1.1 = q.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.2, τ)) *
          (lpExpandR A (q.1, τ) (y.1.1, y.2) * (if y.1.2 = q.2 then 1 else 0)))
      (x.1.1, y.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : x.1.1 = q.1
      · by_cases h₂ : y.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1.1, y.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  rw [hL, hR, ← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _

/-! ## 4. 2BGA: the lifted product of 1 x 1 seeds (the `LP[a, b]` of the literature) -/

/-- **The X-type checks of 2BGA** $H_X = [L(a) \mid R(b)]$ (Lin–Pryadko Eq. (16)). -/
def lp2HX (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => leftMulMat a σ τ) (fun τ => rightMulMat b σ τ) c

/-- **The Z-type checks of 2BGA** $H_Z = [R(b)^{\top} \mid L(a)^{\top}]$ (Lin–Pryadko Eq. (16):
$H_Z^{\top} = \binom{B}{-A}$, and the minus sign disappears over $\mathbb{F}_2$). -/
def lp2HZ (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => rightMulMat b τ σ) (fun τ => leftMulMat a τ σ) c

theorem lp2HX_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inl τ) = leftMulMat a σ τ := rfl

theorem lp2HX_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inr τ) = rightMulMat b σ τ := rfl

theorem lp2HZ_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inl τ) = rightMulMat b τ σ := rfl

theorem lp2HZ_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inr τ) = leftMulMat a τ σ := rfl

/-- **CSS compatibility of 2BGA**: $H_X H_Z^{\top} = L(a)R(b) + R(b)L(a) = 0$. -/
theorem lp2_orthogonal [Fintype G] (a b : G → ZMod 2) :
    lp2HX a b * (lp2HZ a b).transpose = 0 := by
  ext σ σ'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lp2HX_inl, lp2HX_inr, lp2HZ_inl, lp2HZ_inr]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _

/-! ## 5. Reusable lemmas on lengths and dimensions -/

omit [Group G] in
/-- **The number of qubits of LP**: $\ell\,(n_A m_B + m_A n_B)$. -/
theorem lp_qubit_count [Fintype G] {mA nA mB nB : ℕ} :
    Fintype.card (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G))
      = (nA * mB + mA * nB) * Fintype.card G := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  ring

omit [Group G] in
/-- The number of X-type check rows of LP: $m_A m_B \ell$. -/
theorem lp_row_count_X [Fintype G] {mA mB : ℕ} :
    Fintype.card ((Fin mA × Fin mB) × G) = mA * mB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [Group G] in
/-- The number of Z-type check rows of LP: $n_A n_B \ell$. -/
theorem lp_row_count_Z [Fintype G] {nA nB : ℕ} :
    Fintype.card ((Fin nA × Fin nB) × G) = nA * nB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [Group G] in
/-- **The code length of 2BGA**: $n = 2\ell$ (the direct sum of two $\ell$ blocks). -/
theorem lp2_qubit_count [Fintype G] : Fintype.card (G ⊕ G) = 2 * Fintype.card G := by
  rw [Fintype.card_sum]
  ring

/-! ## 6. Relation to HGP: constant seeds make every group fibre an HGP -/

/-- **Lifting** a matrix over $\mathbb{F}_2$ to a matrix of constant group-algebra elements (that
    is,
the image of $\mathbb{F}_2 \subset \mathbb{F}_2[G]$: supported on the identity alone). -/
def liftConst [DecidableEq G] {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (Fin m) (Fin n) (G → ZMod 2) :=
  fun i j g => M i j * (if g = 1 then 1 else 0)

/-- With a constant seed the right regular block expansion degenerates to $A \otimes I_\ell$:
$\widehat A\,(i,\sigma)(j,\tau) = A_{ij}\cdot[\sigma = \tau]$. -/
theorem lpExpandR_liftConst [DecidableEq G] {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (i : Fin m) (σ : G) (j : Fin n) (τ : G) :
    lpExpandR (liftConst A) (i, σ) (j, τ) = A i j * (if σ = τ then 1 else 0) := by
  simp only [lpExpandR, liftConst]
  by_cases h : σ = τ
  · rw [ite_eq_left ((mul_inv_eq_one_iff σ τ).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((mul_inv_eq_one_iff σ τ).mp hc)), ite_eq_right h]

/-- With a constant seed the left regular block expansion degenerates to $B \otimes I_\ell$. -/
theorem lpExpandL_liftConst [DecidableEq G] {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (s : Fin m) (σ : G) (t : Fin n) (τ : G) :
    lpExpandL (liftConst B) (s, σ) (t, τ) = B s t * (if σ = τ then 1 else 0) := by
  simp only [lpExpandL, liftConst]
  by_cases h : σ = τ
  · rw [ite_eq_left ((inv_mul_eq_one_iff σ τ).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((inv_mul_eq_one_iff σ τ).mp hc)), ite_eq_right h]

/-- **With constant seeds the X-type checks of LP are block diagonal in the group index, and every
block is an HGP** (left block). -/
theorem lpHX_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHX A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inl, lpExpandR_liftConst, hgpHX_inl]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]

theorem lpHX_liftConst_inr [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHX A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inr, lpExpandL_liftConst, hgpHX_inr, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]

theorem lpHZ_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHZ A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inl, lpExpandL_liftConst, hgpHZ_inl, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem lpHZ_liftConst_inr [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHZ A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inr, lpExpandR_liftConst, hgpHZ_inr]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]

/-- **On the trivial group ($\ell = 1$) LP is HGP entrywise** ($X$ side).

At $\ell = 1$ the group index has a single element (`Subsingleton G`), so $\delta_{\sigma\tau}$ is
constantly $1$ and the factor in `lpHX_liftConst_inl` disappears. This is the statement of the
literature that "for $R = \mathbb{F}_q$ the lifted product is equivalent to the product
construction" (Panteleev–Kalachev, p. 8). -/
theorem lp_trivialGroup_eq_hgp [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (i : Fin mA) (s : Fin mB) (j : Fin nA) (t : Fin mB) (σ τ : G) :
    lpHX (liftConst A) (liftConst B) ((i, s), σ) (Sum.inl ((j, t), τ))
      = hgpHX A B.transpose (i, s) (Sum.inl (j, t)) := by
  rw [lpHX_liftConst_inl, ite_eq_left (Subsingleton.elim σ τ), mul_one]

/-- **On the trivial group ($\ell = 1$) LP is HGP entrywise** ($Z$ side). -/
theorem lp_trivialGroup_eq_hgp_Z [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (j : Fin nA) (t : Fin nB) (j' : Fin nA) (s : Fin mB) (σ τ : G) :
    lpHZ (liftConst A) (liftConst B) ((j, t), σ) (Sum.inl ((j', s), τ))
      = hgpHZ A B.transpose (j, t) (Sum.inl (j', s)) := by
  rw [lpHZ_liftConst_inl, ite_eq_left (Subsingleton.elim σ τ), mul_one]

end QECCertificates
