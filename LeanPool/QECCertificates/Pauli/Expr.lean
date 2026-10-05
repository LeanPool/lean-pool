/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.KernelBasis

/-!
# Translation theorems between the operator-algebra layer (operator trees) and the decision layer
    (GF(2) symplectic representation)

The specification calls for an **operator-tree intermediate representation** of the
operator-algebra layer, in which the expressions for Pauli and logical operators are
written as trees, together with **machine-checked translation theorems** connecting it to
the GF(2) symplectic representation of the decision layer: operator algebra travels
through trees, distance and rank decisions travel through vectors, and the two
representations each serve their own purpose while meeting. This module is the first
realization of that requirement.

## The two representations

| Layer | Objects | Operation |
|---|---|---|
| operator algebra (trees) | `PauliExpr n`: a leaf is "place a single-site Pauli at position `i`",
    a node is multiplication | `PauliExpr.mul` |
| decision layer (vectors) | `Vec n × Vec n`: the two GF(2) vectors `(Z side, X side)` |
    coordinatewise addition |

The translation `toSymp` evaluates a tree into a Pauli word and then takes its symplectic
encoding; **the main theorem states that it is a multiplicative homomorphism**:
  `toSymp (mul a b) = toSymp a + toSymp b`.

The second translation theorem is the **commutation criterion**: "commuting" at the
operator layer, meaning an even number of anticommuting sites, is equivalent to the
symplectic inner product vanishing at the decision layer. This criterion is the entry
point to every structural statement about stabilizer codes.

## Why both layers are needed

* The tree layer stays close to **expressions**: logical operators, stabilizer generators
  and intermediate circuit results are naturally expressions, and rewriting on trees,
  collecting like terms and cancelling `P·P = 1`, does not require expanding into
  $2^n$-dimensional vectors.
* The vector layer stays close to **decision**: commutation, rank and distance are all
  linear algebra over GF(2), and the vector layer can call the whole
  `QECCertificates.GF2` machinery directly.

## Main results

* `Pauli.symp_mul`: single-site multiplication corresponds to addition of symplectic
  encodings.
* `Pauli.anti_eq_symp`: the single-site anticommutation indicator equals the single-site
  symplectic inner product.
* `toSymp_mul` / `toSymp_one`: **the translation is a multiplicative homomorphism**.
* `commutesWord_iff_symplectic` / `commutes_iff_symplectic`: **the commutation criterion,
  in word form and in tree form**.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Single-site Pauli operators -/

/-- Single-qubit Pauli operators, modulo phase; the phase does not enter the symplectic
representation. -/
inductive Pauli where
  | I | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Pauli where
  elems := {.I, .X, .Y, .Z}
  complete := by intro p; cases p <;> simp

namespace Pauli

/-- Pauli multiplication modulo phase: the group operation after quotienting the Pauli
group by $\{\pm1,\pm i\}$. -/
def mul : Pauli → Pauli → Pauli
  | .I, q => q
  | p, .I => p
  | .X, .X => .I
  | .X, .Y => .Z
  | .X, .Z => .Y
  | .Y, .X => .Z
  | .Y, .Y => .I
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Z, .Y => .X
  | .Z, .Z => .I

/-- **Symplectic encoding**: `(Z component, X component)`. $I\mapsto(0,0)$,
$X\mapsto(0,1)$, $Z\mapsto(1,0)$, $Y\mapsto(1,1)$. -/
def symp : Pauli → ZMod 2 × ZMod 2
  | .I => (0, 0)
  | .X => (0, 1)
  | .Y => (1, 1)
  | .Z => (1, 0)

/-- **The single-site anticommutation indicator**: 1, meaning anticommute, when neither
factor is the identity and the two differ, and 0, meaning commute, otherwise.

It is given directly by the physical definition, since $X,Y,Z$ anticommute pairwise,
without recourse to the symplectic encoding; `anti_eq_symp` below is the machine-checked
result that it agrees with the symplectic inner product. -/
def anti : Pauli → Pauli → ZMod 2
  | .I, _ => 0
  | _, .I => 0
  | .X, .X => 0
  | .Y, .Y => 0
  | .Z, .Z => 0
  | _, _ => 1

@[simp] lemma mul_I_left (p : Pauli) : mul .I p = p := by cases p <;> rfl
@[simp] lemma mul_I_right (p : Pauli) : mul p .I = p := by cases p <;> rfl
@[simp] lemma mul_self (p : Pauli) : mul p p = .I := by cases p <;> rfl
lemma mul_comm (p q : Pauli) : mul p q = mul q p := by fin_cases p <;> fin_cases q <;> rfl
lemma mul_assoc (p q r : Pauli) : mul (mul p q) r = mul p (mul q r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> rfl

/-- **Translation theorem, single site**: single-site multiplication carries over to
coordinatewise addition of symplectic encodings. -/
lemma symp_mul (p q : Pauli) : symp (mul p q) = symp p + symp q := by
  fin_cases p <;> fin_cases q <;> decide

@[simp] lemma anti_self (p : Pauli) : anti p p = 0 := by cases p <;> rfl
lemma anti_comm (p q : Pauli) : anti p q = anti q p := by fin_cases p <;> fin_cases q <;> decide

/-- **Translation theorem, single-site commutation criterion**: the anticommutation
indicator equals exactly the single-site symplectic inner product `(z_p x_q + z_q x_p)`. -/
lemma anti_eq_symp (p q : Pauli) :
    anti p q = (symp p).1 * (symp q).2 + (symp q).1 * (symp p).2 := by
  fin_cases p <;> fin_cases q <;> decide

end Pauli

/-! ## Pauli words (the objects of the decision layer) -/

/-- A Pauli word: a single-site Pauli at every position. This is the preimage of the
symplectic representation. -/
abbrev PauliWord (n : ℕ) := Fin n → Pauli

/-- **The symplectic vector pair of the decision layer**: `(Z side, X side)`. -/
def sympWord (w : PauliWord n) : Vec n × Vec n :=
  ((fun i => (Pauli.symp (w i)).1), (fun i => (Pauli.symp (w i)).2))

@[simp] lemma sympWord_fst (w : PauliWord n) : (sympWord w).1 = fun i => (Pauli.symp (w i)).1 := rfl
@[simp] lemma sympWord_snd (w : PauliWord n) : (sympWord w).2 = fun i => (Pauli.symp (w i)).2 := rfl

/-- **Commutation at the operator layer**: the number of anticommuting sites is even,
that is, the sum over GF(2) is zero. -/
def commutesWord (u v : PauliWord n) : Prop := (∑ i, Pauli.anti (u i) (v i)) = 0

lemma commutesWord_symm {u v : PauliWord n} (h : commutesWord u v) : commutesWord v u := by
  rw [commutesWord] at h ⊢
  have hswap : (∑ i, Pauli.anti (v i) (u i)) = (∑ i, Pauli.anti (u i) (v i)) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_comm (v i) (u i)
  rw [hswap]; exact h

/-- Every Pauli word commutes with itself, since the symplectic form is alternating. -/
@[simp] lemma commutesWord_self (u : PauliWord n) : commutesWord u u := by
  rw [commutesWord]
  exact Finset.sum_eq_zero fun i _ => Pauli.anti_self (u i)

/-- **The commutation criterion, word form**: commutation at the operator layer if and
only if the symplectic inner product vanishes at the decision layer.

The proof transports the single-site correspondence `anti_eq_symp` pointwise and then
splits the sum; "commutation" in the two layers is one and the same GF(2) quadratic form
written two ways. -/
theorem commutesWord_iff_symplectic (u v : PauliWord n) :
    commutesWord u v ↔
      (sympWord u).1 ⬝ᵥ (sympWord v).2 + (sympWord v).1 ⬝ᵥ (sympWord u).2 = 0 := by
  rw [commutesWord]
  have hcongr : ∑ i, Pauli.anti (u i) (v i)
      = ∑ i, ((sympWord u).1 i * (sympWord v).2 i + (sympWord v).1 i * (sympWord u).2 i) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_eq_symp (u i) (v i)
  rw [hcongr, Finset.sum_add_distrib]
  rw [show (∑ i, (sympWord u).1 i * (sympWord v).2 i)
        = (sympWord u).1 ⬝ᵥ (sympWord v).2 from rfl,
      show (∑ i, (sympWord v).1 i * (sympWord u).2 i)
        = (sympWord v).1 ⬝ᵥ (sympWord u).2 from rfl]

/-! ## Operator trees (the objects of the operator-algebra layer) -/

/-- **Operator trees**: a leaf is "place a single-site Pauli at position `i`", a node is
multiplication, and there is an explicit unit.

This is the operator-tree intermediate representation of the operator-algebra layer
called for by the specification: rewriting on trees, collecting and cancelling
$P\cdot P = 1$, does not require expanding into $2^n$-dimensional vectors. -/
inductive PauliExpr (n : ℕ) where
  /-- Place the single-site Pauli `p` at position `i`. -/
  | atom (i : Fin n) (p : Pauli)
  /-- The identity operator. -/
  | one
  /-- A multiplication node. -/
  | mul (a b : PauliExpr n)

namespace PauliExpr

/-- Tree evaluation: a leaf expands to a single-site Pauli on the unit vector, and a
multiplication node multiplies coordinatewise. -/
def eval : PauliExpr n → PauliWord n
  | .atom i p => fun j => if j = i then p else .I
  | .one => fun _ => .I
  | .mul a b => fun i => Pauli.mul (eval a i) (eval b i)

/-- **The translation between the two layers**: operator tree to GF(2) symplectic vector
pair. -/
def toSymp (e : PauliExpr n) : Vec n × Vec n := sympWord (eval e)

@[simp] lemma eval_one : eval (.one : PauliExpr n) = fun _ => Pauli.I := rfl

@[simp] lemma eval_mul (a b : PauliExpr n) :
    eval (.mul a b) = fun i => Pauli.mul (eval a i) (eval b i) := rfl

@[simp] lemma toSymp_one : toSymp (.one : PauliExpr n) = 0 := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [toSymp, sympWord, Pauli.symp]

/-- **The main translation theorem, a multiplicative homomorphism**: multiplication on
operator trees carries over to coordinatewise addition of symplectic vectors.

This is the content of "the two representations meet": the structural operation of the
tree layer, namely multiplication, is linear at the decision layer, so an expression on
trees can be translated as a whole to the vector layer and handed to the linear algebra
machinery of `QECCertificates.GF2`. -/
theorem toSymp_mul (a b : PauliExpr n) : toSymp (.mul a b) = toSymp a + toSymp b := by
  refine Prod.ext ?_ ?_ <;>
    · funext i
      simp only [toSymp, sympWord, eval_mul, Prod.fst_add, Prod.snd_add, Pi.add_apply,
        Pauli.symp_mul, Prod.fst_add, Prod.snd_add]

/-- Translation of a leaf: only position `i` is nonzero. -/
lemma toSymp_atom (i : Fin n) (p : Pauli) :
    toSymp (.atom i p)
      = ((fun j => if j = i then (Pauli.symp p).1 else 0),
         (fun j => if j = i then (Pauli.symp p).2 else 0)) := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    · simp only [toSymp, sympWord, eval]
      by_cases h : j = i <;> simp [h, Pauli.symp]

/-- **Commutation at the operator layer, tree form**: evaluate the two trees and test
commutation of the resulting words. -/
def commutes (a b : PauliExpr n) : Prop := commutesWord (eval a) (eval b)

/-- **The translation theorem for commutation, tree form**: commutation at the tree layer
if and only if the symplectic inner product vanishes at the decision layer.

This is the main public criterion of this module: every structural statement about
stabilizer codes, whether an element lies in the stabilizer group, whether a logical
operator commutes with the stabilizers, or whether a distance candidate commutes with the
checks, reduces to it. -/
theorem commutes_iff_symplectic (a b : PauliExpr n) :
    commutes a b ↔ (toSymp a).1 ⬝ᵥ (toSymp b).2 + (toSymp b).1 ⬝ᵥ (toSymp a).2 = 0 :=
  commutesWord_iff_symplectic (eval a) (eval b)

end PauliExpr

end QECCertificates
