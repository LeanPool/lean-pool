/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp

/-!
# Noun Polynomial Representation (NPR)

The paper's succinct polynomial representation of nouns and its collision-soundness bounds
(`main.tex:1162–1226`).  A noun `n = (dt, w)` (`main.tex:1164`) is a leaf array `dt ∈ 𝔽^λ`
together with a Dyck word `w ∈ {0,1}^{2(λ−1)}` fixing the tree shape.  The leaf array is
`Noun.leafList` and the Dyck word `Noun.dyckWord` (both from `Nock/Dyck.lean`), cast into a
field `K` at this layer.

Contents:
* `Φ`  (`main.tex:1170–1173`) — the NPR: a noun ↦ triple of univariate polynomials
    `Φ(dt,w) = ( X^{|dt|},  Σ dtᵢ X^{i−1},  Σ wᵢ X^{i−1} )`.
* `fn` (`def:ion_univariate`, `main.tex:1180–1184`) — the fingerprint
    `fn(n; r) = Φ(dt,w)[r,r,r] = (r^{|dt|}, F_d(r), F_w(r))`, `r ∈ K`.
* `NPR_decomp` (`Lem:NPR_decomp`, `main.tex:1218–1226`) — the three `cons` concatenation
    identities (with the corrected Φ₃ exponents; see the section header).
* `collision_card_le` / `collision_prob_le` (`lem:ion_univariate_sec`, `main.tex:1188`) —
    distinct nouns collide under `fn` for at most `2(2Λ−1)` values of `r`.
* `collision_table_card_le` / `collision_table_prob_le` (`corr:ion_single_security`,
    `main.tex:1197`) — union bound over `k` nouns: `Pr ≤ ε · k(k−1)/2`.

Everything is proved over an ARBITRARY finite field `K` (`[Field K] [Fintype K]
[DecidableEq K]`): no concrete field, no primality axiom.  "`Pr_{r∈K}[…]`" is the counting
measure (satisfying `r` count divided by `|K| = Fintype.card K`); the core results are the
exact cardinality bounds (`…_card_le`), with `…_prob_le` dividing by `|K|` in `ℚ`.
Schwartz–Zippel is `Polynomial.card_roots'` via `card_eval_zero_le`.
-/

@[expose] public section

open Polynomial

namespace Nock

namespace NPR

/-! ### Coefficient-vector polynomials -/

section CPoly
variable {K : Type*} [Field K]

/-- `cpoly f n = Σ_{i<n} f i · X^i`: the polynomial with coefficient vector `(f 0,…,f (n−1))`. -/
noncomputable def cpoly (f : ℕ → K) (n : ℕ) : K[X] := ∑ i ∈ Finset.range n, C (f i) * X ^ i

theorem cpoly_coeff (f : ℕ → K) (n j : ℕ) :
    (cpoly f n).coeff j = if j < n then f j else 0 := by
  unfold cpoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range n) j f]
  simp [Finset.mem_range]

theorem cpoly_sub (f g : ℕ → K) (n : ℕ) :
    cpoly f n - cpoly g n = cpoly (fun i => f i - g i) n := by
  unfold cpoly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← sub_mul, ← C_sub]

theorem cpoly_natDegree_le (f : ℕ → K) (n : ℕ) : (cpoly f n).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [cpoly_coeff]
  have : ¬ N < n := by omega
  simp [this]

theorem cpoly_ne_zero_of_coeff {f g : ℕ → K} {n j : ℕ} (hj : j < n) (h : f j ≠ g j) :
    cpoly f n - cpoly g n ≠ 0 := by
  rw [cpoly_sub]
  intro hzero
  apply h
  have hc : (cpoly (fun i => f i - g i) n).coeff j = f j - g j := by
    rw [cpoly_coeff]; simp [hj]
  rw [hzero, coeff_zero] at hc
  exact sub_eq_zero.mp hc.symm

end CPoly

/-! ### List-indexed polynomials -/

section ListPoly
variable {K : Type*} [Field K]

/-- The polynomial whose coefficient vector is the list `l` (default `0` past the end). -/
noncomputable def listPoly (l : List K) : K[X] :=
  cpoly (fun i => l.getD i 0) l.length

theorem listPoly_natDegree_le (l : List K) : (listPoly l).natDegree ≤ l.length - 1 :=
  cpoly_natDegree_le _ _

/-- Two equal-length lists that differ have distinct coefficient polynomials. -/
theorem listPoly_sub_ne_zero {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) (hne : l₁ ≠ l₂) :
    listPoly l₁ - listPoly l₂ ≠ 0 := by
  -- find a position where they differ
  have hex : ∃ j, j < l₁.length ∧ l₁.getD j 0 ≠ l₂.getD j 0 := by
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    apply hne
    apply List.ext_getElem hlen
    intro j hj hj2
    have hjeq := h j hj
    rwa [List.getD_eq_getElem l₁ 0 hj, List.getD_eq_getElem l₂ 0 (hlen ▸ hj)] at hjeq
  obtain ⟨j, hj, hval⟩ := hex
  unfold listPoly
  rw [hlen]
  exact cpoly_ne_zero_of_coeff (hlen ▸ hj) hval

theorem listPoly_sub_natDegree_le {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) :
    (listPoly l₁ - listPoly l₂).natDegree ≤ l₁.length - 1 := by
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  exact ⟨listPoly_natDegree_le l₁, by rw [hlen]; exact listPoly_natDegree_le l₂⟩

/-! #### Concatenation identities for `listPoly` (the algebraic backbone of `Lem:NPR_decomp`).

    These express how a list-indexed polynomial factors when its coefficient list is split.
    They are what turn the DFS/Dyck concatenation of nouns under `cell` into the polynomial
    identities of `Lem:NPR_decomp` (main.tex:1218). -/

theorem listPoly_coeff (l : List K) (j : ℕ) :
    (listPoly l).coeff j = if j < l.length then l.getD j 0 else 0 := by
  unfold listPoly; rw [cpoly_coeff]

@[simp] theorem listPoly_nil : listPoly ([] : List K) = 0 := by
  unfold listPoly cpoly; simp

/-- `listPoly (x :: l) = C x + X · listPoly l`: prepending a coefficient shifts by one. -/
theorem listPoly_cons (x : K) (l : List K) :
    listPoly (x :: l) = C x + X * listPoly l := by
  ext j
  rw [coeff_add, listPoly_coeff]
  match j with
  | 0 =>
      rw [mul_coeff_zero, coeff_X_zero, zero_mul, add_zero, coeff_C_zero,
        List.getD_cons_zero]
      simp
  | k + 1 =>
      rw [coeff_X_mul, listPoly_coeff, coeff_C, List.getD_cons_succ, List.length_cons]
      simp

/-- **`listPoly (a ++ b) = listPoly a + X^{|a|} · listPoly b`** — the paper's stated
    concatenation rule (main.tex:1218 discussion): a coefficient list `a ++ b` gives the
    polynomial of `a` plus the polynomial of `b` shifted up by `|a|` places. -/
theorem listPoly_append (a b : List K) :
    listPoly (a ++ b) = listPoly a + X ^ a.length * listPoly b := by
  induction a with
  | nil => simp
  | cons x a' ih =>
      rw [List.cons_append, listPoly_cons, ih, listPoly_cons, List.length_cons, pow_succ]
      ring

end ListPoly

/-! ### The NPR and the fingerprint -/

section FnLayer
variable {K : Type*} [Field K]

/-- Leaf array `dt` cast into the field `K` (ATOM MODEL (a): `Nat → K`), main.tex:1164. -/
def leafF (n : Noun) : List K := n.leafList.map (fun k : ℕ => (k : K))

/-- Dyck word `w ∈ {0,1}*` cast into the field `K` (`0 ↦ 0`, `1 ↦ 1`), main.tex:1166. -/
def dyckBits (n : Noun) : List K := n.dyckWord.map (fun b => if b then (1 : K) else 0)

@[simp] theorem leafF_length (n : Noun) : (leafF (K := K) n).length = n.leaves := by
  simp [leafF]

theorem dyckBits_length (n : Noun) : (dyckBits (K := K) n).length + 2 = 2 * n.leaves := by
  simp only [dyckBits, List.length_map]
  exact n.dyckWord_length

/-- **The Noun Polynomial Representation (main.tex:1170–1173).**
    `Φ(dt,w) = ( X₁^{|dt|},  Σ dtᵢ X₂^{i−1},  Σ wᵢ X₃^{i−1} )` — represented as a triple of
    univariate polynomials (each in its own indeterminate `X`). -/
noncomputable def Φ (n : Noun) : K[X] × K[X] × K[X] :=
  (X ^ n.leaves, listPoly (leafF n), listPoly (dyckBits n))

/-- **The fingerprint (def:ion_univariate, main.tex:1180–1184).**
    `fn(n; r) = Φ(dt,w)[r,r,r] = (r^{|dt|}, F_d(r), F_w(r))`, evaluated at `r ∈ K`. -/
noncomputable def fn (n : Noun) (r : K) : K × K × K :=
  (r ^ n.leaves, (listPoly (leafF n)).eval r, (listPoly (dyckBits n)).eval r)

/-- The fingerprint is `Φ` evaluated at `(r,r,r)` (main.tex:1183). -/
theorem fn_eq_Φ_eval (n : Noun) (r : K) :
    fn n r = ((Φ n).1.eval r, (Φ (K := K) n).2.1.eval r, (Φ n).2.2.eval r) := by
  simp [fn, Φ]

@[simp] theorem Φ_fst (n : Noun) : (Φ (K := K) n).1 = X ^ n.leaves := rfl
@[simp] theorem Φ_snd_fst (n : Noun) : (Φ (K := K) n).2.1 = listPoly (leafF n) := rfl
@[simp] theorem Φ_snd_snd (n : Noun) : (Φ (K := K) n).2.2 = listPoly (dyckBits n) := rfl

end FnLayer

/-! ### `Lem:NPR_decomp` — the memory-table backbone (main.tex:1218)

    How the three NPR polynomials concatenate under `cons`.  We first record the two
    structural concatenation lemmas (leaf array in DFS order; Dyck word by the grammar
    `w = 0·w_L·1·w_R`), then read off the three `Φ`-identities.

    ⚠ **FAITHFULNESS — the Φ₃ (Dyck) exponents (main.tex:1223).**  The paper prints
        `Φ(n)₃ = Φ(nL)₃ + X^{2(λL−1)} + X^{2λL−1}·Φ(nR)₃`.
    Derived carefully against `Dyck.encode`'s grammar `w = 0·w_L·1·w_R` and the paper's own
    `F_w(X) = Σ_i w_i X^{i−1}` (`listPoly`), the CORRECT identity is
        `Φ(n)₃ = X·Φ(nL)₃ + X^{2λL−1} + X^{2λL}·Φ(nR)₃`.
    The paper's form is off by one global factor of `X` (equivalently: it drops the leading
    open-delimiter bit's `X`-shift), i.e. paper-RHS `= X⁻¹·(correct RHS)`.  Concretely, for
    `n = cons(atom,atom)` the Dyck word is `[0,1]`, so `F_w(n) = X`, which the correct
    identity yields (`X·0 + X^{2·1−1} + X^{2·1}·0 = X`) but the paper's yields `1`
    (`0 + X^{2(1−1)} + X^{2·1−1}·0`).  We prove and use the correct identity `Phi3_cons`
    and flag this deviation. -/

section Decomp
variable {K : Type*} [Field K]

/-- Leaf array concatenates under `cell` (DFS order), main.tex:1218. -/
@[simp] theorem leafF_cell (l r : Noun) :
    leafF (K := K) (Noun.cell l r) = leafF l ++ leafF r := by
  simp [leafF, Noun.leafList]

/-- Dyck word under `cell`: `w = 0 · w_L · 1 · w_R` (the grammar of `Dyck.encode`,
    main.tex:337), cast to field bits (`false ↦ 0`, `true ↦ 1`). -/
theorem dyckBits_cell (l r : Noun) :
    dyckBits (K := K) (Noun.cell l r)
      = (0 : K) :: (dyckBits l ++ (1 : K) :: dyckBits r) := by
  simp only [dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode, List.map_cons,
    List.map_append]
  norm_num

/-- **`Lem:NPR_decomp`, Φ₁ (main.tex:1221):** `Φ(cons(l,r))₁ = Φ(l)₁ · Φ(r)₁`,
    i.e. `X^{|dt|} = X^{λL}·X^{λR}`. -/
theorem Phi1_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).1 = (Φ l).1 * (Φ r).1 := by
  simp only [Φ_fst, Noun.leaves, pow_add]

/-- **`Lem:NPR_decomp`, Φ₂ (main.tex:1222):** `Φ(cons(l,r))₂ = Φ(l)₂ + X^{λL}·Φ(r)₂`. -/
theorem Phi2_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.1 = (Φ l).2.1 + X ^ l.leaves * (Φ r).2.1 := by
  simp only [Φ_snd_fst, leafF_cell, listPoly_append, leafF_length]

/-- **`Lem:NPR_decomp`, Φ₃ (main.tex:1223), CORRECTED exponents (see the section header):**
    `Φ(cons(l,r))₃ = X·Φ(l)₃ + X^{2λL−1} + X^{2λL}·Φ(r)₃`. -/
theorem Phi3_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.2
      = X * (Φ l).2.2 + X ^ (2 * l.leaves - 1) + X ^ (2 * l.leaves) * (Φ r).2.2 := by
  have hd : (dyckBits (K := K) l).length + 2 = 2 * l.leaves := dyckBits_length l
  have h1 : (dyckBits (K := K) l).length + 1 = 2 * l.leaves - 1 := by omega
  simp only [Φ_snd_snd, dyckBits_cell, listPoly_cons, listPoly_append, C_0, C_1]
  rw [← h1, ← hd]
  ring

/-- **`Lem:NPR_decomp` (main.tex:1218).**  The three algebraic identities characterizing
    `cons`.  We state the paper's `↔ n = cons(nL,nR)` as `Φ n = Φ (cons nL nR)` — *field-noun*
    equality: `Φ n = Φ n'` is equality of the pair (leaf-count, leaf polynomial, Dyck polynomial),
    i.e. of the `(dyck word, 𝔽-valued leaf array)`, which is the paper's notion of noun equality
    over `𝔽` (the paper's nouns are field-valued, `main.tex:347–349`, `1023`).  (Structural
    `n = cell nL nR` implies it via `congrArg`, `NPR_decomp_of_cons`; the converse to *structural*
    `Nat` equality does NOT hold — distinct `Nat` leaves congruent mod the characteristic give the
    same field-noun (compiled counterexample `RedTeam.Batch5.b5_npr_decomp_field_not_structural`
    over `ZMod 5`), the "same field-noun"
    phenomenon also underlying `collision_card_le`.  This module does not prove `Φ` injective on
    field-nouns; that is the paper's ion property, whose soundness error is bounded by
    `collision_prob_le`.) -/
theorem NPR_decomp (n nL nR : Noun) :
    Φ (K := K) n = Φ (K := K) (Noun.cell nL nR)
      ↔ ( (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
        ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
        ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
            + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 ) := by
  constructor
  · intro h
    rw [h]
    exact ⟨Phi1_cons nL nR, Phi2_cons nL nR, Phi3_cons nL nR⟩
  · rintro ⟨h1, h2, h3⟩
    have e1 : (Φ (K := K) n).1 = (Φ (K := K) (Noun.cell nL nR)).1 := by
      rw [h1, Phi1_cons]
    have e2 : (Φ (K := K) n).2.1 = (Φ (K := K) (Noun.cell nL nR)).2.1 := by
      rw [h2, Phi2_cons]
    have e3 : (Φ (K := K) n).2.2 = (Φ (K := K) (Noun.cell nL nR)).2.2 := by
      rw [h3, Phi3_cons]
    exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, e3⟩⟩

/-- Structural `←` direction of `Lem:NPR_decomp`: if `n` is literally `cons(nL,nR)` then its
    NPR satisfies the three identities. -/
theorem NPR_decomp_of_cons {n nL nR : Noun} (h : n = Noun.cell nL nR) :
    (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
    ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
    ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
        + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 :=
  (NPR_decomp n nL nR).mp (by rw [h])

/-! #### Fingerprint-level `cons` composition (the constraint form)

    `Lem:NPR_decomp` characterizes `cons` at the polynomial level.  A zkVM AIR never carries
    the polynomials — a trace row carries only the *evaluated* fingerprints `fn(·; x) ∈ K³` —
    so a cons gadget states the same identities as field arithmetic on fingerprint components.
    These are the evaluations of `Phi1_cons`/`Phi2_cons`/`Phi3_cons` at `x`, plus an
    inverse-free multiplied-through form of the Dyck identity (`fn_cons_dyck_constraint`).
    That form is a **completeness** identity for honest `fn` values (no `x⁻¹` in the
    statement).  It is **not** a proved soundness theorem for committed columns, and at
    `x = 0` it degenerates to `0 = 0` (every noun has ≥1 leaf, so `fn₁(l;0) = 0`), constraining
    nothing — useful as an AIR-style equation only for nonzero challenges.

    ⚠ **Orientation.**  This layer's `fn` / `fnHorner` evaluate with the FIRST leaf/Dyck
    symbol at the constant coefficient (`listPoly`).  A different Horner convention that
    places the first symbol at the highest power would need mirrored cons identities; those
    mirrored equations are **not** theorems in this file.  `fnHorner_eq_fn` ties the running
    code to the non-mirrored orientation proved here. -/

/-- `fn₁` composes multiplicatively under `cons` (evaluation of `Phi1_cons`):
    `fn₁(cons(l,r)) = fn₁(l)·fn₁(r)`. -/
theorem fn_cons_size (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).1 = (fn l x).1 * (fn r x).1 := by
  simp only [fn, Noun.leaves, pow_add]

/-- `fn₂` (leaf fingerprint) composes affinely under `cons` (evaluation of `Phi2_cons`):
    `fn₂(cons(l,r)) = fn₂(l) + fn₁(l)·fn₂(r)`. -/
theorem fn_cons_leaf (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).2.1 = (fn l x).2.1 + (fn l x).1 * (fn r x).2.1 := by
  simp only [fn, leafF_cell, listPoly_append, eval_add, eval_mul, eval_pow, eval_X,
    leafF_length]

/-- `fn₃` (Dyck fingerprint) composes under `cons` with the delimiter power made explicit
    (evaluation of the corrected `Phi3_cons`):
    `fn₃(cons(l,r)) = x·fn₃(l) + x^{2λL−1} + x^{2λL}·fn₃(r)`. -/
theorem fn_cons_dyck (l r : Noun) (x : K) :
    (fn (Noun.cell l r) x).2.2
      = x * (fn l x).2.2 + x ^ (2 * l.leaves - 1)
        + x ^ (2 * l.leaves) * (fn r x).2.2 := by
  have h := congrArg (Polynomial.eval x) (Phi3_cons (K := K) l r)
  simpa only [fn, Φ_snd_snd, eval_add, eval_mul, eval_pow, eval_X] using h

/-- **Fingerprint `cons` composition (`fn_cons`)** — `fn(cons(l,r); x)` as field arithmetic
    over the children's fingerprints, with the Dyck delimiter power explicit. -/
theorem fn_cons (l r : Noun) (x : K) :
    fn (Noun.cell l r) x
      = ( (fn l x).1 * (fn r x).1
        , (fn l x).2.1 + (fn l x).1 * (fn r x).2.1
        , x * (fn l x).2.2 + x ^ (2 * l.leaves - 1)
            + x ^ (2 * l.leaves) * (fn r x).2.2 ) :=
  Prod.ext_iff.mpr ⟨fn_cons_size l r x,
    Prod.ext_iff.mpr ⟨fn_cons_leaf l r x, fn_cons_dyck l r x⟩⟩

/-- **Inverse-free (AIR-constraint) form of the Dyck composition.**  Multiplying
    `fn_cons_dyck` through by `x` replaces the loose power with fingerprint components —
    `x·x^{2λL−1} = x^{2λL} = fn₁(l)²` — so every term is a product of components and `x`:

        `x·fn₃(cons(l,r)) = x²·fn₃(l) + fn₁(l)² + x·fn₁(l)²·fn₃(r)`.

    Completeness identity for honest fingerprints (no `x⁻¹` in the statement).  Not a
    soundness theorem for committed columns; at `x = 0` both sides are 0, so the equation
    constrains nothing there. -/
theorem fn_cons_dyck_constraint (l r : Noun) (x : K) :
    x * (fn (Noun.cell l r) x).2.2
      = x ^ 2 * (fn l x).2.2 + (fn l x).1 ^ 2 + x * (fn l x).1 ^ 2 * (fn r x).2.2 := by
  have hlam : 1 ≤ l.leaves := l.one_le_leaves
  have hsz : ((fn l x).1 : K) = x ^ l.leaves := rfl
  have hpow : x * x ^ (2 * l.leaves - 1) = (x ^ l.leaves) ^ 2 := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  rw [fn_cons_dyck, hsz, mul_add, mul_add, hpow]
  ring

/-- Division form of the Dyck composition, for witness generators that carry a committed
    `x⁻¹` (`fn₃(cons(l,r)) = x·fn₃(l) + fn₁(l)²·x⁻¹ + fn₁(l)²·fn₃(r)`), valid for `x ≠ 0`. -/
theorem fn_cons_dyck_inv (l r : Noun) {x : K} (hx : x ≠ 0) :
    (fn (Noun.cell l r) x).2.2
      = x * (fn l x).2.2 + (fn l x).1 ^ 2 * x⁻¹ + (fn l x).1 ^ 2 * (fn r x).2.2 := by
  have h := fn_cons_dyck_constraint l r x
  field_simp at h ⊢
  exact h

end Decomp

/-! ### Schwartz–Zippel / root counting -/

section SchwartzZippel
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A nonzero polynomial of natDegree `d` vanishes at at most `d` points of `K`. -/
theorem card_eval_zero_le (q : K[X]) (hq : q ≠ 0) :
    (Finset.univ.filter (fun r : K => q.eval r = 0)).card ≤ q.natDegree := by
  have hset : (Finset.univ.filter (fun r : K => q.eval r = 0)) = q.roots.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hq, IsRoot.def]
  rw [hset]
  calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' q

end SchwartzZippel

/-! ### The collision-soundness bound (lem:ion_univariate_sec, main.tex:1188) -/

section Collision
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **`ε_col^{Λ,𝔽}` — the single-instance collision-soundness error (main.tex:1204).**
    The paper names the collision error `ε^{Λ,𝔽}_col := ε(Λ,K)` (main.tex:1204) where
    `ε(Λ,K) = 2·(2Λ−1)/|K|` is the bound of `Lem:ion_univariate_sec` (main.tex:1192).
    We name it here as a standalone constant.  (`2·Λ−1` uses `ℕ` truncated subtraction; over
    the operative range `Λ ≥ 1` — always forced by `Noun.one_le_leaves` in every use below —
    it agrees with the paper's `2(2Λ−1)`; see `epsCol_eq` for the real-arithmetic form.) -/
def epsCol (Λ : ℕ) : ℚ := ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K)

omit [Field K] [DecidableEq K] in
/-- `ε_col` in the paper's real (non-truncated) arithmetic form `2(2Λ−1)/|K|`, valid for
    `Λ ≥ 1` (main.tex:1204/1192). -/
theorem epsCol_eq {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    epsCol (K := K) Λ = 2 * (2 * (Λ : ℚ) - 1) / (Fintype.card K) := by
  unfold epsCol
  have h1 : (1 : ℕ) ≤ 2 * Λ := by omega
  rw [Nat.cast_mul]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring

/-- **lem:ion_univariate_sec (main.tex:1188), cardinality form — tight bound.**
    For distinct field-nouns of length `≤ Λ`, the fingerprint `fn` collides for at most
    `2Λ − 1` values of `r ∈ K`.

    "distinct field-nouns" (the paper's `n₁ ≠ n₂` in `𝒩^{λ≤Λ}(𝔽)`, main.tex:1181) is the
    hypothesis `hne`: the NPR data `(dt, w) = (leafF, dyckBits)` differ.  (Operationally
    distinct `Noun`s that agree after casting leaves into `K` are the *same* field-noun and
    genuinely have equal fingerprints, so this is exactly the right premise.)

    Proof = univariate Schwartz–Zippel: at least one of the three difference polynomials
    `X^{λ₁}−X^{λ₂}`, `F_{d₁}−F_{d₂}`, `F_{w₁}−F_{w₂}` is nonzero of natDegree `≤ 2Λ−1`, and a
    collision forces `r` to be its root. -/
theorem collision_card_le_tight (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * Λ - 1 := by
  have hΛ : 1 ≤ Λ := le_trans n₁.one_le_leaves h₁
  -- reduce to: some difference polynomial `P` is nonzero, deg ≤ 2Λ−1, and collision ⟹ root
  suffices h : ∃ P : K[X], P ≠ 0 ∧ P.natDegree ≤ 2 * Λ - 1 ∧
      (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)) ⊆
      (Finset.univ.filter (fun r : K => P.eval r = 0)) by
    obtain ⟨P, hPne, hPdeg, hPsub⟩ := h
    calc (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card
        ≤ (Finset.univ.filter (fun r : K => P.eval r = 0)).card := Finset.card_le_card hPsub
      _ ≤ P.natDegree := card_eval_zero_le P hPne
      _ ≤ 2 * Λ - 1 := hPdeg
  by_cases hlam : n₁.leaves = n₂.leaves
  · -- equal length λ: distinguished by the leaf poly or the dyck poly
    simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
    rcases hne with hd | hd
    · -- leaf arrays differ (equal length λ)
      refine ⟨listPoly (NPR.leafF n₁) - listPoly (NPR.leafF n₂), ?_, ?_, ?_⟩
      · exact NPR.listPoly_sub_ne_zero (by simp [hlam]) hd
      · refine le_trans (NPR.listPoly_sub_natDegree_le (by simp [hlam])) ?_
        rw [NPR.leafF_length]; omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.1) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
    · -- dyck words differ (equal length 2(λ−1))
      refine ⟨listPoly (NPR.dyckBits n₁) - listPoly (NPR.dyckBits n₂), ?_, ?_, ?_⟩
      · refine NPR.listPoly_sub_ne_zero ?_ hd
        have e1 := NPR.dyckBits_length (K := K) n₁
        have e2 := NPR.dyckBits_length (K := K) n₂
        omega
      · refine le_trans (NPR.listPoly_sub_natDegree_le ?_) ?_
        · have e1 := NPR.dyckBits_length (K := K) n₁
          have e2 := NPR.dyckBits_length (K := K) n₂
          omega
        · have e1 := NPR.dyckBits_length (K := K) n₁
          omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.2) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
  · -- lengths differ: distinguished by the first component X^{λ}
    refine ⟨X ^ n₁.leaves - X ^ n₂.leaves, ?_, ?_, ?_⟩
    · intro h
      have hcoeff := congrArg (fun q => Polynomial.coeff q n₁.leaves) h
      simp only [coeff_sub, coeff_X_pow, coeff_zero, ite_eq_right hlam, sub_zero] at hcoeff
      exact one_ne_zero hcoeff
    · refine le_trans (natDegree_sub_le _ _) ?_
      rw [natDegree_X_pow, natDegree_X_pow, max_le_iff]; omega
    · intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      have := congrArg (fun x => x.1) hr.2
      simp only [NPR.fn] at this
      rw [eval_sub, eval_X_pow, eval_X_pow, sub_eq_zero]; exact this

/-- **lem:ion_univariate_sec (main.tex:1188), cardinality form — paper's stated bound.**
    The collision set has size `≤ 2(2Λ−1)` (the constant printed in the paper; the tight
    bound `collision_card_le_tight` gives `2Λ−1`). -/
theorem collision_card_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * (2 * Λ - 1) :=
  le_trans (collision_card_le_tight Λ n₁ n₂ h₁ h₂ hne) (by omega)

/-- **lem:ion_univariate_sec (main.tex:1188), probability form.**  With the counting-measure
    convention, `Pr_{r∈K}[fn n₁ = fn n₂] ≤ 2(2Λ−1)/|K| = ε(Λ,K)`. -/
theorem collision_prob_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    have : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast collision_card_le Λ n₁ n₂ h₁ h₂ hne

/-- **lem:ion_univariate_sec (main.tex:1192), probability form in terms of `ε_col`.**
    Restatement of `collision_prob_le` against the named constant `epsCol` (main.tex:1204):
    `Pr_{r∈K}[fn n₁ = fn n₂; n₁ ≠ n₂] ≤ ε_col^{Λ,𝔽}`. -/
theorem collision_prob_le_epsCol (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ :=
  collision_prob_le Λ n₁ n₂ h₁ h₂ hne

end Collision

/-! ### Union bound over a table of nouns (corr:ion_single_security, main.tex:1197) -/

section Table
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `k² − k = k(k−1)` (Nat, robust to truncated subtraction). -/
private theorem sq_sub_self (k : ℕ) : k * k - k = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ n => rw [Nat.succ_sub_one, Nat.mul_succ]; omega

/-- **corr:ion_single_security (main.tex:1197), cardinality form.**  For a table of `k = |s|`
    nouns of length `≤ Λ`, the number of `r ∈ K` for which *some* pair of distinct nouns
    collides is `≤ k(k−1)·(2Λ−1)`.  (Union bound over ordered distinct index pairs, each
    contributing `≤ 2Λ−1` by `collision_card_le_tight`.) -/
theorem collision_table_card_le {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ s.card * (s.card - 1) * (2 * Λ - 1) := by
  classical
  set g : ι × ι → Finset K := fun ij =>
    Finset.univ.filter (fun r : K => NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))) with hg
  have hsub : (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
      NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))))
      ⊆ s.offDiag.biUnion g := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨ij, hij, hcol, hdi⟩ := hr.2
    refine Finset.mem_biUnion.mpr ⟨ij, hij, ?_⟩
    simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcol, hdi⟩
  have hcard : ∀ ij ∈ s.offDiag, (g ij).card ≤ 2 * Λ - 1 := by
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    by_cases hd : (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))
    · -- distinct: bound by the single-pair collision count
      refine le_trans (Finset.card_le_card ?_)
        (collision_card_le_tight Λ (f ij.1) (f ij.2) (hf _ hi) (hf _ hj) hd)
      intro r hr
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hr.1
    · -- equal field-nouns: the filtered set is empty
      have hempty : g ij = ∅ := by
        simp only [hg, Finset.filter_eq_empty_iff]
        intro r _
        rintro ⟨_, hdiff⟩
        exact hd hdiff
      rw [hempty]; simp
  calc (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
          NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
          (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
            ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ (s.offDiag.biUnion g).card := Finset.card_le_card hsub
    _ ≤ ∑ _ij ∈ s.offDiag, (2 * Λ - 1) :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum hcard)
    _ = s.offDiag.card * (2 * Λ - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = s.card * (s.card - 1) * (2 * Λ - 1) := by
        rw [Finset.offDiag_card, sq_sub_self]

/-- Casting helper: `↑(k(k−1)) = k(k−1)` bridging `ℕ` truncated subtraction into `ℚ`. -/
private theorem natCast_mul_pred (k : ℕ) : ((k * (k - 1) : ℕ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) := by
  rcases k with _ | k
  · simp
  · push_cast; ring

/-- **corr:ion_single_security (main.tex:1197), probability form — union bound.**  With
    `ε := ε_col = 2(2Λ−1)/|K|`, the probability that some pair among `k = |s|` nouns collides
    is `≤ ε · k(k−1)/2`.  This is the paper's second (union-bound) inequality, main.tex:1200.

    ⚠ **The paper's FIRST (tight) inequality `Pr ≤ 1 − (1−ε)^{k(k−1)/2}` is NOT proven here,
    and is not soundly provable in this model.**  The paper's proof (main.tex:2361) obtains it
    by asserting "the probability of no table collisions is `(1−p)^{k(k−1)/2}`", i.e. by
    treating the `k(k−1)/2` pairwise collision events as *independent*.  In our (and the
    paper's real) probability model those events all share the SAME random `r ∈ K`, so they
    are NOT independent, and a product/independence bound is unavailable: the only estimate the
    root-counting machinery yields is the ADDITIVE union bound (`card_biUnion_le`), giving the
    `≤ ε·k(k−1)/2` below.  The product form is moreover genuinely FALSE in the worst case
    admitted by our per-pair root-count bounds: for `m := k(k−1)/2` pairwise collision sets
    that are pairwise disjoint (each of the maximal `2Λ−1` roots) and together partition `K`,
    the collision probability is `1`, which exceeds `1−(1−ε)^m < 1`.  Consistently, our proven
    union bound `ε·m` is `≥` the tight `1−(1−ε)^m` (Bernoulli, `one_sub_one_sub_pow_le`; equality
    only in the degenerate `ε = 0` / `m ≤ 1` cases, strict for `m ≥ 2, ε > 0`), so the tight
    expression is a stronger claim that this model cannot license.  The union bound below is the
    rigorous, model-faithful claim; the paper describes a "non-optimal but easier to show" bound
    (main.tex:2361) which is what we prove here. -/
theorem collision_table_prob_le {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
          * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    have : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  have hcard := collision_table_card_le (K := K) Λ s f hf
  have hne0 : (Fintype.card K : ℚ) ≠ 0 := ne_of_gt hpos
  rw [div_le_iff₀ hpos]
  -- the two `|K|`s cancel; both sides reduce to `k(k−1)·(2Λ−1)`
  have hrhs : (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
        * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) * (Fintype.card K)
      = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
    field_simp
    push_cast
    ring
  rw [hrhs]
  calc ((_ : ℕ) : ℚ) ≤ ((s.card * (s.card - 1) * (2 * Λ - 1) : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
        rw [Nat.cast_mul, natCast_mul_pred]

/-- **corr:ion_single_security (main.tex:1197), union bound in terms of `ε_col`.**
    Restatement of `collision_table_prob_le` against the named constant `epsCol`
    (main.tex:1204): `Pr[∃ colliding pair] ≤ ε_col^{Λ,𝔽} · k(k−1)/2`. -/
theorem collision_table_prob_le_epsCol {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) :=
  collision_table_prob_le Λ s f hf

/-- **Bernoulli's inequality (the paper's `1 − (1−ε)^m < ε·m` step, main.tex:1200/2361).**
    For any `ε ≤ 2` and `m : ℕ`, `1 − (1−ε)^m ≤ m·ε`.  This is the pure real inequality
    relating the paper's two collision-error expressions: the tight
    `1 − (1−ε)^{k(k−1)/2}` and the union bound `ε·k(k−1)/2` (`m = k(k−1)/2`).

    NOTE: this lemma establishes only the *arithmetic* relation `tight ≤ union`.  It does
    NOT (and cannot, in this shared-randomness model) establish that the collision
    probability is bounded by the tight expression — see the ⚠ note on
    `collision_table_prob_le`.  It is exactly what shows the union bound we DO prove is the
    weaker (larger) of the paper's two stated bounds, faithfully reproducing the paper's
    `<` chain. -/
theorem one_sub_one_sub_pow_le (ε : ℚ) (hε : ε ≤ 2) (m : ℕ) :
    1 - (1 - ε) ^ m ≤ (m : ℚ) * ε := by
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) m
  have hmul : (m : ℚ) * (-ε) = -((m : ℚ) * ε) := by ring
  have h1 : (1 : ℚ) + -ε = 1 - ε := by ring
  rw [hmul, h1] at hb
  linarith

end Table

end NPR
end Nock
