/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li
-/
module

public import LeanPool.EilenbergZilber.Bisimplicial
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Eilenberg–Mac Lane derived-operator API for the normalized Eilenberg–Zilber homotopy

This file builds the **tiny, local derived-operator API** needed to formalize Eilenberg–Mac Lane's
*recursive* construction of the Eilenberg–Zilber homotopy `Φ` (Eilenberg–Mac Lane II, Thm 2.1a,
the identity `∂Φ + Φ∂ = ∇f − i` modulo norms). It is the input to
`eilenbergZilberNormalized` in `BisimplicialNormalized.lean`.

We deliberately **do not** use an explicit closed-form homotopy; the literature only ever proves
the contraction identity via the recursion + derived operators, so we follow EM directly.

## Design

EM's "natural operators" `M : (K×L)_s → (K×L)_q` (their (2.10)) are, on a bisimplicial object `X`,
exactly finite `ℤ`-linear combinations of **letters**: a pair of `SimplexCategory` maps
`(β, γ) : ⟦q⟧ ⟶ ⟦s⟧` acting on the diagonal `F₂.obj X = diag X` by

`(X.obj ⟦s⟧).map γ.op ≫ (X.map β.op).app ⟦q⟧ : X_{s,s} ⟶ X_{q,q}`.

* `OpLetter s q` — one such pair, `DerivedOp s q := OpLetter s q →₀ ℤ` — a formal `ℤ`-combination.
* `DerivedOp.realize X` — realize a formal operator as an actual degreewise hom on `F₂.obj X`.
* `DerivedOp.prime` — EM's derived operator `M ↦ M'` (prepend the 0-th coface `δ⁰` to each letter).
* `DerivedOp.Frontal` — every letter fixes the bottom vertex (avoids the 0-th face `F₀`).

"Modulo norms" is represented (per the project's `PInfty` strategy) by postcomposing with
`retractionN₂ X = PInftyToNormalizedMooreComplex (diag X)`: a term is a *norm* iff it dies after
`≫ retractionN₂`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace LeanPool.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category C] [Abelian C]

/-! ### Operators as formal `ℤ`-combinations of letters -/

/-- A **letter**: a pair of `SimplexCategory` maps `⟦q⟧ ⟶ ⟦s⟧`. The `fst` map acts on the
horizontal (first / `K`) simplicial variable and `snd` on the vertical (second / `L`) one.
Realized on a bisimplicial object it gives a single summand `X_{s,s} ⟶ X_{q,q}` of an EM
natural operator (their (2.10)). -/
structure OpLetter (s q : ℕ) where
  /-- Horizontal (`K`-side) `SimplexCategory` map. -/
  fst : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌
  /-- Vertical (`L`-side) `SimplexCategory` map. -/
  snd : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌

noncomputable instance (s q : ℕ) : DecidableEq (OpLetter s q) := Classical.decEq _

/-- An EM natural operator `(K×L)_s → (K×L)_q` (their (2.10)): a finite `ℤ`-linear combination of
letters, with uniqueness of representation supplied by carrying the representation as data. -/
abbrev DerivedOp (s q : ℕ) := OpLetter s q →₀ ℤ

/-- Realize a single letter as a degreewise hom on the diagonal complex `F₂.obj X`. -/
noncomputable def OpLetter.realize {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) :
    (F₂.obj X).X s ⟶ (F₂.obj X).X q :=
  (X.obj (Opposite.op ⦋s⦌)).map l.snd.op ≫ (X.map l.fst.op).app (Opposite.op ⦋q⦌)

/-- Realize a formal operator as a degreewise hom on `F₂.obj X` (`ℤ`-linear extension of
`OpLetter.realize`). -/
noncomputable def DerivedOp.realize {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (F₂.obj X).X s ⟶ (F₂.obj X).X q :=
  M.sum fun l c => c • l.realize X

/-! ### The derived operator `M ↦ M'` (EM (2.10)) -/

/-- The 0-th-coface shift of a monotone map: `0 ↦ 0`, `j+1 ↦ θ(j)+1`. This is EM's `δ⁰`
prepending used to define the derived operator. -/
def primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋s + 1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j =>
        ⟨min (if (j : ℕ) = 0 then 0
              else (SimplexCategory.Hom.toOrderHom θ
                ⟨(j : ℕ) - 1, (by have := j.isLt; omega : (j : ℕ) - 1 < q + 1)⟩ : ℕ) + 1) (s + 1),
          by omega⟩
      monotone' := by
        intro a b hab
        have hab' : (a : ℕ) ≤ (b : ℕ) := hab
        simp only [Fin.mk_le_mk]
        split_ifs with ha hb hb
        · omega
        · omega
        · omega
        · have hmono : (SimplexCategory.Hom.toOrderHom θ
              ⟨(a : ℕ) - 1, (by have := a.isLt; omega : (a : ℕ) - 1 < q + 1)⟩ : ℕ) ≤
              (SimplexCategory.Hom.toOrderHom θ
              ⟨(b : ℕ) - 1, (by have := b.isLt; omega : (b : ℕ) - 1 < q + 1)⟩ : ℕ) :=
            (SimplexCategory.Hom.toOrderHom θ).monotone (by simp only [Fin.mk_le_mk]; omega)
          omega }

/-- The derived operator on a single letter: prime both `SimplexCategory` maps. -/
def OpLetter.prime {s q : ℕ} (l : OpLetter s q) : OpLetter (s + 1) (q + 1) :=
  ⟨primeHom l.fst, primeHom l.snd⟩

/-- EM's **derived operator** `M ↦ M'` (their (2.10)): prime every letter, `ℤ`-linearly. -/
noncomputable def DerivedOp.prime {s q : ℕ} (M : DerivedOp s q) : DerivedOp (s + 1) (q + 1) :=
  Finsupp.mapDomain OpLetter.prime M

/-! ### Composition of operators (vertical, on the diagonal) -/

/-- Composition of letters: `comp l₂ l₁` realizes to `realize l₁ ≫ realize l₂` (apply `l₁` then
`l₂`). Horizontal and vertical maps compose independently. -/
def OpLetter.comp {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) : OpLetter s r :=
  ⟨l₂.fst ≫ l₁.fst, l₂.snd ≫ l₁.snd⟩

/-- `ℤ`-bilinear composition of operators (apply `M₁` then `M₂`). -/
noncomputable def DerivedOp.comp {s q r : ℕ} (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    DerivedOp s r :=
  M₁.sum fun l₁ c₁ => M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c₁ * c₂)

/-! ### Functoriality / `ℤ`-linearity of `realize`

These let the abstract operator identities (`prime_comp_truncBoundary`, `lastFace_comp_prime`,
`boundary_comp_D0`, …) be pushed to genuine hom identities on `F₂.obj X`, so the EM induction can
run at the operator level and only be realized at the end. -/

@[simp] lemma realize_zero {s q : ℕ} (X : BisimplicialObject C) :
    (0 : DerivedOp s q).realize X = 0 := by
  simp [DerivedOp.realize]

@[simp] lemma realize_single {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) (c : ℤ) :
    DerivedOp.realize X (Finsupp.single l c) = c • l.realize X := by
  simp [DerivedOp.realize, Finsupp.sum_single_index]

lemma realize_add {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M + N).realize X = M.realize X + N.realize X := by
  simp [DerivedOp.realize, Finsupp.sum_add_index', zero_smul, add_smul]

lemma realize_neg {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (-M).realize X = -(M.realize X) := by
  simp [DerivedOp.realize, Finsupp.sum_neg_index, neg_smul]

lemma realize_sub {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M - N).realize X = M.realize X - N.realize X := by
  simp [sub_eq_add_neg, realize_add, realize_neg]

private noncomputable def realizeAddMonoidHom {s q : ℕ} (X : BisimplicialObject C) :
    DerivedOp s q →+ ((F₂.obj X).X s ⟶ (F₂.obj X).X q) where
  toFun M := M.realize X
  map_zero' := realize_zero X
  map_add' := realize_add X

lemma realize_zsmul {s q : ℕ} (X : BisimplicialObject C) (c : ℤ) (M : DerivedOp s q) :
    (c • M).realize X = c • M.realize X :=
  map_zsmul (realizeAddMonoidHom X) c M

/-- A single composed letter realizes to the composition of the realizations (the Pattern-5
bifunctor merge: interleave the horizontal/vertical legs via naturality of `X.map _`). -/
private lemma OpLetter.realize_comp {s q r : ℕ} (X : BisimplicialObject C) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) :
    (l₂.comp l₁).realize X = l₁.realize X ≫ l₂.realize X := by
  change (X.obj (Opposite.op ⦋s⦌)).map (l₂.snd ≫ l₁.snd).op ≫
      (X.map (l₂.fst ≫ l₁.fst).op).app (Opposite.op ⦋r⦌) =
    ((X.obj (Opposite.op ⦋s⦌)).map l₁.snd.op ≫ (X.map l₁.fst.op).app (Opposite.op ⦋q⦌)) ≫
      ((X.obj (Opposite.op ⦋q⦌)).map l₂.snd.op ≫ (X.map l₂.fst.op).app (Opposite.op ⦋r⦌))
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% ((X.map l₁.fst.op).naturality l₂.snd.op)]

/-- `comp` is additive in its right argument. -/
private lemma DerivedOp.comp_add_right {s q r : ℕ} (M₂ : DerivedOp q r) (M N : DerivedOp s q) :
    M₂.comp (M + N) = M₂.comp M + M₂.comp N := by
  simp only [DerivedOp.comp]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [add_mul, Finsupp.single_add]; rw [Finsupp.sum_add]

/-- `comp` is additive in its left argument. -/
private lemma DerivedOp.add_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M + N).comp K = M.comp K + N.comp K := by
  simp only [DerivedOp.comp]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro l₁ _
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [mul_add, Finsupp.single_add]

/-- `comp` on a right `single`. -/
private lemma DerivedOp.comp_single_right {s q r : ℕ} (M₂ : DerivedOp q r) (l₁ : OpLetter s q)
    (c : ℤ) :
    M₂.comp (Finsupp.single l₁ c) = M₂.sum fun l₂ c₂ => Finsupp.single (l₂.comp l₁) (c * c₂) := by
  rw [DerivedOp.comp, Finsupp.sum_single_index (by simp)]

/-- `comp` of two `single`s. -/
private lemma DerivedOp.single_comp_single {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q)
    (c₂ c₁ : ℤ) :
    DerivedOp.comp (Finsupp.single l₂ c₂) (Finsupp.single l₁ c₁) =
      Finsupp.single (l₂.comp l₁) (c₁ * c₂) := by
  rw [DerivedOp.comp_single_right, Finsupp.sum_single_index (by simp)]

/-- `realize` turns operator composition into hom composition (contravariantly: apply `M₁` then
`M₂`). The functoriality fact that drives the operator-level induction. Proved by reducing to the
single-single case (`OpLetter.realize_comp`) via bilinearity of `comp` and additivity of
`realize`. -/
lemma realize_comp {s q r : ℕ} (X : BisimplicialObject C) (M₂ : DerivedOp q r)
    (M₁ : DerivedOp s q) :
    (M₂.comp M₁).realize X = M₁.realize X ≫ M₂.realize X := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, realize_add, ih, realize_add, Preadditive.add_comp]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, realize_add, ih₂, realize_add, Preadditive.comp_add]
      congr 1
      simp only [DerivedOp.single_comp_single, realize_single, OpLetter.realize_comp,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
      rw [mul_comm c₂ c₁]

/-- The identity letter realizes to the identity hom. -/
lemma realize_single_id {q : ℕ} (X : BisimplicialObject C) :
    DerivedOp.realize X (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp q q) = 𝟙 ((F₂.obj X).X q) := by
  rw [realize_single, one_smul]
  change (X.obj (Opposite.op ⦋q⦌)).map (𝟙 _).op ≫ (X.map (𝟙 _).op).app (Opposite.op ⦋q⦌) =
    𝟙 ((X.obj (Opposite.op ⦋q⦌)).obj (Opposite.op ⦋q⦌))
  simp

/-! ### Distinguished operators: degeneracy `D₀`, faces, boundaries -/

/-- The 0-th degeneracy operator `D₀ = s₀ × s₀ : (K×L)_q → (K×L)_{q+1}` of EM (2.13). -/
noncomputable def D0op (q : ℕ) : DerivedOp q (q + 1) :=
  Finsupp.single ⟨SimplexCategory.σ 0, SimplexCategory.σ 0⟩ 1

/-- The `i`-th face operator `F_i = δ_i × δ_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def faceOp (q : ℕ) (i : Fin (q + 2)) : DerivedOp (q + 1) q :=
  Finsupp.single ⟨SimplexCategory.δ i, SimplexCategory.δ i⟩ 1

/-- The **last face** `F₀` in EM's `∂ = F₀ − ∂'` decomposition — here the 0-th face `F_0`. -/
noncomputable def lastFaceOp (q : ℕ) : DerivedOp (q + 1) q :=
  faceOp q 0

/-- The **truncated boundary** `∂' = Σ_{i≥1} (-1)^{i-1} F_i` (the part of the boundary omitting the
0-th face), so that the full boundary is `∂ = F₀ − ∂'`. -/
noncomputable def truncBoundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i.succ

/-- The full simplicial boundary operator `∂ = Σ_i (-1)^i F_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def boundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i

/-! ### Frontality -/

/-- A `SimplexCategory` map is **frontal** if it fixes the bottom vertex `0` (equivalently its
operator word avoids the 0-th face `F₀`). -/
def IsFrontalHom {a b : ℕ} (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌) : Prop :=
  SimplexCategory.Hom.toOrderHom f 0 = 0

/-- An operator is **frontal** (EM) if every letter in its support is frontal in both variables.
This is the property of **derived (primed) operators** — `primeHom` fixes `0`, so any `M.prime` is
frontal in this strong sense (`prime_frontal`). It is what the homotopy identity (2.3) consumes
(via `prime_comp_D0_of_frontal`). -/
def DerivedOp.Frontal {s q : ℕ} (M : DerivedOp s q) : Prop :=
  ∀ l ∈ M.support, IsFrontalHom l.fst ∧ IsFrontalHom l.snd

/-! ### The realized operators agree with the chain-complex data

These tie the formal operators to the actual differentials / maps on `F₂.obj X`, so the abstract
operator identities below can be transported to statements about `Homotopy.comm`. -/

/-- The realized `i`-th face is the `i`-th face of the diagonal simplicial object: the
horizontal/vertical legs of `⟨δ i, δ i⟩` reassemble into `(diag X).δ i` via naturality of
`X.map (δ i).op`. -/
lemma realize_faceOp (X : BisimplicialObject C) (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).realize X = (diag.obj X).δ i := by
  rw [faceOp, realize_single, one_smul, OpLetter.realize, SimplicialObject.δ, diag_obj_map]
  exact (X.map (SimplexCategory.δ i).op).naturality (SimplexCategory.δ i).op

/-- The realized boundary operator is the differential of `F₂.obj X`. -/
lemma realize_boundaryOp (X : BisimplicialObject C) (q : ℕ) :
    (boundaryOp q).realize X = (F₂.obj X).d (q + 1) q := by
  rw [show (F₂.obj X).d (q + 1) q
      = (AlternatingFaceMapComplex.obj (diag.obj X)).d (q + 1) q from rfl,
    AlternatingFaceMapComplex.obj_d_eq,
    show (boundaryOp q).realize X = realizeAddMonoidHom X (boundaryOp q) from rfl,
    boundaryOp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show realizeAddMonoidHom X (faceOp q i) = (faceOp q i).realize X from rfl,
    realize_faceOp]

/-- `∂ = F₀ − ∂'` (EM, just above (2.13)): the full boundary splits as the 0-th face minus the
truncated boundary. -/
lemma boundaryOp_eq (q : ℕ) :
    boundaryOp q = lastFaceOp q - truncBoundaryOp q := by
  rw [boundaryOp, Fin.sum_univ_succ, lastFaceOp, truncBoundaryOp, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_zsmul]

/-! ### Algebra of the derived operator `prime`

`prime` is additive and **multiplicative** (`(β∘γ)' = β'∘γ'`), and on faces it shifts the index
(`prime(δ_i) = δ_{i+1}`). Consequently EM's truncated boundary is *literally* the derived operator
of the boundary: `∂' = prime(∂)` (`prime_boundaryOp`). These are exactly what make EM's family
identity `∂'M' = M'∂'` hold — it is just `prime` applied (via `prime_comp`) to the chain-map
condition `∂M = M∂`, with no ad-hoc index juggling. This is why we no longer state a separate
(mis-indexed) `prime_comp_truncBoundary`. -/

@[simp] lemma prime_zero {s q : ℕ} : (0 : DerivedOp s q).prime = 0 := by
  simp [DerivedOp.prime]

lemma prime_add {s q : ℕ} (M N : DerivedOp s q) : (M + N).prime = M.prime + N.prime := by
  simp [DerivedOp.prime, Finsupp.mapDomain_add]

/-- The 0-th coface shift is **multiplicative**: `(g ≫ f)' = g' ≫ f'`. The combinatorial core of
`prime`-multiplicativity (a `SimplexCategory` identity, no `Finsupp`). -/
lemma primeHom_comp {s q r : ℕ} (g : (⦋r⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (f : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    primeHom (g ≫ f) = primeHom g ≫ primeHom f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  apply Fin.ext
  by_cases hj : (j : ℕ) = 0
  · simp [hj]
  · generalize_proofs h1 h2 h3
    simp only [ite_eq_right hj]
    have hbq : ((SimplexCategory.Hom.toOrderHom g) ⟨(j : ℕ) - 1, h1⟩ : ℕ) < q + 1 := Fin.isLt _
    rw [ite_eq_right (by omega)]
    congr 2
    congr 1
    congr 1
    apply Fin.ext
    set t : ℕ := ↑((SimplexCategory.Hom.toOrderHom g) ⟨(j : ℕ) - 1, h1⟩)
    have ht : t < q + 1 := by simpa [t] using hbq
    have hmin : min (t + 1) (q + 1) = t + 1 := Nat.min_eq_left (Nat.succ_le_of_lt ht)
    simp [t, hmin]

/-- Letter-level multiplicativity of `prime`: `(l₂ ∘ l₁)' = l₂' ∘ l₁'`. -/
lemma OpLetter.prime_comp {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) :
    (l₂.comp l₁).prime = l₂.prime.comp l₁.prime := by
  simp only [OpLetter.prime, OpLetter.comp, primeHom_comp]

/-- **`prime` is multiplicative** (`(β∘γ)' = β'∘γ'`), so `(M₂ ∘ M₁)' = M₂' ∘ M₁'`. The key fact
behind EM's `∂'M' = M'∂'`. Reduced to the single–single case `OpLetter.prime_comp` by bilinearity
of `comp` and additivity of `prime`. -/
lemma prime_comp {s q r : ℕ} (M₂ : DerivedOp q r) (M₁ : DerivedOp s q) :
    (M₂.comp M₁).prime = M₂.prime.comp M₁.prime := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp, DerivedOp.prime]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, prime_add, ih, prime_add, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp, DerivedOp.prime]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, prime_add, ih₂, prime_add, DerivedOp.add_comp]
      congr 1
      simp only [DerivedOp.single_comp_single, DerivedOp.prime, Finsupp.mapDomain_single,
        OpLetter.prime_comp]

private lemma δ_toOrderHom_apply {n : ℕ} (k : Fin (n + 2))
    (j : Fin ((⦋n⦌ : SimplexCategory).len + 1)) :
    (SimplexCategory.δ k).toOrderHom j = k.succAbove j := rfl

private lemma σ_toOrderHom_apply {n : ℕ} (k : Fin (n + 1))
    (j : Fin ((⦋n + 1⦌ : SimplexCategory).len + 1)) :
    (SimplexCategory.σ k).toOrderHom j = k.predAbove j := rfl

/-- `primeHom` shifts the face map index: `prime(δ_i) = δ_{i+1}`. The combinatorial core of
`prime_faceOp`. -/
lemma primeHom_δ {q : ℕ} (i : Fin (q + 2)) :
    primeHom (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  simp only [δ_toOrderHom_apply]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  split_ifs <;>
    (try simp_all only [Fin.val_castSucc, Fin.val_succ]) <;> omega

/-- **`prime` shifts faces**: `prime(δ_i) = δ_{i+1}` (prepending the `0`-th vertex pushes the
omitted vertex up by one). -/
lemma prime_faceOp (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).prime = faceOp (q + 1) i.succ := by
  simp only [faceOp, DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.prime, primeHom_δ]

/-- `primeHom` shifts the degeneracy map index: `prime(σ_i) = σ_{i+1}` (prepending the `0`-th vertex
pushes the doubled vertex up by one). The degeneracy analog of `primeHom_δ`. -/
lemma primeHom_σ {q : ℕ} (i : Fin (q + 1)) :
    primeHom (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  simp only [σ_toOrderHom_apply, Fin.predAbove]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_pred, Fin.coe_castPred] <;> omega

/-- `prime` bundled as an additive hom, so it distributes over `Finset.sum` (`map_sum`) and
`zsmul` (`map_zsmul`). -/
private noncomputable def primeAddHom {s q : ℕ} :
    DerivedOp s q →+ DerivedOp (s + 1) (q + 1) where
  toFun := DerivedOp.prime
  map_zero' := prime_zero
  map_add' := prime_add

/-- **`∂' = prime(∂)`** (EM): the truncated boundary is the derived operator of the full boundary.
Note the degree shift — `prime` of the degree-`q` boundary is the truncated boundary at degree
`q+1` (this is the index offset that the literal EM transcription hides). -/
lemma prime_boundaryOp (q : ℕ) :
    (boundaryOp q).prime = truncBoundaryOp (q + 1) := by
  simp only [boundaryOp, truncBoundaryOp]
  rw [show (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i).prime
      = primeAddHom (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show primeAddHom (faceOp q i) = (faceOp q i).prime from rfl, prime_faceOp]

/-! ### Core derived-operator identities (EM I.3, used in the (2.13) induction) -/

/-- `primeHom θ` is frontal: it fixes the bottom vertex `0` (`primeHom` sends `0 ↦ 0`). -/
lemma primeHom_frontal {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    IsFrontalHom (primeHom θ) := by
  simp [IsFrontalHom, primeHom]

/-- The derived operator preserves frontality (EM: `M'` is always frontal, since `primeHom` fixes
`0`). -/
lemma prime_frontal {s q : ℕ} (M : DerivedOp s q) : (M.prime).Frontal := by
  intro l hl
  have hl' := Finsupp.mapDomain_support hl
  rw [Finset.mem_image] at hl'
  obtain ⟨l', _, rfl⟩ := hl'
  exact ⟨primeHom_frontal _, primeHom_frontal _⟩

/-- For a **frontal** map (`θ 0 = 0`), the prepended vertex collapses against `σ 0`:
`primeHom θ ≫ σ 0 = σ 0 ≫ θ`. The combinatorial core of `prime_comp_D0_of_frontal`; frontality
is exactly what makes the two sides agree at the bottom vertex. -/
lemma primeHom_comp_degenZero {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (hθ : IsFrontalHom θ) :
    primeHom θ ≫ SimplexCategory.σ (0 : Fin (s + 1))
      = SimplexCategory.σ (0 : Fin (q + 1)) ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · -- `j = 0`: both sides land on the bottom vertex; `σ 0` and `primeHom` send `0 ↦ 0`, and
    -- `θ 0 = 0` (frontality) closes `0 = ↑(θ 0)`.
    apply Fin.ext
    simp only [IsFrontalHom] at hθ
    simp only [SimplexCategory.len_mk, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact (congrArg Fin.val hθ).symm
  · -- `j = k.succ`: `primeHom θ` gives `θ(k) + 1`, then `σ 0` (always `0 < θ(k)+1`) drops back to
    -- `θ(k) = min (θ k) s`, matching `θ (σ 0 (k.succ)) = θ k`.
    apply Fin.ext
    simp [primeHom, SimplexCategory.σ, Fin.predAbove]
    have hk := (SimplexCategory.Hom.toOrderHom θ k).isLt
    simp only [SimplexCategory.len_mk] at hk
    split_ifs <;> simp_all [Fin.lt_def]

/-- **Frontal ⟹ priming commutes with `D₀`** (EM, from Lemma I.3.3: `(β')^* D₀ = D₀ β^*`).
For a frontal operator, `M' ∘ D₀ = D₀ ∘ M`. -/
lemma prime_comp_D0_of_frontal {s q : ℕ} (M : DerivedOp s q) (hM : M.Frontal) :
    (M.prime).comp (D0op s) = (D0op q).comp M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f hlf hc ih =>
    have hl := hM l (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hlf, add_zero]
      exact hc)
    have hf : DerivedOp.Frontal f := fun l' hl' => hM l' (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by rintro rfl; exact hlf hl'), zero_add,
        ← Finsupp.mem_support_iff]
      exact hl')
    rw [prime_add, DerivedOp.add_comp, DerivedOp.comp_add_right, ih hf]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, D0op, D0op,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, one_mul, mul_one]
    congr 1
    simp only [OpLetter.comp, OpLetter.prime, primeHom_comp_degenZero l.fst hl.1,
      primeHom_comp_degenZero l.snd hl.2]

/-- The 0-th face "eats" the prepended vertex: `δ 0 ≫ primeHom θ = θ ≫ δ 0`. The combinatorial
core of `lastFace_comp_prime`. -/
lemma faceZero_comp_primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫ primeHom θ
      = θ ≫ SimplexCategory.δ (0 : Fin (s + 2)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  -- Unfold the two `δ 0` cofaces to `Fin.succAbove 0 = Fin.succ`, then `simp` evaluates the
  -- `primeHom` `if`/`min` (both legs send `j ↦ θ(j) + 1`); the leftover `↑(θ j) ≤ s` is `isLt`.
  dsimp only [SimplexCategory.δ, Fin.succAboveOrderEmb, OrderEmbedding.coe_ofStrictMono,
    Function.Embedding.coeFn_mk]
  simp only [SimplexCategory.mkHom, Fin.succAbove_zero, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, OrderEmbedding.coe_ofStrictMono, Fin.val_succ,
    Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, Fin.eta, Nat.add_min_add_right, Nat.add_right_cancel_iff, inf_eq_left]
  have hj := (SimplexCategory.Hom.toOrderHom θ j).isLt
  simp only [SimplexCategory.len_mk] at hj
  omega

/-- **`F₀ M' = M F₀`** (EM, Lemma I.3.3): dropping the bottom face commutes with priming. The one
derived-operator/boundary identity that is *not* a consequence of multiplicativity, since the
outer `F₀` is unprimed. -/
lemma lastFace_comp_prime {s q : ℕ} (M : DerivedOp s q) :
    (lastFaceOp q).comp (M.prime) = M.comp (lastFaceOp s) := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f _ _ ih =>
    rw [prime_add, DerivedOp.comp_add_right, ih, DerivedOp.add_comp]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, lastFaceOp, faceOp, lastFaceOp, faceOp,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, mul_one, one_mul]
    congr 1
    simp only [OpLetter.comp, OpLetter.prime, faceZero_comp_primeHom]

/-- Post-composition with `D₀` on the right, bundled additively so `map_sum`/`map_zsmul` distribute
it over the boundary sum. -/
private noncomputable def compRightD0 (q : ℕ) :
    DerivedOp (q + 2) (q + 1) →+ DerivedOp (q + 1) (q + 1) where
  toFun M := M.comp (D0op (q + 1))
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N _

/-- Pre-composition with `D₀` on the left, bundled additively. -/
private noncomputable def compLeftD0 (q : ℕ) :
    DerivedOp (q + 1) q →+ DerivedOp (q + 1) (q + 1) where
  toFun M := (D0op q).comp M
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.comp_add_right (D0op q) M N

/-- The `i ≥ 2` simplicial identity `F_{k+2} D₀ = D₀ F_{k+1}` at the operator level
(`δ_{k+2} ≫ σ_0 = σ_0 ≫ δ_{k+1}`). -/
private lemma faceSuccSucc_comp_D0 (q : ℕ) (k : Fin (q + 1)) :
    (faceOp (q + 1) k.succ.succ).comp (D0op (q + 1))
      = (D0op q).comp (faceOp q k.succ) := by
  rw [faceOp, D0op, D0op, faceOp, DerivedOp.single_comp_single,
    DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.comp]
  congr 1 <;>
    exact SimplexCategory.δ_comp_σ_of_gt (i := k.succ) (j := 0) (by simp [Fin.lt_def])

/-- The two unit faces `F_0 D₀ = F_1 D₀ = 1` (`δ_0 ≫ σ_0 = δ_1 ≫ σ_0 = 𝟙`); used to cancel the
first two terms of `∂ D₀`. -/
private lemma face_zero_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 3))).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1

private lemma face_one_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 2)).succ).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.comp]
  congr 1 <;> exact SimplexCategory.δ_comp_σ_succ

/-- Simplicial identity `∂ D₀ = D₀ ∂'` at the operator level.

Writing `∂ = F₀ - ∂'`, the terms `F₀ D₀` and `F₁ D₀` both equal the identity, so the remaining
faces assemble to `D₀ ∂'`. -/
lemma boundary_comp_D0 (q : ℕ) :
    (boundaryOp (q + 1)).comp (D0op (q + 1)) =
      (D0op q).comp (truncBoundaryOp q) := by
  have hL : (boundaryOp (q + 1)).comp (D0op (q + 1))
      = ∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • (faceOp (q + 1) i).comp (D0op (q + 1)) := by
    rw [boundaryOp,
      show (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i).comp (D0op (q + 1))
        = compRightD0 q (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul (compRightD0 q) _ _
  have hR : (D0op q).comp (truncBoundaryOp q)
      = ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • (D0op q).comp (faceOp q k.succ) := by
    rw [truncBoundaryOp,
      show (D0op q).comp (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ)
        = compLeftD0 q (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun k _ => map_zsmul (compLeftD0 q) _ _
  rw [hL, hR, Fin.sum_univ_succ, Fin.sum_univ_succ, face_zero_comp_D0, face_one_comp_D0]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, pow_zero, pow_one, one_smul,
    neg_one_zsmul]
  rw [add_neg_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [faceSuccSucc_comp_D0]
  congr 1
  rw [pow_succ, pow_succ]
  ring

/-! ### Killing norms with `PInfty`

For the homotopy identity, the relevant norms are the **diagonal** degenerate terms in `D(K×L)`.
They are detected by postcomposing with
`retractionN₂ = PInftyToNormalizedMooreComplex (diag X)`, which kills diagonal degeneracies of the
diagonal simplicial object.

The lemmas in this section package that kill mechanism in the forms used later by the EM
induction. -/

/-- The realization of a **diagonal letter** `⟨θ, θ⟩` is the diagonal map `(diag X).map θ.op`
(`realize_faceOp` generalized off the face case): the horizontal/vertical legs reassemble by
naturality of `X.map θ.op`. -/
lemma realize_diagLetter (X : BisimplicialObject C) {s q : ℕ}
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) = (diag.obj X).map θ.op := by
  rw [realize_single, one_smul, OpLetter.realize, diag_obj_map]
  exact (X.map θ.op).naturality θ.op

/-- A diagonal degeneracy `⟨θ, θ⟩` with `θ` non-monic is killed by `retractionN₂`.

Its realization is the diagonal map `(diag X).map θ.op`, and a non-monic `θ` is a simplicial
degeneracy, so `degeneracy_comp_PInfty` applies after factoring `PInfty` through the Moore
inclusion. -/
lemma realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono {s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) ≫ (retractionN₂ X).f q = 0 := by
  rw [realize_diagLetter]
  -- `(diag X).map θ.op` is a degeneracy of `diag X` (θ non-mono); factor `PInfty = retr ≫ incl`
  -- and cancel the mono Moore inclusion (Pattern 1).
  have : Mono ((inclusionOfMooreComplexMap (diag.obj X)).f q) := by
    rw [inclusionOfMooreComplexMap_f]; exact Subobject.arrow_mono _
  refine zero_of_comp_mono ((inclusionOfMooreComplexMap (diag.obj X)).f q) ?_
  exact (Category.assoc _ _ _).trans <|
    (congrArg ((diag.obj X).map θ.op ≫ ·)
      ((HomologicalComplex.comp_f _ _ q).symm.trans
        (congrArg (fun φ => HomologicalComplex.Hom.f φ q)
          (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (diag.obj X))))).trans
      (degeneracy_comp_PInfty (diag.obj X) q θ hθ)

/-- A diagonal degeneracy on the output side kills any composite after `retractionN₂`.

If `M = ⟨θ, θ⟩ ∘ N` with `θ` non-monic, then `realize M ≫ retractionN₂ = 0`. This is the form
used later, where the norm term is expressed as a diagonal degeneracy postcomposed with an
arbitrary operator. -/
lemma realize_comp_diagLetter_not_mono_comp_retractionN₂ {r s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
    DerivedOp.realize X (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N) ≫
        (retractionN₂ X).f q = 0 := by
  rw [realize_comp, Category.assoc,
    realize_diagLetter_comp_retractionN₂_eq_zero_of_not_mono X θ hθ, Limits.comp_zero]

/-! ### The Eilenberg–Mac Lane homotopy `h = ∇f` and the recursion (2.13) -/

/- `hOp` is the formal derived operator representing `h = ∇f`. Later arguments use only its
realization and its formal interaction with `prime`, `comp`, and frontality, not the explicit
description of its letters. -/
/-- A single summand of `h = ∇f`: split `q = p + (q - p)`, apply the AW front/back
faces, then apply one `(p, q-p)` shuffle. The two `eqToHom`s transport across
`p + (q-p) = q`. -/
noncomputable def hLetter (q : ℕ) (p : Fin (q + 1)) (μ : Shuffle (p : ℕ) (q - p)) :
    OpLetter q q where
  fst :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleFstHom μ ≫ ιFront (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))
  snd :=
    eqToHom (congrArg SimplexCategory.mk (by omega : q = (p : ℕ) + (q - p))) ≫
      shuffleSndHom μ ≫ ιBack (p : ℕ) (q - p) ≫
        eqToHom (congrArg SimplexCategory.mk (by omega : (p : ℕ) + (q - p) = q))

/-- `h = ∇f` as a derived operator: sum over the Alexander-Whitney split and then over
shuffles. -/
noncomputable def hOp (q : ℕ) : DerivedOp q q :=
  ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
    Finsupp.single (hLetter q p μ) μ.sign

omit [Abelian C] in
private lemma awShuffleLetter_core (X : BisimplicialObject C) (p r : ℕ) (μ : Shuffle p r) :
    (X.map (ιFront p r).op).app (Opposite.op ⦋p + r⦌) ≫
        (X.obj (Opposite.op ⦋p⦌)).map (ιBack p r).op ≫
          (X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌) =
      (X.obj (Opposite.op ⦋p + r⦌)).map (shuffleSndHom μ ≫ ιBack p r).op ≫
        (X.map (shuffleFstHom μ ≫ ιFront p r).op).app (Opposite.op ⦋p + r⦌) := by
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, ← op_comp]
  slice_lhs 1 2 =>
    rw [← (X.map (ιFront p r).op).naturality (shuffleSndHom μ ≫ ιBack p r).op]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [← NatTrans.comp_app]

private lemma hLetter_realize_of_add_eq (X : BisimplicialObject C) (p r q : ℕ)
    (h : p + r = q) (μ : Shuffle p r) :
    (OpLetter.mk
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleFstHom μ ≫ ιFront p r ≫
        eqToHom (congrArg SimplexCategory.mk h))
      (eqToHom (congrArg SimplexCategory.mk h.symm) ≫ shuffleSndHom μ ≫ ιBack p r ≫
        eqToHom (congrArg SimplexCategory.mk h))).realize X =
      eqToHom (by
        simp only [F₂, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
        rw [← h]) ≫
        awComponent X p r ≫
          ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌)) ≫
          eqToHom (by
            simp only [F₂, Functor.comp_obj, alternatingFaceMapComplex_obj_X, diag_obj_obj]
            rw [← h]) := by
  subst q
  change (X.obj (Opposite.op ⦋p + r⦌)).map
        (eqToHom rfl ≫ shuffleSndHom μ ≫ ιBack p r ≫ eqToHom rfl).op ≫
      (X.map (eqToHom rfl ≫ shuffleFstHom μ ≫ ιFront p r ≫ eqToHom rfl).op).app
        (Opposite.op ⦋p + r⦌) =
    𝟙 ((X.obj (Opposite.op ⦋p + r⦌)).obj (Opposite.op ⦋p + r⦌)) ≫ awComponent X p r ≫
      ((X.obj (Opposite.op ⦋p⦌)).map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + r⦌)) ≫
      𝟙 ((X.obj (Opposite.op ⦋p + r⦌)).obj (Opposite.op ⦋p + r⦌))
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, awComponent, Category.assoc]
  exact (awShuffleLetter_core X p r μ).symm

/-- Realization of one `hLetter` summand is the corresponding `awComponent ≫ ezComponent` shuffle
summand. This is the Pattern-5 merge of the AW front/back faces with the shuffle degeneracies. -/
lemma hLetter_realize (X : BisimplicialObject C) (q : ℕ) (p : Fin (q + 1))
    (μ : Shuffle (p : ℕ) (q - p)) :
    (hLetter q p μ).realize X =
      eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫
        awComponent X p (q - p) ≫
          ((X.obj (Opposite.op ⦋(p : ℕ)⦌)).map (shuffleSndHom μ).op ≫
            (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋(p : ℕ) + (q - p)⦌)) ≫
          eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) := by
  have hpq : (p : ℕ) + (q - p) = q :=
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)
  simpa [hLetter, hpq] using hLetter_realize_of_add_eq X (p : ℕ) (q - p) q hpq μ

/-- `hOp` realizes to the composite `alexanderWhitney ≫ shuffleMap = ∇f` on `F₂.obj X`. -/
lemma realize_hOp (X : BisimplicialObject C) (q : ℕ) :
    (hOp q).realize X = (alexanderWhitney X ≫ shuffleMap X).f q := by
  have hrealize :
      (hOp q).realize X =
        ∑ p : Fin (q + 1), ∑ μ : Shuffle (p : ℕ) (q - p),
          μ.sign • (hLetter q p μ).realize X := by
    change realizeAddMonoidHom X (hOp q) = _
    rw [hOp, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp [realizeAddMonoidHom, realize_single]
  rw [hrealize, alexanderWhitney_comp_shuffleMap_f]
  simp only [hLetter_realize, ezComponent, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]


/-- **The Eilenberg–Mac Lane homotopy `Φ`** as a derived operator, defined by EM's recursion (2.13):
`Φ₀ = 0` and `Φ_{q} = − Φ'_{q-1} + h'_{q} D₀` for `q > 0`. Here `Φ_q : (K×L)_q → (K×L)_{q+1}`. -/
noncomputable def phiOp : (q : ℕ) → DerivedOp q (q + 1)
  | 0 => 0
  | (q + 1) => -(phiOp q).prime + (hOp (q + 1)).prime.comp (D0op (q + 1))

/-- Composition of frontal `SimplexCategory` maps is frontal (`0 ↦ 0 ↦ 0`). -/
lemma IsFrontalHom.comp {a b c : ℕ} {f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌}
    {g : (⦋b⦌ : SimplexCategory) ⟶ ⦋c⦌} (hf : IsFrontalHom f) (hg : IsFrontalHom g) :
    IsFrontalHom (f ≫ g) := by
  simp only [IsFrontalHom, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply] at *
  rw [hf, hg]

/-- The zero operator is (vacuously) frontal. -/
lemma DerivedOp.Frontal.zero {s q : ℕ} : (0 : DerivedOp s q).Frontal := by
  intro l hl
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hl

/-- A single frontal letter gives a frontal operator. -/
lemma DerivedOp.Frontal.single {s q : ℕ} (l : OpLetter s q) (c : ℤ)
    (hl : IsFrontalHom l.fst ∧ IsFrontalHom l.snd) :
    DerivedOp.Frontal (Finsupp.single l c) := by
  intro l' hl'
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hl')]
  exact hl

/-- Frontality is preserved by negation (same support). -/
lemma DerivedOp.Frontal.neg {s q : ℕ} {M : DerivedOp s q} (hM : M.Frontal) : (-M).Frontal :=
  fun l hl => hM l (by simpa using hl)

/-- Frontality is preserved by addition (support ⊆ union). -/
lemma DerivedOp.Frontal.add {s q : ℕ} {M N : DerivedOp s q} (hM : M.Frontal) (hN : N.Frontal) :
    (M + N).Frontal := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
  · exact hM l h
  · exact hN l h

/-! ### Packaging the homotopy on `F₂` (raw, modulo norms) -/

/-- `Φ` packaged as a degree-`+1` `Homotopy.hom` family on `F₂.obj X` (the unnormalized diagonal):
`phiOp i` realized (transported along `j = i+1`) on the single nonzero entry, `0` elsewhere. -/
noncomputable def phiHomRaw (X : BisimplicialObject C) (i j : ℕ) :
    (F₂.obj X).X i ⟶ (F₂.obj X).X j :=
  if h : j = i + 1 then (phiOp i).realize X ≫ eqToHom (by rw [h]) else 0

/-- `prevD` of `phiHomRaw` is the realized operator `∂Φ` (apply `Φ` then `∂`):
`prevD n (phiHomRaw X) = (phiOp n).realize X ≫ (boundaryOp n).realize X`. -/
lemma prevD_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    prevD n (phiHomRaw X) = DerivedOp.realize X ((boundaryOp n).comp (phiOp n)) := by
  rw [prevD_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dite_eq_left rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- `dNext` of `phiHomRaw` (at `n+1`) is the realized operator `Φ∂` (apply `∂` then `Φ`):
`dNext (n+1) (phiHomRaw X) = (boundaryOp n).realize X ≫ (phiOp n).realize X`. -/
lemma dNext_phiHomRaw (X : BisimplicialObject C) (n : ℕ) :
    dNext (n + 1) (phiHomRaw X) = DerivedOp.realize X ((phiOp n).comp (boundaryOp n)) := by
  rw [dNext_eq (phiHomRaw X) (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), phiHomRaw,
    dite_eq_left rfl, eqToHom_refl, Category.comp_id, realize_comp, ← realize_boundaryOp]

/-- The identity operator `i = 𝟙 × 𝟙 : (K×L)_q → (K×L)_q` (EM's `i`). Realizes to `𝟙`
(`realize_single_id`). -/
noncomputable def idOp (q : ℕ) : DerivedOp q q := Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1

/-! #### Abstract properties of `h = ∇f` used by the EM induction

From this point on, the induction uses `hOp` only through formal operator identities, not by
unfolding its explicit summands. -/

/-- The represented simplicial type `Δ[s] : b ↦ (⦋b⦌ ⟶ ⦋s⦌)` (the `SimplexCategory` Yoneda). -/
abbrev ysimp (s : ℕ) : SimplexCategoryᵒᵖ ⥤ Type := yoneda.obj (⦋s⦌ : SimplexCategory)

/-- The bi-represented **bisimplicial type** at `(s, s)`: `(a, b) ↦ (⦋a⦌ ⟶ ⦋s⦌) × (⦋b⦌ ⟶ ⦋s⦌)`,
the horizontal map acting on the first factor and the vertical on the second. -/
def bitype (s : ℕ) : BisimplicialObject (Type) where
  obj a :=
    { obj := fun b => (ysimp s).obj a × (ysimp s).obj b
      map := fun {b b'} g => TypeCat.ofHom fun p => (p.1, (ysimp s).map g p.2)
      map_id := by intro b; ext p <;> simp
      map_comp := by intro b b' b'' g g'; ext p <;> simp }
  map := fun {a a'} f =>
    { app := fun b => TypeCat.ofHom fun p => ((ysimp s).map f p.1, p.2)
      naturality := by intro b b' g; ext p <;> simp }
  map_id := by intro a; ext b p <;> simp
  map_comp := by intro a a' a'' f f'; ext b p <;> simp

/-- Postcompose a (bi)simplicial type with the free `ℤ`-module functor. -/
noncomputable def freeWhisker :
    (SimplexCategoryᵒᵖ ⥤ Type) ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ Type (ModuleCat.{0} ℤ)).obj (ModuleCat.free ℤ)

/-- A **universal bisimplicial object** detecting all derived operators out of degree `s`:
the free `ℤ`-module on the bi-represented bisimplicial set at `(s, s)`. Realizing a derived
operator against it recovers it as a `Finsupp`, so `realize (univOp s)` is injective
(`realize_univOp_injective`). -/
noncomputable def univOp (s : ℕ) : BisimplicialObject (ModuleCat.{0} ℤ) :=
  bitype s ⋙ freeWhisker

/-- The underlying pair of `SimplexCategory` maps of a letter. Injective (a letter *is* its pair),
so it indexes the free `ℤ`-module realizing `univOp`. -/
private def opToPair {s q : ℕ} (l : OpLetter s q) :
    ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) × ((⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) := (l.fst, l.snd)

private lemma opToPair_injective {s q : ℕ} :
    Function.Injective (opToPair (s := s) (q := q)) := by
  intro l l' h
  cases l; cases l'
  simpa only [opToPair, Prod.mk.injEq, OpLetter.mk.injEq] using h

/-- The universal generator `(𝟙, 𝟙) ∈ X_{s,s}` for `X = univOp s`. -/
private noncomputable def univGen (s : ℕ) : (F₂.obj (univOp s)).X s :=
  ModuleCat.freeMk (R := ℤ) ((𝟙 (⦋s⦌ : SimplexCategory)), (𝟙 (⦋s⦌ : SimplexCategory)))

private lemma realize_univOp_single_gen_one {s q : ℕ} (l : OpLetter s q) :
    (DerivedOp.realize (univOp s) (Finsupp.single l 1)) (univGen s)
      = ModuleCat.freeMk (R := ℤ) (opToPair l) := by
  rw [realize_single, one_smul]
  simp only [OpLetter.realize, univOp, freeWhisker, univGen, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app, bitype, ysimp,
    yoneda_obj_map, Quiver.Hom.unop_op, opToPair]
  erw [ModuleCat.comp_apply, ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  exact congrArg ModuleCat.freeMk (by simp)

private lemma realize_univOp_single_gen {s q : ℕ} (l : OpLetter s q) (c : ℤ) :
    (DerivedOp.realize (univOp s) (Finsupp.single l c)) (univGen s)
      = Finsupp.single (opToPair l) c := by
  rw [show (Finsupp.single l c : DerivedOp s q) = c • Finsupp.single l 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one], realize_zsmul]
  rw [show (ConcreteCategory.hom (c • DerivedOp.realize (univOp s) (Finsupp.single l 1)))
        (univGen s)
        = c • (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l 1)))
          (univGen s) from rfl,
    realize_univOp_single_gen_one, ModuleCat.freeMk]
  exact (Finsupp.smul_single c (opToPair l) 1).trans (by rw [smul_eq_mul, mul_one])

/-- Realizing `M` on `univOp` and evaluating at the universal generator recovers `M` (reindexed
along the letter-to-pair bijection): `realize (univOp s) M (gen) = mapDomain opToPair M`. -/
private lemma realize_univOp_gen {s q : ℕ} (M : DerivedOp s q) :
    (DerivedOp.realize (univOp s) M) (univGen s) = Finsupp.mapDomain opToPair M := by
  induction M using Finsupp.induction with
  | zero => rw [realize_zero, Finsupp.mapDomain_zero]; rfl
  | single_add l c f _ _ ih =>
      rw [realize_add,
        show (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)
              + DerivedOp.realize (univOp s) f)) (univGen s)
            = (ConcreteCategory.hom (DerivedOp.realize (univOp s) (Finsupp.single l c)))
                (univGen s)
              + (ConcreteCategory.hom (DerivedOp.realize (univOp s) f)) (univGen s) from rfl,
        realize_univOp_single_gen, ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rfl

/-- `realize` against the universal object is **injective**: a derived operator is determined by
its realization on `univOp`. This is the faithfulness principle that lets us deduce formal
`DerivedOp` identities from their (realized) chain-level counterparts. -/
lemma realize_univOp_injective {s q : ℕ} :
    Function.Injective (fun M : DerivedOp s q => M.realize (univOp s)) := by
  intro M N h
  have hg := congrArg
    (fun φ : (F₂.obj (univOp s)).X s ⟶ (F₂.obj (univOp s)).X q =>
      (ConcreteCategory.hom φ) (univGen s)) h
  simp only [realize_univOp_gen] at hg
  exact Finsupp.mapDomain_injective opToPair_injective hg

/-- **`∂ h = h ∂` (EM line 155, `∂*h' = h'∂*`).** `h = ∇f` is a chain map, so `boundaryOp` commutes
with `hOp`. Proof: `realize` against the universal object is injective, and on the realized side
this is just the chain-map condition `comm` of `alexanderWhitney ≫ shuffleMap`. -/
lemma boundaryOp_comp_hOp (q : ℕ) :
    (boundaryOp q).comp (hOp (q + 1)) = (hOp q).comp (boundaryOp q) := by
  apply realize_univOp_injective
  change ((boundaryOp q).comp (hOp (q + 1))).realize (univOp (q + 1))
    = ((hOp q).comp (boundaryOp q)).realize (univOp (q + 1))
  rw [realize_comp, realize_comp, realize_hOp, realize_hOp, realize_boundaryOp]
  exact (alexanderWhitney (univOp (q + 1)) ≫ shuffleMap (univOp (q + 1))).comm (q + 1) q

/-- **`F₀ h' = h F₀` (EM, Lemma I.3.3).** Just `lastFace_comp_prime` specialized to `hOp`. -/
lemma lastFace_comp_hPrime (q : ℕ) :
    (lastFaceOp q).comp ((hOp q).prime) = (hOp q).comp (lastFaceOp q) :=
  lastFace_comp_prime (hOp q)

/-- Base degree: `hOp 0` agrees with the identity after postcomposing with `retractionN₂`. -/
lemma hOp_zero_comp_retraction (X : BisimplicialObject C) :
    DerivedOp.realize X (hOp 0) ≫ (retractionN₂ X).f 0 =
      DerivedOp.realize X (idOp 0) ≫ (retractionN₂ X).f 0 := by
  rw [realize_hOp, idOp, realize_single_id, awShuffle_f_zero, HomologicalComplex.id_f]

/-! #### Exact-identity backbone for the EM induction

The induction is organized at the formal `DerivedOp` level. We encode the error term
`Φ∂ + ∂Φ + i - h` as a structural norm class `IsNorm`, prove that this class is closed under
`prime`, and only at the end convert structural norms into vanishing statements after
postcomposing with `retractionN₂`. -/

/-- Right composition `· .comp N` bundled additively (general `compRightD0`). -/
private noncomputable def compRightHom {s q r : ℕ} (M₂ : DerivedOp q r) :
    DerivedOp s q →+ DerivedOp s r where
  toFun N := M₂.comp N
  map_zero' := by simp [DerivedOp.comp]
  map_add' := DerivedOp.comp_add_right M₂

/-- Left composition `M ↦ M.comp K` bundled additively. -/
private noncomputable def compLeftHom {s q r : ℕ} (M₁ : DerivedOp s q) :
    DerivedOp q r →+ DerivedOp s r where
  toFun M₂ := M₂.comp M₁
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N M₁

lemma DerivedOp.comp_neg {s q r : ℕ} (M₂ : DerivedOp q r) (N : DerivedOp s q) :
    M₂.comp (-N) = -(M₂.comp N) := map_neg (compRightHom M₂) N

lemma DerivedOp.neg_comp {s q r : ℕ} (M : DerivedOp q r) (K : DerivedOp s q) :
    (-M).comp K = -(M.comp K) := map_neg (compLeftHom K) M

lemma DerivedOp.comp_sub {s q r : ℕ} (M₂ : DerivedOp q r) (M N : DerivedOp s q) :
    M₂.comp (M - N) = M₂.comp M - M₂.comp N := map_sub (compRightHom M₂) M N

lemma DerivedOp.sub_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M - N).comp K = M.comp K - N.comp K := map_sub (compLeftHom K) M N

lemma prime_neg {s q : ℕ} (M : DerivedOp s q) : (-M).prime = -M.prime :=
  map_neg primeAddHom M

/-- Associativity of letter composition (`≫`-associativity in each coordinate). -/
private lemma OpLetter.comp_assoc {s q r p : ℕ} (l₃ : OpLetter r p) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) : (l₃.comp l₂).comp l₁ = l₃.comp (l₂.comp l₁) := by
  simp only [OpLetter.comp, Category.assoc]

/-- Associativity of `DerivedOp.comp` (reduces to `single_comp_single` + bilinearity). -/
lemma DerivedOp.comp_assoc {s q r p : ℕ} (M₃ : DerivedOp r p) (M₂ : DerivedOp q r)
    (M₁ : DerivedOp s q) : (M₃.comp M₂).comp M₁ = M₃.comp (M₂.comp M₁) := by
  induction M₁ using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, ih, DerivedOp.comp_add_right, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction M₂ using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.comp_add_right, DerivedOp.add_comp, ih₂, DerivedOp.add_comp,
        DerivedOp.comp_add_right]
      congr 1
      clear ih₂
      induction M₃ using Finsupp.induction with
      | zero => simp [DerivedOp.comp]
      | single_add l₃ c₃ h _ _ ih₃ =>
        rw [DerivedOp.add_comp, DerivedOp.add_comp, ih₃, DerivedOp.add_comp]
        congr 1
        rw [DerivedOp.single_comp_single, DerivedOp.single_comp_single,
          DerivedOp.single_comp_single, DerivedOp.single_comp_single, OpLetter.comp_assoc]
        congr 1
        ring

@[simp] lemma DerivedOp.zero_comp {s q r : ℕ} (N : DerivedOp s q) :
    DerivedOp.comp (0 : DerivedOp q r) N = 0 := by simp [DerivedOp.comp]

/-- Structural norm class for diagonal degeneracies, closed under `+` and `neg`.

The point of this definition is that closure under `prime` is formal, so the induction can be run
before realizing operators on a bisimplicial object. -/
inductive IsNorm : {s q : ℕ} → DerivedOp s q → Prop where
  | zero {s q : ℕ} : IsNorm (0 : DerivedOp s q)
  | add {s q : ℕ} {M N : DerivedOp s q} : IsNorm M → IsNorm N → IsNorm (M + N)
  | neg {s q : ℕ} {M : DerivedOp s q} : IsNorm M → IsNorm (-M)
  | diagDegen {r s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
      IsNorm (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N)

/-- `prime` of a diagonal letter `⟨θ,θ⟩` is the diagonal of `primeHom θ`. -/
lemma prime_single_diag {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.prime (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1)
      = Finsupp.single (⟨primeHom θ, primeHom θ⟩ : OpLetter (s + 1) (q + 1)) 1 := by
  simp [DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.prime]

/-- `primeHom` preserves non-monicity: `primeHom θ` is injective iff `θ` is, and `Mono` in
`SimplexCategory` is injectivity. -/
lemma primeHom_not_mono {s q : ℕ} {θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌} (hθ : ¬ Mono θ) :
    ¬ Mono (primeHom θ) := by
  rw [SimplexCategory.mono_iff_injective] at hθ ⊢
  intro hinj
  apply hθ
  intro a b hab
  have key : ∀ c : Fin (q + 1),
      (SimplexCategory.Hom.toOrderHom (primeHom θ)) c.succ
        = (SimplexCategory.Hom.toOrderHom θ c).succ := by
    intro c
    apply Fin.ext
    have hle : (SimplexCategory.Hom.toOrderHom θ c : ℕ) ≤ s :=
      Nat.lt_succ_iff.mp (SimplexCategory.Hom.toOrderHom θ c).isLt
    simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
      SimplexCategory.len_mk, Fin.val_succ]
    rw [ite_eq_right (by omega : ¬ ((c : ℕ) + 1 = 0))]
    simp only [Nat.add_sub_cancel, Fin.eta]
    omega
  have hsucc : (SimplexCategory.Hom.toOrderHom (primeHom θ)) a.succ
      = (SimplexCategory.Hom.toOrderHom (primeHom θ)) b.succ := by
    rw [key, key, hab]
  exact Fin.succ_injective _ (hinj hsucc)

/-- `prime` fixes the identity map: `primeHom 𝟙 = 𝟙` (`0 ↦ 0`, `j+1 ↦ 𝟙(j)+1 = j+1`). -/
lemma primeHom_id (q : ℕ) : primeHom (𝟙 (⦋q⦌ : SimplexCategory)) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  have hj : (j : ℕ) ≤ q + 1 := Nat.lt_succ_iff.mp j.isLt
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk, SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
  split_ifs with h <;> omega

/-- `i' = i` (md 173–175, implicit in priming the IH's `−c_q`): the derived operator of the
identity is the identity. -/
lemma prime_idOp (q : ℕ) : (idOp q).prime = idOp (q + 1) := by
  rw [idOp, prime_single_diag, primeHom_id, idOp]

/-- **`F₀ D₀ = i`** (`δ_0 ≫ σ_0 = 𝟙`): the last face undoes the 0-th degeneracy. Repackages the
existing `face_zero_comp_D0` (`lastFaceOp = faceOp _ 0`). -/
lemma lastFace_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (D0op (q + 1)) = idOp (q + 1) := by
  rw [lastFaceOp, idOp]
  exact face_zero_comp_D0 q

/-- Right unit for `DerivedOp.comp`: `M ∘ i = M` (`l ≫ 𝟙 = l` in each coordinate). -/
lemma comp_idOp {s q : ℕ} (M : DerivedOp s q) : M.comp (idOp s) = M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l c f _ _ ih =>
      rw [DerivedOp.add_comp, ih]
      congr 1
      rw [idOp, DerivedOp.single_comp_single, one_mul]
      congr 1
      simp only [OpLetter.comp, Category.comp_id]

/-- **`F₀ h' D₀ = h` (EM line 192).** `F₀ h' D₀ = (h F₀) D₀ = h (F₀ D₀) = h`, using
`lastFace_comp_hPrime` and `F₀ D₀ = i` (`δ_0 ≫ σ_0 = 𝟙`). -/
lemma lastFace_comp_hPrime_comp_D0 (q : ℕ) :
    (lastFaceOp (q + 1)).comp (((hOp (q + 1)).prime).comp (D0op (q + 1))) = hOp (q + 1) := by
  rw [← DerivedOp.comp_assoc, lastFace_comp_hPrime, DerivedOp.comp_assoc, lastFace_comp_D0,
    comp_idOp]

/-! #### EM (2.12): `f` and `∇` preserve norms ⟹ `h = ∇f` preserves norms

EM (2.12) is a *composition* fact: `f = AW` and `∇ = shuffleMap` each carry the (diagonal)
degenerate subcomplex into the (bi-)degenerate subcomplex, so `h = ∇f` does too. The two halves are
genuine Dold–Kan combinatorial inputs (Phase-4-level); the composite `h`-statement then follows
*for free* via `realize_hOp`.

* **`∇`-half (6b):** `retractionN₁_inclusionN₁_shuffleMap_retractionN₂` — a degenerate-`F₁` element
  (image of `1 − retractionN₁ ≫ inclusionN₁`) is sent by `∇` to a degenerate diagonal element,
  killed by `retractionN₂`.
* **`f`-half:** `alexanderWhitney_diagDegen_comp_retractionN₁` — a diagonal degeneracy `⟨θ,θ⟩`
  followed by `AW` lands in the degenerate part of `F₁`, killed by `retractionN₁`. -/

/-- If a simplex operator `f : ⦋n+1⦌ ⟶ Δ'` identifies the adjacent pair `a.castSucc, a.succ`
(i.e. it is "constant across the `a`-th step"), then it factors through the codegeneracy `σ a`:
`f = σ a ≫ (δ a.castSucc ≫ f)`. The section `δ a.castSucc` undoes `σ a` away from the collapsed
pair (`Fin.succAbove_predAbove`), and on the pair the hypothesis `hf` patches it. -/
private lemma factor_through_σ {n : ℕ} {Δ' : SimplexCategory} (a : Fin (n + 1))
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ Δ')
    (hf : f.toOrderHom a.castSucc = f.toOrderHom a.succ) :
    f = SimplexCategory.σ a ≫ SimplexCategory.δ a.castSucc ≫ f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.σ, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change _ = (SimplexCategory.Hom.toOrderHom f) (a.castSucc.succAbove (a.predAbove x))
  by_cases hx : x = a.castSucc
  · subst hx
    rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
    exact hf
  · rw [Fin.succAbove_predAbove hx]

/-- A codegeneracy `σ a` is never a monomorphism (it identifies the adjacent pair `a.castSucc`,
`a.succ`). -/
private lemma sigma_not_mono {n : ℕ} (a : Fin (n + 1)) : ¬ Mono (SimplexCategory.σ a) := by
  rw [SimplexCategory.mono_iff_injective]
  intro hinj
  have key : a.castSucc = a.succ := by
    apply hinj
    change a.predAbove a.castSucc = a.predAbove a.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  exact absurd key (ne_of_lt Fin.castSucc_lt_succ)

/-- `PInfty` of the diagonal in degree `n`, typed on the `(n, n)` entry of `X`. -/
noncomputable def diagPInfty (X : BisimplicialObject C) (n : ℕ) :
    (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) ⟶
      (X.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) :=
  (PInfty : F₂.obj X ⟶ F₂.obj X).f n

/-- **Shared per-summand kill (degeneracy ⟹ diagonal degeneracy).** A single Eilenberg–Zilber
summand `(X_⦋s⦌).map v.op ≫ (X.map h.op)_⦋n+1⦌`, in which the horizontal leg `h` and the vertical
leg `v` are *both constant across the `a`-th step* (`a.castSucc ↦ a.succ`), factors through the
diagonal codegeneracy `(diag X).map (σ a).op` and is therefore annihilated by `PInfty`. This is the
direction-agnostic core: the inner kill feeds it `v = sndHom ≫ σ_i` (constant by `exists_snd_step`),
the outer kill feeds it `h = fstHom ≫ σ_i`. -/
private lemma summand_kill {N s t : ℕ} (X : BisimplicialObject C)
    (h : (⦋N⦌ : SimplexCategory) ⟶ ⦋s⦌) (v : (⦋N⦌ : SimplexCategory) ⟶ ⦋t⦌)
    (a : Fin N)
    (hh : (SimplexCategory.Hom.toOrderHom h) a.castSucc = (SimplexCategory.Hom.toOrderHom h) a.succ)
    (hv : (SimplexCategory.Hom.toOrderHom v) a.castSucc =
      (SimplexCategory.Hom.toOrderHom v) a.succ) :
    (X.obj (Opposite.op ⦋s⦌)).map v.op ≫ (X.map h.op).app (Opposite.op ⦋N⦌) ≫
      diagPInfty X N = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by
    have : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0); omega⟩
  have hfh := factor_through_σ a h hh
  have hfv := factor_through_σ a v hv
  set h' : (⦋n⦌ : SimplexCategory) ⟶ ⦋s⦌ := SimplexCategory.δ a.castSucc ≫ h with hh'_def
  set v' : (⦋n⦌ : SimplexCategory) ⟶ ⦋t⦌ := SimplexCategory.δ a.castSucc ≫ v with hv'_def
  have hvop : v.op = v'.op ≫ (SimplexCategory.σ a).op := by rw [hfv, op_comp]
  have hhop : h.op = h'.op ≫ (SimplexCategory.σ a).op := by rw [hfh, op_comp]
  -- the diagonal-degeneracy tail is killed by `PInfty`
  have hbr : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌)
      = (diag.obj X).map (SimplexCategory.σ a).op := by
    rw [(X.map (SimplexCategory.σ a).op).naturality, ← diag_obj_map]
  have hkill : (X.obj (Opposite.op ⦋n⦌)).map (SimplexCategory.σ a).op ≫
      (X.map (SimplexCategory.σ a).op).app (Opposite.op ⦋n + 1⦌) ≫
      diagPInfty X (n + 1) = 0 := by
    rw [← Category.assoc, hbr]
    exact degeneracy_comp_PInfty (diag.obj X) (n + 1) (SimplexCategory.σ a) (sigma_not_mono a)
  rw [hvop, hhop, Functor.map_comp, Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [(X.map h'.op).naturality_assoc, hkill]
  simp

/-- **EZ–degeneracy kill, inner (vertical) direction (the per-summand combinatorial core).**
A `(p, m+1)`-shuffle component of a chain that is *degenerate in the inner simplicial direction*
(in the image of the inner degeneracy `s_i = (X_⦋p⦌).map (σ i).op : X_{p,m} → X_{p,m+1}`) is sent by
the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (1 ⊗ s_i) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_inner_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (p m : ℕ) (i : Fin (m + 1)) :
    (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ i).op ≫ ezComponent X p (m + 1) ≫
        diagPInfty X (p + (m + 1)) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨a, ha1, ha2, ha3⟩ := Shuffle.exists_snd_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ)) a.succ := by
    simp only [shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.fst_coe]
    exact ha3
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ ≫ SimplexCategory.σ i)) a.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.snd_coe]
    have e1 : (μ.1 a.castSucc).2 = i.castSucc := Fin.ext (by rw [Fin.val_castSucc]; omega)
    have e2 : (μ.1 a.succ).2 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    change (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.castSucc).2
        = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 a.succ).2
    rw [e1, e2]
    change i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hcomp : X _⦋p⦌.map (SimplexCategory.σ i).op ≫
      (X _⦋p⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋p + (m + 1)⦌)) ≫
      diagPInfty X (p + (m + 1)) = 0 := by
    simp only [Category.assoc]
    rw [← Category.assoc (X _⦋p⦌.map (SimplexCategory.σ i).op), ← Functor.map_comp, ← op_comp]
    exact summand_kill X (shuffleFstHom μ) (shuffleSndHom μ ≫ SimplexCategory.σ i) a hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **EZ–degeneracy kill, outer (horizontal) direction (the per-summand combinatorial core).**
An `(a+1, q)`-shuffle component of a chain that is *degenerate in the outer simplicial direction*
(in the image of the outer degeneracy `s_i = (X.map (σ i).op).app ⦋q⦌ : X_{a,q} → X_{a+1,q}`)
is sent
by the Eilenberg–Zilber component to a *diagonally* degenerate chain, hence annihilated by `PInfty`.

EM Lemma I.5.3 content: `∇ ∘ (s_i ⊗ 1) = s_? ∘ ∇'` lands in a diagonal degeneracy. -/
lemma ezComponent_outer_degeneracy_comp_PInfty (X : BisimplicialObject C)
    (a q : ℕ) (i : Fin (a + 1)) :
    (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫ ezComponent X (a + 1) q ≫
        diagPInfty X (a + 1 + q) = 0 := by
  rw [ezComponent, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro μ _
  obtain ⟨b, hb1, hb2, hb3⟩ := Shuffle.exists_fst_step μ i.val (by have := i.isLt; omega)
  have hh : (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleFstHom μ ≫ SimplexCategory.σ i)) b.succ := by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.fst_coe]
    have e1 : (μ.1 b.castSucc).1 = i.castSucc := Fin.ext (by rw [Fin.val_castSucc]; omega)
    have e2 : (μ.1 b.succ).1 = i.succ := Fin.ext (by rw [Fin.val_succ]; omega)
    change (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.castSucc).1
        = (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ i)) (μ.1 b.succ).1
    rw [e1, e2]
    change i.predAbove i.castSucc = i.predAbove i.succ
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have hv : (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.castSucc
          = (SimplexCategory.Hom.toOrderHom (shuffleSndHom μ)) b.succ := by
    simp only [shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.snd_coe]
    exact hb3
  have hcomp : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋q⦌) ≫
      (X _⦋a + 1⦌.map (shuffleSndHom μ).op ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)) ≫
      diagPInfty X (a + 1 + q) = 0 := by
    have happ : (X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) ≫
        (X.map (shuffleFstHom μ).op).app (Opposite.op ⦋a + 1 + q⦌)
        = (X.map (shuffleFstHom μ ≫ SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌) := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp only [Category.assoc]
    rw [← (X.map (SimplexCategory.σ i).op).naturality_assoc,
      ← Category.assoc ((X.map (SimplexCategory.σ i).op).app (Opposite.op ⦋a + 1 + q⦌)), happ]
    exact summand_kill X (shuffleFstHom μ ≫ SimplexCategory.σ i) (shuffleSndHom μ) b hh hv
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp, smul_zero]

/-- **Inner `QInfty`-degeneracy kill.** The inner (vertical) `QInfty` projector at degree `q`,
precomposed with the Eilenberg–Zilber component and the diagonal `PInfty`, vanishes. Each summand of
the Mathlib `decomposition_Q` ends in an inner degeneracy `(X_⦋p⦌).σ`, killed by
`ezComponent_inner_degeneracy_comp_PInfty`. -/
private lemma QInfty_inner_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q ≫ ezComponent X p q ≫
        diagPInfty X (p + q) = 0 := by
  cases q with
  | zero => rw [QInfty_f_0, zero_comp]
  | succ m =>
    rw [QInfty_f, decomposition_Q m (m + 1), Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.σ (Fin.rev i)).op ≫
        ezComponent X p (m + 1) ≫ diagPInfty X (p + (m + 1)) = 0 :=
      ezComponent_inner_degeneracy_comp_PInfty X p m (Fin.rev i)
    simp only [SimplicialObject.σ, Category.assoc, hkill, comp_zero]

/-- **Outer `QInfty`-degeneracy kill.** The outer (horizontal) `QInfty` projector at degree `p`
(evaluated at inner degree `q`), precomposed with the Eilenberg–Zilber component and the diagonal
`PInfty`, vanishes. Each summand of the Mathlib `decomposition_Q` ends in an outer degeneracy
`(X.map (σ _).op).app ⦋q⦌`, killed by `ezComponent_outer_degeneracy_comp_PInfty`. -/
private lemma QInfty_outer_ezComponent_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌) ≫ ezComponent X p q ≫
        diagPInfty X (p + q) = 0 := by
  cases p with
  | zero => rw [QInfty_f_0]; simp
  | succ a =>
    rw [QInfty_f, decomposition_Q a (a + 1), NatTrans.app_sum, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hkill : (X.map (SimplexCategory.σ (Fin.rev i)).op).app (Opposite.op ⦋q⦌) ≫
        ezComponent X (a + 1) q ≫ diagPInfty X (a + 1 + q) = 0 :=
      ezComponent_outer_degeneracy_comp_PInfty X a q (Fin.rev i)
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc]
    rw [SimplicialObject.σ, hkill, comp_zero, comp_zero]

/-- The inner `PInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def innerPInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (PInfty (X := X.obj (Opposite.op ⦋p⦌))).f q

/-- The outer `PInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def outerPInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((PInfty (X := X)).f p).app (Opposite.op ⦋q⦌)

/-- The inner `QInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def innerQInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  (QInfty (X := X.obj (Opposite.op ⦋p⦌))).f q

/-- The outer `QInfty` in bidegree `(p, q)`, typed on `X_{p,q}`. -/
private noncomputable def outerQInfty (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((QInfty (X := X)).f p).app (Opposite.op ⦋q⦌)

/-- The inclusion of `X_{p,q}` into `F₁.obj X` in total degree `p + q`. -/
private noncomputable def ιF₁ (X : BisimplicialObject C) (p q : ℕ) :
    (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶ (F₁.obj X).X (p + q) :=
  HomologicalComplex₂.ιTotal (doubleComplex X) (ComplexShape.down ℕ) p q (p + q)
    (by simp [ComplexShape.π_def])

private lemma innerPInfty_eq (X : BisimplicialObject C) (p q : ℕ) :
    innerPInfty X p q = 𝟙 _ - innerQInfty X p q :=
  eq_sub_iff_add_eq.mpr (PInfty_f_add_QInfty_f (X := X.obj (Opposite.op ⦋p⦌)) q)

private lemma outerPInfty_eq (X : BisimplicialObject C) (p q : ℕ) :
    outerPInfty X p q = 𝟙 _ - outerQInfty X p q :=
  eq_sub_iff_add_eq.mpr
    (congrArg (fun f => NatTrans.app f (Opposite.op ⦋q⦌)) (PInfty_f_add_QInfty_f (X := X) p))

private lemma innerQInfty_ezComponent_diagPInfty (X : BisimplicialObject C) (p q : ℕ) :
    innerQInfty X p q ≫ ezComponent X p q ≫ diagPInfty X (p + q) = 0 :=
  QInfty_inner_ezComponent_PInfty X p q

private lemma outerQInfty_ezComponent_diagPInfty (X : BisimplicialObject C) (p q : ℕ) :
    outerQInfty X p q ≫ ezComponent X p q ≫ diagPInfty X (p + q) = 0 :=
  QInfty_outer_ezComponent_PInfty X p q

private lemma sub_one_sub_comp_eq_zero {A Z : C} (a b : A ⟶ A) (f : A ⟶ Z)
    (ha : a ≫ f = 0) (hb : b ≫ f = 0) : f - (𝟙 A - a) ≫ (𝟙 A - b) ≫ f = 0 := by
  simp [Preadditive.sub_comp, ha, hb]

/-- The `(p, q)` component of `retractionN₁ ≫ inclusionN₁` is `outerPInfty ≫ innerPInfty`. -/
private lemma retraction_inclusion_component (X : BisimplicialObject C) (p q : ℕ) :
    ((PInftyToNormalizedMooreComplex (X.obj (Opposite.op ⦋p⦌))).f q ≫
      ((normalizedMooreComplex C).map ((PInftyToNormalizedMooreComplex X).f p)).f q) ≫
      (((normalizedMooreComplex C).map ((inclusionOfMooreComplexMap X).f p)).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q) =
    outerPInfty X p q ≫ innerPInfty X p q := by
  have e1 : ((normalizedMooreComplex C).map ((PInftyToNormalizedMooreComplex X).f p)).f q ≫
      ((normalizedMooreComplex C).map ((inclusionOfMooreComplexMap X).f p)).f q =
      ((normalizedMooreComplex C).map ((PInfty (X := X)).f p)).f q :=
    (congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      ((normalizedMooreComplex C).map_comp _ _)).symm.trans
      (congrArg (fun g => ((normalizedMooreComplex C).map g).f q)
        (congrArg (fun φ => HomologicalComplex.Hom.f φ p)
          (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)))
  have e2 : ((normalizedMooreComplex C).map ((PInfty (X := X)).f p)).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q =
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q ≫ outerPInfty X p q :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      ((inclusionOfMooreComplex C).naturality ((PInfty (X := X)).f p))
  have e3 : (PInftyToNormalizedMooreComplex (X.obj (Opposite.op ⦋p⦌))).f q ≫
      (inclusionOfMooreComplexMap (X.obj (Opposite.op ⦋p⦌))).f q = innerPInfty X p q :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ q)
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap _)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans e2))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ outerPInfty X p q) e3).trans (PInfty_f_naturality q ((PInfty (X := X)).f p)).symm

private lemma ιF₁_shuffleMap_PInfty (X : BisimplicialObject C) (p q : ℕ) :
    ιF₁ X p q ≫ (shuffleMap X ≫ PInfty).f (p + q) = ezComponent X p q ≫ diagPInfty X (p + q) := by
  rw [HomologicalComplex.comp_f]
  dsimp only [shuffleMap, ιF₁]
  erw [HomologicalComplex₂.ι_totalDesc_assoc]
  exact (Category.assoc _ _ _).trans (congrArg (ezComponent X p q ≫ ·) (Category.id_comp _))

/-- The degenerate part of `F₁` is sent by `shuffleMap` to a diagonal degeneracy, hence is killed by
`PInfty`.

Concretely, after decomposing the complementary projector
`𝟙 - retractionN₁ ≫ inclusionN₁` bidegreewise, the resulting inner- and outer-degenerate pieces are
annihilated by `ezComponent_inner_degeneracy_comp_PInfty` and
`ezComponent_outer_degeneracy_comp_PInfty`. -/
lemma degenerate_shuffleMap_comp_PInfty (X : BisimplicialObject C) :
    (𝟙 (F₁.obj X) - retractionN₁ X ≫ inclusionN₁ X) ≫ shuffleMap X ≫
        (PInfty : F₂.obj X ⟶ F₂.obj X) = 0 := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  subst hpq
  erw [comp_zero]
  have hr' : ιF₁ X p q ≫ (retractionN₁ X ≫ inclusionN₁ X).f (p + q) =
      (outerPInfty X p q ≫ innerPInfty X p q) ≫ ιF₁ X p q := by
    rw [retractionN₁, inclusionN₁, ← Functor.map_comp, HomologicalComplex₂.totalFunctor_map]
    dsimp only [ιF₁]
    erw [HomologicalComplex₂.ιTotal_map]
    exact congrArg (· ≫ _) (retraction_inclusion_component X p q)
  change ιF₁ X p q ≫ ((𝟙 (F₁.obj X) - retractionN₁ X ≫ inclusionN₁ X) ≫ shuffleMap X ≫
    (PInfty : F₂.obj X ⟶ F₂.obj X)).f (p + q) = 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, Preadditive.sub_comp,
    Preadditive.comp_sub, HomologicalComplex.id_f, Category.id_comp, reassoc_of% hr',
    ιF₁_shuffleMap_PInfty, outerPInfty_eq, innerPInfty_eq]
  exact sub_one_sub_comp_eq_zero _ _ _ (outerQInfty_ezComponent_diagPInfty X p q)
    (innerQInfty_ezComponent_diagPInfty X p q)

/-- The round trip `retractionN₁ ≫ inclusionN₁` is absorbed under `shuffleMap ≫ PInfty`.

The correction term `1 - retractionN₁ ≫ inclusionN₁` lands in the degenerate part of the diagonal,
which `PInfty` kills. -/
@[reassoc]
lemma retractionN₁_inclusionN₁_shuffleMap_PInfty (X : BisimplicialObject C) :
    retractionN₁ X ≫ inclusionN₁ X ≫ shuffleMap X ≫ (PInfty : F₂.obj X ⟶ F₂.obj X)
      = shuffleMap X ≫ PInfty := by
  have key := degenerate_shuffleMap_comp_PInfty X
  rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at key
  rw [← Category.assoc]
  exact key.symm

/-- The corresponding absorption identity after replacing `PInfty` by `retractionN₂`. -/
@[reassoc]
lemma retractionN₁_inclusionN₁_shuffleMap_retractionN₂ (X : BisimplicialObject C) :
    retractionN₁ X ≫ inclusionN₁ X ≫ shuffleMap X ≫ retractionN₂ X
      = shuffleMap X ≫ retractionN₂ X := by
  have : Mono (inclusionN₂ X) := by rw [inclusionN₂]; infer_instance
  rw [← cancel_mono (inclusionN₂ X)]
  simp only [Category.assoc]
  rw [inclusionN₂, retractionN₂]
  erw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Functor.comp_obj,
    retractionN₁_inclusionN₁_shuffleMap_PInfty X]

/-- **Every norm dies under `retractionN₂`** (for every `X`). Structural induction: linear cases are
`realize`-linearity; the two generators are the (2)-diagonal kill and EM (2.12). -/
lemma IsNorm.kill {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) (X : BisimplicialObject C) :
    DerivedOp.realize X M ≫ (retractionN₂ X).f q = 0 := by
  induction h with
  | zero => rw [realize_zero, Limits.zero_comp]
  | add _ _ ihM ihN => rw [realize_add, Preadditive.add_comp, ihM, ihN, add_zero]
  | neg _ ihM => rw [realize_neg, Preadditive.neg_comp, ihM, neg_zero]
  | diagDegen θ hθ N => exact realize_comp_diagLetter_not_mono_comp_retractionN₂ X θ hθ N

/-- The structural norm class is closed under `prime`. -/
lemma IsNorm.prime {s q : ℕ} {M : DerivedOp s q} (h : IsNorm M) : IsNorm M.prime := by
  induction h with
  | zero => rw [prime_zero]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [prime_add]; exact ihM.add ihN
  | neg _ ihM => rw [prime_neg]; exact ihM.neg
  | diagDegen θ hθ N =>
      rw [prime_comp, prime_single_diag]
      exact IsNorm.diagDegen (primeHom θ) (primeHom_not_mono hθ) N.prime

private lemma simplex_one_hom_ext {f g : (⦋1⦌ : SimplexCategory) ⟶ ⦋1⦌}
    (h : ∀ j, SimplexCategory.Hom.toOrderHom f j = SimplexCategory.Hom.toOrderHom g j) :
    f = g := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact h j

private lemma hLetter_one_zero :
    hLetter 1 0 (default : Shuffle 0 1) =
      ⟨SimplexCategory.σ 0 ≫ SimplexCategory.δ 1, 𝟙 _⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero,
    eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ιFront, SimplexCategory.mkHom,
    Fin.val_eq_zero, Fin.zero_eta, Category.comp_id, Category.id_comp, shuffleSndHom, ιBack,
    zero_add, Fin.eta, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma hLetter_one_one :
    hLetter 1 1 (default : Shuffle 1 0) =
      ⟨𝟙 _, SimplexCategory.σ 0 ≫ SimplexCategory.δ 0⟩ := by
  simp only [hLetter, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.add_zero, eqToHom_refl, shuffleFstHom, SimplexCategory.len_mk, ιFront,
    SimplexCategory.mkHom, Fin.eta, Category.comp_id, Category.id_comp, shuffleSndHom, ιBack,
    Nat.mod_succ, Fin.val_eq_zero, add_zero, Fin.mk_one, OpLetter.mk.injEq]
  constructor
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl
  · apply simplex_one_hom_ext
    intro j
    fin_cases j <;> rfl

private lemma phi_op_zero_eq_diagDegen :
    (phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1 =
      (D0op 0).comp (faceOp 0 1) := by
  simp only [Nat.reduceAdd, phiOp, DerivedOp.zero_comp, prime_zero, neg_zero, zero_add, Fin.isValue]
  rw [boundaryOp_eq 1, DerivedOp.sub_comp, lastFace_comp_hPrime_comp_D0 0]
  abel_nf
  simp [truncBoundaryOp, hOp, D0op, faceOp, idOp, hLetter_one_zero, hLetter_one_one,
    DerivedOp.prime, OpLetter.prime, DerivedOp.add_comp, DerivedOp.comp_add_right,
    DerivedOp.neg_comp,
    DerivedOp.single_comp_single, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Shuffle.sign_default_zero_left,
    Shuffle.sign_default_zero_right, OpLetter.comp, primeHom_comp, primeHom_δ, primeHom_σ,
    primeHom_id, Category.assoc]
  have hδ₁σ₀ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₀ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁σ₀δ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁σ₀δ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₁σ₁ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  have hδ₂σ₁ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    apply simplex_one_hom_ext; intro j; fin_cases j <;> rfl
  simp [hδ₁σ₀, hδ₂σ₀, hδ₁σ₁σ₀δ₁, hδ₂σ₁σ₀δ₁, hδ₁σ₁, hδ₂σ₁]
  abel

private lemma sigma_zero_not_mono : ¬ Mono (SimplexCategory.σ (0 : Fin 1)) := by
  rw [SimplexCategory.mono_iff_injective]
  intro h
  have h01 := h (show
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (0 : Fin 2) =
      (SimplexCategory.Hom.toOrderHom (SimplexCategory.σ (0 : Fin 1))) (1 : Fin 2) from rfl)
  norm_num at h01

/-- Base case for the exact induction: the degree-1 error term is a norm. -/
lemma phi_op_isNorm_zero :
    IsNorm ((phiOp 0).comp (boundaryOp 0) + (boundaryOp 1).comp (phiOp 1) + idOp 1 - hOp 1) := by
  rw [phi_op_zero_eq_diagDegen, D0op]
  exact IsNorm.diagDegen (SimplexCategory.σ (0 : Fin 1)) sigma_zero_not_mono (faceOp 0 1)

/-- The error term `Φ∂ + ∂Φ + i - h` satisfies the same `prime` recursion as `Φ`.

After rewriting `∂ = F₀ - ∂'` and `Φ = -Φ' + h' D₀`, the remaining identity is a formal operator
calculation using `lastFace_comp_prime`, `boundaryOp_comp_hOp`, and `boundary_comp_D0`. -/
lemma phi_op_succ_eq (q : ℕ) :
    (phiOp (q + 1)).comp (boundaryOp (q + 1)) + (boundaryOp (q + 1 + 1)).comp (phiOp (q + 1 + 1)) +
        idOp (q + 1 + 1) - hOp (q + 1 + 1) =
      ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
        idOp (q + 1) - hOp (q + 1)).prime := by
  simp only [sub_eq_add_neg, prime_add, prime_neg]
  rw [prime_comp, prime_comp, prime_boundaryOp, prime_boundaryOp, prime_idOp]
  conv_lhs => simp only [phiOp, boundaryOp_eq]
  simp only [DerivedOp.sub_comp, DerivedOp.comp_sub, DerivedOp.neg_comp, DerivedOp.comp_neg,
    DerivedOp.add_comp, DerivedOp.comp_add_right]
  rw [lastFace_comp_prime, lastFace_comp_hPrime_comp_D0]
  conv_rhs => simp only [phiOp]
  -- Rewrite the surviving `∂' h' D₀` term as `h' - h' D₀ ∂'`; all other terms cancel formally.
  have stepA : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime)
      = (hOp (q + 1)).prime.comp (truncBoundaryOp (q + 1 + 1)) := by
    have h2 := congrArg DerivedOp.prime (boundaryOp_comp_hOp (q + 1))
    simp only [prime_comp, prime_boundaryOp] at h2
    exact h2
  have stepC : (truncBoundaryOp (q + 1 + 1)).comp (D0op (q + 1 + 1))
      = idOp (q + 1 + 1) - (D0op (q + 1)).comp (truncBoundaryOp (q + 1)) := by
    have hb := boundary_comp_D0 (q + 1)
    rw [boundaryOp_eq (q + 1 + 1), DerivedOp.sub_comp, lastFace_comp_D0] at hb
    rw [← hb]; abel
  have hkey : (truncBoundaryOp (q + 1 + 1)).comp ((hOp (q + 1 + 1)).prime.comp (D0op (q + 1 + 1)))
      = (hOp (q + 1)).prime
        - ((hOp (q + 1)).prime.comp (D0op (q + 1))).comp (truncBoundaryOp (q + 1)) := by
    rw [← DerivedOp.comp_assoc, stepA, DerivedOp.comp_assoc, stepC, DerivedOp.comp_sub, comp_idOp,
      ← DerivedOp.comp_assoc]
  rw [hkey]
  simp only [DerivedOp.add_comp, DerivedOp.neg_comp]
  abel

/-- The error term `Φ∂ + ∂Φ + i - h` is a norm in every degree. -/
lemma phi_op_isNorm (q : ℕ) :
    IsNorm ((phiOp q).comp (boundaryOp q) + (boundaryOp (q + 1)).comp (phiOp (q + 1)) +
      idOp (q + 1) - hOp (q + 1)) := by
  induction q with
  | zero => exact phi_op_isNorm_zero
  | succ q ih => rw [phi_op_succ_eq q]; exact ih.prime

/-- Operator-level form of the EM homotopy identity, modulo norms.

This is the realized statement corresponding to `Φ∂ + ∂Φ + i ≡ h`, obtained by killing the
structural norm term from `phi_op_isNorm` with `retractionN₂`. -/
lemma phi_comm_op (X : BisimplicialObject C) (q : ℕ) :
    (DerivedOp.realize X ((phiOp q).comp (boundaryOp q)) +
        DerivedOp.realize X ((boundaryOp (q + 1)).comp (phiOp (q + 1))) +
        DerivedOp.realize X (idOp (q + 1))) ≫ (retractionN₂ X).f (q + 1) =
      DerivedOp.realize X (hOp (q + 1)) ≫ (retractionN₂ X).f (q + 1) := by
  have h := (phi_op_isNorm q).kill X
  rw [realize_sub, realize_add, realize_add, Preadditive.sub_comp] at h
  exact sub_eq_zero.mp h

/-- EM's homotopy identity `∂Φ + Φ∂ = ∇f - i`, after postcomposing with `retractionN₂`. -/
lemma phi_comm_retraction (X : BisimplicialObject C) (n : ℕ) :
    (dNext n (phiHomRaw X) + prevD n (phiHomRaw X) +
        (𝟙 (F₂.obj X) : (F₂.obj X) ⟶ (F₂.obj X)).f n) ≫ (retractionN₂ X).f n =
      (alexanderWhitney X ≫ shuffleMap X).f n ≫ (retractionN₂ X).f n := by
  have hid : ∀ m : ℕ, (𝟙 (F₂.obj X) : (F₂.obj X) ⟶ (F₂.obj X)).f m
      = DerivedOp.realize X (idOp m) := by
    intro m; rw [HomologicalComplex.id_f, idOp, realize_single_id]
  cases n with
  | zero =>
      have hp : prevD 0 (phiHomRaw X) = 0 := by
        rw [prevD_phiHomRaw]; simp [phiOp, realize_comp]
      have hd : dNext 0 (phiHomRaw X) = 0 := by rw [dNext]; simp
      rw [hp, hd]
      simp only [zero_add]
      rw [hid, ← realize_hOp]
      exact (hOp_zero_comp_retraction X).symm
  | succ m =>
      rw [dNext_phiHomRaw, prevD_phiHomRaw, hid, ← realize_hOp]
      exact phi_comm_op X m

/-! ### Descent to the normalized diagonal `N₂` -/

/-- The normalized Moore complex `N₂` is a retract of `F₂`: `inclusionN₂ ≫ retractionN₂ = 𝟙`. -/
@[reassoc]
lemma inclusionN₂_comp_retractionN₂ (X : BisimplicialObject C) :
    inclusionN₂ X ≫ retractionN₂ X = 𝟙 (N₂.obj X) := by
  rw [inclusionN₂, retractionN₂]
  exact (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (diag.obj X)).id

/-- `Φ` conjugated onto the normalized diagonal `N₂.obj X` (EM's homotopy on `K ×_N L`):
`inclusionN₂ ≫ phiOp.realize ≫ retractionN₂`. -/
noncomputable def phiHomNorm (X : BisimplicialObject C) (i j : ℕ) :
    (N₂.obj X).X i ⟶ (N₂.obj X).X j :=
  if h : j = i + 1 then
    (inclusionN₂ X).f i ≫ (phiOp i).realize X ≫ eqToHom (by rw [h]) ≫ (retractionN₂ X).f j
  else 0

lemma phiHomNorm_zero (X : BisimplicialObject C) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) : phiHomNorm X i j = 0 :=
  dite_eq_right fun h => hij (by rw [ComplexShape.down_Rel]; omega)

/-- `phiHomNorm` is the conjugate of `phiHomRaw` by `inclusionN₂ … retractionN₂`. -/
lemma phiHomNorm_eq (X : BisimplicialObject C) (i j : ℕ) :
    phiHomNorm X i j = (inclusionN₂ X).f i ≫ phiHomRaw X i j ≫ (retractionN₂ X).f j := by
  by_cases h : j = i + 1
  · simp only [phiHomNorm, phiHomRaw, dite_eq_left h, Category.assoc]
  · simp only [phiHomNorm, phiHomRaw, dite_eq_right h, Limits.comp_zero, Limits.zero_comp]

/-- `phiHomNorm` as an explicit family (for the `dNext`/`prevD` conjugation lemmas). -/
private lemma phiHomNorm_funext (X : BisimplicialObject C) :
    phiHomNorm X = fun a b => (inclusionN₂ X).f a ≫ phiHomRaw X a b ≫ (retractionN₂ X).f b := by
  funext a b; exact phiHomNorm_eq X a b

/-- `dNext` commutes with the `inclusionN₂ … retractionN₂` conjugation (both are chain maps). -/
lemma dNext_phiHomNorm (X : BisimplicialObject C) (i : ℕ) :
    dNext i (phiHomNorm X) =
      (inclusionN₂ X).f i ≫ dNext i (phiHomRaw X) ≫ (retractionN₂ X).f i := by
  rw [phiHomNorm_funext, dNext_comp_left, dNext_comp_right]

/-- `prevD` commutes with the `inclusionN₂ … retractionN₂` conjugation (both are chain maps). -/
lemma prevD_phiHomNorm (X : BisimplicialObject C) (j : ℕ) :
    prevD j (phiHomNorm X) =
      (inclusionN₂ X).f j ≫ prevD j (phiHomRaw X) ≫ (retractionN₂ X).f j := by
  rw [phiHomNorm_funext, prevD_comp_left, prevD_comp_right]


/-- **(6b)** The normalized `AW ≫ ∇` is the `N₂`-conjugate of the unnormalized `AW ≫ ∇`.
Unfolding the definitions, `normalizedAlexanderWhitney ≫ normalizedShuffleMap`
`= ι₂ ≫ AW ≫ (retractionN₁ ≫ inclusionN₁) ≫ ∇ ≫ ρ₂`; the inner Dold–Kan round-trip
`retractionN₁ ≫ inclusionN₁` (the `PInfty` idempotent on `F₁`) is absorbed, leaving
`ι₂ ≫ (AW ≫ ∇) ≫ ρ₂`. -/
lemma normalizedAW_shuffle_eq (X : BisimplicialObject C) :
    normalizedAlexanderWhitney X ≫ normalizedShuffleMap X
      = inclusionN₂ X ≫ (alexanderWhitney X ≫ shuffleMap X) ≫ retractionN₂ X := by
  rw [normalizedAlexanderWhitney, normalizedShuffleMap]
  simp only [Category.assoc]
  have : Mono (inclusionN₂ X) := by rw [inclusionN₂]; infer_instance
  rw [← cancel_mono (inclusionN₂ X)]
  simp only [Category.assoc]
  rw [inclusionN₂, retractionN₂]
  erw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Functor.comp_obj,
    retractionN₁_inclusionN₁_shuffleMap_PInfty X]

/-- **`AW ≫ ∇ ≃ 𝟙` on the normalized diagonal `N₂`** via the Eilenberg–Mac Lane homotopy `Φ`
(EM Thm 2.1a, `∂Φ + Φ∂ = ∇f − i`). This is the contraction homotopy used by
`eilenbergZilberNormalized` (`BisimplicialNormalized.lean`). -/
noncomputable def homotopyAWShuffleNormalized (X : BisimplicialObject C) :
    Homotopy (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X) (𝟙 (N₂.obj X)) where
  hom := phiHomNorm X
  zero := phiHomNorm_zero X
  comm := by
    intro i
    -- `𝟙 N₂` factors through `F₂`:
    -- `(𝟙 N₂).f i = ι₂.f i ≫ ρ₂.f i` (`inclusionN₂_comp_retractionN₂`).
    have hid : (𝟙 (N₂.obj X) : (N₂.obj X) ⟶ (N₂.obj X)).f i
        = (inclusionN₂ X).f i ≫ (retractionN₂ X).f i := by
      rw [← HomologicalComplex.comp_f, inclusionN₂_comp_retractionN₂]
    -- Conjugate everything onto `F₂` (6a/6b), then replace `(AW≫∇)≫ρ₂` by the EM identity (5c).
    rw [normalizedAW_shuffle_eq, dNext_phiHomNorm, prevD_phiHomNorm, hid,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← phi_comm_retraction X i]
    -- Both sides are now `ι₂ ≫ (…) ≫ ρ₂`; distribute the sum and kill the `𝟙` term.
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.id_f, Category.id_comp]

end BisimplicialObject

end LeanPool.EilenbergZilber
