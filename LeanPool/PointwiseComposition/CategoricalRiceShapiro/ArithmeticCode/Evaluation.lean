/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Basic
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.FoundationCompat

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation of arithmetic codes in an arbitrary model

Every result in this module describes `Semiformula.Evalb` for the arithmetic
formula `FFL.FirstOrder.Arithmetic.code c` under an arbitrary assignment in an
arbitrary structure.

Two results assume a model of `𝐏𝐀⁻`.  `eval_codeConst` states the value of a
constant code, and needs that assumption already for the numeral cast
`(m : M)`.  `eval_codeConst_iff` characterises that value, and additionally
uses evaluator functionality (`eval_unique`, proved in
`CategoricalRiceShapiro.ArithmeticCode.FoundationCompat`, which also assumes
`𝐏𝐀⁻`).  Every other evaluation result in this module assumes only
`ORingStructure M`.

The equivalences for the primitive constructors and for composition are the
reusable core; the derived constructors and the congruence law under a
composed-code context are proved from them.
-/

@[expose] public section

open Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M]

/-!
### Primitive constructors -/

theorem eval_zero_iff {k : ℕ} (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.zero k)) ↔ z = 0 := by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.empty_eq]

theorem eval_one_iff {k : ℕ} (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.one k)) ↔ z = 1 := by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.empty_eq]

theorem eval_proj_iff {k : ℕ} (i : Fin k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.proj i)) ↔ z = v i := by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def]

theorem eval_add_iff {k : ℕ} (i j : Fin k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.add i j)) ↔
      z = v i + v j :=
  by
  have hop : ((v i :> fun _ => v j) : Fin 2 → M) = ![v i, v j] :=
    by
    funext x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro y; simp
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.comp_vecCons', hop]

theorem eval_mul_iff {k : ℕ} (i j : Fin k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.mul i j)) ↔
      z = v i * v j :=
  by
  have hop : ((v i :> fun _ => v j) : Fin 2 → M) = ![v i, v j] :=
    by
    funext x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro y; simp
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.comp_vecCons', hop]

theorem eval_equal_iff {k : ℕ} (i j : Fin k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.equal i j)) ↔
      ((v i = v j ∧ z = 1) ∨ (¬v i = v j ∧ z = 0)) :=
  by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.empty_eq]

theorem eval_lt_iff {k : ℕ} (i j : Fin k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.lt i j)) ↔
      ((v i < v j ∧ z = 1) ∨ (¬v i < v j ∧ z = 0)) :=
  by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Function.comp_def,
    Matrix.empty_eq, -not_lt]

/-!
### Composition -/

theorem eval_comp_iff {m k : ℕ} (c : Code m) (d : Fin m → Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.comp c d)) ↔
      ∃ w : Fin m → M,
        Semiformula.Evalb (z :> w) (FFL.FirstOrder.Arithmetic.code c) ∧
          ∀ i : Fin m, Semiformula.Evalb (w i :> v) (FFL.FirstOrder.Arithmetic.code (d i)) :=
  by
  simp [FFL.FirstOrder.Arithmetic.code, FFL.FirstOrder.Arithmetic.codeAux, Semiformula.eval_rew,
    Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']

theorem eval_comp₂_iff {k : ℕ} (c : Code 2) (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.comp c ![A, B])) ↔
      ∃ e : Fin 2 → M,
        Semiformula.Evalb (z :> e) (FFL.FirstOrder.Arithmetic.code c) ∧
          Semiformula.Evalb (e 0 :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
            Semiformula.Evalb (e 1 :> v) (FFL.FirstOrder.Arithmetic.code B) :=
  by
  rw [eval_comp_iff]
  simp [Fin.forall_fin_two]

/-!
### Derived constructors -/

theorem eval_codeAdd_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeAdd A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧ z = a + b :=
  by
  rw [codeAdd, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, hB⟩
    exact ⟨e 0, e 1, hA, hB, (eval_add_iff 0 1 z e).mp he⟩
  · rintro ⟨a, b, hA, hB, hz⟩
    exact
      ⟨![a, b], (eval_add_iff 0 1 z ![a, b]).mpr (by simpa using hz), by simpa using hA, by
        simpa using hB⟩

theorem eval_codeMul_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeMul A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧ z = a * b :=
  by
  rw [codeMul, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, hB⟩
    exact ⟨e 0, e 1, hA, hB, (eval_mul_iff 0 1 z e).mp he⟩
  · rintro ⟨a, b, hA, hB, hz⟩
    exact
      ⟨![a, b], (eval_mul_iff 0 1 z ![a, b]).mpr (by simpa using hz), by simpa using hA, by
        simpa using hB⟩

theorem eval_codeEq_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeEq A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧
            ((a = b ∧ z = 1) ∨ (¬a = b ∧ z = 0)) :=
  by
  rw [codeEq, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, hB⟩
    exact ⟨e 0, e 1, hA, hB, (eval_equal_iff 0 1 z e).mp he⟩
  · rintro ⟨a, b, hA, hB, hcase⟩
    exact
      ⟨![a, b], (eval_equal_iff 0 1 z ![a, b]).mpr (by simpa using hcase), by simpa using hA, by
        simpa using hB⟩

theorem eval_codeLt_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeLt A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧
            ((a < b ∧ z = 1) ∨ (¬a < b ∧ z = 0)) :=
  by
  rw [codeLt, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, hB⟩
    exact ⟨e 0, e 1, hA, hB, (eval_lt_iff 0 1 z e).mp he⟩
  · rintro ⟨a, b, hA, hB, hcase⟩
    exact
      ⟨![a, b], (eval_lt_iff 0 1 z ![a, b]).mpr (by simpa using hcase), by simpa using hA, by
        simpa using hB⟩

theorem eval_codeSucc_iff {k : ℕ} (A : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeSucc A)) ↔
      ∃ a : M, Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧ z = a + 1 :=
  by
  rw [codeSucc, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, hB⟩
    have h1 : e 1 = 1 := (eval_one_iff (e 1) v).mp hB
    refine ⟨e 0, hA, ?_⟩
    have hz := (eval_add_iff 0 1 z e).mp he
    rw [h1] at hz
    exact hz
  · rintro ⟨a, hA, hz⟩
    exact
      ⟨![a, 1], (eval_add_iff 0 1 z ![a, 1]).mpr (by simpa using hz), by simpa using hA, by
        simpa using (eval_one_iff (1 : M) v).mpr rfl⟩

theorem eval_codePos_iff {k : ℕ} (A : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codePos A)) ↔
      ∃ a : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          ((0 < a ∧ z = 1) ∨ (¬0 < a ∧ z = 0)) :=
  by
  rw [codePos, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, h0, hA⟩
    have he0 : e 0 = 0 := (eval_zero_iff (e 0) v).mp h0
    refine ⟨e 1, hA, ?_⟩
    have hcase := (eval_lt_iff 0 1 z e).mp he
    rw [he0] at hcase
    exact hcase
  · rintro ⟨a, hA, hcase⟩
    exact
      ⟨![0, a], (eval_lt_iff 0 1 z ![0, a]).mpr (by simpa using hcase), by
        simpa using (eval_zero_iff (0 : M) v).mpr rfl, by simpa using hA⟩

theorem eval_codeInv_iff {k : ℕ} (A : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeInv A)) ↔
      ∃ a : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          ((a = 0 ∧ z = 1) ∨ (¬a = 0 ∧ z = 0)) :=
  by
  rw [codeInv, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, hA, h0⟩
    have he1 : e 1 = 0 := (eval_zero_iff (e 1) v).mp h0
    refine ⟨e 0, hA, ?_⟩
    have hcase := (eval_equal_iff 0 1 z e).mp he
    rw [he1] at hcase
    exact hcase
  · rintro ⟨a, hA, hcase⟩
    exact
      ⟨![a, 0], (eval_equal_iff 0 1 z ![a, 0]).mpr (by simpa using hcase), by simpa using hA, by
        simpa using (eval_zero_iff (0 : M) v).mpr rfl⟩

theorem eval_codeAnd_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeAnd A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧
            ((0 < a * b ∧ z = 1) ∨ (¬0 < a * b ∧ z = 0)) :=
  by
  rw [codeAnd, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, h0, hmul⟩
    have he0 : e 0 = 0 := (eval_zero_iff (e 0) v).mp h0
    obtain ⟨a, b, hA, hB, hab⟩ :=
      (eval_codeMul_iff A B (e 1) v).mp (by simpa only [codeMul] using hmul)
    refine ⟨a, b, hA, hB, ?_⟩
    have hcase := (eval_lt_iff 0 1 z e).mp he
    rw [he0, hab] at hcase
    exact hcase
  · rintro ⟨a, b, hA, hB, hcase⟩
    refine
      ⟨![0, a * b], (eval_lt_iff 0 1 z ![0, a * b]).mpr (by simpa using hcase), by
        simpa using (eval_zero_iff (0 : M) v).mpr rfl, ?_⟩
    have := (eval_codeMul_iff A B (a * b) v).mpr ⟨a, b, hA, hB, rfl⟩
    simpa only [codeMul, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using this

theorem eval_codeOr_iff {k : ℕ} (A B : Code k) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeOr A B)) ↔
      ∃ a b : M,
        Semiformula.Evalb (a :> v) (FFL.FirstOrder.Arithmetic.code A) ∧
          Semiformula.Evalb (b :> v) (FFL.FirstOrder.Arithmetic.code B) ∧
            ((0 < a + b ∧ z = 1) ∨ (¬0 < a + b ∧ z = 0)) :=
  by
  rw [codeOr, eval_comp₂_iff]
  constructor
  · rintro ⟨e, he, h0, hadd⟩
    have he0 : e 0 = 0 := (eval_zero_iff (e 0) v).mp h0
    obtain ⟨a, b, hA, hB, hab⟩ :=
      (eval_codeAdd_iff A B (e 1) v).mp (by simpa only [codeAdd] using hadd)
    refine ⟨a, b, hA, hB, ?_⟩
    have hcase := (eval_lt_iff 0 1 z e).mp he
    rw [he0, hab] at hcase
    exact hcase
  · rintro ⟨a, b, hA, hB, hcase⟩
    refine
      ⟨![0, a + b], (eval_lt_iff 0 1 z ![0, a + b]).mpr (by simpa using hcase), by
        simpa using (eval_zero_iff (0 : M) v).mpr rfl, ?_⟩
    have := (eval_codeAdd_iff A B (a + b) v).mpr ⟨a, b, hA, hB, rfl⟩
    simpa only [codeAdd, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using this

/-!
### Weakening and constants -/

theorem eval_codeHead_iff {k : ℕ} (z : M) (w : Fin (k + 1) → M) :
    Semiformula.Evalb (z :> w) (FFL.FirstOrder.Arithmetic.code (codeHead (n := k))) ↔ z = w 0 :=
  eval_proj_iff (0 : Fin (k + 1)) z w

theorem eval_codeLift_iff {k : ℕ} (d : Code k) (z t : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> (t :> v)) (FFL.FirstOrder.Arithmetic.code (codeLift d)) ↔
      Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code d) :=
  by
  simp only [Nat.succ_eq_add_one, code, Matrix.zero_cons_succ_eq_self, codeLift, codeAux,
    Rew.hom_finitary2, Rew.bind_fvar, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Semiterm.val_bvar,
    Semiformula.eval_exsClosure, LogicalConnective.HomClass.map_and, Matrix.comp_vecCons',
    Semiterm.val_fvar, Matrix.conj_hom_prop, Semiformula.eval_operator, Matrix.cons_val_fin_one,
    Tarski.Structure.eq_iff_eq, Fin.isValue, Matrix.cons_val_one, LogicalConnective.Prop.and_eq]
  constructor
  · rintro ⟨w, hw, hi⟩
    have hwv : w = v := funext hi
    rw [hwv] at hw
    simpa using hw
  · intro h
    exact ⟨v, by simpa using h, fun i => rfl⟩

theorem eval_codeConst [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (m : ℕ) (v : Fin k → M) :
    Semiformula.Evalb (((m : ℕ) : M) :> v)
      (FFL.FirstOrder.Arithmetic.code (codeConst (n := k) m)) :=
  by
  induction m with
  | zero =>
    have h0 : (((0 : ℕ)) : M) = (0 : M) := by simp
    rw [h0]
    exact (eval_zero_iff (0 : M) v).mpr rfl
  | succ p
    ih =>
    have hcast : (((p + 1 : ℕ)) : M) = ((p : ℕ) : M) + 1 := by push_cast; rfl
    rw [hcast, codeConst]
    exact (eval_codeSucc_iff (codeConst (n := k) p) _ v).mpr ⟨((p : ℕ) : M), ih, rfl⟩

theorem eval_codeConst_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (m : ℕ) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (codeConst (n := k) m)) ↔
      z = (m : M) :=
  by
  constructor
  · intro h
    exact eval_unique h (eval_codeConst m v)
  · intro h
    rw [h]
    exact eval_codeConst m v

/-!
### Bridges between a graph and a constant -/

/-- A code whose graph holds at the standard value `m` under the assignment
`v` has, at that same assignment, exactly the graph of the constant code `m`.

The hypothesis is one instance of the graph; functionality of evaluation turns
it into the full equivalence. -/
theorem eval_iff_codeConst_of_eval {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ}
    (d : Code r) (m : ℕ) (v : Fin r → M) (hd : Semiformula.Evalb ((m : M) :> v) (code d))
    (z : M) :
    Semiformula.Evalb (z :> v) (code d) ↔
      Semiformula.Evalb (z :> v) (code (codeConst (n := r) m)) :=
  by
  rw [eval_codeConst_iff]
  constructor
  · intro hz
    exact eval_unique hz hd
  · intro hz
    rw [hz]
    exact hd

/-- Lifting a constant code past one argument is the constant code of the
larger arity. -/
theorem eval_codeLift_codeConst_iff {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ}
    (m : ℕ) (z t : M) (v : Fin r → M) :
    Semiformula.Evalb (z :> t :> v) (code (codeLift (codeConst (n := r) m))) ↔
      Semiformula.Evalb (z :> t :> v) (code (codeConst (n := r + 1) m)) :=
  by rw [eval_codeLift_iff, eval_codeConst_iff, eval_codeConst_iff]

/-!
### Graph agreement across arities and assignments -/

/-- Two codes have the same graph, each under its own assignment. -/
abbrev EvalEq {k l : ℕ} (A : Code k) (v : Fin k → M) (A' : Code l) (v' : Fin l → M) :
    Prop :=
  ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v') (code A')

/-- Projections agree when the selected assignment entries agree. -/
theorem evalEq_proj {k l : ℕ} (i : Fin k) (j : Fin l) (v : Fin k → M) (v' : Fin l → M)
    (h : v i = v' j) : EvalEq (Code.proj i) v (Code.proj j) v' :=
  by
  intro x
  rw [eval_proj_iff, eval_proj_iff, h]

/-- Zero codes have the same graph under any two assignments. -/
theorem evalEq_zero {k l : ℕ} (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (Code.zero k) v (Code.zero l) v' :=
  by
  intro x
  rw [eval_zero_iff, eval_zero_iff]

/-- Head codes agree under assignments with the same head. -/
theorem evalEq_codeHead {k l : ℕ} (t : M) (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (codeHead (n := k)) (t :> v) (codeHead (n := l)) (t :> v') :=
  evalEq_proj 0 0 _ _ rfl

/-- Successor-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeSucc {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeSucc A) v (codeSucc A') v' :=
  by
  intro x
  rw [eval_codeSucc_iff, eval_codeSucc_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

/-- Positive-test code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codePos {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codePos A) v (codePos A') v' :=
  by
  intro x
  rw [eval_codePos_iff, eval_codePos_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

/-- Boolean-inverse code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeInv {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeInv A) v (codeInv A') v' :=
  by
  intro x
  rw [eval_codeInv_iff, eval_codeInv_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

/-- Addition-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeAdd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeAdd A B) v (codeAdd A' B') v' :=
  by
  intro x
  rw [eval_codeAdd_iff, eval_codeAdd_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- Multiplication-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeMul {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeMul A B) v (codeMul A' B') v' :=
  by
  intro x
  rw [eval_codeMul_iff, eval_codeMul_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- Equality-test code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeEq {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeEq A B) v (codeEq A' B') v' :=
  by
  intro x
  rw [eval_codeEq_iff, eval_codeEq_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- Order-test code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeLt {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeLt A B) v (codeLt A' B') v' :=
  by
  intro x
  rw [eval_codeLt_iff, eval_codeLt_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- Conjunction-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeAnd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeAnd A B) v (codeAnd A' B') v' :=
  by
  intro x
  rw [eval_codeAnd_iff, eval_codeAnd_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- Disjunction-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeOr {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeOr A B) v (codeOr A' B') v' :=
  by
  intro x
  rw [eval_codeOr_iff, eval_codeOr_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

/-- A lift ignores its head, so the two heads need not agree. -/
theorem evalEq_codeLift {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (t t' : M) (hA : EvalEq A v A' v') :
    EvalEq (codeLift A) (t :> v) (codeLift A') (t' :> v') :=
  by
  intro x
  rw [eval_codeLift_iff, eval_codeLift_iff]
  exact hA x

/-- One codes have the same graph under any two assignments. -/
theorem evalEq_one {k l : ℕ} (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (Code.one k) v (Code.one l) v' := by intro x; rw [eval_one_iff, eval_one_iff]

/-- Composition with a shared outer code. -/
theorem evalEq_comp {k l m : ℕ} (c : Code m) (ds : Fin m → Code k)
    (ds' : Fin m → Code l) {v : Fin k → M} {v' : Fin l → M}
    (h : ∀ i, EvalEq (ds i) v (ds' i) v') : EvalEq (c.comp ds) v (c.comp ds') v' :=
  by
  intro x
  rw [eval_comp_iff, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hwi⟩; exact ⟨w, hw, fun i => (h i (w i)).mp (hwi i)⟩
  · rintro ⟨w, hw, hwi⟩; exact ⟨w, hw, fun i => (h i (w i)).mpr (hwi i)⟩

/-- Constant codes agree under assignments of any arities. -/
theorem evalEq_codeConst {k l : ℕ} (m : ℕ) (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (codeConst (n := k) m) v (codeConst (n := l) m) v' := by
  induction m with
  | zero => exact evalEq_zero v v'
  | succ m ih => exact evalEq_codeSucc ih

/-!
### Valuation-local congruence for the derived constructors

Each lemma below fixes one assignment `v` and transports an equivalence of the
argument codes, quantified over the possible argument values, to an equivalence
of the constructed codes.  No assignment other than `v` occurs, and no model
assumption beyond `ORingStructure M` is used.  Composition is already covered
by `eval_comp_congr`. -/

theorem eval_comp_congr {m k : ℕ} (c : Code m) (d e : Fin m → Code k) (z : M) (v : Fin k → M)
    (h :
      ∀ (i : Fin m) (x : M),
        Semiformula.Evalb (x :> v) (FFL.FirstOrder.Arithmetic.code (d i)) ↔
          Semiformula.Evalb (x :> v) (FFL.FirstOrder.Arithmetic.code (e i))) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.comp c d)) ↔
      Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (Code.comp c e)) :=
  evalEq_comp c d e h z

theorem eval_codeSucc_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeSucc A)) ↔
      Semiformula.Evalb (z :> v) (code (codeSucc A')) :=
  evalEq_codeSucc hA z

theorem eval_codePos_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codePos A)) ↔
      Semiformula.Evalb (z :> v) (code (codePos A')) :=
  evalEq_codePos hA z

theorem eval_codeInv_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeInv A)) ↔
      Semiformula.Evalb (z :> v) (code (codeInv A')) :=
  evalEq_codeInv hA z

theorem eval_codeAdd_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeAdd A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeAdd A' B')) :=
  evalEq_codeAdd hA hB z

theorem eval_codeMul_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeMul A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeMul A' B')) :=
  evalEq_codeMul hA hB z

theorem eval_codeEq_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeEq A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeEq A' B')) :=
  evalEq_codeEq hA hB z

theorem eval_codeLt_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeLt A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeLt A' B')) :=
  evalEq_codeLt hA hB z

theorem eval_codeAnd_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeAnd A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeAnd A' B')) :=
  evalEq_codeAnd hA hB z

theorem eval_codeOr_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeOr A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeOr A' B')) :=
  evalEq_codeOr hA hB z

/-- An equivalence at `v` lifts to an equivalence at every assignment extending
`v` by one value. -/
theorem eval_codeLift_congr {k : ℕ} (A A' : Code k) (z t : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> t :> v) (code (codeLift A)) ↔
      Semiformula.Evalb (z :> t :> v) (code (codeLift A')) :=
  evalEq_codeLift t t hA z

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
