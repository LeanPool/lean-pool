/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Arithmetic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Bounded search and primitive recursion

`codeBall` decides a bounded universal statement by minimizing the first
counterexample.  The primitive-recursion constructor `codePrec` minimizes a
Gödel-beta code of the whole computation history: `codePrecPredicate` states
that a candidate history has the right initial entry and satisfies the step
relation `codePrecStep` at every index below the argument, and `codePrec`
reads the final entry out of the least such history.

Each construction is accompanied by the theorem that it realizes the intended
function over the natural numbers.  Those `Computes` theorems are the input of
the standard-model bridge, which turns a computation over `ℕ` into evaluation at
standard numerals in an arbitrary model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- The characteristic value of `∀ j ≤ v i, dφ j`, decided by minimizing the
first index at which `dφ` fails or the bound is passed. -/
def codeBall {n : ℕ} (dφ : Code (n + 1)) (i : Fin n) : Code n :=
  codeBind (codeRfindPos (codeOr (codeInv dφ) (codeLe (codeLift (Code.proj i)) codeHead)))
    (codeEq codeHead (codeLift (Code.proj i)))

/-- The arguments at which the step function is applied inside a history: the
history index, the entry recorded at that index, and the ambient arguments. -/
def precStepArgs {n : ℕ} : Fin (n + 2) → Code (n + 3) :=
  Fin.cases (Code.proj 0)
    (Fin.cases (codeBeta (Code.proj 1) (Code.proj 0)) (fun j => Code.proj j.succ.succ.succ))

/-- The step relation between consecutive entries of a history. -/
def codePrecStep {n : ℕ} (dg : Code (n + 2)) : Code (n + 3) :=
  codeEq (codeBeta (Code.proj 1) (codeSucc (Code.proj 0))) (dg.comp precStepArgs)

/-- Reindex a code past the history and index arguments. -/
def codeTailTail {n : ℕ} (df : Code n) : Code (n + 2) :=
  df.comp (fun j => Code.proj j.succ.succ)

/-- A candidate history is correct: its initial entry is the base value, and
every step below the argument agrees with the step function. -/
def codePrecPredicate {n : ℕ} (df : Code n) (dg : Code (n + 2)) : Code (n + 2) :=
  codeAnd (codeEq (codeBeta (Code.proj 0) (codeConst 0)) (codeTailTail df))
    (codeBall (codePrecStep dg) 1)

/-- Primitive recursion with base `df` and step `dg`, read from the least
correct history. -/
def codePrec {n : ℕ} (df : Code n) (dg : Code (n + 2)) : Code (n + 1) :=
  codeBind (codeRfindPos (codePrecPredicate df dg)) (codeBeta codeHead (codeLift codeHead))

/-!
### Standard computations over the natural numbers -/

theorem computes_codeBall {n : ℕ} {dφ : Code (n + 1)} {φ : List.Vector ℕ n → ℕ → ℕ}
    (hφ : Computes dφ (fun w => φ w.tail w.head)) (i : Fin n) :
    Computes (codeBall dφ i) (fun v => Nat.ball (v.get i) (φ v)) :=
  by
  have hF :
    Computes (codeOr (codeInv dφ) (codeLe (codeLift (Code.proj i)) codeHead))
      (fun w => Nat.or (Nat.inv (φ w.tail w.head)) (isLeNat (w.tail.get i) w.head)) :=
    computes_codeOr (computes_codeInv hφ)
      (computes_codeLe (computes_codeLift (computes_proj i)) computes_codeHead)
  have hb :=
    eval_codeBind (eval_codeRfindPos hF)
      (computes_codeEq computes_codeHead (computes_codeLift (computes_proj i)))
  refine eval_of_eq hb ?_
  funext v
  have key :
    ∀ x : ℕ, (0 < Nat.or (Nat.inv (φ v x)) (isLeNat (v.get i) x)) ↔ (φ v x = 0 ∨ v.get i ≤ x) :=
    by
    intro x
    simp only [Nat.orNat_pos_iff, Nat.inv_pos_iff, isLeNat_pos_iff]
    omega
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  by_cases H : ∀ m < v.get i, 0 < φ v m
  · refine ⟨v.get i, ?_, ?_⟩
    · refine Nat.mem_rfind.mpr ?_
      refine ⟨?_, ?_⟩
      · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq]
        exact (key (v.get i)).mpr (Or.inr (le_refl _))
      · intro m hm
        rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not]
        intro hcon
        rcases (key m).mp hcon with h0 | hle
        · have := H m hm; omega
        · omega
    · have hb1 : Nat.ball (v.get i) (φ v) = 1 :=
        Nat.ball_pos_iff_eq_one.mpr (Nat.ball_pos_iff.mpr H)
      simp [isEqNat, hb1]
  · have Hex : ∃ m, m < v.get i ∧ φ v m = 0 :=
      by
      by_contra hc
      refine H (fun m hm => ?_)
      rcases Nat.eq_zero_or_pos (φ v m) with h0 | hp
      · exact absurd ⟨m, hm, h0⟩ hc
      · exact hp
    obtain ⟨hx, hpx⟩ := Nat.find_spec Hex
    have hlx : ∀ y, y < Nat.find Hex → ¬(y < v.get i ∧ φ v y = 0) := fun y hy =>
      Nat.find_min Hex hy
    refine ⟨Nat.find Hex, ?_, ?_⟩
    · refine Nat.mem_rfind.mpr ?_
      refine ⟨?_, ?_⟩
      · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq]
        exact (key (Nat.find Hex)).mpr (Or.inl hpx)
      · intro m hm
        rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not]
        intro hcon
        rcases (key m).mp hcon with h0 | hle
        · exact hlx m hm ⟨by omega, h0⟩
        · omega
    · have hb0 : Nat.ball (v.get i) (φ v) = 0 :=
        Nat.ball_eq_zero_iff.mpr ⟨Nat.find Hex, hx, hpx⟩
      have hne : Nat.find Hex ≠ v.get i := by omega
      simp [isEqNat, hb0, hne]

private def precStepVals {n : ℕ} : Fin (n + 2) → List.Vector ℕ (n + 3) → ℕ :=
  Fin.cases (fun w => w.get 0)
    (Fin.cases (fun w => Nat.beta (w.get 1) (w.get 0)) (fun j w => w.get j.succ.succ.succ))

private lemma computes_precStepArgs {n : ℕ} (k : Fin (n + 2)) :
    Computes (precStepArgs (n := n) k) (precStepVals k) :=
  by
  refine Fin.cases ?_ ?_ k
  · exact computes_proj 0
  · intro j
    refine Fin.cases ?_ ?_ j
    · exact eval_codeBeta (computes_proj 1) (computes_proj 0)
    · intro l; exact computes_proj _

private lemma ofFn_precStepVals {n : ℕ} (w : List.Vector ℕ (n + 3)) :
    (List.Vector.ofFn fun k => precStepVals k w) =
      w.head ::ᵥ Nat.beta w.tail.head w.head ::ᵥ w.tail.tail.tail :=
  by
  refine List.Vector.ext ?_
  intro k
  refine Fin.cases ?_ ?_ k
  · simp [precStepVals]
  · intro j
    refine Fin.cases ?_ ?_ j
    · simp [precStepVals, List.Vector.get_one]
    · intro l
      simp only [precStepVals, Fin.cases_succ, List.Vector.get_ofFn]
      exact
        (((List.Vector.get_tail_succ w.tail.tail l).trans
                (List.Vector.get_tail_succ w.tail l.succ)).trans
            (List.Vector.get_tail_succ w l.succ.succ)).symm

theorem computes_codePrecStep {n : ℕ} {dg : Code (n + 2)} {g : List.Vector ℕ (n + 2) → ℕ}
    (hg : Computes dg g) :
    Computes (codePrecStep dg)
      (fun w =>
        isEqNat (Nat.beta w.tail.head (w.head + 1))
          (g (w.head ::ᵥ Nat.beta w.tail.head w.head ::ᵥ w.tail.tail.tail))) :=
  by
  refine
    (computes_codeEq (eval_codeBeta (computes_proj 1) (computes_codeSucc (computes_proj 0)))
          (computes_comp hg computes_precStepArgs)).of_eq
      ?_
  intro w
  rw [ofFn_precStepVals]
  simp [List.Vector.get_one]

private lemma computes_codeTailTail {n : ℕ} {df : Code n} {f : List.Vector ℕ n → ℕ}
    (hf : Computes df f) : Computes (codeTailTail df) (fun w => f w.tail.tail) :=
  by
  refine
    (computes_comp (g := fun j w => w.get j.succ.succ) hf
          (fun j => computes_proj j.succ.succ)).of_eq
      ?_
  intro w
  congr 1
  refine List.Vector.ext ?_
  intro j
  simp only [List.Vector.get_ofFn]
  exact ((List.Vector.get_tail_succ w.tail j).trans (List.Vector.get_tail_succ w j.succ)).symm

theorem computes_codePrecPredicate {n : ℕ} {df : Code n} {dg : Code (n + 2)}
    {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ} (hf : Computes df f)
    (hg : Computes dg g) :
    Computes (codePrecPredicate df dg)
      (fun w =>
        Nat.and (isEqNat (Nat.beta w.head 0) (f w.tail.tail))
          (Nat.ball w.tail.head
            (fun i =>
              isEqNat (Nat.beta w.head (i + 1))
                (g (i ::ᵥ Nat.beta w.head i ::ᵥ w.tail.tail))))) :=
  by
  have hball :=
    computes_codeBall (φ := fun (v : List.Vector ℕ (n + 2)) (i : ℕ) =>
      isEqNat (Nat.beta v.head (i + 1)) (g (i ::ᵥ Nat.beta v.head i ::ᵥ v.tail.tail)))
      (computes_codePrecStep hg) (1 : Fin (n + 2))
  refine
    (computes_codeAnd
          (computes_codeEq (eval_codeBeta (computes_proj 0) (computes_codeConst 0))
            (computes_codeTailTail hf))
          hball).of_eq
      ?_
  intro w
  simp [List.Vector.get_one]

theorem computes_codePrec {n : ℕ} {df : Code n} {dg : Code (n + 2)} {f : List.Vector ℕ n → ℕ}
    {g : List.Vector ℕ (n + 2) → ℕ} (hf : Computes df f) (hg : Computes dg g) :
    Computes (codePrec df dg)
      (fun v => v.head.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail))) :=
  by
  have hb :=
    eval_codeBind (eval_codeRfindPos (computes_codePrecPredicate hf hg))
      (eval_codeBeta computes_codeHead (computes_codeLift computes_codeHead))
  refine eval_of_eq hb ?_
  funext v
  have key :
    ∀ m : ℕ,
      (0 <
          Nat.and (isEqNat (Nat.beta m 0) (f v.tail))
            (Nat.ball v.head
              (fun i => isEqNat (Nat.beta m (i + 1)) (g (i ::ᵥ Nat.beta m i ::ᵥ v.tail))))) ↔
        (Nat.beta m 0 = f v.tail ∧
          ∀ i < v.head, Nat.beta m (i + 1) = g (i ::ᵥ Nat.beta m i ::ᵥ v.tail)) :=
    by
    intro m
    simp only [Nat.and_pos_iff, isEqNat_pos_iff, Nat.ball_pos_iff]
  have hex :
    ∃ z : ℕ,
      Nat.beta z 0 = f v.tail ∧
        ∀ i < v.head, Nat.beta z (i + 1) = g (i ::ᵥ Nat.beta z i ::ᵥ v.tail) :=
    ⟨Nat.unbeta (Nat.Arithmetic₁.recSequence f g v.head v.tail),
      Nat.Arithmetic₁.beta_unbeta_recSequence_zero f g v.head v.tail, fun i hi =>
      Nat.Arithmetic₁.beta_unbeta_recSequence_succ f g v.head v.tail hi⟩
  obtain ⟨hz0, hzs⟩ := Nat.find_spec hex
  have hzm :
    ∀ m,
      m < Nat.find hex →
        ¬(Nat.beta m 0 = f v.tail ∧
            ∀ i < v.head, Nat.beta m (i + 1) = g (i ::ᵥ Nat.beta m i ::ᵥ v.tail)) :=
    fun m hm => Nat.find_min hex hm
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨Nat.find hex, ?_, ?_⟩
  · refine Nat.mem_rfind.mpr ?_
    refine ⟨?_, ?_⟩
    · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq]
      exact (key (Nat.find hex)).mpr ⟨hz0, hzs⟩
    · intro m hm
      rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not]
      intro hcon
      exact hzm m hm ((key m).mp hcon)
  · rw [Part.mem_some_iff]
    exact (Nat.Arithmetic₁.beta_eq_rec f g hz0 hzs).symm

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
