/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Division-free arithmetic programs over a field and their operation counts. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.RecursiveBlock

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

namespace LinearExpression

variable {Input : Type*}

def sumFin : (n : ℕ) → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .literal 0
  | n + 1, f => .add (f 0) (sumFin n (fun i => f i.succ))

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression F Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

def linear {Term : Type*} [Fintype Term] (a : Term → F) (wire : Term → Input) :
    Expression F Input :=
  sumFin (Fintype.card Term) (fun i =>
    .mul (.literal (a ((Fintype.equivFin Term).symm i)))
      (.input (wire ((Fintype.equivFin Term).symm i))))

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) (inputs : Input → F) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

structure Family (F Input Output : Type*) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family F Input Output) (inputs : Input → F) (o : Output) : F :=
  p.program.eval inputs (p.output o)

def cost (p : Family F Input Output) : ℕ := p.program.cost

def expressions [Fintype Output] (e : Output → Expression F Input) : Family F Input Output :=
  let p := Expression.compileFamily e
  ⟨p.registers, p.program, p.output⟩

theorem eval_expressions [Fintype Output] (e : Output → Expression F Input)
    (inputs : Input → F) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression F Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

def compose (p : Family F Input Mid) (q : Family F Mid Output) : Family F Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose (p : Family F Input Mid) (q : Family F Mid Output)
    (inputs : Input → F) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family F Input Mid) (q : Family F Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

def mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family F Input Output) :
    Family F NewInput Output :=
  ⟨p.registers, p.program.mapInput f, p.output⟩

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) (inputs : NewInput → F) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

omit [Field F] in
theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

def parallel : (r : ℕ) → (Fin r → Family F Input Output) → Family F Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        (Program.oldIndex _ _ (head.output o.2))
        (fun i => Program.newIndex _ _ (tail.output (i, o.2))) o.1 }

theorem eval_parallel (r : ℕ) (p : Fin r → Family F Input Output)
    (inputs : Input → F) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

omit [Field F] in
theorem cost_parallel (r : ℕ) (p : Fin r → Family F Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

def copies (r : ℕ) (p : Family F Input Output) :
    Family F (Fin r × Input) (Fin r × Output) :=
  parallel r (fun i => p.mapInputs (fun x => (i, x)))

theorem eval_copies (r : ℕ) (p : Family F Input Output)
    (inputs : Fin r × Input → F) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

omit [Field F] in
theorem cost_copies (r : ℕ) (p : Family F Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

def ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) :
    Family F (MatrixInput m l q) (Fin m × Fin q) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

omit [Field F] in
@[simp] theorem cost_ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) :
    (ofMatrix p).cost = p.cost := rfl

theorem eval_ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) (hp : p.Correct)
    (inputs : MatrixInput m l q → F) (o : Fin m × Fin q) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

def join {n m : ℕ} (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

theorem rank_bilinear_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left : Fin n₁ × Fin n₂ → F) (right : Fin n₂ × Fin n₃ → F)
    (i : Fin n₁) (k : Fin n₃) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

def leftBlock (a : Fin r → Fin n₁ × Fin n₂ → F)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F) (q : Fin r) :
    Matrix (Fin m₁) (Fin m₂) F :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n₂ × Fin n₃ → F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F) (q : Fin r) :
    Matrix (Fin m₂) (Fin m₃) F :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

theorem block_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m₂) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

section BlockPrograms

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

def inputExpressions (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    Fin r × MatrixInput m₁ m₂ m₃ →
      Expression F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
  | (q, .inl (s, t)) => LinearExpression.linear (a q)
      (fun x => .inl (join x.1 s, join x.2 t))
  | (q, .inr (t, u)) => LinearExpression.linear (b q)
      (fun y => .inr (join y.1 t, join y.2 u))

def inputFamily (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    Family F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
      (Fin r × MatrixInput m₁ m₂ m₃) :=
  Family.expressions (inputExpressions a b)

theorem inputFamily_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (x : MatrixInput m₁ m₂ m₃) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    (inputFamily (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) a b).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) := by
  rw [inputFamily, Family.cost_expressions]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type,
    inputExpressions, LinearExpression.cost_linear, Fintype.card_prod,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

def recursiveProducts (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (p : MatrixAlgorithm F m₁ m₂ m₃) :
    Family F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
      (Fin r × (Fin m₁ × Fin m₃)) :=
  (inputFamily a b).compose (Family.copies r (Family.ofMatrix p))

theorem recursiveProducts_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (s : Fin m₁) (u : Fin m₃) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (recursiveProducts a b p).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

def outputExpressions (c : Fin r → Fin n₃ × Fin n₁ → F) :
    Fin (n₁ * m₁) × Fin (n₃ * m₃) → Expression F (Fin r × (Fin m₁ × Fin m₃)) :=
  fun o => LinearExpression.linear
    (fun q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

def outputFamily (c : Fin r → Fin n₃ × Fin n₁ → F) :
    Family F (Fin r × (Fin m₁ × Fin m₃)) (Fin (n₁ * m₁) × Fin (n₃ * m₃)) :=
  Family.expressions (outputExpressions c)

theorem outputFamily_eval (c : Fin r → Fin n₃ × Fin n₁ → F)
    (inputs : Fin r × (Fin m₁ × Fin m₃) → F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n₃ × Fin n₁ → F) :
    (outputFamily (m₁ := m₁) (m₃ := m₃) c).cost = 2 * r * n₁ * n₃ * m₁ * m₃ := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

def algorithm (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) :
    MatrixAlgorithm F (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

theorem algorithm_correct
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (algorithm a b c p).cost = r * p.cost +
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃)) r)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n₁ * m₁) (n₂ * m₂) (n₃ * m₃), q.Correct ∧
      q.cost = r * p.cost +
        2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end BlockPrograms

end MatrixMultiplication.Arithmetic.RecursiveBlock

end

end MatrixMultiplicationAllFields
