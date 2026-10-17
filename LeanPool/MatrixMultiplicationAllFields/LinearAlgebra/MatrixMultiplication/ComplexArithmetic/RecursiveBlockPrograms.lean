/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic interfaces specialized from the shared field-generic implementation. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

namespace LinearExpression

variable {Input : Type*}

/-- Form a finite sum of arithmetic expressions for the block-recursion construction. -/
abbrev sumFin : (n : ℕ) → (Fin n → Expression Input) → Expression Input :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.sumFin (F := ℂ)

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.eval_sumFin (F := ℂ) n f inputs

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.cost_sumFin (F := ℂ) n f

/-- Encode a finite linear combination of selected input wires as an arithmetic expression. -/
abbrev linear {Term : Type*} [Fintype Term] (a : Term → ℂ) (wire : Term → Input) :
    Expression Input :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.linear (F := ℂ) a wire

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) (inputs : Input → ℂ) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.eval_linear (F := ℂ) a wire inputs

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.cost_linear (F := ℂ) a wire

end LinearExpression

/-- A shared complex straight-line program with an indexed family of outputs. -/
abbrev Family (Input Output : Type*) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family ℂ Input Output

namespace Family

variable {Input Mid Output : Type*}

/-- Evaluate one member of a program's output family. -/
abbrev eval (p : Family Input Output) (inputs : Input → ℂ) (o : Output) : ℂ :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval (F := ℂ) p inputs o

/-- Arithmetic cost of the shared program, counting each gate once. -/
abbrev cost (p : Family Input Output) : ℕ :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost (F := ℂ) p

/-- Compile an indexed family of expressions into a shared output program. -/
abbrev expressions [Fintype Output] (e : Output → Expression Input) : Family Input Output :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.expressions (F := ℂ) e

theorem eval_expressions [Fintype Output] (e : Output → Expression Input)
    (inputs : Input → ℂ) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_expressions (F := ℂ) e inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_expressions (F := ℂ) e

/-- Connect the outputs of one program family to the inputs of another. -/
abbrev compose (p : Family Input Mid) (q : Family Mid Output) : Family Input Output :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.compose (F := ℂ) p q

theorem eval_compose (p : Family Input Mid) (q : Family Mid Output)
    (inputs : Input → ℂ) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_compose (F := ℂ) p q inputs o

theorem cost_compose (p : Family Input Mid) (q : Family Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_compose (F := ℂ) p q

/-- Relabel the input wires of a program family. -/
abbrev mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family Input Output) :
    Family NewInput Output :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.mapInputs (F := ℂ) f p

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) (inputs : NewInput → ℂ) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_mapInputs (F := ℂ) f p inputs o

theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) : (p.mapInputs f).cost = p.cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_mapInputs (F := ℂ) f p

/-- Concatenate a finite family of programs with a common input space. -/
abbrev parallel : (r : ℕ) → (Fin r → Family Input Output) → Family Input (Fin r × Output) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.parallel (F := ℂ)

theorem eval_parallel (r : ℕ) (p : Fin r → Family Input Output)
    (inputs : Input → ℂ) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_parallel (F := ℂ) r p inputs o

theorem cost_parallel (r : ℕ) (p : Fin r → Family Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_parallel (F := ℂ) r p

/-- Run independent copies of a program family on separately indexed inputs. -/
abbrev copies (r : ℕ) (p : Family Input Output) :
    Family (Fin r × Input) (Fin r × Output) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.copies (F := ℂ) r p

theorem eval_copies (r : ℕ) (p : Family Input Output)
    (inputs : Fin r × Input → ℂ) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_copies (F := ℂ) r p inputs o

theorem cost_copies (r : ℕ) (p : Family Input Output) :
    (copies r p).cost = r * p.cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_copies (F := ℂ) r p

/-- View a matrix multiplication algorithm as a family indexed by output positions. -/
abbrev ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    Family (MatrixInput m) (Fin m × Fin m) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.ofMatrix (F := ℂ) p

theorem cost_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    (ofMatrix p).cost = p.cost :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix (F := ℂ) p

theorem eval_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) (hp : p.Correct)
    (inputs : MatrixInput m → ℂ) (o : Fin m × Fin m) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval_ofMatrix (F := ℂ) p hp inputs o

end Family

variable {n r m : ℕ}

/-- Flatten a pair of finite block and within-block indices. -/
abbrev join (i : Fin n) (j : Fin m) : Fin (n * m) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.join i j

theorem rank_bilinear_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left right : Fin n × Fin n → ℂ) (i k : Fin n) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.rank_bilinear_identity (F := ℂ)
    a b c h left right i k

/-- The left matrix block obtained from one linear form in a tensor-rank decomposition. -/
abbrev leftBlock (a : Fin r → Fin n × Fin n → ℂ)
    (A : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.leftBlock (F := ℂ) a A q

/-- The right matrix block obtained from one linear form in a tensor-rank decomposition. -/
abbrev rightBlock (b : Fin r → Fin n × Fin n → ℂ)
    (B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.rightBlock (F := ℂ) b B q

theorem block_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ)
    (i k : Fin n) (s u : Fin m) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.block_identity (F := ℂ) a b c h A B i k s u

/-- Expressions forming the left and right inputs to all recursive block products. -/
abbrev inputExpressions (a b : Fin r → Fin n × Fin n → ℂ) :
    Fin r × MatrixInput m → Expression (MatrixInput (n * m)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.inputExpressions (F := ℂ) a b

/-- Compile the input linear forms required by a tensor-rank block decomposition. -/
abbrev inputFamily (a b : Fin r → Fin n × Fin n → ℂ) :
    Family (MatrixInput (n * m)) (Fin r × MatrixInput m) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.inputFamily (F := ℂ) a b

theorem inputFamily_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (x : MatrixInput m) :
    (inputFamily a b).eval (MatrixMultiplication.Arithmetic.matrixInputs A B) (q, x) =
      MatrixMultiplication.Arithmetic.matrixInputs (leftBlock a A q) (rightBlock b B q) x :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.inputFamily_eval (F := ℂ) a b A B q x

theorem inputFamily_cost (a b : Fin r → Fin n × Fin n → ℂ) :
    (inputFamily (m := m) a b).cost = 4 * r * n ^ 2 * m ^ 2 := by
  convert MatrixMultiplication.Arithmetic.RecursiveBlock.inputFamily_cost (F := ℂ) a b using 1
  ring

/-- Run the smaller matrix algorithm on each pair of transformed input blocks. -/
abbrev recursiveProducts (a b : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    Family (MatrixInput (n * m)) (Fin r × (Fin m × Fin m)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.recursiveProducts (F := ℂ) a b p

theorem recursiveProducts_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) (hp : p.Correct)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (s u : Fin m) :
    (recursiveProducts a b p).eval (MatrixMultiplication.Arithmetic.matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.recursiveProducts_eval (F := ℂ) a b p hp A B q s u

theorem recursiveProducts_cost (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (recursiveProducts a b p).cost = 4 * r * n ^ 2 * m ^ 2 + r * p.cost := by
  convert MatrixMultiplication.Arithmetic.RecursiveBlock.recursiveProducts_cost (F := ℂ)
    a b p using 1
  ring

/-- Expressions recombining recursive products into the final matrix entries. -/
abbrev outputExpressions (c : Fin r → Fin n × Fin n → ℂ) :
    Fin (n * m) × Fin (n * m) → Expression (Fin r × (Fin m × Fin m)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.outputExpressions (F := ℂ) c

/-- Compile the output linear forms of the tensor-rank decomposition. -/
abbrev outputFamily (c : Fin r → Fin n × Fin n → ℂ) :
    Family (Fin r × (Fin m × Fin m)) (Fin (n * m) × Fin (n * m)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.outputFamily (F := ℂ) c

theorem outputFamily_eval (c : Fin r → Fin n × Fin n → ℂ)
    (inputs : Fin r × (Fin m × Fin m) → ℂ) (i k : Fin n) (s u : Fin m) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.outputFamily_eval (F := ℂ) c inputs i k s u

theorem outputFamily_cost (c : Fin r → Fin n × Fin n → ℂ) :
    (outputFamily (m := m) c).cost = 2 * r * n ^ 2 * m ^ 2 := by
  convert MatrixMultiplication.Arithmetic.RecursiveBlock.outputFamily_cost (F := ℂ) c using 1
  ring

/-- Construct the larger matrix algorithm from a rank decomposition and a smaller algorithm. -/
abbrev algorithm (a b c : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    MatrixAlgorithm (n * m) :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.algorithm (F := ℂ) a b c p

theorem algorithm_correct
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm m) (hp : p.Correct) : (algorithm a b c p).Correct :=
  MatrixMultiplication.Arithmetic.RecursiveBlock.algorithm_correct (F := ℂ) a b c h p hp

theorem algorithm_cost (a b c : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (algorithm a b c p).cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  convert MatrixMultiplication.Arithmetic.RecursiveBlock.algorithm_cost (F := ℂ) a b c p using 1
  ring

theorem rank_block_step (h : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) r)
    (p : MatrixAlgorithm m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm (n * m), q.Correct ∧
      q.cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  obtain ⟨q, hq, hcost⟩ := MatrixMultiplication.Arithmetic.RecursiveBlock.rank_block_step h p hp
  refine ⟨q, hq, ?_⟩
  change MatrixMultiplication.Arithmetic.MatrixAlgorithm.cost q = _
  rw [hcost]
  ring

end MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

end

end MatrixMultiplicationAllFields
