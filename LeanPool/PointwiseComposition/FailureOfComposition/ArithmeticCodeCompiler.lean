/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ProgramGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.ArithmeticProgramOperations
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteMinimizationGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Compilation of Foundation's finite-arity arithmetic codes to unary Mathlib
program descriptions, with arithmetic proofs for the encoded inputs.
-/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace ArithmeticCodeCompiler

open ProgramGraph

/-- The ACode construction in `FailureOfComposition.ArithmeticCodeCompiler`. -/
abbrev ACode :=
  Nat.ArithPart₁.Code

/-- Nested pairs ending in zero encode a fixed finite input vector. -/
noncomputable def encodeVector {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] :
    {n : ℕ} → (Fin n → M) → M
  | 0, _ => 0
  | n + 1, v => pair (v 0) (encodeVector (fun i : Fin n => v i.succ))

/-- The projection Code construction in `FailureOfComposition.ArithmeticCodeCompiler`. -/
def projectionCode : (n : ℕ) → Fin n → PCode
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases .left (fun j => .comp (projectionCode n j) .right) i

/-- The tuple Code construction in `FailureOfComposition.ArithmeticCodeCompiler`. -/
def tupleCode : (n : ℕ) → (Fin n → PCode) → PCode
  | 0, _ => .zero
  | n + 1, d => .pair (d 0) (tupleCode n (fun i => d i.succ))

/-- The swap Code construction in `FailureOfComposition.ArithmeticCodeCompiler`. -/
def swapCode : PCode :=
  .pair .right .left

/-- The search Zero Code construction in `FailureOfComposition.ArithmeticCodeCompiler`. -/
def searchZeroCode (c : PCode) : PCode :=
  .comp (.rfind' (.comp c swapCode)) (.pair Nat.Partrec.Code.id .zero)

/-- Structural compilation preserves the finite vector coding at every
constructor; minimization prepends its candidate to that vector. -/
def compile : {n : ℕ} → ACode n → PCode
  | _, .zero _ => .zero
  | _, .one _ => Nat.Partrec.Code.const 1
  | n, .add i j =>
    .comp ConcreteEvaluator.addProgram (.pair (projectionCode n i) (projectionCode n j))
  | n, .mul i j =>
    .comp ConcreteEvaluator.mulProgram (.pair (projectionCode n i) (projectionCode n j))
  | n, .proj i => projectionCode n i
  | n, .equal i j =>
    .comp ConcreteEvaluator.eqProgram (.pair (projectionCode n i) (projectionCode n j))
  | n, .lt i j =>
    .comp ConcreteEvaluator.ltProgram (.pair (projectionCode n i) (projectionCode n j))
  | _, @Nat.ArithPart₁.Code.comp _ n c d =>
    .comp (compile c) (tupleCode n (fun i => compile (d i)))
  | _, .rfind c => searchZeroCode (compile c)

/-- Unary programs accept the ordinary input directly. -/
def unaryCompile (c : ACode 1) : PCode :=
  .comp (compile c) (.pair Nat.Partrec.Code.id .zero)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem computes_projection :
    {n : ℕ} →
      ∀ (i : Fin n) (v : Fin n → M) (y : M),
        Computes (projectionCode n i) (encodeVector v) y ↔ y = v i
  | 0, i, _, _ => Fin.elim0 i
  | n + 1, i, v, y => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [projectionCode, Fin.cases_zero, encodeVector, computes_left, pi₁_pair]
    · rw [projectionCode, Fin.cases_succ]
      rw [computes_comp]
      simp_rw [computes_right]
      simp only [encodeVector, pi₂_pair, exists_eq_left]
      exact computes_projection j (fun k => v k.succ) y

theorem computes_tuple :
    (n : ℕ) →
      ∀ (d : Fin n → PCode) (x z : M),
        Computes (tupleCode n d) x z ↔
          ∃ w : Fin n → M, z = encodeVector w ∧ ∀ i, Computes (d i) x (w i)
  | 0, d, x, z => by
    rw [tupleCode, computes_zero]
    simp only [encodeVector]
    constructor
    · intro h
      exact ⟨Fin.elim0, h, fun i => Fin.elim0 i⟩
    · rintro ⟨_, h, _⟩
      exact h
  | n + 1, d, x, z => by
    rw [tupleCode, computes_pair]
    constructor
    · rintro ⟨a, b, ha, hb, hz⟩
      obtain ⟨w, rfl, hw⟩ := (computes_tuple n (fun i => d i.succ) x b).mp hb
      refine ⟨a :> w, ?_, ?_⟩
      · simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] using hz
      · intro i
        exact Fin.cases ha (fun j => hw j) i
    · rintro ⟨w, rfl, hw⟩
      refine ⟨w 0, encodeVector (fun i : Fin n => w i.succ), hw 0, ?_, rfl⟩
      exact
        (computes_tuple n (fun i => d i.succ) x _).mpr
          ⟨(fun i => w i.succ), rfl, fun i => hw i.succ⟩

theorem computes_binary_application {n : ℕ} (p : PCode) (i j : Fin n) (v : Fin n → M) (y : M) :
    Computes (.comp p (.pair (projectionCode n i) (projectionCode n j))) (encodeVector v) y ↔
      Computes p (pair (v i) (v j)) y :=
  by
  rw [computes_comp]
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := (computes_pair _ _ _ _).mp hu
    rw [(computes_projection i v a).mp ha, (computes_projection j v b).mp hb] at hp
    exact hp
  · intro hp
    refine ⟨pair (v i) (v j), ?_, hp⟩
    exact
      (computes_pair _ _ _ _).mpr
        ⟨v i, v j, (computes_projection i v _).mpr rfl, (computes_projection j v _).mpr rfl,
          rfl⟩

theorem computes_swap (a b z : M) : Computes swapCode (pair a b) z ↔ z = pair b a :=
  by
  rw [swapCode, computes_pair]
  simp only [computes_right, computes_left, pi₁_pair, pi₂_pair]
  constructor
  · rintro ⟨a', b', rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨b, a, rfl, rfl, h⟩

theorem computes_candidate_swap (c : PCode) (a b z : M) :
    Computes (.comp c swapCode) (pair a b) z ↔ Computes c (pair b a) z :=
  by
  rw [computes_comp]
  simp only [computes_swap, exists_eq_left]

omit [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] in
private theorem arithmetic_eval_iff_aux {n : ℕ} (c : ACode n) (z : M) (v : Fin n → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code c) ↔
      Semiformula.Evalf (M := M) (z :> v) (FFL.FirstOrder.Arithmetic.codeAux c) :=
  by
  simp [FFL.FirstOrder.Arithmetic.code, Semiformula.eval_rew, Matrix.empty_eq,
    Function.comp_def]

omit [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] in
private theorem arithmetic_rfind_eval {n : ℕ} (c : ACode (n + 1)) (z : M) (v : Fin n → M) :
    Semiformula.Evalb (z :> v) (FFL.FirstOrder.Arithmetic.code (.rfind c)) ↔
      Semiformula.Evalb ((0 : M) :> z :> v) (FFL.FirstOrder.Arithmetic.code c) ∧
        ∀ t : M,
          t < z →
            ∃ w : M,
              w ≠ 0 ∧ Semiformula.Evalb (w :> t :> v) (FFL.FirstOrder.Arithmetic.code c) :=
  by
  simp only [arithmetic_eval_iff_aux]
  simp [FFL.FirstOrder.Arithmetic.codeAux, Semiformula.eval_rew, Function.comp_def,
    Matrix.empty_eq, Matrix.comp_vecCons']

theorem computes_pair_zero (x z : M) :
    Computes (.pair Nat.Partrec.Code.id .zero) x z ↔ z = pair x 0 :=
  by
  rw [computes_pair]
  simp only [computes_id, computes_zero]
  constructor
  · rintro ⟨a, b, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨x, 0, rfl, rfl, h⟩

theorem computes_searchZero (c : PCode) (x y : M) :
    Computes (searchZeroCode c) x y ↔
      Computes c (pair y x) 0 ∧ ∀ k : M, k < y → ∃ z : M, z ≠ 0 ∧ Computes c (pair k x) z :=
  by
  rw [searchZeroCode, computes_comp]
  simp only [computes_pair_zero, exists_eq_left]
  have h := ConcreteEvaluator.eventualGraph_rfind_code_eval (.comp c swapCode) x y
  change
    Computes (.rfind' (.comp c swapCode)) (pair x 0) y ↔
      Computes (.comp c swapCode) (pair x y) 0 ∧
        ∀ k : M, k < y → ∃ z : M, z ≠ 0 ∧ Computes (.comp c swapCode) (pair x k) z at h
  simpa only [computes_candidate_swap] using h

/-- The structural compiler preserves the graph in every PA model. All input
components and outputs may be nonstandard elements of that model. -/
theorem computes_compile {n : ℕ} (c : ACode n) (v : Fin n → M) (y : M) :
    Computes (compile c) (encodeVector v) y ↔
      Semiformula.Evalb (y :> v) (FFL.FirstOrder.Arithmetic.code c) :=
  by
  induction c generalizing y with
  | zero n => rw [compile, computes_zero, CategoricalRiceShapiro.ArithmeticCode.eval_zero_iff]
  | one
    n =>
    rw [compile, computes_const, CategoricalRiceShapiro.ArithmeticCode.eval_one_iff]
    simp only [Nat.cast_one]
  | add i j =>
    rw [compile, computes_binary_application, ConcreteEvaluator.computes_add_iff,
      CategoricalRiceShapiro.ArithmeticCode.eval_add_iff]
  | mul i j =>
    rw [compile, computes_binary_application, ConcreteEvaluator.computes_mul_iff,
      CategoricalRiceShapiro.ArithmeticCode.eval_mul_iff]
  | proj i =>
    rw [compile, computes_projection, CategoricalRiceShapiro.ArithmeticCode.eval_proj_iff]
  | equal i j =>
    rw [compile, computes_binary_application, ConcreteEvaluator.computes_eq_iff,
      CategoricalRiceShapiro.ArithmeticCode.eval_equal_iff]
  | lt i j =>
    rw [compile, computes_binary_application, ConcreteEvaluator.computes_lt_iff,
      CategoricalRiceShapiro.ArithmeticCode.eval_lt_iff]
  | comp c d ihc
    ihd =>
    rw [compile, computes_comp, CategoricalRiceShapiro.ArithmeticCode.eval_comp_iff]
    constructor
    · rintro ⟨u, hu, hc⟩
      obtain ⟨w, rfl, hw⟩ := (computes_tuple _ _ _ _).mp hu
      exact ⟨w, (ihc w y).mp hc, fun i => (ihd i v (w i)).mp (hw i)⟩
    · rintro ⟨w, hc, hd⟩
      refine ⟨encodeVector w, ?_, (ihc w y).mpr hc⟩
      exact (computes_tuple _ _ _ _).mpr ⟨w, rfl, fun i => (ihd i v (w i)).mpr (hd i)⟩
  | rfind c ih =>
    rw [compile, computes_searchZero, arithmetic_rfind_eval]
    have hi (k z : M) := ih (k :> v) z
    simp only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] at hi
    exact
      and_congr (hi y 0)
        (forall_congr' fun k =>
          imp_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => hi k z)

/-- Unary compilation realizes the source arithmetic graph on the ordinary
input, without exposing the tuple representation. -/
theorem computes_unaryCompile (c : ACode 1) (x y : M) :
    Computes (unaryCompile c) x y ↔
      Semiformula.Evalb ![y, x] (FFL.FirstOrder.Arithmetic.code c) :=
  by
  rw [unaryCompile, computes_comp]
  simp only [computes_pair_zero, exists_eq_left]
  have h := computes_compile c ![x] y
  simpa only [encodeVector, Matrix.cons_val_zero] using h

/-- The source arithmetic-code graph, in input-output argument order. -/
def sourceGraph (c : ACode 1) : ProofSearch.Graph :=
  ((.mkSigma (FFL.FirstOrder.Arithmetic.code c) (code_sigma_one c)) : Σ₁.Semisentence 2).rew
    (Rew.subst ![(#1 : ArithmeticSemiterm Empty 2), #0])

omit [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] in
theorem sourceGraph_eval (c : ACode 1) (x y : M) :
    (sourceGraph c).val.Evalb ![x, y] ↔
      Semiformula.Evalb ![y, x] (FFL.FirstOrder.Arithmetic.code c) :=
  by simp [sourceGraph]

/-- PA proves the uniform realization equation for this explicit compiler. -/
theorem unaryCompile_realizes (c : ACode 1) :
    ProofSearch.Uniform 𝐏𝐀 (ConcreteEvaluator.eventualGraph (encode (unaryCompile c)))
      (sourceGraph c) :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, ProofSearch.uniformSentence_eval]
  intro x y
  rw [sourceGraph_eval]
  exact computes_unaryCompile c x y

end ArithmeticCodeCompiler
end FailureOfComposition

end

end PointwiseComposition
