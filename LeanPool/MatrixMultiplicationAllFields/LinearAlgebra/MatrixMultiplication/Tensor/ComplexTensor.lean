/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation

/-- A three-legged coefficient array over the given scalar type. -/
abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

/-- Tensor formed by multiplying one coefficient function from each leg. -/
def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

/-- Existence of a decomposition as a sum of r rank-one tensors. -/
def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

/-- Apply a linear coordinate map independently to each of the three tensor legs. -/
def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

/-- Contract the first two tensor legs against coefficient functions. -/
def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

/-- Tensor product with paired coordinates on each of the three legs. -/
def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

/-- Block-diagonal direct sum retaining a common summand tag on all three legs. -/
def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

/-- The n-fold tensor product, indexed by words of length n on each leg. -/
def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

/-- Precompose each tensor coordinate with a map of its index set. -/
def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

section ComplexTopology

variable {X Y Z X' Y' Z' : Type*}

/-- Membership in the topological closure of tensors of rank at most r. -/
def BorderRankAtMost
    (T : Tensor ℂ X Y Z) (r : ℕ) : Prop :=
  T ∈ closure {S | RankAtMost S r}

/-- Tensors obtainable by applying three linear coordinate maps to a fixed tensor. -/
def restrictionOrbit [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Set (Tensor ℂ X' Y' Z') :=
  {U | ∃ (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    U = restrict A B C T}

/-- Membership in the topological closure of a tensor's restriction orbit. -/
def DegeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  U ∈ closure (restrictionOrbit T)

theorem RankAtMost.borderRankAtMost
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : RankAtMost T r) :
    BorderRankAtMost T r := subset_closure h

/-- Pulling back coordinates preserves border-rank bounds, without finiteness assumptions. -/
theorem BorderRankAtMost.pullback {T : Tensor ℂ X Y Z} {r : ℕ}
    (h : BorderRankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    BorderRankAtMost (Tensor.pullback fx fy fz T) r := by
  have hcontinuous : Continuous
      (Tensor.pullback fx fy fz : Tensor ℂ X Y Z → Tensor ℂ X' Y' Z') := by
    unfold Tensor.pullback
    fun_prop
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.pullback fx fy fz S) r} :=
    isClosed_closure.preimage hcontinuous
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.pullback fx fy fz S) r} := by
    intro S hS
    exact subset_closure (hS.pullback fx fy fz)
  exact closure_minimal hsubset hclosed h

theorem continuous_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Continuous (Tensor.restrict A B C) := by
  unfold restrict
  fun_prop

theorem BorderRankAtMost.restrict [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : BorderRankAtMost T r)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    BorderRankAtMost (Tensor.restrict A B C T) r := by
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.restrict A B C S) r} :=
    isClosed_closure.preimage (continuous_restrict A B C)
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.restrict A B C S) r} := by
    intro S hS
    exact (hS.restrict A B C).borderRankAtMost
  exact closure_minimal hsubset hclosed h

theorem continuous_product_left {U V W : Type*} (S : Tensor ℂ U V W) :
    Continuous (fun T : Tensor ℂ X Y Z => Tensor.product T S) := by
  unfold product
  fun_prop

theorem continuous_product_right {U V W : Type*} (T : Tensor ℂ X Y Z) :
    Continuous (fun S : Tensor ℂ U V W => Tensor.product T S) := by
  unfold product
  fun_prop

theorem BorderRankAtMost.product {U V W : Type*}
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W} {r s : ℕ}
    (hT : BorderRankAtMost T r) (hS : BorderRankAtMost S s) :
    BorderRankAtMost (Tensor.product T S) (r * s) := by
  have hexact : ∀ T' : Tensor ℂ X Y Z, RankAtMost T' r →
      BorderRankAtMost (Tensor.product T' S) (r * s) := by
    intro T' hT'
    have hclosed : IsClosed {S' : Tensor ℂ U V W |
        BorderRankAtMost (Tensor.product T' S') (r * s)} :=
      isClosed_closure.preimage (continuous_product_right T')
    have hsubset : {S' : Tensor ℂ U V W | RankAtMost S' s} ⊆
        {S' | BorderRankAtMost (Tensor.product T' S') (r * s)} := by
      intro S' hS'
      exact (hT'.product hS').borderRankAtMost
    exact closure_minimal hsubset hclosed hS
  have hclosed : IsClosed {T' : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.product T' S) (r * s)} :=
    isClosed_closure.preimage (continuous_product_left S)
  exact closure_minimal hexact hclosed hT

theorem BorderRankAtMost.of_degeneration [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {r : ℕ}
    (hT : BorderRankAtMost T r) (hTU : DegeneratesTo T U) :
    BorderRankAtMost U r := by
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | BorderRankAtMost S r} := by
    rintro S ⟨A, B, C, rfl⟩
    exact hT.restrict A B C
  exact closure_minimal hsubset isClosed_closure hTU

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
