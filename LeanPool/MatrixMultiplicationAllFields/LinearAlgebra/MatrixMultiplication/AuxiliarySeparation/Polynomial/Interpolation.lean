/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Polynomial/Interpolation.lean`,
by Jeroen Zuiddam, 2026: interpolation nodes taken from an embedding of `ℕ` into `K ∖ {0}`
(upstream: `1, …, D+1` in ℂ); `ℂ` replaced by a field `K`; removed the ℂ-only lemma
`restrictionDegeneration_power_rankAtMost`, which the retained proof does not need;
`[IsAlgClosed K]` is assumed by the declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Exact interpolation away from zero

The coefficient-extraction theorem already proved for matrix multiplication is
used here with `D + 1` pairwise distinct nonzero elements of `K`, chosen using an
embedding of the naturals (`interpolationNode`).  In particular a polynomial
degeneration can be recovered by a finite sum of its ordinary restrictions at
nonzero parameters, with the leading power divided out at each parameter.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The nonzero elements of an infinite field form an infinite set. -/
theorem infinite_nonzero [Infinite K] : Infinite ↥({0}ᶜ : Set K) :=
  Set.infinite_coe_iff.mpr (Set.finite_singleton (0 : K)).infinite_compl

variable (K) in
/-- A choice of `D + 1` distinct nonzero interpolation parameters.  Over `ℂ` the
paper uses `1, ..., D + 1`; here any infinite field suffices (an algebraically
closed field is infinite), so the parameters are taken from an embedding of
`ℕ` into the nonzero elements. -/
def interpolationNode [IsAlgClosed K] (D : ℕ) (i : Fin (D + 1)) : K :=
  (@Infinite.natEmbedding _ infinite_nonzero i.val).1

theorem interpolationNode_injective [IsAlgClosed K] (D : ℕ) :
    Function.Injective (interpolationNode K D) := by
  intro i j hij
  apply Fin.ext
  exact (@Infinite.natEmbedding _ infinite_nonzero).injective (Subtype.ext hij)

theorem interpolationNode_ne_zero [IsAlgClosed K] (D : ℕ) (i : Fin (D + 1)) :
    interpolationNode K D i ≠ 0 := by
  have h := (@Infinite.natEmbedding _ (infinite_nonzero (K := K)) i.val).2
  exact Set.mem_compl_singleton_iff.mp h

/-- The constant-coefficient functional expressed in the Lagrange basis. -/
def constantInterpolationWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (i : ι) : K :=
  (Lagrange.basis Finset.univ nodes i).coeff 0

/-- Exact constant recovery; this specializes the existing coefficient theorem. -/
theorem constant_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (hinj : Function.Injective nodes) (p : Polynomial K)
    (hdegree : p.degree < Fintype.card ι) :
    p.coeff 0 = ∑ i, constantInterpolationWeight nodes i * p.eval (nodes i) := by
  simpa only [constantInterpolationWeight, mul_comm] using
    Tensor.coeff_eq_sum_eval nodes hinj p 0 hdegree

/-- A degree-`D` polynomial is recovered at zero using only nonzero parameters. -/
theorem constant_eq_sum_nonzero_eval [IsAlgClosed K] (D : ℕ) (p : Polynomial K)
    (hdegree : p.degree ≤ D) :
    p.coeff 0 = ∑ i, constantInterpolationWeight (interpolationNode K D) i *
      p.eval (interpolationNode K D i) := by
  apply constant_eq_sum_eval _ (interpolationNode_injective D)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt hdegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

/-- Removing a leading power before interpolation only requires evaluations at
nonzero nodes.  The degree bound is on the normalized polynomial. -/
theorem leading_eq_sum_normalized_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0) (p q : Polynomial K) (d : ℕ)
    (hp : p = Polynomial.X ^ d * q) (hdegree : q.degree < Fintype.card ι) :
    p.coeff d = ∑ i, constantInterpolationWeight nodes i *
      (nodes i ^ d)⁻¹ * p.eval (nodes i) := by
  have hcoeff : p.coeff d = q.coeff 0 := by
    rw [hp, Polynomial.coeff_X_pow_mul']
    simp
  rw [hcoeff, constant_eq_sum_eval nodes hinj q hdegree]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have hpow : nodes i ^ d ≠ 0 := pow_ne_zero d (hnonzero i)
  calc
    constantInterpolationWeight nodes i * q.eval (nodes i) =
        constantInterpolationWeight nodes i *
          ((nodes i ^ d)⁻¹ * (nodes i ^ d)) * q.eval (nodes i) := by
            rw [inv_mul_cancel₀ hpow, mul_one]
    _ = _ := by ring

/-- A leading coefficient is a finite linear combination of normalized
evaluations, assuming all lower coefficients vanish. -/
theorem leading_eq_sum_nonzero_eval [IsAlgClosed K] (D d : ℕ) (p : Polynomial K)
    (hvanish : ∀ j < d, p.coeff j = 0) (hdegree : p.degree ≤ D) :
    p.coeff d = ∑ i, constantInterpolationWeight (interpolationNode K D) i *
      (interpolationNode K D i ^ d)⁻¹ * p.eval (interpolationNode K D i) := by
  obtain ⟨q, hp⟩ := Polynomial.X_pow_dvd_iff.mpr hvanish
  apply leading_eq_sum_normalized_eval _ (interpolationNode_injective D)
    (interpolationNode_ne_zero D) p q d hp
  have hqdegree : q.degree ≤ p.degree := by
    rw [hp, mul_comm]
    exact Polynomial.degree_le_mul_left q (pow_ne_zero d Polynomial.X_ne_zero)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt (le_trans hqdegree hdegree)
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

section PolynomialRestriction

variable {X Y Z X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'}
variable {k Lx Ly Lz : ℕ}

/-- Evaluating the polynomial restriction evaluates its three local maps. -/
theorem restrictionDegeneration_eval
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (t : K) (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').eval t =
      Tensor.restrict (fun a x => (L.leftMap a x).eval t)
        (fun b y => (L.middleMap b y).eval t)
        (fun c z => (L.rightMap c z).eval t) T x' y' z' := by
  simp only [Tensor.PolynomialRestrictionDegeneration.basePolynomial, Tensor.restrict,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- The degree of a polynomial restriction is bounded by the sum of the
degrees of its three local maps. -/
theorem restrictionDegeneration_degree
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').degree ≤ (Lx + Ly + Lz : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold Tensor.PolynomialRestrictionDegeneration.basePolynomial Tensor.restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hconstant : (Polynomial.C (T x y z)).natDegree ≤ 0 := by simp
  simpa using Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hconstant

/-- The existing polynomial-approximation API applies to a polynomial
restriction as soon as the source tensor has a rank bound. -/
def restrictionDegenerationApproximation
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.PolynomialApproximation U r k (Lx + Ly + Lz) where
  polynomial := L.basePolynomial
  rank_bound := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  vanishes := L.vanishes
  leading := L.leading
  degree_bound := restrictionDegeneration_degree L

/-- A polynomial degeneration yields an exact finite sum of ordinary
restrictions at nonzero parameters.  There are `Lx + Ly + Lz + 1` terms. -/
theorem restrictionDegeneration_recovery [IsAlgClosed K]
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    U x' y' z' = ∑ i,
      constantInterpolationWeight (interpolationNode K (Lx + Ly + Lz)) i *
      (interpolationNode K (Lx + Ly + Lz) i ^ k)⁻¹ *
      Tensor.restrict
        (fun a x => (L.leftMap a x).eval (interpolationNode K (Lx + Ly + Lz) i))
        (fun b y => (L.middleMap b y).eval (interpolationNode K (Lx + Ly + Lz) i))
        (fun c z => (L.rightMap c z).eval (interpolationNode K (Lx + Ly + Lz) i))
        T x' y' z' := by
  rw [← L.leading x' y' z']
  change (L.basePolynomial x' y' z').coeff k = _
  rw [leading_eq_sum_nonzero_eval (Lx + Ly + Lz) k
    (L.basePolynomial x' y' z') (L.vanishes x' y' z')
    (restrictionDegeneration_degree L x' y' z')]
  simp_rw [restrictionDegeneration_eval]

/-- Finite interpolation converts a polynomial degeneration into an exact
rank bound with its explicit number of evaluation parameters. -/
theorem restrictionDegeneration_rankAtMost [IsAlgClosed K]
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.RankAtMost U ((Lx + Ly + Lz + 1) * r) := by
  have hbase := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  change Tensor.RankAtMost L.basePolynomial r at hbase
  have hdegree (x' : X') (y' : Y') (z' : Z') :
      (L.basePolynomial x' y' z').degree <
        Fintype.card (Fin (Lx + Ly + Lz + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (restrictionDegeneration_degree L x' y' z')
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (Lx + Ly + Lz)))
  have h := hbase.coeff (interpolationNode K (Lx + Ly + Lz))
    (interpolationNode_injective _) k hdegree
  have hleading : (fun x' y' z' => (L.basePolynomial x' y' z').coeff k) = U := by
    funext x' y' z'
    exact L.leading x' y' z'
  simpa only [hleading, Fintype.card_fin] using h

end PolynomialRestriction

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
