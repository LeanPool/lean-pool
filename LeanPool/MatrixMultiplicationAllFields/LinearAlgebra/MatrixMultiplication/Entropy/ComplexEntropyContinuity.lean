/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_eq_negMulLog (p : ℝ) : entropyTerm p = Real.negMulLog p := rfl

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

theorem mul_entropyTerm_inv (x : ℝ) : x * entropyTerm x⁻¹ = Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [entropyTerm, Real.log_inv]
    calc
      _ = (x * x⁻¹) * Real.log x := by ring
      _ = Real.log x := by rw [mul_inv_cancel₀ hx, one_mul]

theorem finiteEntropy_uniform {A : Type*} [Fintype A] :
    finiteEntropy (fun _a : A => (Fintype.card A : ℝ)⁻¹) =
      Real.log (Fintype.card A) := by
  simp only [finiteEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_entropyTerm_inv (Fintype.card A)

theorem finiteEntropy_deterministic {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : finiteEntropy (fun b => if b = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change entropyTerm (if b = a then 1 else 0) = 0
  split_ifs <;> simp

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem concaveOn_entropyTerm : ConcaveOn ℝ (Set.Ici 0) entropyTerm :=
  Real.concaveOn_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finsetSum _ fun value _ =>
    continuous_entropyTerm.comp (continuous_apply value)

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

theorem tendsto_entropyTerm_zero {I : Type*} {l : Filter I} {p : I → ℝ}
    (h : Tendsto p l (𝓝 0)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 0) := by
  simpa only [entropyTerm_zero] using tendsto_entropyTerm h

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

theorem finiteEntropy_mix_le {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * finiteEntropy p + b * finiteEntropy q ≤
      finiteEntropy (fun i => a * p i + b * q i) := by
  calc
    a * finiteEntropy p + b * finiteEntropy q =
        ∑ i, (a * entropyTerm (p i) + b * entropyTerm (q i)) := by
      simp only [finiteEntropy, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ finiteEntropy (fun i => a * p i + b * q i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact concaveOn_entropyTerm.2 (hp i) (hq i) ha hb hab

theorem finiteEntropy_le_log_card {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (htotal : ∑ a, p a = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card A) := by
  classical
  have hcard : 0 < Fintype.card A := by
    by_contra h
    have : IsEmpty A := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    simp at htotal
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr hcard
  have hw : ∑ _a : A, (Fintype.card A : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul, hn.ne']
  have hJ := concaveOn_entropyTerm.le_map_sum
    (t := (Finset.univ : Finset A))
    (w := fun _a : A => (Fintype.card A : ℝ)⁻¹) (p := p)
    (fun _a _ha => (inv_pos.mpr hn).le) hw (fun a _ha => hp a)
  have hJ' : (Fintype.card A : ℝ)⁻¹ * finiteEntropy p ≤
      entropyTerm (Fintype.card A : ℝ)⁻¹ := by
    simpa only [smul_eq_mul, ← Finset.mul_sum, htotal, mul_one, finiteEntropy] using hJ
  calc
    finiteEntropy p = (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ)⁻¹ * finiteEntropy p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ (Fintype.card A : ℝ) * entropyTerm (Fintype.card A : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hJ' hn.le
    _ = Real.log (Fintype.card A) := mul_entropyTerm_inv (Fintype.card A)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

@[simp] theorem uniform_entropy [Nonempty A] :
    finiteEntropy (uniform A).mass = Real.log (Fintype.card A) :=
  finiteEntropy_uniform

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

@[simp] theorem pure_entropy (a : A) : finiteEntropy (pure a).mass = 0 := by
  classical
  exact finiteEntropy_deterministic a

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

theorem entropy_le_log_card (p : FiniteLaw A) :
    finiteEntropy p.mass ≤ Real.log (Fintype.card A) :=
  finiteEntropy_le_log_card p.mass p.nonneg p.total

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

theorem entropy_tendsto {I : Type*} {l : Filter I}
    {p : I → FiniteLaw A} {q : FiniteLaw A}
    (h : ∀ a, Tendsto (fun i => (p i).mass a) l (𝓝 (q.mass a))) :
    Tendsto (fun i => finiteEntropy (p i).mass) l (𝓝 (finiteEntropy q.mass)) :=
  tendsto_finiteEntropy_of_tendsto h

end FiniteLaw
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
