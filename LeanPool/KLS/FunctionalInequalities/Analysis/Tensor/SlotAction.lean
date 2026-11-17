/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Matrices acting on one slot of a coordinate tensor

Order-`r` coordinate tensors on `ℝⁿ`, their Euclidean inner product, the action `H^{(s)}` of a
matrix on the `s`-th input
and `Σ_H = Σ_s H^{(s)}` (BKL arXiv:2610.05474v1, p. 23), and the algebra (89)–(91) of the proof of
Lemma 5.1 at `A = Id`:
the drift expression is at least `½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩` when `Σ_i H_i² ≤ 8 Id`.
-/

@[expose] public section

noncomputable section

open Matrix

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- The Euclidean inner product of two order-`r` coordinate tensors on `ℝⁿ`. -/
def inner (T S : (Fin r → Fin n) → ℝ) : ℝ := ∑ J, T J * S J

/--
`H^{(s)}`: the matrix `H` acting on the `s`-th input of an order-`r` tensor (BKL arXiv:2610.05474v1,
p. 23). -/
def actOn (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    (Fin r → Fin n) → ℝ := fun J => ∑ k, H (J s) k * T (Function.update J s k)

/-- `Σ_H = Σ_s H^{(s)}`. -/
def actSum (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun J => ∑ s, actOn H s T J

private lemma cross_bound (x y : (Fin r → Fin n) → ℝ) :
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y ≤ -2 * inner x y := by
  calc
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y =
        ∑ J, (-(1 / 2 : ℝ) * (x J * x J) - 2 * (y J * y J)) := by
          unfold inner
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ J, (-2 * (x J * y J)) := by
      apply Finset.sum_le_sum
      intro J hJ
      nlinarith [sq_nonneg (x J - 2 * y J)]
    _ = -2 * inner x y := by
      unfold inner
      rw [Finset.mul_sum]

private lemma slot_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
    ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
      8 * ∑ J, T J ^ 2 := by
  classical
  cases r with
  | zero =>
      exact Fin.elim0 s
  | succ q =>
      let e := Fin.insertNthEquiv (fun _ : Fin (q + 1) => Fin n) s
      have heval (a : Fin n) (K : Fin q → Fin n) :
          e (a, K) s = a := by
        simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
      have hupd (a b : Fin n) (K : Fin q → Fin n) :
          Function.update (e (a, K)) s b = e (b, K) := by
        funext j
        by_cases hj : j = s
        · subst j
          simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
        · simp [Function.update, hj, e, Fin.insertNthEquiv_apply, Fin.insertNth,
            Fin.succAboveCases]
      have hri (i : Fin n) :
          ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ x : Fin n × (Fin q → Fin n),
              (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
        symm
        refine Fintype.sum_equiv (M := ℝ) e
          (fun x : Fin n × (Fin q → Fin n) =>
            (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2)
          (fun J => (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2) ?_
        rintro ⟨a, K⟩
        simp only [heval, hupd]
      have hsum :
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := by
        calc
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
              ∑ i, ∑ x : Fin n × (Fin q → Fin n),
                (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hri i
          _ = ∑ i, ∑ a, ∑ K : Fin q → Fin n,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => (∑ k, H i a k * T (e (k, K))) ^ 2)
          _ = ∑ i, ∑ K : Fin q → Fin n, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
          _ = ∑ K : Fin q → Fin n, ∑ i, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                rw [Finset.sum_comm]
      have hpoint (K : Fin q → Fin n) :
          ∑ i, ∑ a, (∑ k, H i a k * T (e (k, K))) ^ 2 ≤
            8 * ∑ a, T (e (a, K)) ^ 2 := by
        simpa using h8 (fun b => T (e (b, K)))
      have heq :
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
            ∑ J, T J ^ 2 := by
        calc
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
              ∑ a, ∑ K : Fin q → Fin n, T (e (a, K)) ^ 2 := by
                rw [Finset.sum_comm]
          _ = ∑ x : Fin n × (Fin q → Fin n), T (e x) ^ 2 := by
                symm
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => T (e (a, K)) ^ 2)
          _ = ∑ J, T J ^ 2 := by
                exact Fintype.sum_equiv (M := ℝ) e
                  (fun x : Fin n × (Fin q → Fin n) => T (e x) ^ 2)
                  (fun J => T J ^ 2) (fun _ => rfl)
      calc
        ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := hsum
        _ ≤ ∑ K : Fin q → Fin n, 8 * ∑ a, T (e (a, K)) ^ 2 := by
              apply Finset.sum_le_sum
              intro K hK
              exact hpoint K
        _ = 8 * (∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2) := by
              rw [Finset.mul_sum]
        _ = 8 * ∑ J, T J ^ 2 := by rw [heq]

private lemma actSum_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ) :
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
      (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
  classical
  have hi (i : Fin n) :
      inner (actSum (H i) T) (actSum (H i) T) ≤
        (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
    unfold inner actSum
    calc
      ∑ J, (∑ s, actOn (H i) s T J) * (∑ s, actOn (H i) s T J) ≤
          ∑ J, (r : ℝ) * ∑ s, (actOn (H i) s T J) * (actOn (H i) s T J) := by
            apply Finset.sum_le_sum
            intro J hJ
            simpa only [pow_two, Finset.card_univ, Fintype.card_fin] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (Fin r)))
                (f := fun s : Fin r => actOn (H i) s T J))
      _ = (r : ℝ) * ∑ s, ∑ J,
            (actOn (H i) s T J) * (actOn (H i) s T J) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
        ∑ i, (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          apply Finset.sum_le_sum
          intro i hi'
          exact hi i
    _ = (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          rw [Finset.mul_sum]

private lemma fin_sum_const_mul (q : ℕ) (x : ℝ) :
    (∑ _ : Fin q, x) = (q : ℝ) * x := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sum_sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ ∑ x, f x ^ 2 := by
  exact Finset.sum_nonneg (fun x hx => sq_nonneg (f x))

/--
**The algebra of BKL Lemma 5.1, (89)–(91)** at `A = Id`: for symmetric `H_i` with `Σ_i H_i² ≤ 8 Id`
and any
tensors `T, W_i, L` of order `r = m − 1 ≥ 1`, the drift expression of (89),
`−(m+1)|T|² − 2⟨T, L⟩ + Σ|W_i|² − 2Σ⟨W_i, Σ_{H_i}T⟩ + ½Σ|Σ_{H_i}T|² + ½ΣΣ_s|H_i^{(s)}T|²`, is at
least
`½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩`. -/
theorem drift_expression_ge {m : ℕ} (hm : r + 1 = m) (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i, (H i).IsHermitian)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T L : (Fin r → Fin n) → ℝ) (W : Fin n → (Fin r → Fin n) → ℝ) :
    (1 / 2 : ℝ) * ∑ i, inner (W i) (W i) - 17 * (m : ℝ) ^ 2 * inner T T - 2 * inner T L ≤
      -((m : ℝ) + 1) * inner T T - 2 * inner T L + ∑ i, inner (W i) (W i) -
            2 * ∑ i, inner (W i) (actSum (H i) T) +
          (1 / 2 : ℝ) * ∑ i, inner (actSum (H i) T) (actSum (H i) T) +
        (1 / 2 : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
  classical
  have hH_used : (0 : ℝ) ≤ 0 := by exact (fun _ : ∀ i, (H i).IsHermitian => le_rfl) hH
  have hcross :
    -(1 / 2 : ℝ) * ∑ i, inner (W i) (W i) - 2 * ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
      -2 * ∑ i, inner (W i) (actSum (H i) T) := by
    have hi (i : Fin n) := cross_bound (W i) (actSum (H i) T)
    calc
      -(1 / 2 : ℝ) * ∑ i, inner (W i) (W i) - 2 * ∑ i, inner (actSum (H i) T) (actSum (H i) T) =
          ∑ i,
            (-(1 / 2 : ℝ) * inner (W i) (W i) - 2 * inner (actSum (H i) T) (actSum (H i) T)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ∑ i, -2 * inner (W i) (actSum (H i) T) := by
        apply Finset.sum_le_sum
        intro i hi'
        exact hi i
      _ = -2 * ∑ i, inner (W i) (actSum (H i) T) := by rw [Finset.mul_sum]
  have hslot : ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) ≤ 8 * (r : ℝ) * inner T T := by
    calc
      ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) =
          ∑ s, ∑ i, inner (actOn (H i) s T) (actOn (H i) s T) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ s, 8 * ∑ J, T J ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        simpa only [inner, actOn, pow_two] using slot_bound H h8 T s
      _ = 8 * (r : ℝ) * inner T T := by
        rw [fin_sum_const_mul]
        unfold inner
        simp only [pow_two]
        ring
  have hact := actSum_bound H T
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hC :
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤ (r : ℝ) * (8 * (r : ℝ) * inner T T) :=
    le_trans hact (mul_le_mul_of_nonneg_left hslot hr)
  have hA : 0 ≤ inner T T := by
    unfold inner
    simpa only [pow_two] using sum_sq_nonneg T
  have hDnonneg : 0 ≤ ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
    simp only [inner]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro s hs
    simpa only [pow_two] using sum_sq_nonneg (actOn (H i) s T)
  have hmcast : (m : ℝ) = (r : ℝ) + 1 := by exact_mod_cast hm.symm
  have hcoef : 0 ≤ 17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2 := by
    rw [hmcast]
    nlinarith [sq_nonneg (r : ℝ)]
  have hprod : 0 ≤ (17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2) * inner T T :=
    mul_nonneg hcoef hA
  nlinarith [hcross, hC, hA, hDnonneg, hprod, hH_used]

end FunctionalInequalities.Analysis.CoordinateTensor

section SlotActionAlgebra

open Matrix

/-! Commutation and inner-product algebra of slot actions. -/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- Slot actions at different slots commute. -/
theorem actOn_actOn_comm (M N : Matrix (Fin n) (Fin n) ℝ) {s t : Fin r} (hst : s ≠ t)
    (T : (Fin r → Fin n) → ℝ) : actOn M s (actOn N t T) = actOn N t (actOn M s T) := by
  classical
  funext J
  simp only [actOn]
  have hNt (k : Fin n) : Function.update J s k t = J t := by
    rw [Function.update_apply, ite_eq_right (Ne.symm hst)]
  have hNs (l : Fin n) : Function.update J t l s = J s := by
    rw [Function.update_apply, ite_eq_right hst]
  have hupd (k l : Fin n) :
      Function.update (Function.update J s k) t l =
        Function.update (Function.update J t l) s k := by
    exact Function.update_comm hst k l J
  calc
    (∑ k, M (J s) k * (∑ l, N (Function.update J s k t) l *
      T (Function.update (Function.update J s k) t l))) =
        ∑ k, ∑ l, M (J s) k *
          (N (Function.update J s k t) l *
            T (Function.update (Function.update J s k) t l)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mul_sum]
    _ = ∑ l, ∑ k, M (J s) k *
          (N (Function.update J s k t) l *
            T (Function.update (Function.update J s k) t l)) := by
              rw [Finset.sum_comm]
    _ = ∑ l, ∑ k, M (J s) k *
          (N (J t) l *
            T (Function.update (Function.update J t l) s k)) := by
              apply Finset.sum_congr rfl
              intro l hl
              apply Finset.sum_congr rfl
              intro k hk
              rw [hNt k, hupd k l]
    _ = ∑ l, N (J t) l *
          (∑ k, M (J s) k *
            T (Function.update (Function.update J t l) s k)) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ = ∑ l, N (J t) l *
          (∑ k, M (Function.update J t l s) k *
            T (Function.update (Function.update J t l) s k)) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hNs l]

/-- A product of matrices acts as the composition at the same slot. -/
theorem actOn_mul (M N : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    actOn (M * N) s T = actOn M s (actOn N s T) := by
  classical
  funext J
  simp only [actOn]
  calc
    (∑ k, (M * N) (J s) k * T (Function.update J s k)) =
        ∑ k, (∑ l, M (J s) l * N l k) * T (Function.update J s k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact congrArg (fun x : ℝ => x * T (Function.update J s k))
            (Matrix.mul_apply (M := M) (N := N) (i := J s) (k := k))
    _ = ∑ k, ∑ l, (M (J s) l * N l k) *
          T (Function.update J s k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
    _ = ∑ k, ∑ l, (M (J s) k * N k l) *
          T (Function.update J s l) := by
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, M (J s) k *
          (N (Function.update J s k s) l *
            T (Function.update (Function.update J s k) s l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [Function.update_self, Function.update_idem]
          ring
    _ = ∑ k, M (J s) k *
          (∑ l, N (Function.update J s k s) l *
            T (Function.update (Function.update J s k) s l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]

/-- The slot action of a symmetric matrix is self-adjoint for `inner`. -/
theorem inner_actOn_left (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T S : (Fin r → Fin n) → ℝ) : inner (actOn M s T) S = inner T (actOn M s S) := by
  classical
  let f : ((Fin r → Fin n) × Fin n) → ((Fin r → Fin n) × Fin n) :=
    fun x => (Function.update x.1 s x.2, x.1 s)
  have hf : Function.Involutive f := by
    rintro ⟨J, k⟩
    dsimp [f]
    apply Prod.ext
    · rw [Function.update_idem, Function.update_eq_self]
    · exact Function.update_self s k J
  let e : Equiv.Perm ((Fin r → Fin n) × Fin n) := hf.toPerm
  have heval (J : Fin r → Fin n) (k : Fin n) :
      e (J, k) = (Function.update J s k, J s) := by
    rfl
  calc
    inner (actOn M s T) S =
        ∑ J, ∑ k, M (J s) k * T (Function.update J s k) * S J := by
          unfold inner actOn
          apply Finset.sum_congr rfl
          intro J hJ
          rw [Finset.sum_mul]
    _ = ∑ x : (Fin r → Fin n) × Fin n,
          M (x.1 s) x.2 * T (Function.update x.1 s x.2) * S x.1 := by
          symm
          exact Fintype.sum_prod_type' (γ := ℝ)
            (α₁ := Fin r → Fin n) (α₂ := Fin n)
            (fun J k => M (J s) k * T (Function.update J s k) * S J)
    _ = ∑ x : (Fin r → Fin n) × Fin n,
          T x.1 * M (x.1 s) x.2 * S (Function.update x.1 s x.2) := by
          refine Fintype.sum_equiv (M := ℝ) e
            (fun x : (Fin r → Fin n) × Fin n =>
              M (x.1 s) x.2 * T (Function.update x.1 s x.2) * S x.1)
            (fun x : (Fin r → Fin n) × Fin n =>
              T x.1 * M (x.1 s) x.2 * S (Function.update x.1 s x.2)) ?_
          rintro ⟨J, k⟩
          simp only [heval, Function.update_self, Function.update_idem,
            Function.update_eq_self]
          rw [hM.apply (J s) k]
          ring
    _ = ∑ J, ∑ k, T J * M (J s) k * S (Function.update J s k) := by
          exact Fintype.sum_prod_type' (γ := ℝ)
            (α₁ := Fin r → Fin n) (α₂ := Fin n)
            (fun J k => T J * M (J s) k * S (Function.update J s k))
    _ = inner T (actOn M s S) := by
          unfold inner actOn
          apply Finset.sum_congr rfl
          intro J hJ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring

/-- `⟨T, (M²)^{(s)} T⟩ = |M^{(s)} T|²` for symmetric `M`. -/
theorem inner_actOn_mul_self (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T : (Fin r → Fin n) → ℝ) :
    inner T (actOn (M * M) s T) = inner (actOn M s T) (actOn M s T) := by
  rw [actOn_mul]
  exact (inner_actOn_left M hM s T (actOn M s T)).symm

/--
`|Σ_M T|² = Σ_s |M^{(s)} T|² + Σ_{s ≠ t} ⟨T, M^{(s)} M^{(t)} T⟩` for symmetric `M` (BKL (87)–(88)).
-/
theorem inner_actSum_actSum (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (T : (Fin r → Fin n) → ℝ) :
    inner (actSum M T) (actSum M T) =
      ∑ s, inner (actOn M s T) (actOn M s T) +
        ∑ s, ∑ t ∈ Finset.univ.erase s, inner T (actOn M s (actOn M t T)) := by
  classical
  have hexpand :
    inner (actSum M T) (actSum M T) = ∑ s, ∑ t, inner (actOn M s T) (actOn M t T) := by
    unfold inner actSum
    calc
      (∑ J, (∑ s, actOn M s T J) * (∑ t, actOn M t T J)) =
          ∑ J, ∑ s, ∑ t, (actOn M s T J) * (actOn M t T J) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.sum_mul_sum]
      _ = ∑ s, ∑ J, ∑ t, (actOn M s T J) * (actOn M t T J) := by rw [Finset.sum_comm]
      _ = ∑ s, ∑ t, ∑ J, (actOn M s T J) * (actOn M t T J) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ t, inner (actOn M s T) (actOn M t T) := by rfl
  calc
    inner (actSum M T) (actSum M T) = ∑ s, ∑ t, inner (actOn M s T) (actOn M t T) := hexpand
    _ =
        ∑ s,
          (inner (actOn M s T) (actOn M s T) +
            ∑ t ∈ Finset.univ.erase s, inner (actOn M s T) (actOn M t T)) := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      exact
        Finset.add_sum_erase (Finset.univ : Finset (Fin r))
          (fun t => inner (actOn M s T) (actOn M t T)) (Finset.mem_univ s)
    _ =
        (∑ s, inner (actOn M s T) (actOn M s T)) +
          ∑ s, ∑ t ∈ Finset.univ.erase s, inner (actOn M s T) (actOn M t T) := by
      rw [Finset.sum_add_distrib]
    _ =
        (∑ s, inner (actOn M s T) (actOn M s T)) +
          ∑ s, ∑ t ∈ Finset.univ.erase s, inner T (actOn M s (actOn M t T)) := by
      apply congrArg (fun x : ℝ => (∑ s, inner (actOn M s T) (actOn M s T)) + x)
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      exact inner_actOn_left M hM s T (actOn M t T)

end FunctionalInequalities.Analysis.CoordinateTensor

end SlotActionAlgebra
