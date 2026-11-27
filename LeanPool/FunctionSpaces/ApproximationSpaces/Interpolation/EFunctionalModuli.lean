/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.EFunctional

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Moduli of smoothness for `ρ`-normed couples

The coincidence of approximation spaces with classical spaces defined by a modulus of
smoothness (`ApproximationScheme.ModulusData`) needs the triangle inequality: the near-best
approximants are telescoped over arbitrarily many levels. For a quasi-norm with constant `C`
the telescoping would cost `C^k` at level `k`. In `L_p`, `0 < p < 1`, the `p`-th power of the
quasi-norm is subadditive, and DeVore–Popov (Trans. Amer. Math. Soc. 305 (1988), (2.3)) telescope
with `‖∑ f_j‖_p^μ ≤ ∑ ‖f_j‖_p^μ`, `μ ≤ min(1, p)`. This file states the coincidence theorem in
that form, for a couple `A = (N₀, N₁)` (`InterpCouple`) with an exponent `ρ > 0`.

An `InterpCouple.ModulusData A ρ θ` bundles

* the couple axioms: `N₀(0) = 0`, `N₀` even, `N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ`, and a
  subadditive even complexity `N₁` with `N₁(0) = 0`;
* a modulus `ω(f, k)` (the modulus of smoothness at the scale `2^(-k)`) with
  `ω(f + g, k)^ρ ≤ ω(f, k)^ρ + ω(g, k)^ρ` and `ω(f, k) ≤ C₀ N₀(f)`;
* a **Jackson inequality** `E(2^k, f) ≤ C_J ω(f, k)` at every level, for the E-functional
  `E(t, f) = inf {N₀(f - b) : N₁(b) ≤ t}` (`InterpCouple.eFunctional`);
* an **inverse inequality** of order `θ`: `ω(a, k) ≤ C_B 2^(-(k-j)θ) N₀(a)` for `N₁(a) ≤ 2^j`
  (with `k - j` truncated at `0`).

With the classical quasi-norm `‖f‖^ω_{s,q} = N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q}`
(`InterpCouple.ModulusData.modNorm`) and the dyadic norm of the E-method
`N₀(f) + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}` (`InterpCouple.eNormDyadic`):

* `‖f‖_E ≤ max(1, C_J) ‖f‖^ω_{s,q}` for every `s` and `q`
  (`InterpCouple.ModulusData.eNormDyadic_le_modNorm`);
* `‖f‖^ω_{s,q} ≤ K ‖f‖_E` for `0 ≤ s < θ` and every `q`
  (`InterpCouple.ModulusData.modNorm_le_eNormDyadic`). The proof follows DeVore–Popov, proof of
  Theorem 4.8: near-best `b_k` with `N₁(b_k) ≤ 2^k`, the telescoping
  `f = (f - b_k) + b_0 + ∑_{j<k} (b_{j+1} - b_j)`, the inverse inequality for each block in
  `ρ`-th powers, and Hardy's inequality in `ℓ_{q/ρ}` with the exponent `(θ - s)ρ`
  (`ENNReal.hardy_sum_le'`), since `‖(a_k^ρ)_k‖_{ℓ_{q/ρ}} = ‖a‖_{ℓ_q}^ρ`
  (`ENNReal.lqNorm_div_fun_rpow`).

So, if only `0` has complexity below `1`, then for `0 < s < θ` and `q ≠ 0` the approximation
space `E_{s,q}` of the couple is the classical space
(`InterpCouple.ModulusData.memEMethod_iff_modNorm_lt_top`). For `p < 1` the K-functional of
`(L_p, W^r_p)` on an interval vanishes identically (Ditzian–Hristov–Ivanov, Constr. Approx. 11
(1995)), so the representation of the classical spaces as interpolation spaces has no analogue
there, and the theorem goes through the Jackson and inverse inequalities directly.
-/

@[expose] public section

open Finset
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U]

/-- `N₀(a - b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` if `N₀` is even and `N₀^ρ` is subadditive. -/
theorem norm0_sub_rpow_le {A : InterpCouple U} {ρ : ℝ} (hneg : ∀ a, A.norm0 (-a) = A.norm0 a)
    (hadd : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (a b : U) :
    A.norm0 (a - b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ := by
  rw [sub_eq_add_neg, ← hneg b]
  exact hadd a (-b)

/-- `N₁(a - b) ≤ N₁(a) + N₁(b)` if `N₁` is even and subadditive. -/
theorem norm1_sub_le {A : InterpCouple U} (hneg : ∀ a, A.norm1 (-a) = A.norm1 a)
    (hadd : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (a b : U) :
    A.norm1 (a - b) ≤ A.norm1 a + A.norm1 b := by
  rw [sub_eq_add_neg, ← hneg b]
  exact hadd a (-b)

/-- **The dyadic errors with tolerances**: for every couple, `s` and `q`, the sequence
`2^(ks) (E(2^k, f) + N₀(f) 2^(-k(s+1)))` has `ℓ_q` norm at most
`C_q (1 + γ_{1,q}) (N₀(f) + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q})`, with Mathlib's constant
`C_q = LpAddConst q` and `γ_{1,q} = dyadicGeomConst 1 q`, since
`2^(ks) N₀(f) 2^(-k(s+1)) = N₀(f) 2^(-k)`. -/
theorem lqNorm_dyadicWeight_mul_eFunctional_add_le (A : InterpCouple U) (s : ℝ) (q : ℝ≥0∞)
    (f : U) :
    lqNorm q (fun k : ℕ => dyadicWeight s k * (A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
      A.norm0 f * dyadicWeight (-(s + 1)) k)) ≤
        LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q f := by
  set L := lqNorm q fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f
  set γ := dyadicGeomConst 1 q
  have hw : ∀ k : ℕ, dyadicWeight s k * (A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
      A.norm0 f * dyadicWeight (-(s + 1)) k) =
        dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
          A.norm0 f * dyadicWeight (-1) k := fun k => by
    rw [mul_add, mul_left_comm, ← ENNReal.dyadicWeight_add, show s + -(s + 1) = -1 by ring]
  calc lqNorm q (fun k : ℕ => dyadicWeight s k * (A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
        A.norm0 f * dyadicWeight (-(s + 1)) k))
      = lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
          A.norm0 f * dyadicWeight (-1) k) := by
        congr 1
        exact funext hw
    _ ≤ LpAddConst q * (L + A.norm0 f * lqNorm q (dyadicWeight (-1))) := by
        refine (ENNReal.lqNorm_add_le' q _ _).trans ?_
        rw [ENNReal.lqNorm_const_mul]
    _ ≤ LpAddConst q * ((1 + γ) * L + A.norm0 f * (1 + γ)) := by
        gcongr
        · exact le_mul_of_one_le_left' le_self_add
        · exact (ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst zero_le_one).trans le_add_self
    _ = LpAddConst q * (1 + γ) * (A.norm0 f + L) := by ring
    _ = LpAddConst q * (1 + γ) * A.eNormDyadic s q f := rfl

/-- A **modulus of smoothness compatible with a `ρ`-normed couple** `A = (N₀, N₁)`, with inverse
order `θ`: the couple axioms with `ρ`-subadditivity of `N₀` and subadditivity of the complexity
`N₁`, a modulus at the dyadic scales `modulus f k = ω(f, 2^(-k))` whose `ρ`-th power is
subadditive and which is bounded by `C₀ N₀(f)`, a Jackson inequality `E(2^k, f) ≤ C_J ω(f, k)`
for the E-functional, and an inverse inequality `ω(a, k) ≤ C_B 2^(-(k-j)θ) N₀(a)` for
`N₁(a) ≤ 2^j`. -/
structure ModulusData (A : InterpCouple U) (ρ θ : ℝ) where
  /-- The exponent `ρ` is positive. -/
  rho_pos : 0 < ρ
  /-- `N₀(0) = 0`. -/
  norm0_zero : A.norm0 0 = 0
  /-- `N₀` is even. -/
  norm0_neg : ∀ a, A.norm0 (-a) = A.norm0 a
  /-- `N₀^ρ` is subadditive. -/
  norm0_add_rpow_le : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ
  /-- `N₁(0) = 0`. -/
  norm1_zero : A.norm1 0 = 0
  /-- `N₁` is even. -/
  norm1_neg : ∀ a, A.norm1 (-a) = A.norm1 a
  /-- `N₁` is subadditive. -/
  norm1_add_le : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b
  /-- The modulus at the dyadic scales. -/
  modulus : U → ℕ → ℝ≥0∞
  /-- The `ρ`-th power of the modulus is subadditive. -/
  add_rpow_le : ∀ f g k, modulus (f + g) k ^ ρ ≤ modulus f k ^ ρ + modulus g k ^ ρ
  /-- The constant of `ω(f, k) ≤ C₀ N₀(f)`. -/
  C0 : ℝ≥0∞
  /-- The constant `C₀` is finite. -/
  C0_ne_top : C0 ≠ ∞
  /-- `ω(f, k) ≤ C₀ N₀(f)`. -/
  le_norm0 : ∀ f k, modulus f k ≤ C0 * A.norm0 f
  /-- The Jackson constant. -/
  CJ : ℝ≥0∞
  /-- The Jackson constant is finite. -/
  CJ_ne_top : CJ ≠ ∞
  /-- The Jackson inequality `E(2^k, f) ≤ C_J ω(f, k)`. -/
  jackson : ∀ f k, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f ≤ CJ * modulus f k
  /-- The constant of the inverse inequality. -/
  CB : ℝ≥0∞
  /-- The constant of the inverse inequality is finite. -/
  CB_ne_top : CB ≠ ∞
  /-- The inverse inequality `ω(a, k) ≤ C_B 2^(-(k-j)θ) N₀(a)` for `N₁(a) ≤ 2^j`. -/
  inverse : ∀ j k a, A.norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞) →
    modulus a k ≤ CB * dyadicWeight (-θ) (k - j) * A.norm0 a

namespace ModulusData

variable {A : InterpCouple U} {ρ θ : ℝ}

/-- A modulus compatible with a `ρ`-normed couple from **existence statements** for the Jackson
and the inverse constant: the couple axioms, the modulus with its `ρ`-subadditivity and the bound
`ω(f, k) ≤ C₀ N₀(f)`, a Jackson inequality `E(2^k, f) ≤ C_J ω(f, k)` with some finite `C_J`, and
an inverse inequality `ω(a, k) ≤ C_B 2^(-(k-j)θ) N₀(a)`, `N₁(a) ≤ 2^j`, with some finite `C_B`.
The constants are chosen with `Exists.choose`. -/
noncomputable def ofExists (rho_pos : 0 < ρ) (norm0_zero : A.norm0 0 = 0)
    (norm0_neg : ∀ a, A.norm0 (-a) = A.norm0 a)
    (norm0_add_rpow_le : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ)
    (norm1_zero : A.norm1 0 = 0) (norm1_neg : ∀ a, A.norm1 (-a) = A.norm1 a)
    (norm1_add_le : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (modulus : U → ℕ → ℝ≥0∞)
    (add_rpow_le : ∀ f g k, modulus (f + g) k ^ ρ ≤ modulus f k ^ ρ + modulus g k ^ ρ)
    (C0 : ℝ≥0∞) (C0_ne_top : C0 ≠ ∞) (le_norm0 : ∀ f k, modulus f k ≤ C0 * A.norm0 f)
    (hJ : ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧
      ∀ f k, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f ≤ CJ * modulus f k)
    (hB : ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k a, A.norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞) →
      modulus a k ≤ CB * dyadicWeight (-θ) (k - j) * A.norm0 a) :
    A.ModulusData ρ θ where
  rho_pos := rho_pos
  norm0_zero := norm0_zero
  norm0_neg := norm0_neg
  norm0_add_rpow_le := norm0_add_rpow_le
  norm1_zero := norm1_zero
  norm1_neg := norm1_neg
  norm1_add_le := norm1_add_le
  modulus := modulus
  add_rpow_le := add_rpow_le
  C0 := C0
  C0_ne_top := C0_ne_top
  le_norm0 := le_norm0
  CJ := hJ.choose
  CJ_ne_top := hJ.choose_spec.1
  jackson := hJ.choose_spec.2
  CB := hB.choose
  CB_ne_top := hB.choose_spec.1
  inverse := hB.choose_spec.2

variable (M : A.ModulusData ρ θ)

/-- The **classical quasi-norm** `‖f‖^ω_{s,q} = N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q}`. -/
noncomputable def modNorm (s : ℝ) (q : ℝ≥0∞) (f : U) : ℝ≥0∞ :=
  A.norm0 f + lqNorm q (fun k => dyadicWeight s k * M.modulus f k)

variable {s : ℝ} {q : ℝ≥0∞}

/-- The modulus of `0` vanishes. -/
theorem modulus_zero (k : ℕ) : M.modulus 0 k = 0 :=
  le_antisymm ((M.le_norm0 0 k).trans_eq (by rw [M.norm0_zero, mul_zero])) bot_le

/-- The `ρ`-th power of the modulus is subadditive on finite sums (Mathlib's
`Finset.le_sum_of_subadditive`). -/
theorem modulus_sum_rpow_le {ι : Type*} (t : Finset ι) (g : ι → U) (k : ℕ) :
    M.modulus (∑ i ∈ t, g i) k ^ ρ ≤ ∑ i ∈ t, M.modulus (g i) k ^ ρ := by
  have h0 : M.modulus 0 k ^ ρ = 0 := by
    rw [M.modulus_zero, ENNReal.zero_rpow_of_pos M.rho_pos]
  exact Finset.le_sum_of_subadditive (fun f => M.modulus f k ^ ρ) h0.le
    (fun f g => M.add_rpow_le f g k) t g

/-- **The inverse inequality in `ρ`-th powers**: `ω(a, k)^ρ ≤ C_B^ρ 2^(-(k-j)θρ) N₀(a)^ρ` for
`N₁(a) ≤ 2^j`. -/
theorem modulus_rpow_le_of_norm1_le {a : U} {j : ℕ} (ha : A.norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞))
    (k : ℕ) :
    M.modulus a k ^ ρ ≤ M.CB ^ ρ * dyadicWeight (-(θ * ρ)) (k - j) * A.norm0 a ^ ρ := by
  have hρ := M.rho_pos.le
  calc M.modulus a k ^ ρ ≤ (M.CB * dyadicWeight (-θ) (k - j) * A.norm0 a) ^ ρ :=
        ENNReal.rpow_le_rpow (M.inverse j k a ha) hρ
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hρ, ENNReal.mul_rpow_of_nonneg _ _ hρ,
          ENNReal.dyadicWeight_rpow, neg_mul]

/-- **One block of the telescoping sum**: if `N₁(b_j) ≤ 2^j` and `N₁(b_{j+1}) ≤ 2^(j+1)`, and
`N₀(f - b_i) ≤ e_i` for `i = j, j+1` with `e_{j+1} ≤ e_j`, then `b_{j+1} - b_j` has complexity at
most `2^(j+2)` and `ω(b_{j+1} - b_j, k)^ρ ≤ 2 C_B^ρ 4^(θρ) 2^(-(k-j)θρ) e_j^ρ` for `θ ≥ 0`. -/
theorem modulus_sub_rpow_le (hθ : 0 ≤ θ) {f b b' : U} {j k : ℕ} {e e' : ℝ≥0∞}
    (hb : A.norm1 b ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (hb' : A.norm1 b' ≤ ((2 ^ (j + 1) : ℕ) : ℝ≥0∞))
    (he : A.norm0 (f - b) ≤ e) (he' : A.norm0 (f - b') ≤ e') (hee : e' ≤ e) :
    M.modulus (b' - b) k ^ ρ ≤
      2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - j) * e ^ ρ) := by
  have hρ := M.rho_pos.le
  have h2 : 2 ^ (j + 1) + 2 ^ j ≤ 2 ^ (j + 2) := by
    rw [show j + 2 = j + 1 + 1 from rfl, pow_succ 2 (j + 1), pow_succ 2 j]
    omega
  have hN1 : A.norm1 (b' - b) ≤ ((2 ^ (j + 2) : ℕ) : ℝ≥0∞) := by
    refine (norm1_sub_le M.norm1_neg M.norm1_add_le _ _).trans ((add_le_add hb' hb).trans ?_)
    exact_mod_cast h2
  have hN0 : A.norm0 (b' - b) ^ ρ ≤ 2 * e ^ ρ := by
    calc A.norm0 (b' - b) ^ ρ = A.norm0 ((f - b) - (f - b')) ^ ρ := by
          rw [sub_sub_sub_cancel_left]
      _ ≤ A.norm0 (f - b) ^ ρ + A.norm0 (f - b') ^ ρ :=
          norm0_sub_rpow_le M.norm0_neg M.norm0_add_rpow_le _ _
      _ ≤ e ^ ρ + e ^ ρ :=
          add_le_add (ENNReal.rpow_le_rpow he hρ) (ENNReal.rpow_le_rpow (he'.trans hee) hρ)
      _ = 2 * e ^ ρ := (two_mul _).symm
  calc M.modulus (b' - b) k ^ ρ
      ≤ M.CB ^ ρ * dyadicWeight (-(θ * ρ)) (k - (j + 2)) * A.norm0 (b' - b) ^ ρ :=
        M.modulus_rpow_le_of_norm1_le hN1 k
    _ ≤ M.CB ^ ρ * (dyadicWeight (θ * ρ) 2 * dyadicWeight (-(θ * ρ)) (k - j)) * (2 * e ^ ρ) := by
        gcongr
        rw [show k - (j + 2) = k - j - 2 by omega]
        exact ENNReal.dyadicWeight_neg_sub_two_le (mul_nonneg hθ hρ) (k - j)
    _ = _ := by ring

/-- **The modulus at one scale from near-best elements** (DeVore–Popov, proof of Theorem 4.8):
let `θ ≥ 0`, `b_j ∈ U` with `N₁(b_j) ≤ 2^j`, and `e` decreasing with `N₀(f - b_j) ≤ e_j` and
`N₀(f) ≤ e_0`. The telescoping `f = (f - b_k) + b_0 + ∑_{j<k} (b_{j+1} - b_j)`, the
`ρ`-subadditivity of the modulus and the inverse inequality for `b_0` and for each block give
`ω(f, k)^ρ ≤ C₀^ρ e_k^ρ + 2 ∑_{j ≤ k} 2 C_B^ρ 4^(θρ) 2^(-(k-j)θρ) e_j^ρ`. -/
theorem modulus_rpow_le (hθ : 0 ≤ θ) {f : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞}
    (hb1 : ∀ j, A.norm1 (b j) ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (hb0 : ∀ j, A.norm0 (f - b j) ≤ e j)
    (he : Antitone e) (hfe : A.norm0 f ≤ e 0) (k : ℕ) :
    M.modulus f k ^ ρ ≤ M.C0 ^ ρ * e k ^ ρ + 2 * ∑ j ∈ range (k + 1),
      2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ) := by
  have hρ := M.rho_pos.le
  have htel : f = (f - b k) + (b 0 + ∑ j ∈ range k, (b (j + 1) - b j)) := by
    rw [sum_range_sub (fun j => b j) k]
    abel
  have h1 : M.modulus (f - b k) k ^ ρ ≤ M.C0 ^ ρ * e k ^ ρ :=
    (ENNReal.rpow_le_rpow ((M.le_norm0 _ k).trans (mul_le_mul_right (hb0 k) _)) hρ).trans_eq
      (ENNReal.mul_rpow_of_nonneg _ _ hρ)
  have h2 : M.modulus (b 0) k ^ ρ ≤
      2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - 0) * e 0 ^ ρ) := by
    have hn : A.norm0 (b 0) ^ ρ ≤ 2 * e 0 ^ ρ := by
      calc A.norm0 (b 0) ^ ρ = A.norm0 (f - (f - b 0)) ^ ρ := by rw [sub_sub_cancel]
        _ ≤ A.norm0 f ^ ρ + A.norm0 (f - b 0) ^ ρ :=
            norm0_sub_rpow_le M.norm0_neg M.norm0_add_rpow_le _ _
        _ ≤ e 0 ^ ρ + e 0 ^ ρ :=
            add_le_add (ENNReal.rpow_le_rpow hfe hρ) (ENNReal.rpow_le_rpow (hb0 0) hρ)
        _ = 2 * e 0 ^ ρ := (two_mul _).symm
    calc M.modulus (b 0) k ^ ρ
        ≤ M.CB ^ ρ * dyadicWeight (-(θ * ρ)) (k - 0) * A.norm0 (b 0) ^ ρ :=
          M.modulus_rpow_le_of_norm1_le (hb1 0) k
      _ ≤ M.CB ^ ρ * dyadicWeight (-(θ * ρ)) (k - 0) * (2 * e 0 ^ ρ) := by gcongr
      _ = 2 * M.CB ^ ρ * 1 * (dyadicWeight (-(θ * ρ)) (k - 0) * e 0 ^ ρ) := by ring
      _ ≤ _ := by
          gcongr
          exact ENNReal.one_le_dyadicWeight (mul_nonneg hθ hρ) 2
  have h3 : ∀ j ∈ range k, M.modulus (b (j + 1) - b j) k ^ ρ ≤
      2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ) :=
    fun j _ => M.modulus_sub_rpow_le hθ (hb1 j) (hb1 (j + 1)) (hb0 j) (hb0 (j + 1))
      (he (Nat.le_succ j))
  calc M.modulus f k ^ ρ
      = M.modulus ((f - b k) + (b 0 + ∑ j ∈ range k, (b (j + 1) - b j))) k ^ ρ := by
        rw [← htel]
    _ ≤ M.modulus (f - b k) k ^ ρ + (M.modulus (b 0) k ^ ρ +
          ∑ j ∈ range k, M.modulus (b (j + 1) - b j) k ^ ρ) :=
        (M.add_rpow_le _ _ k).trans (add_le_add le_rfl ((M.add_rpow_le _ _ k).trans
          (add_le_add le_rfl (M.modulus_sum_rpow_le _ _ k))))
    _ ≤ M.C0 ^ ρ * e k ^ ρ + (2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 *
          (dyadicWeight (-(θ * ρ)) (k - 0) * e 0 ^ ρ) + ∑ j ∈ range k,
            2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 *
              (dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ)) :=
        add_le_add h1 (add_le_add h2 (sum_le_sum h3))
    _ ≤ _ := add_le_add le_rfl (ENNReal.add_sum_range_le_two_mul_sum (fun j =>
          2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ)) k)

/-- **The weighted modulus at one scale**: with `α = (θ - s)ρ` and `x_j = (2^(js) e_j)^ρ`,
`ModulusData.modulus_rpow_le` multiplied by `2^(ksρ)` reads
`(2^(ks) ω(f, k))^ρ ≤ C₀^ρ x_k + 4 C_B^ρ 4^(θρ) 2^(-kα) ∑_{j ≤ k} 2^(jα) x_j`. -/
theorem dyadicWeight_mul_modulus_rpow_le (hθ : 0 ≤ θ) {f : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞}
    (hb1 : ∀ j, A.norm1 (b j) ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (hb0 : ∀ j, A.norm0 (f - b j) ≤ e j)
    (he : Antitone e) (hfe : A.norm0 f ≤ e 0) (k : ℕ) :
    (dyadicWeight s k * M.modulus f k) ^ ρ ≤ M.C0 ^ ρ * (dyadicWeight s k * e k) ^ ρ +
      4 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-((θ - s) * ρ)) k *
        ∑ j ∈ range (k + 1), dyadicWeight ((θ - s) * ρ) j * (dyadicWeight s j * e j) ^ ρ) := by
  have hρ := M.rho_pos.le
  have hx : ∀ j, (dyadicWeight s j * e j) ^ ρ = dyadicWeight (s * ρ) j * e j ^ ρ := fun j => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hρ, ENNReal.dyadicWeight_rpow]
  have hw : ∀ j ∈ range (k + 1), dyadicWeight (s * ρ) k * dyadicWeight (-(θ * ρ)) (k - j) =
      dyadicWeight (-((θ - s) * ρ)) k * dyadicWeight ((θ - s) * ρ) j * dyadicWeight (s * ρ) j :=
    fun j hj => by
      rw [ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub (s * ρ) (θ * ρ)
        (Nat.lt_succ_iff.1 (mem_range.1 hj)), mul_assoc, ← ENNReal.dyadicWeight_add]
      congr 2 <;> ring
  calc (dyadicWeight s k * M.modulus f k) ^ ρ = dyadicWeight (s * ρ) k * M.modulus f k ^ ρ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hρ, ENNReal.dyadicWeight_rpow]
    _ ≤ dyadicWeight (s * ρ) k * (M.C0 ^ ρ * e k ^ ρ + 2 * ∑ j ∈ range (k + 1),
          2 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 * (dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ)) :=
        mul_le_mul_right (M.modulus_rpow_le hθ hb1 hb0 he hfe k) _
    _ = M.C0 ^ ρ * (dyadicWeight (s * ρ) k * e k ^ ρ) + ∑ j ∈ range (k + 1),
          4 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 *
            (dyadicWeight (s * ρ) k * dyadicWeight (-(θ * ρ)) (k - j) * e j ^ ρ) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [hx]
        rw [Finset.mul_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j hj => by rw [hw j hj]; ring

/-- **The weighted modulus in `ℓ_r`**: under the hypotheses of `ModulusData.modulus_rpow_le`,
for every exponent `r`,
`‖((2^(ks) ω(f, k))^ρ)_k‖_{ℓ_r} ≤ C_r (C₀^ρ + 4 C_B^ρ 4^(θρ) H) ‖((2^(ks) e_k)^ρ)_k‖_{ℓ_r}`, with
Mathlib's constant `C_r = LpAddConst r` and the constant `H = hardyConst ((θ - s)ρ) r` of
Hardy's inequality (`ENNReal.hardy_sum_le'`). -/
theorem lqNorm_rpow_le (hθ : 0 ≤ θ) {f : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞}
    (hb1 : ∀ j, A.norm1 (b j) ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (hb0 : ∀ j, A.norm0 (f - b j) ≤ e j)
    (he : Antitone e) (hfe : A.norm0 f ≤ e 0) (r : ℝ≥0∞) :
    lqNorm r (fun k => (dyadicWeight s k * M.modulus f k) ^ ρ) ≤
      LpAddConst r * (M.C0 ^ ρ + 4 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 *
        hardyConst ((θ - s) * ρ) r) * lqNorm r (fun k => (dyadicWeight s k * e k) ^ ρ) := by
  set x : ℕ → ℝ≥0∞ := fun k => (dyadicWeight s k * e k) ^ ρ with hx
  set α := (θ - s) * ρ
  set K := 4 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2
  have hhardy : lqNorm r (fun k => dyadicWeight (-α) k *
      ∑ j ∈ range (k + 1), dyadicWeight α j * x j) ≤ hardyConst α r * lqNorm r x := by
    refine (ENNReal.hardy_sum_le' α (fun j => dyadicWeight α j * x j)).trans_eq ?_
    congr 2
    funext k
    show dyadicWeight (-α) k * (dyadicWeight α k * x k) = x k
    rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
  calc lqNorm r (fun k => (dyadicWeight s k * M.modulus f k) ^ ρ)
      ≤ lqNorm r (fun k => M.C0 ^ ρ * x k +
          K * (dyadicWeight (-α) k * ∑ j ∈ range (k + 1), dyadicWeight α j * x j)) :=
        ENNReal.lqNorm_mono fun k => M.dyadicWeight_mul_modulus_rpow_le hθ hb1 hb0 he hfe k
    _ ≤ LpAddConst r * (M.C0 ^ ρ * lqNorm r x + K * (hardyConst α r * lqNorm r x)) := by
        refine (ENNReal.lqNorm_add_le' r _ _).trans ?_
        rw [ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
        gcongr
    _ = _ := by ring

/-- The constant of the inverse direction,
`1 + (C_r (C₀^ρ + 4 C_B^ρ 4^(θρ) H))^(1/ρ) C_q (1 + γ_{1,q})` with `r = q/ρ`, Mathlib's constants
`C_r = LpAddConst r`, `C_q = LpAddConst q`, the constant `H = hardyConst ((θ - s)ρ) r` of Hardy's
inequality and `γ_{1,q} = dyadicGeomConst 1 q`. -/
noncomputable def inverseConst (s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  1 + (LpAddConst (q / ENNReal.ofReal ρ) * (M.C0 ^ ρ + 4 * M.CB ^ ρ * dyadicWeight (θ * ρ) 2 *
    hardyConst ((θ - s) * ρ) (q / ENNReal.ofReal ρ))) ^ ρ⁻¹ *
      (LpAddConst q * (1 + dyadicGeomConst 1 q))

/-- The constant of the inverse direction is finite for `s < θ`. -/
theorem inverseConst_ne_top (hsθ : s < θ) (q : ℝ≥0∞) : M.inverseConst s q ≠ ∞ := by
  have hρ := M.rho_pos
  have hα : 0 < (θ - s) * ρ := mul_pos (by linarith) hρ
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hρ.le) ?_) ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top _).ne (ENNReal.add_ne_top.2
      ⟨ENNReal.rpow_ne_top_of_nonneg hρ.le M.C0_ne_top, ?_⟩)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hρ.le M.CB_ne_top)) (ENNReal.dyadicWeight_ne_top _ _))
      (ENNReal.hardyConst_ne_top hα _)
  · exact ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q).ne
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩)

/-- **Jackson's direction**: `N₀(f) + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q} ≤ max(1, C_J) ‖f‖^ω_{s,q}`
for every `s` and `q`. -/
theorem eNormDyadic_le_modNorm (f : U) : A.eNormDyadic s q f ≤ max 1 M.CJ * M.modNorm s q f := by
  have hL : lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f) ≤
      M.CJ * lqNorm q (fun k => dyadicWeight s k * M.modulus f k) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    rw [mul_left_comm]
    gcongr
    exact M.jackson f k
  calc A.eNormDyadic s q f
      ≤ A.norm0 f + M.CJ * lqNorm q (fun k => dyadicWeight s k * M.modulus f k) :=
        add_le_add le_rfl hL
    _ ≤ max 1 M.CJ * A.norm0 f +
          max 1 M.CJ * lqNorm q (fun k => dyadicWeight s k * M.modulus f k) := by
        gcongr
        · exact le_mul_of_one_le_left' (le_max_left _ _)
        · exact le_max_right _ _
    _ = max 1 M.CJ * M.modNorm s q f := by rw [modNorm, mul_add]

/-- **The inverse direction**: for `0 ≤ s < θ` and every `q`,
`‖f‖^ω_{s,q} ≤ K (N₀(f) + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q})` with `K = M.inverseConst s q`. The
near-best elements `b_k` have the tolerances `N₀(f) 2^(-k(s+1))`. -/
theorem modNorm_le_eNormDyadic (hs : 0 ≤ s) (hsθ : s < θ) (f : U) :
    M.modNorm s q f ≤ M.inverseConst s q * A.eNormDyadic s q f := by
  have hθ : 0 ≤ θ := hs.trans hsθ.le
  have hρ := M.rho_pos
  have hone : 1 ≤ M.inverseConst s q := le_self_add
  have hfN : A.norm0 f ≤ A.eNormDyadic s q f := le_self_add
  rcases eq_or_ne (A.norm0 f) ∞ with hf | hf
  · rw [hf, top_le_iff] at hfN
    rw [hfN, ENNReal.mul_top (one_pos.trans_le hone).ne']
    exact le_top
  rcases eq_or_ne (A.norm0 f) 0 with hf0 | hf0
  · have hω : ∀ k, M.modulus f k = 0 := fun k =>
      le_antisymm ((M.le_norm0 f k).trans_eq (by rw [hf0, mul_zero])) bot_le
    simp [modNorm, hf0, hω]
  have hE : ∀ k, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hf (eFunctional_le_norm0 M.norm1_zero f)
  choose b hb1 hb0 using fun k => exists_norm0_sub_le_eFunctional_add (hE k)
    (mul_ne_zero hf0 (ENNReal.dyadicWeight_ne_zero (-(s + 1)) k))
  obtain ⟨e, he_eq⟩ : ∃ e : ℕ → ℝ≥0∞, e = fun k =>
      A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f + A.norm0 f * dyadicWeight (-(s + 1)) k := ⟨_, rfl⟩
  have hbe : ∀ j, A.norm0 (f - b j) ≤ e j := fun j => by rw [he_eq]; exact hb0 j
  have he : Antitone e := by
    rw [he_eq]
    intro i j hij
    exact add_le_add (eFunctional_anti f (Nat.cast_le.2 (Nat.pow_le_pow_right two_pos hij)))
      (mul_le_mul_right (ENNReal.dyadicWeight_anti (by linarith) hij) _)
  have hfe : A.norm0 f ≤ e 0 := by
    rw [he_eq]
    exact le_add_left (le_of_eq (by rw [ENNReal.dyadicWeight_zero_right, mul_one]))
  have hX : lqNorm q (fun k => dyadicWeight s k * e k) ≤
      LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q f := by
    rw [he_eq]
    exact lqNorm_dyadicWeight_mul_eFunctional_add_le A s q f
  have hmain := M.lqNorm_rpow_le (s := s) hθ hb1 hbe he hfe (q / ENNReal.ofReal ρ)
  rw [ENNReal.lqNorm_div_fun_rpow hρ, ENNReal.lqNorm_div_fun_rpow hρ] at hmain
  set K := LpAddConst (q / ENNReal.ofReal ρ) * (M.C0 ^ ρ + 4 * M.CB ^ ρ *
    dyadicWeight (θ * ρ) 2 * hardyConst ((θ - s) * ρ) (q / ENNReal.ofReal ρ))
  set P := LpAddConst q * (1 + dyadicGeomConst 1 q)
  set N := A.eNormDyadic s q f
  have h2 : lqNorm q (fun k => dyadicWeight s k * M.modulus f k) ≤ K ^ ρ⁻¹ * (P * N) := by
    calc lqNorm q (fun k => dyadicWeight s k * M.modulus f k)
        = (lqNorm q (fun k => dyadicWeight s k * M.modulus f k) ^ ρ) ^ ρ⁻¹ :=
          (ENNReal.rpow_rpow_inv hρ.ne' _).symm
      _ ≤ (K * (P * N) ^ ρ) ^ ρ⁻¹ := by
          refine ENNReal.rpow_le_rpow (hmain.trans ?_) (inv_nonneg.2 hρ.le)
          gcongr
      _ = K ^ ρ⁻¹ * (P * N) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hρ.le), ENNReal.rpow_rpow_inv hρ.ne']
  calc M.modNorm s q f = A.norm0 f + lqNorm q (fun k => dyadicWeight s k * M.modulus f k) := rfl
    _ ≤ N + K ^ ρ⁻¹ * (P * N) := add_le_add hfN h2
    _ = (1 + K ^ ρ⁻¹ * P) * N := by ring
    _ = M.inverseConst s q * N := rfl

/-- For `0 ≤ s < θ` and every `q`, the dyadic norm of the E-method is finite iff the classical
quasi-norm `N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q}` is. -/
theorem eNormDyadic_lt_top_iff (hs : 0 ≤ s) (hsθ : s < θ) (f : U) :
    A.eNormDyadic s q f < ∞ ↔ M.modNorm s q f < ∞ :=
  ⟨fun h => (M.modNorm_le_eNormDyadic hs hsθ f).trans_lt
      (ENNReal.mul_lt_top (M.inverseConst_ne_top hsθ q).lt_top h),
    fun h => (M.eNormDyadic_le_modNorm f).trans_lt
      (ENNReal.mul_lt_top (max_lt ENNReal.one_lt_top M.CJ_ne_top.lt_top) h)⟩

/-- **The coincidence theorem for `ρ`-normed couples**: if every `b` with `N₁(b) < 1` is `0`,
then for `0 < s < θ` and `q ≠ 0`, `f ∈ E_{s,q}` iff the classical quasi-norm
`N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q}` is finite. -/
theorem memEMethod_iff_modNorm_lt_top (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (hq0 : q ≠ 0)
    (hs : 0 < s) (hsθ : s < θ) (f : U) : A.MemEMethod s q f ↔ M.modNorm s q f < ∞ := by
  rw [memEMethod_iff_eNormDyadic_lt_top M.norm1_zero hdisc hs.le (Or.inl hs) hq0]
  exact M.eNormDyadic_lt_top_iff hs.le hsθ f

end ModulusData

end InterpCouple
