/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Resum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step3

/-!
# Step3Arith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-3 resummation arithmetic of the annular double sum

Local helpers for ABK26, Section 4.1, proof of Proposition
`p.mathcalE.annular.decomp`, Step 3.  The three Step-3 displays all resum the
*same* object: a guarded annular double sum `sum_{j <= m} sum_{n <= j-1}` whose
`(j,n)`-content is bounded by a polynomial in the scale gap `q = m - n` times a
geometric weight `3^(-c q)`.  This module proves that arithmetic once, at
abstract nonnegative fields.

## The two structural facts

* `annDouble_eq_natIterated` -- the guarded annular double sum is the iterated
  `N`-sum `sum_{u} sum_{i}` under `j = m - u`, `n = m - u - 1 - i`, so that the
  scale gap is `q = m - n = u + i + 1`.  The `j`-multiplicity the manuscript
  writes as `(m - n + 1)` is exactly the number of `(u,i)` pairs with a given
  `u + i`; no multiplicity is inserted or dropped by hand.
* `annDouble_le_of_linear_geom` / `annDouble_le_of_quadratic_geom` -- the two
  resummation bounds, at a linear and at a quadratic polynomial content.  The
  constants `c^(-3)` and `c^(-4)` are the honest ones: a degree-`p` polynomial
  content against `3^(-cq)` over the annular region costs `c^(-(p+2))`, one
  power of `c` for the `q`-sum and one for the annulus multiplicity.

## Where the manuscript's constants come from

`Step 3`'s three displays are instances:

* the `sigma-bar` sum has quadratic content `gamma^2 (m-n)^2 + cstar^(-4)
  gamma^2 |log gamma|^4` at rate `c = s - 2 gamma`, hence `gamma^2
  (s-2gamma)^(-4) + cstar^(-4) gamma^2 |log gamma|^4 (s-2gamma)^(-2)`.
* the two `G_1^b` displays have linear content `(m - n + 2)` at rate `c = s/2`
  resp.  `c = (s - 4 gamma)/2`, hence `s^(-3)` resp.  `(s - 4 gamma)^(-3)`.

## The `1 - 3^(-c) >= c/2` input

Every constant below is produced from `half_le_one_sub_threeRpow_neg` (the
proved convexity input of the resummation module), so no numeric tactic ever
enters a `Real.rpow` or `Real.log` term.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## Polynomial-times-geometric sums on `N` -/

/-- Summability of `(i+1)^0 r^i`. -/
theorem summable_geom_nat {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun i : ℕ => r ^ i) :=
  summable_geometric_of_lt_one hr0 hr1

/-- Summability of `(i+1) r^i`. -/
theorem summable_poly1_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun i : ℕ => ((i : ℝ) + 1) * r ^ i) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  refine (summable_choose_mul_geometric_of_norm_lt_one 1 hnorm).congr fun n => ?_
  rw [Nat.choose_one_right]
  push_cast
  ring

/-- `sum_i (i+1) r^i = (1-r)^(-2)`. -/
theorem tsum_poly1_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' i : ℕ, ((i : ℝ) + 1) * r ^ i = 1 / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h := tsum_choose_mul_geometric_of_norm_lt_one 1 hnorm
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [← h]
  refine tsum_congr fun n => ?_
  rw [Nat.choose_one_right]
  push_cast
  ring

/-- Summability of `(i+1)^2 r^i`. -/
theorem summable_poly2_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ i) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hchSummable : Summable (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one 2 hnorm
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (by positivity) (pow_nonneg hr0 i)) (fun i => ?_)
    (hchSummable.mul_left 2)
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hle : ((i : ℝ) + 1) ^ 2 ≤ 2 * ((i + 2).choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    push_cast
    linarith only [hi]
  calc ((i : ℝ) + 1) ^ 2 * r ^ i ≤ 2 * ((i + 2).choose 2 : ℝ) * r ^ i :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg hr0 i)
    _ = 2 * (((i + 2).choose 2 : ℝ) * r ^ i) := by ring

/-! ## The `N x N` product sums -/

/-- The product-family summability used by every bound below. -/
theorem summable_prodFam_of_nonneg {A B : ℕ → ℝ} (hA0 : ∀ u, 0 ≤ A u)
    (hB0 : ∀ i, 0 ≤ B i) (hA : Summable A) (hB : Summable B) :
    Summable (fun p : ℕ × ℕ => A p.1 * B p.2) :=
  hA.mul_of_nonneg hB hA0 hB0

/-- The product-family sum. -/
theorem tsum_prodFam_of_nonneg {A B : ℕ → ℝ} (hA0 : ∀ u, 0 ≤ A u) (hB0 : ∀ i, 0 ≤ B i)
    (hA : Summable A) (hB : Summable B) :
    ∑' p : ℕ × ℕ, A p.1 * B p.2 = (∑' u : ℕ, A u) * (∑' i : ℕ, B i) :=
  (Summable.tsum_mul_tsum hA hB (summable_prodFam_of_nonneg hA0 hB0 hA hB)).symm

/-! ## The guarded-sum to `N`-shift bridge -/

private theorem natShift_injective (b : ℤ) :
    Function.Injective (fun i : ℕ => b - (i : ℤ)) := by
  intro i j h
  simp only at h
  omega

/-- **The guarded `Z`-sum as an `N`-sum.**  A sum over `{n : n <= b}` is the
`N`-sum along `n = b - i`. -/
theorem tsum_int_guard_le (g : ℤ → ℝ) (b : ℤ) :
    ∑' n : ℤ, (if n ≤ b then g n else 0) = ∑' i : ℕ, g (b - (i : ℤ)) := by
  classical
  set G : ℤ → ℝ := fun n => if n ≤ b then g n else 0 with hG
  have hsupp : Function.support G ⊆ Set.range (fun i : ℕ => b - (i : ℤ)) := by
    intro n hn
    have hle : n ≤ b := by
      by_contra hc
      exact hn (by rw [hG]; exact ite_eq_right hc)
    refine ⟨(b - n).toNat, ?_⟩
    show b - (((b - n).toNat : ℕ) : ℤ) = n
    omega
  have hkey := (natShift_injective b).tsum_eq hsupp
  rw [← hkey]
  refine tsum_congr fun i => ?_
  rw [hG]
  exact ite_eq_left (by omega)

/-- **The guarded annular double sum as an iterated `N`-sum.**  Under `j = m - u`
and `n = m - u - 1 - i` the annular region `{(j,n): j <= m, n <= j - 1}` is
exactly `N x N`, and the scale gap is `m - n = u + i + 1`. -/
theorem annDouble_eq_natIterated (m : ℤ) (h : ℤ → ℤ → ℝ) :
    annDouble m h
      = ∑' u : ℕ, ∑' i : ℕ, h (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) := by
  rw [annDouble_def,
    tsum_int_guard_le (fun j => ∑' n : ℤ, (if n ≤ j - 1 then h j n else 0)) m]
  exact tsum_congr fun u => tsum_int_guard_le (h (m - (u : ℤ))) (m - (u : ℤ) - 1)

/-- The scale gap along the `N x N` parametrization. -/
theorem gap_natIterated (m : ℤ) (u i : ℕ) :
    ((m - (m - (u : ℤ) - 1 - (i : ℤ)) : ℤ) : ℝ) = (u : ℝ) + (i : ℝ) + 1 := by
  push_cast
  ring

/-! ## The abstract resummation bound -/

/-- **The annular resummation bound at an `N x N` majorant.** -/
theorem annDouble_le_of_natMajorant {m : ℤ} {h : ℤ → ℤ → ℝ} {F : ℕ × ℕ → ℝ}
    (hh0 : ∀ j n, 0 ≤ h j n) (hF : Summable F)
    (hle : ∀ u i : ℕ, h (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) ≤ F (u, i)) :
    annDouble m h ≤ ∑' p : ℕ × ℕ, F p := by
  classical
  set H : ℕ × ℕ → ℝ :=
    fun p => h (m - (p.1 : ℤ)) (m - (p.1 : ℤ) - 1 - (p.2 : ℤ)) with hHdef
  have hH0 : ∀ p : ℕ × ℕ, 0 ≤ H p := fun p => hh0 _ _
  have hHle : ∀ p : ℕ × ℕ, H p ≤ F p := fun p => hle p.1 p.2
  have hHsum : Summable H := Summable.of_nonneg_of_le hH0 hHle hF
  have hiter : annDouble m h = ∑' p : ℕ × ℕ, H p := by
    rw [annDouble_eq_natIterated, hHsum.tsum_prod]
  rw [hiter]
  exact Summable.tsum_le_tsum hHle hHsum hF

/-! ## The two polynomial rates -/

private theorem rho_lt_one {c : ℝ} (hc0 : 0 < c) : (3 : ℝ) ^ (-c) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc0])

private theorem rho_nonneg (c : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ (-c) :=
  Real.rpow_nonneg (by norm_num) _

private theorem inv_one_sub_rho_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (1 - (3 : ℝ) ^ (-c))⁻¹ ≤ 2 / c := by
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-c) := by
    linarith only [rho_lt_one hc0]
  have hhalf : c / 2 ≤ 1 - (3 : ℝ) ^ (-c) := half_le_one_sub_threeRpow_neg hc0 hc1
  have hc2 : (0 : ℝ) < c / 2 := by linarith only [hc0]
  have hstep : (1 - (3 : ℝ) ^ (-c))⁻¹ ≤ (c / 2)⁻¹ := inv_anti₀ hc2 hhalf
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The geometric weight along the `N x N` parametrization. -/
private theorem geom_split (c : ℝ) (u i : ℕ) :
    (3 : ℝ) ^ (-(c * ((u : ℝ) + (i : ℝ) + 1)))
      = (3 : ℝ) ^ (-c) * ((3 : ℝ) ^ (-c)) ^ u * ((3 : ℝ) ^ (-c)) ^ i := by
  rw [← threeRpow_neg_natMul c u, ← threeRpow_neg_natMul c i,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **Linear content.**  If the annular `(j,n)`-content is bounded by
`(K1 (m-n) + K0) 3^(-c(m-n))` then the double sum is at most
`16 K1 c^(-3) + 4 K0 c^(-2)`. -/
theorem annDouble_le_of_linear_geom {m : ℤ} {h : ℤ → ℤ → ℝ} {K1 K0 c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hK1 : 0 ≤ K1) (hK0 : 0 ≤ K0)
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      h j n ≤ (K1 * ((m - n : ℤ) : ℝ) + K0)
        * (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ)))) :
    annDouble m h ≤ 16 * K1 / c ^ 3 + 4 * K0 / c ^ 2 := by
  classical
  set rho : ℝ := (3 : ℝ) ^ (-c) with hrho
  have hr0 : 0 ≤ rho := rho_nonneg c
  have hr1 : rho < 1 := rho_lt_one hc0
  have hpos : (0 : ℝ) < 1 - rho := by linarith only [hr1]
  have hinv : (1 - rho)⁻¹ ≤ 2 / c := inv_one_sub_rho_le hc0 hc1
  have hinv0 : (0 : ℝ) < (1 - rho)⁻¹ := inv_pos.2 hpos
  -- the majorant
  set A1 : ℕ → ℝ := fun u => ((u : ℝ) + 1) * rho ^ u with hA1
  set A0 : ℕ → ℝ := fun u => rho ^ u with hA0
  have hA10 : ∀ u, 0 ≤ A1 u := fun u => mul_nonneg (by positivity) (pow_nonneg hr0 u)
  have hA00 : ∀ u, 0 ≤ A0 u := fun u => pow_nonneg hr0 u
  have hA1s : Summable A1 := summable_poly1_geom hr0 hr1
  have hA0s : Summable A0 := summable_geom_nat hr0 hr1
  have hA1v : ∑' u : ℕ, A1 u = 1 / (1 - rho) ^ 2 := tsum_poly1_geom hr0 hr1
  have hA0v : ∑' u : ℕ, A0 u = (1 - rho)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  set F : ℕ × ℕ → ℝ :=
    fun p => K1 * rho * (A1 p.1 * A0 p.2) + K1 * rho * (A0 p.1 * A1 p.2)
      + K0 * rho * (A0 p.1 * A0 p.2) with hF
  have hFsum : Summable F := by
    refine Summable.add (Summable.add ?_ ?_) ?_
    · exact (summable_prodFam_of_nonneg hA10 hA00 hA1s hA0s).mul_left _
    · exact (summable_prodFam_of_nonneg hA00 hA10 hA0s hA1s).mul_left _
    · exact (summable_prodFam_of_nonneg hA00 hA00 hA0s hA0s).mul_left _
  have hmaj : ∀ u i : ℕ,
      h (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) ≤ F (u, i) := by
    intro u i
    have hstep := hle (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) (by omega) (by omega)
    rw [gap_natIterated m u i] at hstep
    refine hstep.trans ?_
    have hgeom : (3 : ℝ) ^ (-(c * ((u : ℝ) + (i : ℝ) + 1)))
        = rho * rho ^ u * rho ^ i := by rw [hrho, geom_split c u i]
    have hgeom0 : (0 : ℝ) ≤ rho * rho ^ u * rho ^ i :=
      mul_nonneg (mul_nonneg hr0 (pow_nonneg hr0 u)) (pow_nonneg hr0 i)
    have hshift : K1 * ((u : ℝ) + (i : ℝ) + 1) + K0 + K1
        = K1 * (((u : ℝ) + 1) + ((i : ℝ) + 1)) + K0 := by ring
    rw [hgeom, hF]
    simp only [hA1, hA0]
    calc (K1 * ((u : ℝ) + (i : ℝ) + 1) + K0) * (rho * rho ^ u * rho ^ i)
        ≤ (K1 * (((u : ℝ) + 1) + ((i : ℝ) + 1)) + K0) * (rho * rho ^ u * rho ^ i) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK1, hshift]) hgeom0
      _ = K1 * rho * (((u : ℝ) + 1) * rho ^ u * rho ^ i)
            + K1 * rho * (rho ^ u * (((i : ℝ) + 1) * rho ^ i))
            + K0 * rho * (rho ^ u * rho ^ i) := by ring
  have hbase := annDouble_le_of_natMajorant hh0 hFsum hmaj
  -- evaluate the majorant
  have hFval : ∑' p : ℕ × ℕ, F p
      = K1 * rho * ((∑' u : ℕ, A1 u) * (∑' i : ℕ, A0 i))
        + K1 * rho * ((∑' u : ℕ, A0 u) * (∑' i : ℕ, A1 i))
        + K0 * rho * ((∑' u : ℕ, A0 u) * (∑' i : ℕ, A0 i)) := by
    rw [hF]
    rw [Summable.tsum_add (Summable.add
        ((summable_prodFam_of_nonneg hA10 hA00 hA1s hA0s).mul_left _)
        ((summable_prodFam_of_nonneg hA00 hA10 hA0s hA1s).mul_left _))
      ((summable_prodFam_of_nonneg hA00 hA00 hA0s hA0s).mul_left _),
      Summable.tsum_add ((summable_prodFam_of_nonneg hA10 hA00 hA1s hA0s).mul_left _)
        ((summable_prodFam_of_nonneg hA00 hA10 hA0s hA1s).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_prodFam_of_nonneg hA10 hA00 hA1s hA0s,
      tsum_prodFam_of_nonneg hA00 hA10 hA0s hA1s,
      tsum_prodFam_of_nonneg hA00 hA00 hA0s hA0s]
  rw [hFval, hA1v, hA0v] at hbase
  refine hbase.trans ?_
  -- the constant arithmetic
  have hcube : (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹) ≤ (2 / c) ^ 3 := by
    have h1 : (0 : ℝ) ≤ (1 - rho)⁻¹ := hinv0.le
    have h2 : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) * (2 / c) :=
      mul_le_mul hinv hinv h1 (by positivity)
    calc (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹)
        ≤ (2 / c) * ((2 / c) * (2 / c)) :=
          mul_le_mul hinv h2 (mul_nonneg h1 h1) (by positivity)
      _ = (2 / c) ^ 3 := by ring
  have hsq : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (1 - rho)⁻¹ := hinv0.le
    calc (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) * (2 / c) :=
          mul_le_mul hinv hinv h1 (by positivity)
      _ = (2 / c) ^ 2 := by ring
  have hrho1 : rho ≤ 1 := hr1.le
  have hne : (1 : ℝ) - rho ≠ 0 := ne_of_gt hpos
  have hsqrw : (1 : ℝ) / (1 - rho) ^ 2 * (1 - rho)⁻¹
      = (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹) := by
    field_simp
  have hsqrw2 : (1 - rho)⁻¹ * (1 / (1 - rho) ^ 2)
      = (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹) := by
    field_simp
  have hK1rho : 0 ≤ K1 * rho := mul_nonneg hK1 hr0
  have hK0rho : 0 ≤ K0 * rho := mul_nonneg hK0 hr0
  have hT1 : K1 * rho * (1 / (1 - rho) ^ 2 * (1 - rho)⁻¹) ≤ K1 * (2 / c) ^ 3 := by
    rw [hsqrw]
    calc K1 * rho * ((1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹))
        ≤ K1 * rho * (2 / c) ^ 3 := mul_le_mul_of_nonneg_left hcube hK1rho
      _ ≤ K1 * 1 * (2 / c) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrho1 hK1) (by positivity)
      _ = K1 * (2 / c) ^ 3 := by ring
  have hT2 : K1 * rho * ((1 - rho)⁻¹ * (1 / (1 - rho) ^ 2)) ≤ K1 * (2 / c) ^ 3 := by
    rw [hsqrw2]
    calc K1 * rho * ((1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹))
        ≤ K1 * rho * (2 / c) ^ 3 := mul_le_mul_of_nonneg_left hcube hK1rho
      _ ≤ K1 * 1 * (2 / c) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrho1 hK1) (by positivity)
      _ = K1 * (2 / c) ^ 3 := by ring
  have hT3 : K0 * rho * ((1 - rho)⁻¹ * (1 - rho)⁻¹) ≤ K0 * (2 / c) ^ 2 := by
    calc K0 * rho * ((1 - rho)⁻¹ * (1 - rho)⁻¹)
        ≤ K0 * rho * (2 / c) ^ 2 := mul_le_mul_of_nonneg_left hsq hK0rho
      _ ≤ K0 * 1 * (2 / c) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrho1 hK0) (by positivity)
      _ = K0 * (2 / c) ^ 2 := by ring
  have hcube3 : ((2 : ℝ) / c) ^ 3 = 8 / c ^ 3 := by
    rw [div_pow]
    norm_num
  have hcube2 : ((2 : ℝ) / c) ^ 2 = 4 / c ^ 2 := by
    rw [div_pow]
    norm_num
  have hfin1 : K1 * (2 / c) ^ 3 = 8 * K1 / c ^ 3 := by
    rw [hcube3]
    ring
  have hfin2 : K0 * (2 / c) ^ 2 = 4 * K0 / c ^ 2 := by
    rw [hcube2]
    ring
  rw [hfin1] at hT1 hT2
  rw [hfin2] at hT3
  refine (add_le_add (add_le_add hT1 hT2) hT3).trans (le_of_eq ?_)
  ring

/-- **Quadratic content.**  If the annular `(j,n)`-content is bounded by
`(K2 (m-n)^2 + K0) 3^(-c(m-n))` then the double sum is at most
`128 K2 c^(-4) + 4 K0 c^(-2)`. -/
theorem annDouble_le_of_quadratic_geom {m : ℤ} {h : ℤ → ℤ → ℝ} {K2 K0 c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hK2 : 0 ≤ K2) (hK0 : 0 ≤ K0)
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      h j n ≤ (K2 * ((m - n : ℤ) : ℝ) ^ 2 + K0)
        * (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ)))) :
    annDouble m h ≤ 128 * K2 / c ^ 4 + 4 * K0 / c ^ 2 := by
  classical
  set rho : ℝ := (3 : ℝ) ^ (-c) with hrho
  have hr0 : 0 ≤ rho := rho_nonneg c
  have hr1 : rho < 1 := rho_lt_one hc0
  have hpos : (0 : ℝ) < 1 - rho := by linarith only [hr1]
  have hinv : (1 - rho)⁻¹ ≤ 2 / c := inv_one_sub_rho_le hc0 hc1
  have hinv0 : (0 : ℝ) < (1 - rho)⁻¹ := inv_pos.2 hpos
  set A2 : ℕ → ℝ := fun u => ((u : ℝ) + 1) ^ 2 * rho ^ u with hA2
  set A0 : ℕ → ℝ := fun u => rho ^ u with hA0
  have hA20 : ∀ u, 0 ≤ A2 u := fun u => mul_nonneg (by positivity) (pow_nonneg hr0 u)
  have hA00 : ∀ u, 0 ≤ A0 u := fun u => pow_nonneg hr0 u
  have hA2s : Summable A2 := summable_poly2_geom hr0 hr1
  have hA0s : Summable A0 := summable_geom_nat hr0 hr1
  have hA2v : ∑' u : ℕ, A2 u ≤ 2 / (1 - rho) ^ 3 := poly2_geom_tail_le hr0 hr1
  have hA0v : ∑' u : ℕ, A0 u = (1 - rho)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  set F : ℕ × ℕ → ℝ :=
    fun p => 2 * K2 * rho * (A2 p.1 * A0 p.2) + 2 * K2 * rho * (A0 p.1 * A2 p.2)
      + K0 * rho * (A0 p.1 * A0 p.2) with hF
  have hFsum : Summable F := by
    refine Summable.add (Summable.add ?_ ?_) ?_
    · exact (summable_prodFam_of_nonneg hA20 hA00 hA2s hA0s).mul_left _
    · exact (summable_prodFam_of_nonneg hA00 hA20 hA0s hA2s).mul_left _
    · exact (summable_prodFam_of_nonneg hA00 hA00 hA0s hA0s).mul_left _
  have hmaj : ∀ u i : ℕ,
      h (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) ≤ F (u, i) := by
    intro u i
    have hstep := hle (m - (u : ℤ)) (m - (u : ℤ) - 1 - (i : ℤ)) (by omega) (by omega)
    rw [gap_natIterated m u i] at hstep
    refine hstep.trans ?_
    have hgeom : (3 : ℝ) ^ (-(c * ((u : ℝ) + (i : ℝ) + 1)))
        = rho * rho ^ u * rho ^ i := by rw [hrho, geom_split c u i]
    rw [hgeom, hF]
    simp only [hA2, hA0]
    have hu : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hsq : ((u : ℝ) + (i : ℝ) + 1) ^ 2
        ≤ 2 * ((u : ℝ) + 1) ^ 2 + 2 * ((i : ℝ) + 1) ^ 2 := by
      have hmono : ((u : ℝ) + (i : ℝ) + 1) ^ 2 ≤ (((u : ℝ) + 1) + ((i : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (by linarith only [hu, hi]) (by linarith only []) 2
      have hcross : (0 : ℝ) ≤ (((u : ℝ) + 1) - ((i : ℝ) + 1)) ^ 2 := sq_nonneg _
      have hexp : (((u : ℝ) + 1) + ((i : ℝ) + 1)) ^ 2
          + (((u : ℝ) + 1) - ((i : ℝ) + 1)) ^ 2
          = 2 * ((u : ℝ) + 1) ^ 2 + 2 * ((i : ℝ) + 1) ^ 2 := by ring
      linarith only [hmono, hcross, hexp]
    have hgeom0 : (0 : ℝ) ≤ rho * rho ^ u * rho ^ i :=
      mul_nonneg (mul_nonneg hr0 (pow_nonneg hr0 u)) (pow_nonneg hr0 i)
    have hstep2 : K2 * ((u : ℝ) + (i : ℝ) + 1) ^ 2 + K0
        ≤ 2 * K2 * ((u : ℝ) + 1) ^ 2 + 2 * K2 * ((i : ℝ) + 1) ^ 2 + K0 := by
      have := mul_le_mul_of_nonneg_left hsq hK2
      linarith only [this]
    calc (K2 * ((u : ℝ) + (i : ℝ) + 1) ^ 2 + K0) * (rho * rho ^ u * rho ^ i)
        ≤ (2 * K2 * ((u : ℝ) + 1) ^ 2 + 2 * K2 * ((i : ℝ) + 1) ^ 2 + K0)
            * (rho * rho ^ u * rho ^ i) := mul_le_mul_of_nonneg_right hstep2 hgeom0
      _ = 2 * K2 * rho * ((((u : ℝ) + 1) ^ 2 * rho ^ u) * rho ^ i)
            + 2 * K2 * rho * (rho ^ u * (((i : ℝ) + 1) ^ 2 * rho ^ i))
            + K0 * rho * (rho ^ u * rho ^ i) := by ring
  have hbase := annDouble_le_of_natMajorant hh0 hFsum hmaj
  have hFval : ∑' p : ℕ × ℕ, F p
      = 2 * K2 * rho * ((∑' u : ℕ, A2 u) * (∑' i : ℕ, A0 i))
        + 2 * K2 * rho * ((∑' u : ℕ, A0 u) * (∑' i : ℕ, A2 i))
        + K0 * rho * ((∑' u : ℕ, A0 u) * (∑' i : ℕ, A0 i)) := by
    rw [hF]
    rw [Summable.tsum_add (Summable.add
        ((summable_prodFam_of_nonneg hA20 hA00 hA2s hA0s).mul_left _)
        ((summable_prodFam_of_nonneg hA00 hA20 hA0s hA2s).mul_left _))
      ((summable_prodFam_of_nonneg hA00 hA00 hA0s hA0s).mul_left _),
      Summable.tsum_add ((summable_prodFam_of_nonneg hA20 hA00 hA2s hA0s).mul_left _)
        ((summable_prodFam_of_nonneg hA00 hA20 hA0s hA2s).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_prodFam_of_nonneg hA20 hA00 hA2s hA0s,
      tsum_prodFam_of_nonneg hA00 hA20 hA0s hA2s,
      tsum_prodFam_of_nonneg hA00 hA00 hA0s hA0s]
  rw [hFval, hA0v] at hbase
  refine hbase.trans ?_
  have hA20' : (0 : ℝ) ≤ ∑' u : ℕ, A2 u := tsum_nonneg hA20
  have hinvle : (0 : ℝ) ≤ (1 - rho)⁻¹ := hinv0.le
  have hne : (1 : ℝ) - rho ≠ 0 := ne_of_gt hpos
  have hcube : (2 : ℝ) / (1 - rho) ^ 3 * (1 - rho)⁻¹ ≤ 2 * (2 / c) ^ 4 := by
    have hrw : (2 : ℝ) / (1 - rho) ^ 3 * (1 - rho)⁻¹
        = 2 * ((1 - rho)⁻¹ * (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹)) := by
      field_simp
    rw [hrw]
    have h2 : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) * (2 / c) :=
      mul_le_mul hinv hinv hinvle (by positivity)
    have h4 : (1 - rho)⁻¹ * (1 - rho)⁻¹ * ((1 - rho)⁻¹ * (1 - rho)⁻¹)
        ≤ ((2 / c) * (2 / c)) * ((2 / c) * (2 / c)) :=
      mul_le_mul h2 h2 (mul_nonneg hinvle hinvle) (by positivity)
    have hrw2 : ((2 : ℝ) / c) * (2 / c) * ((2 / c) * (2 / c)) = (2 / c) ^ 4 := by ring
    rw [hrw2] at h4
    linarith only [h4]
  have hsq : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) ^ 2 := by
    have h2 : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) * (2 / c) :=
      mul_le_mul hinv hinv hinvle (by positivity)
    calc (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ (2 / c) * (2 / c) := h2
      _ = (2 / c) ^ 2 := by ring
  have hK2rho : 0 ≤ 2 * K2 * rho := by positivity
  have hrho1 : rho ≤ 1 := hr1.le
  have hA2sum : (∑' u : ℕ, A2 u) * (1 - rho)⁻¹ ≤ 2 * (2 / c) ^ 4 := by
    calc (∑' u : ℕ, A2 u) * (1 - rho)⁻¹
        ≤ (2 / (1 - rho) ^ 3) * (1 - rho)⁻¹ :=
          mul_le_mul_of_nonneg_right hA2v hinvle
      _ ≤ 2 * (2 / c) ^ 4 := hcube
  have hA2sum' : (1 - rho)⁻¹ * (∑' u : ℕ, A2 u) ≤ 2 * (2 / c) ^ 4 := by
    rw [mul_comm]
    exact hA2sum
  have hT1 : 2 * K2 * rho * ((∑' u : ℕ, A2 u) * (1 - rho)⁻¹)
      ≤ 2 * K2 * (2 * (2 / c) ^ 4) := by
    calc 2 * K2 * rho * ((∑' u : ℕ, A2 u) * (1 - rho)⁻¹)
        ≤ 2 * K2 * rho * (2 * (2 / c) ^ 4) :=
          mul_le_mul_of_nonneg_left hA2sum hK2rho
      _ ≤ 2 * K2 * 1 * (2 * (2 / c) ^ 4) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrho1 (by positivity)) (by positivity)
      _ = 2 * K2 * (2 * (2 / c) ^ 4) := by ring
  have hT2 : 2 * K2 * rho * ((1 - rho)⁻¹ * (∑' i : ℕ, A2 i))
      ≤ 2 * K2 * (2 * (2 / c) ^ 4) := by
    calc 2 * K2 * rho * ((1 - rho)⁻¹ * (∑' i : ℕ, A2 i))
        ≤ 2 * K2 * rho * (2 * (2 / c) ^ 4) :=
          mul_le_mul_of_nonneg_left hA2sum' hK2rho
      _ ≤ 2 * K2 * 1 * (2 * (2 / c) ^ 4) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrho1 (by positivity)) (by positivity)
      _ = 2 * K2 * (2 * (2 / c) ^ 4) := by ring
  have hT3 : K0 * rho * ((1 - rho)⁻¹ * (1 - rho)⁻¹) ≤ K0 * (2 / c) ^ 2 := by
    calc K0 * rho * ((1 - rho)⁻¹ * (1 - rho)⁻¹)
        ≤ K0 * rho * (2 / c) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hK0 hr0)
      _ ≤ K0 * 1 * (2 / c) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrho1 hK0) (by positivity)
      _ = K0 * (2 / c) ^ 2 := by ring
  have hq4 : ((2 : ℝ) / c) ^ 4 = 16 / c ^ 4 := by
    rw [div_pow]
    norm_num
  have hq2 : ((2 : ℝ) / c) ^ 2 = 4 / c ^ 2 := by
    rw [div_pow]
    norm_num
  have hfin1 : 2 * K2 * (2 * ((2 : ℝ) / c) ^ 4) = 64 * K2 / c ^ 4 := by
    rw [hq4]
    ring
  have hfin2 : K0 * ((2 : ℝ) / c) ^ 2 = 4 * K0 / c ^ 2 := by
    rw [hq2]
    ring
  rw [hfin1] at hT1 hT2
  rw [hfin2] at hT3
  refine (add_le_add (add_le_add hT1 hT2) hT3).trans (le_of_eq ?_)
  ring

end

end Algsuperdiff.Section4.Provider.Annular
