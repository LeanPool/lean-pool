/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.Determinant.SingularReduction
import LeanPool.CCDN.Determinant.PrimeAggregation
import LeanPool.CCDN.Determinant.SingularDeterminant

/-! Fourth-power cutoff removes the polynomial-in-degree error from the
singular determinant prime sum, retaining an explicit logarithmic cutoff cost. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real MvPolynomial

/-- For `d⁴ ≤ L < p`, the singular-point correction `d² (d - 1)` is at most `d² √p`. -/
lemma singular_correction_absorb {d p : ℕ} (hd : 0 < d) {L : ℝ}
    (hdL : (d : ℝ) ^ 4 ≤ L) (hpL : L < (p : ℝ)) :
    ((d ^ 2 * (d - 1) : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have hs : (d : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (hpow.trans (hdL.trans hpL.le))
  have hsub : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  push_cast
  exact mul_le_mul_of_nonneg_left (hsub.trans hs) (sq_nonneg _)

/-- The singular correction and sharp point-count term have a bounded total
prime-tail contribution above a fourth-power cutoff. Only logarithmic degree
loss remains when L is a constant multiple of d^4. -/
private theorem singular_determinant_log_lower_cutoff {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x L C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hdL : (f.totalDegree : ℝ) ^ 4 ≤ L) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) - 2 * primeBlockMass * (C + 1)) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hd4 : (f.totalDegree : ℝ) ≤ (f.totalDegree : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
  let m : ℕ → ℝ := fun p =>
    (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)
  have hlocal (p : ℕ) (hp : p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B) (hpL : L < (p : ℝ)) :
      0 < m p ∧ ∃ e : ℕ, (s : ℝ) ^ 2 / 2 / m p - s ≤ e ∧
        (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k)) := by
    have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
    have hchar : f.totalDegree < p := by exact_mod_cast hd4.trans_lt (hdL.trans_lt hpL)
    obtain ⟨hm, e, he, hdiv⟩ := singular_reduction_minorGcd_card_bound hs f g z hz
      (hf p hp hpL) hchar
    exact ⟨by dsimp only [m]; exact_mod_cast hm, e, by rwa [div_div], hdiv⟩
  have h := determinant_log_lower_of_local_divisors hx hd hdL (by linarith : 0 ≤ C + 1)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) B ∅ (empty_subset B)
    (by simp) 0 m (one_pos.trans_le (Int.Matrix.one_le_minorGcd hrows))
    (fun p hp hpL => (hlocal p hp hpL).1) (fun p hp hpL => by
      have hcorr := singular_correction_absorb hd hdL hpL
      have hcount := hupper p hp hpL
      dsimp only [m]
      rw [Nat.cast_add]
      nlinarith) (fun p hp hpL => (hlocal p hp hpL).2) (by simp)
  rw [sum_empty, add_zero] at h
  linarith

/-- The paper's cutoff 27*d^4 leaves precisely a 4*log(d) degree loss,
plus absolute constants and the explicit bad-prime charge. -/
private theorem singular_determinant_log_lower_degree_four {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - 4 * Real.log f.totalDegree - Real.log 27 -
      2 * mertensError - (∑ p ∈ B, Real.log p / p) - 2 * primeBlockMass * (C + 1)) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  have h := singular_determinant_log_lower_cutoff hs f hd g z hz hrows hx hC
    (show (f.totalDegree : ℝ) ^ 4 ≤ 27 * (f.totalDegree : ℝ) ^ 4 from
      le_mul_of_one_le_left (by positivity) (by norm_num))
    B hf hupper
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1
  ring

/-- The absolute error of the plane determinant lower bound at the cutoff
`stepanovThreshold d`, for residue constant `C` (`singular_determinant_log_lower_at_rank`):
`log 27` from `log (27 d⁴) = log 27 + 4 log d`, `2 mertensError` from Mertens' estimate,
`2 primeBlockMass (C + 1)` from the point-count error `C d² √p` and the singular correction
`d² (d - 1) ≤ d² √p`, and `2 (log 4 + 4)` from the term `s (log 4 + 4) x` at `x = s`. -/
def degreeFourDeterminantError (C : ℝ) : ℝ :=
  Real.log 27 + 2 * mertensError + 2 * primeBlockMass * (C + 1) + 2 * (Real.log 4 + 4)

/-- Choosing the prime upper endpoint to equal the row count yields the
plane-case shape of CCDN Proposition 3.2.6, with the geometric point-count and
bad-prime hypotheses explicit. -/
theorem singular_determinant_log_lower_at_rank {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {C : ℝ} (hC : 0 ≤ C) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ B,
      stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ B,
      stepanovThreshold (f.totalDegree : ℝ) < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log f.totalDegree -
      (∑ p ∈ B, Real.log p / p) - degreeFourDeterminantError C) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  have h := singular_determinant_log_lower_degree_four hs f hd g z hz hrows
    (x := (s : ℝ)) (by exact_mod_cast hs) hC B
    (by simpa only [Nat.floor_natCast] using hf)
    (by simpa only [Nat.floor_natCast] using hupper)
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end CCDN
