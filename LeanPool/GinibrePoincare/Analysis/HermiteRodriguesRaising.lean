/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesRaising.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.ComplexHermiteLowering
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Hermite Rodrigues raising

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `raw_raise_left`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

private def raisingTerm (ρ : ℝ) (p q k : ℕ) : Poly :=
  MvPolynomial.C ((-(ρ : ℂ))^k*(k.factorial : ℂ)*(Nat.choose p k : ℂ)*(Nat.choose q k : ℂ))*
    Z^(p-k)*W^(q-k)

private theorem raw_raising_sum (ρ : ℝ) (p q : ℕ) :
    raw ρ p q=∑ k∈Finset.range (q+1), raisingTerm ρ p q k := by
  unfold raw raisingTerm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_right p q)))
  intro k hk hkm
  have hkq : k≤q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpk : p<k := by
    by_contra h
    exact hkm (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min (Nat.le_of_not_gt h) hkq)))
  simp [Nat.choose_eq_zero_of_lt hpk]

private theorem raisingTerm_step (ρ : ℝ) (p q k : ℕ) :
    raisingTerm ρ (p+1) (q+1) (k+1)=
      Z*raisingTerm ρ p (q+1) (k+1)-
        MvPolynomial.C ((ρ : ℂ)*(q+1 : ℂ))*raisingTerm ρ p q k := by
  have hq := congrArg (fun t : ℕ => (t : ℂ)) (Nat.add_one_mul_choose_eq q k)
  push_cast at hq
  have hp : (Nat.choose (p+1) (k+1) : ℂ)=
      (Nat.choose p k : ℂ)+(Nat.choose p (k+1) : ℂ) := by
    exact_mod_cast Nat.choose_succ_succ' p k
  have hcoef :
      (-(ρ : ℂ))^(k+1)*((k+1).factorial : ℂ)*(Nat.choose (p+1) (k+1) : ℂ)*(Nat.choose (q+1) (k+1) :
          ℂ)=
      (-(ρ : ℂ))^(k+1)*((k+1).factorial : ℂ)*(Nat.choose p (k+1) : ℂ)*(Nat.choose (q+1) (k+1) : ℂ)-
      (ρ : ℂ)*(q+1 : ℂ)*((-(ρ : ℂ))^k*(k.factorial : ℂ)*(Nat.choose p k : ℂ)*(Nat.choose q k : ℂ))
          := by
    rw [hp, pow_succ, Nat.factorial_succ]
    push_cast
    linear_combination -((-(ρ : ℂ))^k*-(ρ : ℂ)*(k.factorial : ℂ)*(Nat.choose p k : ℂ))*hq
  unfold raisingTerm
  rw [hcoef]
  simp only [show p+1-(k+1)=p-k by omega, show q+1-(k+1)=q-k by omega,
    map_sub, map_mul]
  by_cases hkp : k<p
  · have he : Z^(p-k)=Z*Z^(p-(k+1)) := by
      rw [show p-k=p-(k+1)+1 by omega, pow_succ]; ring
    rw [he]
    ring
  · have hpk : p<k+1 := by omega
    simp only [Nat.choose_eq_zero_of_lt hpk, Nat.cast_zero, mul_zero, map_zero, zero_mul]
    ring

theorem raw_raise_left (ρ : ℝ) (p q : ℕ) :
    raw ρ (p+1) q=Z*raw ρ p q-MvPolynomial.C ((ρ : ℂ)*(q : ℂ))*raw ρ p (q-1) := by
  cases q with
  | zero => simp [pow_succ, mul_comm]
  | succ q =>
    have hsplit (r : ℕ) : raw ρ r (q+1)=
        (∑ k∈Finset.range (q+1), raisingTerm ρ r (q+1) (k+1))+raisingTerm ρ r (q+1) 0 := by
      rw [raw_raising_sum, Finset.sum_range_succ']
    rw [hsplit (p+1), hsplit p]
    simp only [Nat.succ_sub_one]
    rw [raw_raising_sum]
    simp_rw [raisingTerm_step]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
    have hzero (r : ℕ) : raisingTerm ρ r (q+1) 0=Z^r*W^(q+1) := by simp [raisingTerm]
    rw [hzero, hzero, pow_succ]
    push_cast
    ring

end
end ComplexHermite
end GinibrePoincare
