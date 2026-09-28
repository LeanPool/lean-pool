/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch002
public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch001


public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Zip
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
/-!
# Gerver sofa dependency batch

* `KernelOnly.AlternatingSeries`.
* `KernelOnly.Coordinates`.
* `KernelOnly.EndpointSymmetry`.
* `KernelOnly.Identification`.
* `KernelOnly.ReplayConsequences`.
* `KernelOnly.SoundnessInterfaces`.
* `KernelOnly.TranscendentalSoundness`.
* `KernelOnly.ADCoreSoundness`.
* `KernelOnly.ReducedADSoundness`.
* `KernelOnly.FullADSoundness`.
-/

@[expose] public section

noncomputable section


section

/-!
# Alternating-series kernel for the executable transcendental layer

This file connects the exact rational partial sums used by `ExactReplay` to
Mathlib's real power-series theorems.  The Taylor evaluator is intentionally
used only on arguments in `[0, 1]`; the range-reduction layer proves this
precondition before calling these results.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.ExactReplay

open scoped BigOperators
open Filter Finset

/-- Real magnitude of the `n`th sine-series term. -/
def sinMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

/-- Real magnitude of the `n`th cosine-series term. -/
def cosMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

/-- Real magnitude of the `n`th arctangent-series term. -/
def atanMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

/-- On `[0,1]`, the unsigned sine Taylor terms decrease. -/
theorem antitone_sinMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [sinMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned cosine Taylor terms decrease. -/
theorem antitone_cosMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [cosMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast Nat.factorial_le (by omega)

/-- On `[0,1]`, the unsigned arctangent Taylor terms decrease. -/
theorem antitone_atanMagnitude {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (atanMagnitude x) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [atanMagnitude]
  refine div_le_div₀ (pow_nonneg hx0 _) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast (show 2 * n + 1 ≤ 2 * (n + 1) + 1 by omega)

/-- Casting the executable sine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_sinPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.sinPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          (Nat.factorial (2 * k + 1) : ℝ) := by
  simp only [sinPartial, signedTerm, factorialQ, Rat.cast_sum, neg_one_pow_eq_ite, Nat.even_iff,
    ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable cosine partial sum to `ℝ` gives the corresponding
Mathlib finite Taylor sum. -/
theorem coe_cosPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.cosPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) /
          (Nat.factorial (2 * k) : ℝ) := by
  simp only [cosPartial, signedTerm, factorialQ, Rat.cast_sum, neg_one_pow_eq_ite, Nat.even_iff,
    ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- Casting the executable arctangent partial sum to `ℝ` gives the
corresponding Mathlib finite Taylor sum. -/
theorem coe_atanPartial (x : ℚ) (terms : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x terms : ℚ) : ℝ) =
      ∑ k ∈ Finset.range terms,
        (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          ((2 * k + 1 : ℕ) : ℝ) := by
  simp only [atanPartial, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Rat.cast_sum,
    neg_one_pow_eq_ite, Nat.even_iff, ite_mul, one_mul, neg_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : k % 2 = 0 <;> simp [h, neg_div]

/-- The 20-term sine partial sum is a lower bound and the 19-term partial sum
is an upper bound for every rational argument in `[0,1]`. -/
theorem sine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.sinPartial x 20 : ℚ) : ℝ) ≤ Real.sin (x : ℝ) ∧
      Real.sin (x : ℝ) ≤ ((GerverSofa.ExactReplay.sinPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (sinMagnitude (x : ℝ)) :=
    antitone_sinMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_sin (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * sinMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.sin (x : ℝ))) := by
    simpa only [sinMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_sinPartial]
    simpa only [sinMagnitude, mul_div_assoc, h19] using hupper

/-- The 20-term cosine partial sum is a lower bound and the 19-term partial
sum is an upper bound for every rational argument in `[0,1]`. -/
theorem cosine_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x ≤ 1) :
    ((GerverSofa.ExactReplay.cosPartial x 20 : ℚ) : ℝ) ≤ Real.cos (x : ℝ) ∧
      Real.cos (x : ℝ) ≤ ((GerverSofa.ExactReplay.cosPartial x 19 : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hanti : Antitone (cosMagnitude (x : ℝ)) :=
    antitone_cosMagnitude hx0r hx1r
  have htendRaw := (Real.hasSum_cos (x : ℝ)).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * cosMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.cos (x : ℝ))) := by
    simpa only [cosMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 10
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 9
  have h20 : (2 * 10 : ℕ) = 20 := by norm_num
  have h19 : (2 * 9 + 1 : ℕ) = 19 := by norm_num
  constructor
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h20] using hlower
  · rw [coe_cosPartial]
    simpa only [cosMagnitude, mul_div_assoc, h19] using hupper

/-- Even/odd arctangent partial sums provide certified lower/upper bounds. -/
theorem arctan_between_partials {x : ℚ}
    (hx0 : (0 : ℚ) ≤ x) (hx1 : x < 1) (k : ℕ) :
    ((GerverSofa.ExactReplay.atanPartial x (2 * k + 2) : ℚ) : ℝ) ≤ Real.arctan (x : ℝ) ∧
      Real.arctan (x : ℝ) ≤ ((GerverSofa.ExactReplay.atanPartial x (2 * k + 1) : ℚ) : ℝ) := by
  have hx0r : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1r : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hx1le : (x : ℝ) ≤ 1 := hx1r.le
  have habs : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0r]
    exact hx1r
  have hanti : Antitone (atanMagnitude (x : ℝ)) :=
    antitone_atanMagnitude hx0r hx1le
  have htendRaw := (Real.hasSum_arctan habs).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * atanMagnitude (x : ℝ) i)
        Filter.atTop (nhds (Real.arctan (x : ℝ))) := by
    simpa only [atanMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti (k + 1)
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti k
  constructor
  · rw [coe_atanPartial]
    have hidx : 2 * (k + 1) = 2 * k + 2 := by omega
    simpa only [atanMagnitude, mul_div_assoc, hidx] using hlower
  · rw [coe_atanPartial]
    simpa only [atanMagnitude, mul_div_assoc] using hupper

end GerverSofa.ExactReplay

end

end

end

section

/-!
# Coordinate equivalences for the certified systems

The executable interval layer works with `Fin n → ℝ`, while the manuscript
layer uses named parameter records.  These equivalences are the explicit,
kernel-checked bridge between the two representations.
-/

@[expose] public section

noncomputable section

namespace GerverSofa

namespace Reduced

/-- Named reduced parameters as a four-vector in manuscript order. -/
def coordEquiv : Params ≃ Vec 4 where
  toFun p := ![p.a, p.b, p.phi, p.theta]
  invFun x :=
    { a := x 0
      b := x 1
      phi := x 2
      theta := x 3 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Reduced system expressed in finite-vector coordinates. -/
def vectorSystem (x : Vec 4) : Vec 4 :=
  system (coordEquiv.symm x)

/-- The reduced parameter box expressed in finite-vector coordinates. -/
def vectorBox : Set (Vec 4) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 4) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named reduced
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique_iff y hy := by
    constructor
    · intro hEq
      have hyVec : coordEquiv y ∈ vectorBox := by
        simpa [vectorBox] using hy
      have hzero : vectorSystem (coordEquiv y) = 0 := by
        simpa [Equations, vectorSystem] using hEq
      have h := c.unique (coordEquiv y) hyVec hzero
      apply coordEquiv.injective
      simpa using h
    · rintro rfl
      simpa [Equations, vectorSystem] using c.satisfies

end Reduced

namespace Romik

/-- Named Romik parameters as a 22-vector in verifier order. -/
def coordEquiv : Params ≃ Vec 22 where
  toFun p := ![
    p.k11, p.k12, p.k21, p.k22, p.k31, p.k32, p.k41, p.k42, p.k51, p.k52,
    p.a1, p.a2, p.b1, p.b2, p.c1, p.c2, p.d1, p.d2, p.e1, p.e2,
    p.phi, p.theta
  ]
  invFun x :=
    { k11 := x 0
      k12 := x 1
      k21 := x 2
      k22 := x 3
      k31 := x 4
      k32 := x 5
      k41 := x 6
      k42 := x 7
      k51 := x 8
      k52 := x 9
      a1 := x 10
      a2 := x 11
      b1 := x 12
      b2 := x 13
      c1 := x 14
      c2 := x 15
      d1 := x 16
      d2 := x 17
      e1 := x 18
      e2 := x 19
      phi := x 20
      theta := x 21 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Direct Romik system expressed in finite-vector coordinates. -/
def vectorSystem (x : Vec 22) : Vec 22 :=
  system (coordEquiv.symm x)

/-- The direct Romik box expressed in finite-vector coordinates. -/
def vectorBox : Set (Vec 22) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 22) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named Romik
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique_iff y hy := by
    constructor
    · intro hEq
      have hyVec : coordEquiv y ∈ vectorBox := by
        simpa [vectorBox] using hy
      have hzero : vectorSystem (coordEquiv y) = 0 := by
        simpa [Equations, vectorSystem] using hEq
      have h := c.unique (coordEquiv y) hyVec hzero
      apply coordEquiv.injective
      simpa using h
    · rintro rfl
      simpa [Equations, vectorSystem] using c.satisfies

end Romik

end GerverSofa

end

end

end

section

/-!
# Endpoint symmetry derived from the direct 22-dimensional system

The manuscript obtains the terminal condition `x₂(π/2)=0` from the reflection
symmetry of the five phases.  This file proves the required consequence
without introducing a symmetry assumption and without using numerical
approximations.

FIX12 keeps the BATCH11 mathematics and public theorem statements unchanged,
but factors the formula-level algebra into small coordinate identities.  This
avoids asking `ring` to normalize the fully unfolded five-phase expressions in
one large proof term.
-/

/-! ## Exact parameter consequences of equations 27--34 -/

@[expose] public section

noncomputable section

namespace GerverSofa.Romik

/-- Equation 27. -/
theorem e1_eq_a1_of_equations {p : Params} (heq : Equations p) :
    p.e1 = p.a1 := by
  have h0 := congrFun heq (0 : Fin 22)
  simp [system] at h0
  linarith

/-- Equation 28. -/
theorem e2_eq_neg_a2_of_equations {p : Params} (heq : Equations p) :
    p.e2 = -p.a2 := by
  have h1 := congrFun heq (1 : Fin 22)
  simp [system] at h1
  linarith

/-- Equation 29. -/
theorem d1_eq_quarterPi_sub_b1_of_equations
    {p : Params} (heq : Equations p) :
    p.d1 = Real.pi / 4 - p.b1 := by
  have h2 := congrFun heq (2 : Fin 22)
  simp [system] at h2
  linarith

/-- Equation 30. -/
theorem d2_eq_b2_add_quarterPi_correction_of_equations
    {p : Params} (heq : Equations p) :
    p.d2 = p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4) := by
  have h3 := congrFun heq (3 : Fin 22)
  simp [system] at h3
  linarith

/-- Equation 31. -/
theorem c2_eq_c1_sub_halfPi_of_equations
    {p : Params} (heq : Equations p) :
    p.c2 = p.c1 - Real.pi / 2 := by
  have h4 := congrFun heq (4 : Fin 22)
  simp [system] at h4
  linarith

/-- Equation 33. -/
theorem k12_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k12 = (1 / 4 : ℝ) := by
  have h6 := congrFun heq (6 : Fin 22)
  simp [system] at h6
  linarith

/-- Equation 34. -/
theorem a2_eq_neg_quarter_of_equations {p : Params} (heq : Equations p) :
    p.a2 = -(1 / 4 : ℝ) := by
  have h7 := congrFun heq (7 : Fin 22)
  simp [system] at h7
  linarith

/-- Equations 28 and 34. -/
theorem e2_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.e2 = (1 / 4 : ℝ) := by
  rw [e2_eq_neg_a2_of_equations heq, a2_eq_neg_quarter_of_equations heq]
  norm_num

/-! ## Small definitional coordinate identities

These are deliberately `rfl`: they expose only the second coordinate of one
phase at a time.  Downstream algebra therefore operates on compact scalar
expressions rather than on the fully unfolded `Point`/`rot`/`addK` terms. -/

private theorem path1_snd_formula (p : Params) (t : ℝ) :
    (path1 p t).2 =
      Real.sin t *
          (p.a1 * Real.cos t + p.a2 * Real.sin t - 1) +
        Real.cos t *
          (-p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2) +
        p.k12 := by
  rfl

private theorem path2_snd_formula (p : Params) (t : ℝ) :
    (path2 p t).2 =
      Real.sin t *
          (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2) +
        Real.cos t *
          ((1 / 2 : ℝ) * t - p.b1 - 1) +
        p.k22 := by
  rfl

private theorem path3_snd_formula (p : Params) (t : ℝ) :
    (path3 p t).2 =
      Real.sin t * (p.c1 - t) +
        Real.cos t * (p.c2 + t) +
        p.k32 := by
  rfl

private theorem path4_snd_formula (p : Params) (t : ℝ) :
    (path4 p t).2 =
      Real.sin t *
          (-(1 / 2 : ℝ) * t + p.d1 - 1) +
        Real.cos t *
          (-(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2) +
        p.k42 := by
  rfl

private theorem path5_snd_formula (p : Params) (t : ℝ) :
    (path5 p t).2 =
      Real.sin t *
          (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2) +
        Real.cos t *
          (-p.e2 * Real.cos t + p.e1 * Real.sin t - 1) +
        p.k52 := by
  rfl

/-! ## Formula-level reflection identities -/

/-- The vertical phase-5 formula at reflected time differs from phase 1 only
by its vertical translation constant. -/
theorem phase15_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path5 p (Real.pi / 2 - t)).2 - p.k52 =
      (path1 p t).2 - p.k12 := by
  rw [path5_snd_formula, path1_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [e1_eq_a1_of_equations heq, e2_eq_neg_a2_of_equations heq]
  ring

/-- The vertical phase-4 formula at reflected time differs from phase 2 only
by its vertical translation constant. -/
theorem phase24_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path4 p (Real.pi / 2 - t)).2 - p.k42 =
      (path2 p t).2 - p.k22 := by
  rw [path4_snd_formula, path2_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [d1_eq_quarterPi_sub_b1_of_equations heq,
    d2_eq_b2_add_quarterPi_correction_of_equations heq]
  have hlinear :
      -(1 / 2 : ℝ) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) - 1 =
        (1 / 2 : ℝ) * t - p.b1 - 1 := by
    ring
  have hquadratic :
      -(1 / 4 : ℝ) * (Real.pi / 2 - t) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) * (Real.pi / 2 - t) +
          (p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4)) =
        -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 := by
    ring
  rw [hlinear, hquadratic]
  ring

/-- The middle phase has exact vertical reflection symmetry. -/
theorem phase3_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path3 p (Real.pi / 2 - t)).2 = (path3 p t).2 := by
  rw [path3_snd_formula, path3_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  have hleft :
      p.c1 - (Real.pi / 2 - t) = p.c2 + t := by
    rw [hc2]
    ring
  have hright :
      p.c2 + (Real.pi / 2 - t) = p.c1 - t := by
    rw [hc2]
    ring
  rw [hleft, hright]
  ring

/-! ## Translation constants forced by matching -/

/-- Matching at `θ` and `π/2-θ`, together with middle-phase reflection,
forces the phase-2 and phase-4 vertical translations to coincide. -/
theorem k42_eq_k22_of_equations {p : Params} (heq : Equations p) :
    p.k42 = p.k22 := by
  have h23 : (path2 p p.theta).2 = (path3 p p.theta).2 :=
    congrArg Prod.snd (match_path23_of_equations heq)
  have h34 : (path3 p (Real.pi / 2 - p.theta)).2 =
      (path4 p (Real.pi / 2 - p.theta)).2 :=
    congrArg Prod.snd (match_path34_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.theta
  have h33 := phase3_vertical_reflection_of_equations heq p.theta
  rw [← h34, h33, ← h23] at h24
  linarith

/-- Matching at `φ` and `π/2-φ` then forces the phase-1 and phase-5 vertical
translations to coincide. -/
theorem k52_eq_k12_of_equations {p : Params} (heq : Equations p) :
    p.k52 = p.k12 := by
  have h12 : (path1 p p.phi).2 = (path2 p p.phi).2 :=
    congrArg Prod.snd (match_path12_of_equations heq)
  have h45 : (path4 p (Real.pi / 2 - p.phi)).2 =
      (path5 p (Real.pi / 2 - p.phi)).2 :=
    congrArg Prod.snd (match_path45_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.phi
  have hk := k42_eq_k22_of_equations heq
  rw [hk] at h24
  have hy42 :
      (path4 p (Real.pi / 2 - p.phi)).2 = (path2 p p.phi).2 := by
    linarith
  have hy51 :
      (path5 p (Real.pi / 2 - p.phi)).2 = (path1 p p.phi).2 := by
    calc
      (path5 p (Real.pi / 2 - p.phi)).2 =
          (path4 p (Real.pi / 2 - p.phi)).2 := by
            exact h45.symm
      _ = (path2 p p.phi).2 := hy42
      _ = (path1 p p.phi).2 := h12.symm
  have h15 := phase15_vertical_reflection_of_equations heq p.phi
  rw [hy51] at h15
  linarith

/-- Equations 27--41 force the previously dependent coefficient `k₅₂=1/4`.
It is not an independent hypothesis of the final certificate. -/
theorem k52_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k52 = (1 / 4 : ℝ) := by
  rw [k52_eq_k12_of_equations heq, k12_eq_quarter_of_equations heq]

/-! ## Terminal condition -/

/-- The explicit fifth phase ends at vertical coordinate zero. -/
theorem path5_end_y_zero_of_equations {p : Params} (heq : Equations p) :
    (path5 p (Real.pi / 2)).2 = 0 := by
  rw [path5_snd_formula]
  simp [e2_eq_quarter_of_equations heq,
    k52_eq_quarter_of_equations heq]; norm_num

/-- The certified direct-system box places `π/2` strictly after the fourth
switch, so the literal nested-`if` path uses phase 5 at the endpoint. -/
theorem path_halfPi_eq_path5_of_mem_box {p : Params} (hp : p ∈ box) :
    path p (Real.pi / 2) = path5 p (Real.pi / 2) := by
  have hphi : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have hthetaPos : 0 < p.theta := lt_of_lt_of_le hphi hord.phi_le_theta
  have hthetaLt : p.theta < Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiLt : p.phi < Real.pi / 2 :=
    lt_of_le_of_lt hord.phi_le_theta hthetaLt
  have hetaLt : Real.pi / 2 - p.theta < Real.pi / 2 := by
    linarith
  have htauLt : Real.pi / 2 - p.phi < Real.pi / 2 := by
    linarith
  simp [path, not_le.mpr hphiLt, not_le.mpr hthetaLt,
    not_le.mpr hetaLt, not_le.mpr htauLt]

/-- The terminal vertical normalisation is a theorem of the concrete box and
22 equations.  No reflection hypothesis and no certificate field remain. -/
theorem path_end_y_zero_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    (path p (Real.pi / 2)).2 = 0 := by
  rw [path_halfPi_eq_path5_of_mem_box hp]
  exact path5_end_y_zero_of_equations heq

end GerverSofa.Romik

end

end

end

section

/-!
# Identification with Romik's hallway-intersection reconstruction

This is the set-theoretic part of Proposition `prop:gerver`.  It uses only the
literal definitions and the two endpoint normalisations; the eighteen-piece
boundary statement remains a separate field of `FullArticleCertificate`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.Romik

/-- Romik's fixed-frame reconstruction: initial arm, every supporting hallway,
and the final transported vertical arm. -/
def reconstructedSet (p : Params) : Set Point :=
  {q | q ∈ horizontalArm ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) ∧
    q ∈ (frame p 1).act '' verticalArm}

/-- Convert a physical angle in `[0,π/2]` to normalized time. -/
def normalizedTime (t : ℝ) : ℝ := t / (Real.pi / 2)

@[simp] theorem angle_normalizedTime (t : ℝ) :
    angle (normalizedTime t) = t := by
  have hT : Real.pi / 2 ≠ 0 := by positivity
  simp [angle, normalizedTime, hT]

theorem normalizedTime_mem_unit {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    normalizedTime t ∈ Set.Icc (0 : ℝ) 1 := by
  have hT : 0 < Real.pi / 2 := by positivity
  constructor
  · exact div_nonneg ht.1 (le_of_lt hT)
  · exact (div_le_iff₀ hT).2 (by simpa using ht.2)

/-- Every point of the cap-minus-niche set lies in Romik's hallway
intersection reconstruction. -/
theorem sofa_subset_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p ⊆ reconstructedSet p := by
  intro q hq
  refine ⟨?_, ?_, ?_⟩
  · have hi : (frame p 0).inv.act q ∈ horizontalArm :=
      initial_arm_of_path_zero p hzero ⟨q, hq, rfl⟩
    simpa [frame, angle, hzero, SE2.inv, SE2.act] using hi
  · intro s hs
    exact sofa_subset_hallwayAt p hzero hend s hs hq
  · have hf : (frame p 1).inv.act q ∈ verticalArm :=
      final_arm_of_path_end_y_zero p hend ⟨q, hq, rfl⟩
    exact ⟨(frame p 1).inv.act q, hf, (frame p 1).act_inv_act q⟩

/-- Membership in every physical supporting hallway gives all outer support
inequalities in the cap definition. -/
theorem mem_K0_of_mem_all_hallways
    (p : Params) {q : Point}
    (hbase : 0 ≤ q.2)
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∈ K0 p := by
  refine ⟨hbase, ?_⟩
  intro t ht
  let s := normalizedTime t
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit ht
  have hhall := hall s hs
  have hwall :
      (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) ≤ 1 ∧
       dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    rw [mem_hallwayAt_iff_wall_coordinates] at hhall
    simpa [s] using hhall
  constructor
  · change dot q (u t) ≤ dot (path p t) (u t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.1]
  · change dot q (v t) ≤ dot (path p t) (v t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.2]

/-- Membership in every physical hallway excludes every open interior-time
inner quadrant. -/
theorem not_mem_innerUnion_of_mem_all_hallways
    (p : Params) {q : Point}
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∉ innerUnion p := by
  rintro ⟨t, ht, hinner⟩
  let s := normalizedTime t
  have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit htIcc
  have hhall := hall s hs
  rw [mem_hallwayAt_iff_wall_coordinates] at hhall
  have hwall :
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    simpa [s] using hhall.2
  exact hwall (by simpa [innerQuadrantAt] using hinner)

/-- Conversely, Romik's hallway intersection lies in the concrete
cap-minus-niche set. -/
theorem reconstructedSet_subset_sofa (p : Params) :
    reconstructedSet p ⊆ sofa p := by
  intro q hq
  have hbase : 0 ≤ q.2 := hq.1.2.1
  have hK : q ∈ K0 p := mem_K0_of_mem_all_hallways p hbase hq.2.1
  have hU : q ∉ innerUnion p :=
    not_mem_innerUnion_of_mem_all_hallways p hq.2.1
  refine ⟨hK, ?_⟩
  rintro ⟨_hfan, hinner⟩
  exact hU hinner

/-- Set-theoretic identification `G = Sₓ`, conditional only on the endpoint
normalisations already isolated by the main certificate. -/
theorem sofa_eq_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p = reconstructedSet p := by
  apply Set.Subset.antisymm
  · exact sofa_subset_reconstructedSet p hzero hend
  · exact reconstructedSet_subset_sofa p

end GerverSofa.Romik

end

end

end

section

/-!
# Named consequences of the frozen kernel-only certificate

These handles intentionally reason about the proof-carrying rational data, not
about re-running the expensive Krawczyk/grid search inside kernel reduction.
The latter remains available under `ExactReplay.executable*` for independent
diagnostic comparison.
-/

@[expose] public section

namespace GerverSofa.CertificateManifest
theorem machin_inside_declared :
    RatInterval.strictInsideB machinPi declaredPi = true := by
  simpa [piCheck] using piCheck_eq_true

end GerverSofa.CertificateManifest

end

end

section

/-!
# Semantic interfaces for the executable interval certificate

These definitions state, without hiding any mathematical assumption, the
bridges that turn the frozen rational replay into facts about `Real.sin`,
`Real.cos`, the two real systems, and their Jacobians.  Concrete proof terms
for these interfaces are the remaining analytic part of the end-to-end
certificate; no axiom is declared here.
-/

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

/-- A rational interval list encloses a finite real vector coordinatewise. -/
def EnclosesVec {n : Nat} (box : List RatInterval) (x : Vec n) : Prop :=
  box.length = n ∧
    ∀ i : Fin n, Contains (box.getD i.1 (point 0)) (x i)

/-- A one-dimensional real derivative certificate in the classical
difference-quotient form.  This is the exact real specialization of the
right-hand side of Mathlib's `hasDerivAt_iff_tendsto_slope_zero`: it states
that `(f (x+t)-f x)/t` tends to `f'` as `t → 0`, `t ≠ 0`.

Unlike storing raw `HasDerivAt`/`DifferentiableAt`, this proposition contains
no hidden `AddCommGroup`/`Module` instance path for the codomain `ℝ`; this
removes the instance diamond exposed by Lean 4.33 while retaining the full
mathematical meaning of an actual derivative. -/
def RealDerivativeAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => t⁻¹ * (f (x + t) - f x))
    (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
    (nhds f')

/-- Exact analytic correctness required from the executable trigonometric
layer.  The domain is the physical range used by the Gerver certificate. -/
structure TranscendentalSoundness : Prop where
  pi_mem : Contains ExactReplay.declaredPiInterval Real.pi
  sine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.sineInterval z) (Real.sin x)
  cosine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.cosineInterval z) (Real.cos x)

end GerverSofa

end

end

end

section

/-!
# Soundness of the exact transcendental interval evaluator

This file proves the analytic trust bridge omitted by the executable replay:

* the alternating rational arctangent sums enclose the two Machin terms;
* the computed Machin interval encloses `Real.pi` and lies in the declared
  interval;
* fixed-decimal rounding is outward;
* the small-argument Taylor intervals enclose `Real.sin` and `Real.cos`;
* complementary-angle reduction is sound on `[0, π/2]`;
* externally over-wide intervals fail closed to `[-1,1]` rather than silently
  violating the Taylor precondition.

No project axiom and no floating-point literal occurs in this file.
-/

/-! ## Partial-sum interval consequences -/

@[expose] public section

noncomputable section

namespace GerverSofa.ExactReplay

open RatInterval

/-- The executable sine Taylor hull contains the exact real sine value on
`[0,1]`. -/
theorem sinBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (sinBound x) (Real.sin (x : ℝ)) := by
  have h := sine_between_partials hx0 hx1
  constructor
  · have hmin : min (sinPartial x 19) (sinPartial x 20) ≤ sinPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : sinPartial x 19 ≤ max (sinPartial x 19) (sinPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- The executable cosine Taylor hull contains the exact real cosine value on
`[0,1]`. -/
theorem cosBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (cosBound x) (Real.cos (x : ℝ)) := by
  have h := cosine_between_partials hx0 hx1
  constructor
  · have hmin : min (cosPartial x 19) (cosPartial x 20) ≤ cosPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : cosPartial x 19 ≤ max (cosPartial x 19) (cosPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- Consecutive odd/even arctangent sums form a semantic interval. -/
theorem atanBound_contains {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Contains (atanBound x (2 * k + 1) (2 * k + 2))
      (Real.arctan (x : ℝ)) := by
  have h := arctan_between_partials hx0 hx1 k
  constructor
  · have hmin :
        min (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) ≤
          atanPartial x (2 * k + 2) := min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax :
        atanPartial x (2 * k + 1) ≤
          max (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-! ## Machin identity and the declared interval for π -/

/-- The interval computed from the two exact arctangent Taylor certificates
contains the true value of `π`. -/
theorem machinPi_contains_pi : Contains machinPi Real.pi := by
  have h5 : Contains (atanBound (1 / 5) 43 44)
      (Real.arctan ((1 / 5 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 5 : ℚ)) (by norm_num) (by norm_num) 21)
  have h239 : Contains (atanBound (1 / 239) 13 14)
      (Real.arctan ((1 / 239 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 239 : ℚ)) (by norm_num) (by norm_num) 6)
  have h16 := RatInterval.contains_scale (a := (16 : ℚ)) h5
  have h4 := RatInterval.contains_scale (a := (4 : ℚ)) h239
  have hsub := RatInterval.contains_sub h16 h4
  have hMachin :
      (16 : ℝ) * Real.arctan (1 / 5) -
          4 * Real.arctan (1 / 239) = Real.pi := by
    nlinarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  have hsub' : Contains machinPi
      ((16 : ℝ) * Real.arctan (1 / 5) -
        4 * Real.arctan (1 / 239)) := by
    simpa [machinPi, scale] using hsub
  exact hMachin ▸ hsub'

/-- The executable and proof-carrying manifests contain byte-for-byte equal
Machin intervals.  This is a finite rational normalization, not a numerical
assumption. -/
private theorem ratInterval_eq_of_endpoints {a b : RatInterval}
    (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact lower endpoint agreement between the executable Machin evaluation
and the frozen manifest.  This is a small bounded kernel computation (two
arctangent sums), deliberately separated from the old monolithic replay. -/
private theorem machinPi_lo_eq_manifest :
    machinPi.lo = CertificateManifest.machinPi.lo := by
    decide +kernel

/-- Exact upper endpoint agreement between the executable Machin evaluation
and the frozen manifest. -/
private theorem machinPi_hi_eq_manifest :
    machinPi.hi = CertificateManifest.machinPi.hi := by
    decide +kernel

theorem machinPi_eq_manifest :
    machinPi = CertificateManifest.machinPi :=
  ratInterval_eq_of_endpoints machinPi_lo_eq_manifest machinPi_hi_eq_manifest

/-- The executable declared interval agrees with the frozen manifest. -/
theorem piI_eq_manifest : piI = CertificateManifest.declaredPi := by
  apply ratInterval_eq_of_endpoints
  · decide +kernel
  · decide +kernel

/-- The exact interval used by every transcendental call encloses `Real.pi`. -/
theorem piI_contains_pi : Contains piI Real.pi := by
  have hm : Contains CertificateManifest.machinPi Real.pi := by
    simpa [machinPi_eq_manifest] using machinPi_contains_pi
  have hd : Contains CertificateManifest.declaredPi Real.pi :=
    RatInterval.contains_of_strictInsideB
      CertificateManifest.machin_inside_declared hm
  simpa [piI_eq_manifest] using hd

/-! ## Outward decimal rounding -/

/-- Fixed-decimal floor rounding never exceeds the input rational. -/
theorem floorDecimal_le (x : ℚ) (digits : ℕ := 60) :
    floorDecimal x digits ≤ x := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (div_le_iff₀ hs).2
  have hf : (((⌊x * s⌋ : ℤ) : ℚ)) ≤ x * s := Int.floor_le _
  simpa [floorDecimal, s] using hf

/-- Fixed-decimal ceiling rounding never lies below the input rational. -/
theorem le_ceilDecimal (x : ℚ) (digits : ℕ := 60) :
    x ≤ ceilDecimal x digits := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (le_div_iff₀ hs).2
  have hc : x * s ≤ (((⌈x * s⌉ : ℤ) : ℚ)) := Int.le_ceil _
  simpa [ceilDecimal, s] using hc

/-- The exact 60-decimal conversion is outward in real semantics. -/
theorem outwardDecimal_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) : Contains (outwardDecimal z) x := by
  constructor
  · exact le_trans (by exact_mod_cast floorDecimal_le z.lo (digits := 60)) hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_ceilDecimal z.hi (digits := 60))

/-! ## Small-argument sine and cosine -/

/-- The small sine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem sinSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (sinSmall z) (Real.sin x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := sinBound_contains hz0 hlo1
  have hhiBound := sinBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hloMem : -(Real.pi / 2) ≤ (z.lo : ℝ) := by
    have : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
    nlinarith [Real.pi_pos]
  have hhiMem : (z.hi : ℝ) ≤ Real.pi / 2 := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hmonoLo : Real.sin (z.lo : ℝ) ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hloMem (le_trans hx.2 hhiMem) hx.1
  have hxLower : -(Real.pi / 2) ≤ x := by
    have hneg : -(Real.pi / 2) ≤ (0 : ℝ) := by
      nlinarith [Real.pi_pos]
    exact le_trans hneg (le_trans (by exact_mod_cast hz0) hx.1)
  have hmonoHi : Real.sin x ≤ Real.sin (z.hi : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hxLower hhiMem hx.2
  apply outwardDecimal_contains
  constructor
  · exact le_trans hloBound.1 hmonoLo
  · exact le_trans hmonoHi hhiBound.2

/-- The small cosine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem cosSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (cosSmall z) (Real.cos x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := cosBound_contains hz0 hlo1
  have hhiBound := cosBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlo0 : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
  have hhiPi : (z.hi : ℝ) ≤ Real.pi := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hx0 : (0 : ℝ) ≤ x := le_trans hlo0 hx.1
  have hxPi : x ≤ Real.pi := le_trans hx.2 hhiPi
  have hcosLower : Real.cos (z.hi : ℝ) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx0 hhiPi hx.2
  have hcosUpper : Real.cos x ≤ Real.cos (z.lo : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hlo0 hxPi hx.1
  apply outwardDecimal_contains
  constructor
  · exact le_trans hhiBound.1 hcosLower
  · exact le_trans hcosUpper hloBound.2

/-! ## Range reduction and fail-closed totality -/

/-- Physical clamping preserves every enclosed angle in `[0,π/2]`. -/
theorem physicalClamp_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (physicalClamp z) x := by
  have hpi := piI_contains_pi
  constructor
  · simpa [physicalClamp] using (max_le hx0 hz.1)
  · have hupper : x ≤ ((piI.hi / 2 : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hxhi : x ≤ (piI.hi : ℝ) / 2 := by
        linarith [hxpi, hhi]
      have hcast : (((piI.hi / 2 : ℚ) : ℝ)) = (piI.hi : ℝ) / 2 := by
        norm_num
      rw [hcast]
      exact hxhi
    simpa [physicalClamp] using (le_min hupper hz.2)

/-- Complementary-angle range reduction encloses `π/2-x`. -/
theorem complementInterval_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hxpi : x ≤ Real.pi / 2) :
    Contains (complementInterval z) (Real.pi / 2 - x) := by
  have hpi := piI_contains_pi
  constructor
  · have hzero : 0 ≤ Real.pi / 2 - x := by linarith
    have hdiff : ((piI.lo / 2 - z.hi : ℚ) : ℝ) ≤ Real.pi / 2 - x := by
      have hlo : (piI.lo : ℝ) ≤ Real.pi := hpi.1
      have hdiff' : (piI.lo : ℝ) / 2 - (z.hi : ℝ) ≤ Real.pi / 2 - x := by
        linarith [hlo, hz.2]
      have hcast : (((piI.lo / 2 - z.hi : ℚ) : ℝ)) =
          (piI.lo : ℝ) / 2 - (z.hi : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using (max_le hzero hdiff)
  · have hdiff : Real.pi / 2 - x ≤ ((piI.hi / 2 - z.lo : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hdiff' : Real.pi / 2 - x ≤ (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        linarith [hhi, hz.1]
      have hcast : (((piI.hi / 2 - z.lo : ℚ) : ℝ)) =
          (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using hdiff

/-- Universal fallback for sine. -/
theorem universal_contains_sin (x : ℝ) :
    Contains universalTrigInterval (Real.sin x) := by
  simpa [Contains, universalTrigInterval] using Real.sin_mem_Icc x

/-- Universal fallback for cosine. -/
theorem universal_contains_cos (x : ℝ) :
    Contains universalTrigInterval (Real.cos x) := by
  simpa [Contains, universalTrigInterval] using Real.cos_mem_Icc x

/-- Full soundness of the executable sine interval on the physical angular
range. -/
theorem sinI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (sinI z) (Real.sin x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [sinI]
  split_ifs with hsmall hcomp
  · exact sinSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hcy := cosSmall_contains hy hy0 hcomp
    simpa [Real.cos_pi_div_two_sub] using hcy
  · exact universal_contains_sin x

/-- Full soundness of the executable cosine interval on the physical angular
range. -/
theorem cosI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (cosI z) (Real.cos x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [cosI]
  split_ifs with hsmall hcomp
  · exact cosSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hsy := sinSmall_contains hy hy0 hcomp
    simpa [Real.sin_pi_div_two_sub] using hsy
  · exact universal_contains_cos x

end GerverSofa.ExactReplay

namespace GerverSofa

open RatInterval

end GerverSofa

end

end

end

section

/-!
# Structural soundness of first-order interval automatic differentiation

The executable `ExactReplay.D` object stores a value interval and one interval
for every first partial derivative.  This file supplies the reusable semantic
induction for all constructors actually used by the 4D and 22D certificates.
The concrete systems are handled in a separate module by instantiating these
constructor theorems.
-/

/-! ## Smooth scalar models -/

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

/-- A scalar function together with its coordinate gradient and a proof that
those coordinates are the actual partial derivatives.  The derivative witness
is stored as `RealDerivativeAt`, a first-principles real difference-quotient
limit.  Constructor proofs temporarily move through Mathlib's `HasDerivAt`
API and immediately return to this instance-stable semantic proposition. -/
structure ScalarModel (n : Nat) where
  /-- The real scalar function represented by the model. -/
  value : Vec n → ℝ
  /-- The coordinate gradient of the scalar function. -/
  gradient : Vec n → Vec n
  hasDeriv_update : ∀ x j,
    RealDerivativeAt (fun t : ℝ => value (Function.update x j t))
      (gradient x j) (x j)

namespace ScalarModel

/-- Constant scalar model. -/
def const (n : Nat) (c : ℝ) : ScalarModel n where
  value := fun _ => c
  gradient := fun _ _ => 0
  hasDeriv_update := by
    intro x j
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hasDerivAt_const (x j) c).tendsto_slope_zero

/-- Coordinate projection. -/
def var (n : Nat) (k : Fin n) : ScalarModel n where
  value := fun x => x k
  gradient := fun _ j => if j = k then 1 else 0
  hasDeriv_update := by
    intro x j
    by_cases h : j = k
    · subst k
      have hid : RealDerivativeAt (fun t : ℝ => t) 1 (x j) := by
        simpa only [RealDerivativeAt, smul_eq_mul] using
          (hasDerivAt_id' (x j)).tendsto_slope_zero
      convert hid using 1 <;> simp
    · have hkj : k ≠ j := Ne.symm h
      simpa only [RealDerivativeAt, Function.update_of_ne hkj, ite_eq_right h,
        smul_eq_mul] using (hasDerivAt_const (x j) (x k)).tendsto_slope_zero

/-- Pointwise addition. -/
def add {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x + g.value x
  gradient := fun x j => f.gradient x j + g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hfh.fun_add hgh).tendsto_slope_zero

/-- Pointwise negation. -/
def neg {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => -f.value x
  gradient := fun x j => -f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      hfh.fun_neg.tendsto_slope_zero

/-- Pointwise subtraction. -/
def sub {n : Nat} (f g : ScalarModel n) : ScalarModel n :=
  add f (neg g)

/-- Pointwise multiplication. -/
def mul {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x * g.value x
  gradient := fun x j =>
    f.gradient x j * g.value x + f.value x * g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      (hfh.fun_mul hgh).tendsto_slope_zero

/-- Rational scaling. -/
def scale {n : Nat} (a : ℚ) (f : ScalarModel n) : ScalarModel n where
  value := fun x => (a : ℝ) * f.value x
  gradient := fun x j => (a : ℝ) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hs := HasDerivAt.const_mul (a : ℝ) hfh
    simpa only [RealDerivativeAt, smul_eq_mul] using hs.tendsto_slope_zero

/-- Sine composition. -/
def sin {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.sin (f.value x)
  gradient := fun x j => Real.cos (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.sin.tendsto_slope_zero

/-- Cosine composition. -/
def cos {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.cos (f.value x)
  gradient := fun x j => -Real.sin (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.cos.tendsto_slope_zero

instance {n : Nat} : Add (ScalarModel n) := ⟨add⟩
instance {n : Nat} : Neg (ScalarModel n) := ⟨neg⟩
instance {n : Nat} : Sub (ScalarModel n) := ⟨sub⟩
instance {n : Nat} : Mul (ScalarModel n) := ⟨mul⟩
instance {n : Nat} : HMul ℚ (ScalarModel n) (ScalarModel n) := ⟨scale⟩

/-! The executable systems are written with notation, while constructor-level
    soundness lemmas produce the named operations above.  These tiny simp
    bridges make that definitional equality explicit without unfolding the
    proof-carrying structures themselves. -/
@[simp] theorem add_notation {n : Nat} (f g : ScalarModel n) :
    f + g = add f g := rfl

@[simp] theorem neg_notation {n : Nat} (f : ScalarModel n) :
    -f = neg f := rfl

@[simp] theorem sub_notation {n : Nat} (f g : ScalarModel n) :
    f - g = sub f g := rfl

@[simp] theorem mul_notation {n : Nat} (f g : ScalarModel n) :
    f * g = mul f g := rfl

@[simp] theorem scale_notation {n : Nat} (a : ℚ) (f : ScalarModel n) :
    a * f = scale a f := rfl

@[simp] theorem add_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (add f g).value x = f.value x + g.value x := rfl

@[simp] theorem neg_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (neg f).value x = -f.value x := rfl

@[simp] theorem sub_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (sub f g).value x = f.value x - g.value x := rfl

@[simp] theorem mul_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (mul f g).value x = f.value x * g.value x := rfl

@[simp] theorem scale_value {n : Nat} (a : ℚ) (f : ScalarModel n) (x : Vec n) :
    (scale a f).value x = (a : ℝ) * f.value x := rfl

@[simp] theorem sin_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (sin f).value x = Real.sin (f.value x) := rfl

@[simp] theorem cos_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (cos f).value x = Real.cos (f.value x) := rfl

end ScalarModel

namespace ExactReplay.D

/-! Matching notation bridges for the executable dual intervals. -/
@[simp] theorem add_notation (x y : ExactReplay.D) :
    x + y = addD x y := rfl

@[simp] theorem neg_notation (x : ExactReplay.D) :
    -x = negD x := rfl

@[simp] theorem sub_notation (x y : ExactReplay.D) :
    x - y = subD x y := rfl

@[simp] theorem mul_notation (x y : ExactReplay.D) :
    x * y = mulD x y := rfl

@[simp] theorem scale_notation (a : ℚ) (x : ExactReplay.D) :
    a * x = scaleD a x := rfl

end ExactReplay.D

/-! ## Semantic relation for the executable dual interval -/

/-- An executable dual interval encloses a smooth scalar model on a set. -/
structure DSoundOn {n : Nat} (X : Set (Vec n))
    (d : ExactReplay.D) (f : ScalarModel n) : Prop where
  value_sound : ∀ x ∈ X, Contains d.val (f.value x)
  derivative_length : d.der.length = n
  derivative_sound : ∀ x ∈ X, ∀ j : Fin n,
    Contains (d.der.getD j.1 ExactReplay.zeroI) (f.gradient x j)

/-! ## List access lemmas used by the AD constructors -/

private theorem getD_map_of_lt
    {α β : Type*} (f : α → β) (xs : List α)
    (i : Nat) (h : i < xs.length) (da : α) (db : β) :
    (xs.map f).getD i db = f (xs.getD i da) := by
  have hmap : i < (xs.map f).length := by simpa using h
  rw [List.getD_eq_getElem (xs.map f) db hmap]
  rw [List.getD_eq_getElem xs da h]
  simp

private theorem getD_zipWith_of_lt
    {α β γ : Type*} (f : α → β → γ)
    (xs : List α) (ys : List β) (i : Nat)
    (hx : i < xs.length) (hy : i < ys.length)
    (da : α) (db : β) (dc : γ) :
    (List.zipWith f xs ys).getD i dc =
      f (xs.getD i da) (ys.getD i db) := by
  have hz : i < (List.zipWith f xs ys).length := by
    simpa only [List.length_zipWith] using (lt_min hx hy)
  rw [List.getD_eq_getElem (List.zipWith f xs ys) dc hz]
  rw [List.getD_eq_getElem xs da hx]
  rw [List.getD_eq_getElem ys db hy]
  simp

/-! ## Constructor soundness -/

/-- Exact interval constant. -/
theorem DSoundOn.const {n : Nat} {X : Set (Vec n)}
    {z : RatInterval} {c : ℝ} (hc : Contains z c) :
    DSoundOn X (ExactReplay.D.const z n) (ScalarModel.const n c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hc
  · simp [ExactReplay.D.const]
  · intro x hx j
    simp [ExactReplay.D.const, ExactReplay.zeroI, ScalarModel.const,
      RatInterval.Contains, RatInterval.point]

/-- Rational point constant. -/
theorem DSoundOn.pointConst {n : Nat} {X : Set (Vec n)} (q : ℚ) :
    DSoundOn X (ExactReplay.D.pointConst q n)
      (ScalarModel.const n (q : ℝ)) := by
  apply DSoundOn.const
  exact (RatInterval.contains_point_iff q (q : ℝ)).2 rfl

/-- Coordinate variable read from an enclosing input interval. -/
theorem DSoundOn.varD {n : Nat} {X : Set (Vec n)}
    (input : RatInterval) (k : Fin n)
    (hinput : ∀ x ∈ X, Contains input (x k)) :
    DSoundOn X (ExactReplay.D.varD input k.1 n) (ScalarModel.var n k) := by
  refine ⟨hinput, ?_, ?_⟩
  · simp [ExactReplay.D.varD]
  · intro x hx j
    have hj : j.1 < (List.range n).length := by simp
    change Contains
      (((List.range n).map
        (fun m => RatInterval.point (if m = k.1 then 1 else 0))).getD
          j.1 ExactReplay.zeroI)
      (if j = k then 1 else 0)
    rw [getD_map_of_lt (fun m => RatInterval.point (if m = k.1 then 1 else 0))
      (List.range n) j.1 hj 0 ExactReplay.zeroI]
    have hjrange : (List.range n).getD j.1 0 = j.1 := by
      rw [List.getD_eq_getElem (List.range n) 0 hj]
      simp
    rw [hjrange]
    by_cases hjk : j = k
    · subst k
      simp [RatInterval.Contains, RatInterval.point]
    · have hval : j.1 ≠ k.1 := by
        intro hval
        exact hjk (Fin.ext hval)
      simp [hjk, hval, RatInterval.Contains, RatInterval.point]

/-- Addition constructor. -/
theorem DSoundOn.add {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.addD dx dy) (ScalarModel.add f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_add (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.addD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simp [hx.derivative_length]
    have hjy : j.1 < dy.der.length := by simp [hy.derivative_length]
    change Contains
      ((List.zipWith RatInterval.add dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j + g.gradient x j)
    rw [getD_zipWith_of_lt RatInterval.add dx.der dy.der j.1 hjx hjy
      ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (hx.derivative_sound x hX j) (hy.derivative_sound x hX j)

/-- Negation constructor. -/
theorem DSoundOn.neg {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.negD d) (ScalarModel.neg f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_neg (h.value_sound x hX)
  · simp [ExactReplay.D.negD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map RatInterval.neg).getD j.1 ExactReplay.zeroI)
      (-f.gradient x j)
    rw [getD_map_of_lt RatInterval.neg d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_neg (h.derivative_sound x hX j)

/-- Subtraction constructor. -/
theorem DSoundOn.sub {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.subD dx dy) (ScalarModel.sub f g) := by
  simpa [ExactReplay.D.subD, ScalarModel.sub] using hx.add hy.neg

/-- Multiplication constructor and product rule. -/
theorem DSoundOn.mul {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.mulD dx dy) (ScalarModel.mul f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_mul (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.mulD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simp [hx.derivative_length]
    have hjy : j.1 < dy.der.length := by simp [hy.derivative_length]
    change Contains
      ((List.zipWith
        (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
          (RatInterval.mul dx.val ddy))
        dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j * g.value x + f.value x * g.gradient x j)
    rw [getD_zipWith_of_lt
      (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
        (RatInterval.mul dx.val ddy))
      dx.der dy.der j.1 hjx hjy ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (RatInterval.contains_mul (hx.derivative_sound x hX j)
        (hy.value_sound x hX))
      (RatInterval.contains_mul (hx.value_sound x hX)
        (hy.derivative_sound x hX j))

/-- Rational scaling constructor. -/
theorem DSoundOn.scale {n : Nat} {X : Set (Vec n)}
    (a : ℚ) {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.scaleD a d) (ScalarModel.scale a f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_scale (h.value_sound x hX)
  · simp [ExactReplay.D.scaleD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (ExactReplay.scale a)).getD j.1 ExactReplay.zeroI)
      ((a : ℝ) * f.gradient x j)
    rw [getD_map_of_lt (ExactReplay.scale a) d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_scale (h.derivative_sound x hX j)

/-- Sine constructor and chain rule. -/
theorem DSoundOn.sin {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.sinD d) (ScalarModel.sin f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.sinI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.sinD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (RatInterval.mul (ExactReplay.cosI d.val))).getD
        j.1 ExactReplay.zeroI)
      (Real.cos (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (RatInterval.mul (ExactReplay.cosI d.val)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_mul
      (ExactReplay.cosI_contains (h.value_sound x hX)
        (hphysical x hX).1 (hphysical x hX).2)
      (h.derivative_sound x hX j)

/-- Cosine constructor and chain rule. -/
theorem DSoundOn.cos {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.cosD d) (ScalarModel.cos f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.cosI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.cosD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simp [h.derivative_length]
    change Contains
      ((d.der.map (fun z => RatInterval.neg
        (RatInterval.mul (ExactReplay.sinI d.val) z))).getD
        j.1 ExactReplay.zeroI)
      (-Real.sin (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (fun z => RatInterval.neg
      (RatInterval.mul (ExactReplay.sinI d.val) z)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    simpa only [neg_mul] using
      RatInterval.contains_neg (RatInterval.contains_mul
        (ExactReplay.sinI_contains (h.value_sound x hX)
          (hphysical x hX).1 (hphysical x hX).2)
        (h.derivative_sound x hX j))

end GerverSofa

end

end

end

section

/-!
# Concrete interval-AD soundness for the reduced 4D system

This module instantiates the constructor-level AD theorem with equations
(F1)--(F4), proves that the frozen rational list is exactly the manuscript box,
and identifies the four smooth scalar models with `Reduced.vectorSystem`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

namespace Reduced

/-- The four frozen rational intervals are exactly the named reduced box. -/
theorem inputBox_exact (x : Vec 4) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.reducedInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, qR, coordEquiv] at hx
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4]
    · intro i
      fin_cases i <;>
        simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
          CertificateManifest.q, RatInterval.Contains] <;>
        aesop
  · rintro ⟨hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, qR, coordEquiv]
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, RatInterval.Contains] at h0 h1 h2 h3
    aesop

/-- Scalar models matching the four reduced equations. -/
def models : Fin 4 → ScalarModel 4 :=
  let a := ScalarModel.var 4 (0 : Fin 4)
  let b := ScalarModel.var 4 (1 : Fin 4)
  let phi := ScalarModel.var 4 (2 : Fin 4)
  let theta := ScalarModel.var 4 (3 : Fin 4)
  let one := ScalarModel.const 4 1
  let half := ScalarModel.const 4 (1 / 2 : ℝ)
  let quarter := ScalarModel.const 4 (1 / 4 : ℝ)
  let piM := ScalarModel.const 4 Real.pi
  let cp := ScalarModel.cos phi
  let sp := ScalarModel.sin phi
  let ct := ScalarModel.cos theta
  let st := ScalarModel.sin theta
  let delta := theta - phi
  let f1 := a * (ct - cp) - (2 : ℚ) * b * sp + (delta - one) * ct - st + cp + sp
  let f2 := a * ((3 : ℚ) * st + sp) - (2 : ℚ) * b * cp
    + (3 : ℚ) * (delta - one) * st + (3 : ℚ) * ct - sp + cp
  let f3 := a * cp - sp - half + half * cp - b * sp
  let f4 := a + (1 / 2 : ℚ) * piM - phi - theta - b
    + half * delta * (one + a) + quarter * delta * delta
  ![f1, f2, f3, f4]

/-- The model values are definitionally the manuscript reduced system after
coordinate conversion. -/
theorem vectorSystem_eq_models (x : Vec 4) :
    vectorSystem x = fun i => (models i).value x := by
  funext i
  fin_cases i <;>
    simp [vectorSystem, coordEquiv, system, models, ScalarModel.var,
      ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
      ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos] <;>
    ring

end Reduced

end GerverSofa

end

end

end

section

/-!
# Concrete interval-AD soundness for the direct 22D Romik system

The direct system contains five trigonometric path pieces, three derivative
pieces and six matching pairs.  To avoid 22 unrelated derivative proofs, this
file evaluates every expression in a proof-carrying dual object.  Its first
projection is the exact executable `ExactReplay.D`; its second projection is a
smooth real scalar model; and its third field is the constructor-level
soundness theorem from `ADCoreSoundness`.
-/

/-! ## Exact identification of the 22D input box

The 22 coordinates are kept as separate tiny lemmas.  This is deliberately
chunked: expanding all 44 rational endpoint inequalities in one `simp` call
exhausts the default heartbeat budget even though every coordinate identity is
individually trivial. -/

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

namespace Romik

private theorem fullInputBox_coord_0_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 0) (x 0) ↔
      qR (-21032242207268875141628571849) 100000000000000000000000000000 ≤ x 0 ∧
      x 0 ≤ qR (-21032242207268875141608571849) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_1_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 1) (x 1) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 1 ∧
      x 1 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_2_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 2) (x 2) ↔
      qR (-91917929277159332227479610289) 100000000000000000000000000000 ≤ x 2 ∧
      x 2 ≤ qR (-91917929277159332227459610289) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_3_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 3) (x 3) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 3 ∧
      x 3 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_4_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 4) (x 4) ↔
      qR (-15344080735756291713875357283) 25000000000000000000000000000 ≤ x 4 ∧
      x 4 ≤ qR (-15344080735756291713870357283) 25000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_5_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 5) (x 5) ↔
      qR 17792529580064437214538861001 20000000000000000000000000000 ≤ x 5 ∧
      x 5 ≤ qR 17792529580064437214542861001 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_6_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 6) (x 6) ↔
      qR (-15417358304445500741761623987) 50000000000000000000000000000 ≤ x 6 ∧
      x 6 ≤ qR (-15417358304445500741751623987) 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_7_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 7) (x 7) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 7 ∧
      x 7 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_8_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 8) (x 8) ↔
      qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ x 8 ∧
      x 8 ≤ qR (-20344080735756291713870857283) 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_9_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 9) (x 9) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 9 ∧
      x 9 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_10_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 10) (x 10) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 10 ∧
      x 10 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_11_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 11) (x 11) ↔
      qR (-2500000000000000000001) 10000000000000000000000 ≤ x 11 ∧
      x 11 ≤ qR (-2499999999999999999999) 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_12_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 12) (x 12) ↔
      qR (-52762459802678462416060380937) 100000000000000000000000000000 ≤ x 12 ∧
      x 12 ≤ qR (-52762459802678462416040380937) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_13_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 13) (x 13) ↔
      qR 92025838516063762289360579501 100000000000000000000000000000 ≤ x 13 ∧
      x 13 ≤ qR 92025838516063762289380579501 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_14_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 14) (x 14) ↔
      qR 313022761424232933776114655193 500000000000000000000000000000 ≤ x 14 ∧
      x 14 ≤ qR 313022761424232933776214655193 500000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_15_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 15) (x 15) ↔
      qR (-151160128631428920268654781) 160000000000000000000000000 ≤ x 15 ∧
      x 15 ≤ qR (-151160128631428920268622781) 160000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_16_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 16) (x 16) ↔
      qR 1641278451780291167220080819 1250000000000000000000000000 ≤ x 16 ∧
      x 16 ≤ qR 1641278451780291167220330819 1250000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_17_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 17) (x 17) ↔
      qR (-105076534082910887440587258861) 200000000000000000000000000000 ≤ x 17 ∧
      x 17 ≤ qR (-105076534082910887440547258861) 200000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_18_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 18) (x 18) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 18 ∧
      x 18 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_19_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 19) (x 19) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 19 ∧
      x 19 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_20_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 20) (x 20) ↔
      qR 1958868239504182093160893749 50000000000000000000000000000 ≤ x 20 ∧
      x 20 ≤ qR 78354729580167283726435751 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_21_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 21) (x 21) ↔
      qR 34065075469136244723692787727 50000000000000000000000000000 ≤ x 21 ∧
      x 21 ≤ qR 34065075469136244723692787983 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]

/-- The 22 frozen rational intervals are exactly the named direct-system box. -/
theorem inputBox_exact (x : Vec 22) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.fullInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, coordEquiv] at hx
    rcases hx with ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi, h3lo, h3hi, h4lo, h4hi, h5lo, h5hi, h6lo,
      h6hi, h7lo, h7hi, h8lo, h8hi, h9lo, h9hi, h10lo, h10hi, h11lo, h11hi, h12lo, h12hi, h13lo,
      h13hi, h14lo, h14hi, h15lo, h15hi, h16lo, h16hi, h17lo, h17hi, h18lo, h18hi, h19lo, h19hi,
      h20lo, h20hi, h21lo, h21hi⟩
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.fullInputBox, CertificateManifest.z22]
    · intro i
      fin_cases i
      · exact (fullInputBox_coord_0_iff x).2 ⟨h0lo, h0hi⟩
      · exact (fullInputBox_coord_1_iff x).2 ⟨h1lo, h1hi⟩
      · exact (fullInputBox_coord_2_iff x).2 ⟨h2lo, h2hi⟩
      · exact (fullInputBox_coord_3_iff x).2 ⟨h3lo, h3hi⟩
      · exact (fullInputBox_coord_4_iff x).2 ⟨h4lo, h4hi⟩
      · exact (fullInputBox_coord_5_iff x).2 ⟨h5lo, h5hi⟩
      · exact (fullInputBox_coord_6_iff x).2 ⟨h6lo, h6hi⟩
      · exact (fullInputBox_coord_7_iff x).2 ⟨h7lo, h7hi⟩
      · exact (fullInputBox_coord_8_iff x).2 ⟨h8lo, h8hi⟩
      · exact (fullInputBox_coord_9_iff x).2 ⟨h9lo, h9hi⟩
      · exact (fullInputBox_coord_10_iff x).2 ⟨h10lo, h10hi⟩
      · exact (fullInputBox_coord_11_iff x).2 ⟨h11lo, h11hi⟩
      · exact (fullInputBox_coord_12_iff x).2 ⟨h12lo, h12hi⟩
      · exact (fullInputBox_coord_13_iff x).2 ⟨h13lo, h13hi⟩
      · exact (fullInputBox_coord_14_iff x).2 ⟨h14lo, h14hi⟩
      · exact (fullInputBox_coord_15_iff x).2 ⟨h15lo, h15hi⟩
      · exact (fullInputBox_coord_16_iff x).2 ⟨h16lo, h16hi⟩
      · exact (fullInputBox_coord_17_iff x).2 ⟨h17lo, h17hi⟩
      · exact (fullInputBox_coord_18_iff x).2 ⟨h18lo, h18hi⟩
      · exact (fullInputBox_coord_19_iff x).2 ⟨h19lo, h19hi⟩
      · exact (fullInputBox_coord_20_iff x).2 ⟨h20lo, h20hi⟩
      · exact (fullInputBox_coord_21_iff x).2 ⟨h21lo, h21hi⟩
  · rintro ⟨_hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, coordEquiv]
    have h0 := (fullInputBox_coord_0_iff x).1 (hx (0 : Fin 22))
    have h1 := (fullInputBox_coord_1_iff x).1 (hx (1 : Fin 22))
    have h2 := (fullInputBox_coord_2_iff x).1 (hx (2 : Fin 22))
    have h3 := (fullInputBox_coord_3_iff x).1 (hx (3 : Fin 22))
    have h4 := (fullInputBox_coord_4_iff x).1 (hx (4 : Fin 22))
    have h5 := (fullInputBox_coord_5_iff x).1 (hx (5 : Fin 22))
    have h6 := (fullInputBox_coord_6_iff x).1 (hx (6 : Fin 22))
    have h7 := (fullInputBox_coord_7_iff x).1 (hx (7 : Fin 22))
    have h8 := (fullInputBox_coord_8_iff x).1 (hx (8 : Fin 22))
    have h9 := (fullInputBox_coord_9_iff x).1 (hx (9 : Fin 22))
    have h10 := (fullInputBox_coord_10_iff x).1 (hx (10 : Fin 22))
    have h11 := (fullInputBox_coord_11_iff x).1 (hx (11 : Fin 22))
    have h12 := (fullInputBox_coord_12_iff x).1 (hx (12 : Fin 22))
    have h13 := (fullInputBox_coord_13_iff x).1 (hx (13 : Fin 22))
    have h14 := (fullInputBox_coord_14_iff x).1 (hx (14 : Fin 22))
    have h15 := (fullInputBox_coord_15_iff x).1 (hx (15 : Fin 22))
    have h16 := (fullInputBox_coord_16_iff x).1 (hx (16 : Fin 22))
    have h17 := (fullInputBox_coord_17_iff x).1 (hx (17 : Fin 22))
    have h18 := (fullInputBox_coord_18_iff x).1 (hx (18 : Fin 22))
    have h19 := (fullInputBox_coord_19_iff x).1 (hx (19 : Fin 22))
    have h20 := (fullInputBox_coord_20_iff x).1 (hx (20 : Fin 22))
    have h21 := (fullInputBox_coord_21_iff x).1 (hx (21 : Fin 22))
    exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
      h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2, h12.1, h12.2, h13.1, h13.2,
      h14.1, h14.2, h15.1, h15.2, h16.1, h16.2, h17.1, h17.2, h18.1, h18.2, h19.1, h19.2, h20.1,
      h20.2, h21.1, h21.2⟩

/-- All four switching times used by the direct evaluator lie in `[0,π/2]`. -/
theorem full_switches_physical {x : Vec 22} (hx : x ∈ vectorBox) :
    (0 ≤ x 20 ∧ x 20 ≤ Real.pi / 2) ∧
    (0 ≤ x 21 ∧ x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 21 ∧ Real.pi / 2 - x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 20 ∧ Real.pi / 2 - x 20 ≤ Real.pi / 2) := by
  let p := coordEquiv.symm x
  have hp : p ∈ box := hx
  have hphiPos : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have htheta0 : 0 ≤ p.theta :=
    le_trans hphiPos.le hord.phi_le_theta
  have hthetaHalf : p.theta ≤ Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiHalf : p.phi ≤ Real.pi / 2 :=
    le_trans hord.phi_le_theta hthetaHalf
  change
    (0 ≤ p.phi ∧ p.phi ≤ Real.pi / 2) ∧
    (0 ≤ p.theta ∧ p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.theta ∧
      Real.pi / 2 - p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.phi ∧
      Real.pi / 2 - p.phi ≤ Real.pi / 2)
  constructor
  · exact ⟨hphiPos.le, hphiHalf⟩
  constructor
  · exact ⟨htheta0, hthetaHalf⟩
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-! ## Proof-carrying dual expressions -/

/-- One executable interval dual paired with its real semantic model. -/
structure SoundDual (n : Nat) (X : Set (Vec n)) where
  /-- The interval value and derivative data being certified. -/
  d : ExactReplay.D
  /-- The real scalar function and gradient represented by the interval data. -/
  model : ScalarModel n
  sound : DSoundOn X d model

namespace SoundDual

variable {n : Nat} {X : Set (Vec n)}

/-- A constant scalar model with a certified interval enclosure. -/
def const (z : RatInterval) (c : ℝ) (h : Contains z c) : SoundDual n X :=
  ⟨ExactReplay.D.const z n, ScalarModel.const n c, DSoundOn.const h⟩

/-- A rational constant represented by a singleton interval and zero gradient. -/
def pointConst (q : ℚ) : SoundDual n X :=
  ⟨ExactReplay.D.pointConst q n, ScalarModel.const n (q : ℝ),
    DSoundOn.pointConst q⟩

/-- A coordinate projection with its certified input interval. -/
def var (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) : SoundDual n X :=
  ⟨ExactReplay.D.varD input k.1 n, ScalarModel.var n k,
    DSoundOn.varD input k h⟩

/-- Addition with certified interval value and gradient enclosures. -/
def add (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.addD a.d b.d, ScalarModel.add a.model b.model,
    a.sound.add b.sound⟩

/-- Negation with certified interval value and gradient enclosures. -/
def neg (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.negD a.d, ScalarModel.neg a.model, a.sound.neg⟩

/-- Subtraction with certified interval value and gradient enclosures. -/
def sub (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.subD a.d b.d, ScalarModel.sub a.model b.model,
    a.sound.sub b.sound⟩

/-- Multiplication with certified interval value and gradient enclosures. -/
def mul (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.mulD a.d b.d, ScalarModel.mul a.model b.model,
    a.sound.mul b.sound⟩

/-- Rational scaling with certified interval value and gradient enclosures. -/
def scale (q : ℚ) (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.scaleD q a.d, ScalarModel.scale q a.model,
    DSoundOn.scale q a.sound⟩

/-- Sine with certified interval value and gradient enclosures. -/
def sin (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.sinD a.d, ScalarModel.sin a.model, a.sound.sin h⟩

/-- Cosine with certified interval value and gradient enclosures. -/
def cos (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.cosD a.d, ScalarModel.cos a.model, a.sound.cos h⟩

instance : Add (SoundDual n X) := ⟨add⟩
instance : Neg (SoundDual n X) := ⟨neg⟩
instance : Sub (SoundDual n X) := ⟨sub⟩
instance : Mul (SoundDual n X) := ⟨mul⟩
instance : HMul ℚ (SoundDual n X) (SoundDual n X) := ⟨scale⟩

/-! Small projection lemmas keep the simplifier away from the proof fields of
`SoundDual`.  All are definitional equalities. -/
@[simp] theorem const_model_value (z : RatInterval) (c : ℝ)
    (h : Contains z c) (x : Vec n) :
    (const z c h : SoundDual n X).model.value x = c := rfl

@[simp] theorem pointConst_model_value (q : ℚ) (x : Vec n) :
    (pointConst q : SoundDual n X).model.value x = (q : ℝ) := rfl

@[simp] theorem var_model_value (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) (x : Vec n) :
    (var input k h : SoundDual n X).model.value x = x k := rfl

@[simp] theorem add_model_value (a b : SoundDual n X) (x : Vec n) :
    (a + b).model.value x = a.model.value x + b.model.value x := rfl

@[simp] theorem neg_model_value (a : SoundDual n X) (x : Vec n) :
    (-a).model.value x = -a.model.value x := rfl

@[simp] theorem sub_model_value (a b : SoundDual n X) (x : Vec n) :
    (a - b).model.value x = a.model.value x - b.model.value x := rfl

@[simp] theorem mul_model_value (a b : SoundDual n X) (x : Vec n) :
    (a * b).model.value x = a.model.value x * b.model.value x := rfl

@[simp] theorem scale_model_value (q : ℚ) (a : SoundDual n X) (x : Vec n) :
    (q * a).model.value x = (q : ℝ) * a.model.value x := rfl

@[simp] theorem sin_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (sin a h).model.value x = Real.sin (a.model.value x) := rfl

@[simp] theorem cos_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (cos a h).model.value x = Real.cos (a.model.value x) := rfl

end SoundDual

/-- A certified physical angle, used to justify every sine/cosine constructor. -/
structure AngleDual (n : Nat) (X : Set (Vec n)) where
  /-- The certified scalar model for the angle variable. -/
  dual : SoundDual n X
  physical : ∀ x ∈ X, 0 ≤ dual.model.value x ∧
    dual.model.value x ≤ Real.pi / 2

namespace AngleDual

variable {n : Nat} {X : Set (Vec n)}

/-- Sine with certified interval value and gradient enclosures. -/
def sin (t : AngleDual n X) : SoundDual n X :=
  SoundDual.sin t.dual t.physical

/-- Cosine with certified interval value and gradient enclosures. -/
def cos (t : AngleDual n X) : SoundDual n X :=
  SoundDual.cos t.dual t.physical

@[simp] theorem sin_model_value (t : AngleDual n X) (x : Vec n) :
    t.sin.model.value x = Real.sin (t.dual.model.value x) := rfl

@[simp] theorem cos_model_value (t : AngleDual n X) (x : Vec n) :
    t.cos.model.value x = Real.cos (t.dual.model.value x) := rfl

end AngleDual

/-- Named proof-carrying versions of all direct-system variables. -/
structure FullVars (X : Set (Vec 22)) where
  /-- Horizontal translation coefficient for phase 1 as a certified dual interval. -/
  k11 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 1 as a certified dual interval. -/
  k12 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 2 as a certified dual interval. -/
  k21 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 2 as a certified dual interval. -/
  k22 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 3 as a certified dual interval. -/
  k31 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 3 as a certified dual interval. -/
  k32 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 4 as a certified dual interval. -/
  k41 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 4 as a certified dual interval. -/
  k42 : SoundDual 22 X
  /-- Horizontal translation coefficient for phase 5 as a certified dual interval. -/
  k51 : SoundDual 22 X
  /-- Vertical translation coefficient for phase 5 as a certified dual interval. -/
  k52 : SoundDual 22 X
  /-- Coefficient 1 in the phase 1 closed formula as a certified dual interval. -/
  a1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 1 closed formula as a certified dual interval. -/
  a2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 2 closed formula as a certified dual interval. -/
  b1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 2 closed formula as a certified dual interval. -/
  b2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 3 closed formula as a certified dual interval. -/
  c1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 3 closed formula as a certified dual interval. -/
  c2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 4 closed formula as a certified dual interval. -/
  d1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 4 closed formula as a certified dual interval. -/
  d2 : SoundDual 22 X
  /-- Coefficient 1 in the phase 5 closed formula as a certified dual interval. -/
  e1 : SoundDual 22 X
  /-- Coefficient 2 in the phase 5 closed formula as a certified dual interval. -/
  e2 : SoundDual 22 X

/-- The 22 coordinate variables equipped with their input-enclosure proofs. -/
def inputDual (i : Fin 22) : SoundDual 22 vectorBox :=
  SoundDual.var (ExactReplay.getI ExactReplay.fullInputBox i.1) i (by
    intro x hx
    exact ((inputBox_exact x).1 hx).2 i)

@[simp] theorem inputDual_model_value (i : Fin 22) (x : Vec 22) :
    (inputDual i).model.value x = x i := rfl

/-- Named first twenty variables in verifier order. -/
def fullVars : FullVars vectorBox where
  k11 := inputDual 0
  k12 := inputDual 1
  k21 := inputDual 2
  k22 := inputDual 3
  k31 := inputDual 4
  k32 := inputDual 5
  k41 := inputDual 6
  k42 := inputDual 7
  k51 := inputDual 8
  k52 := inputDual 9
  a1 := inputDual 10
  a2 := inputDual 11
  b1 := inputDual 12
  b2 := inputDual 13
  c1 := inputDual 14
  c2 := inputDual 15
  d1 := inputDual 16
  d2 := inputDual 17
  e1 := inputDual 18
  e2 := inputDual 19

/-- Exact proof-carrying π constant. -/
def piDual : SoundDual 22 vectorBox :=
  SoundDual.const ExactReplay.piI Real.pi ExactReplay.piI_contains_pi

@[simp] theorem piDual_model_value (x : Vec 22) :
    piDual.model.value x = Real.pi := rfl

/-- First switching angle. -/
def phiDual : AngleDual 22 vectorBox where
  dual := inputDual 20
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).1

@[simp] theorem phiDual_model_value (x : Vec 22) :
    phiDual.dual.model.value x = x 20 := rfl

/-- Second switching angle. -/
def thetaDual : AngleDual 22 vectorBox where
  dual := inputDual 21
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).2.1

@[simp] theorem thetaDual_model_value (x : Vec 22) :
    thetaDual.dual.model.value x = x 21 := rfl

private theorem eta_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - thetaDual.dual).model.value x) =
      Real.pi / 2 - x 21 := by
  simp; ring

/-- Reflected third switching angle `π/2-θ`. -/
def etaDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - thetaDual.dual
  physical := by
    intro x hx
    rw [eta_raw_model_value]
    exact (full_switches_physical hx).2.2.1

@[simp] theorem etaDual_model_value (x : Vec 22) :
    etaDual.dual.model.value x = Real.pi / 2 - x 21 := by
  exact eta_raw_model_value x

private theorem tau_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - phiDual.dual).model.value x) =
      Real.pi / 2 - x 20 := by
  simp; ring

/-- Reflected fourth switching angle `π/2-φ`. -/
def tauDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - phiDual.dual
  physical := by
    intro x hx
    rw [tau_raw_model_value]
    exact (full_switches_physical hx).2.2.2

@[simp] theorem tauDual_model_value (x : Vec 22) :
    tauDual.dual.model.value x = Real.pi / 2 - x 20 := by
  exact tau_raw_model_value x

/-- Rotation of a proof-carrying body-frame vector. -/
def rotDual (t : AngleDual 22 vectorBox)
    (z1 z2 : SoundDual 22 vectorBox) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ct := t.cos
  let st := t.sin
  (ct * z1 - st * z2, st * z1 + ct * z2)

/-- One proof-carrying path piece. -/
def pathPieceDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  let data : SoundDual 22 vectorBox × SoundDual 22 vectorBox ×
      SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
    if j = 1 then
      (p.a1 * ct + p.a2 * st - one,
       -p.a2 * ct + p.a1 * st - half,
       p.k11, p.k12)
    else if j = 2 then
      (-quarter * t.dual * t.dual + p.b1 * t.dual + p.b2,
       half * t.dual - p.b1 - one,
       p.k21, p.k22)
    else if j = 3 then
      (p.c1 - t.dual, p.c2 + t.dual, p.k31, p.k32)
    else if j = 4 then
      (-half * t.dual + p.d1 - one,
       -quarter * t.dual * t.dual + p.d1 * t.dual + p.d2,
       p.k41, p.k42)
    else
      (p.e1 * ct + p.e2 * st - half,
       -p.e2 * ct + p.e1 * st - one,
       p.k51, p.k52)
  let rr := rotDual t data.1 data.2.1
  (rr.1 + data.2.2.1, rr.2 + data.2.2.2)

/-- Body-frame derivative coefficients for one phase. -/
def alphaBetaDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  if j = 1 then
    (-(2 : ℚ) * p.a1 * st + (2 : ℚ) * p.a2 * ct + half,
     (2 : ℚ) * p.a1 * ct + (2 : ℚ) * p.a2 * st - one)
  else if j = 2 then
    (one + (2 : ℚ) * p.b1 - t.dual,
     -quarter * t.dual * t.dual + p.b1 * t.dual + p.b2 + half)
  else if j = 3 then
    (-one - p.c2 - t.dual, one + p.c1 - t.dual)
  else if j = 4 then
    (quarter * t.dual * t.dual - p.d1 * t.dual - p.d2 - half,
     (2 : ℚ) * p.d1 - one - t.dual)
  else
    (one - (2 : ℚ) * p.e1 * st + (2 : ℚ) * p.e2 * ct,
     (2 : ℚ) * p.e1 * ct + (2 : ℚ) * p.e2 * st - half)

/-- World-frame derivative piece. -/
def pathPrimeDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ab := alphaBetaDual j t p
  rotDual t ab.1 ab.2

/-- The complete proof-carrying direct system in manuscript order. -/
def fullDualOutput : List (SoundDual 22 vectorBox) :=
  let p := fullVars
  let halfPi := (1 / 2 : ℚ) * piDual
  let quarterPi := (1 / 4 : ℚ) * piDual
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let first : List (SoundDual 22 vectorBox) := [
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * ((2 : ℚ) * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - one + p.a1,
    p.k12 - quarter,
    p.a2 + quarter
  ]
  let pairs := [
    (pathPieceDual 1 phiDual p, pathPieceDual 2 phiDual p),
    (pathPrimeDual 1 phiDual p, pathPrimeDual 2 phiDual p),
    (pathPieceDual 2 thetaDual p, pathPieceDual 3 thetaDual p),
    (pathPrimeDual 2 thetaDual p, pathPrimeDual 3 thetaDual p),
    (pathPieceDual 3 etaDual p, pathPieceDual 4 etaDual p),
    (pathPieceDual 4 tauDual p, pathPieceDual 5 tauDual p)
  ]
  let matchEqs := pairs.flatMap (fun lr =>
    [lr.1.1 - lr.2.1, lr.1.2 - lr.2.2])
  let lhs := pathPieceDual 1 phiDual p
  let xe := pathPieceDual 3 etaDual p
  let ae := (alphaBetaDual 3 etaDual p).1
  let be :=
    (xe.1 - ae * etaDual.sin, xe.2 + ae * etaDual.cos)
  first ++ matchEqs ++ [lhs.1 - be.1, lhs.2 - be.2]

/-! Public-shape unfold lemmas for the three derivative path pieces.

`Systems.lean` deliberately hides the helper `pathPrimeFromAB`.  When `system`
is unfolded outside that file, the private helper survives as an inaccessible
constant, so `ring` cannot see that the right-hand side is just a rotation.
These `rfl` lemmas expose exactly the public normal form needed by the four
derivative-matching equations. -/
private theorem pathPrime1_eq_rot (p : Params) (t : ℝ) :
    pathPrime1 p t = rot t (alphaBeta1 p t) := rfl

private theorem pathPrime2_eq_rot (p : Params) (t : ℝ) :
    pathPrime2 p t = rot t (alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot (p : Params) (t : ℝ) :
    pathPrime3 p t = rot t (alphaBeta3 p t) := rfl

/-! The semantic identification is split coordinatewise so each normalization
gets its own heartbeat budget.  A single 22-way `fin_cases <;> simp <;> ring`
command is mathematically fine but deterministically exhausts 200000 heartbeats. -/

private theorem fullDualOutput_model_eq_0 (x : Vec 22) :
    ((fullDualOutput.getD 0 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (0 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_1 (x : Vec 22) :
    ((fullDualOutput.getD 1 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (1 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_2 (x : Vec 22) :
    ((fullDualOutput.getD 2 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (2 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_3 (x : Vec 22) :
    ((fullDualOutput.getD 3 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (3 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_4 (x : Vec 22) :
    ((fullDualOutput.getD 4 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (4 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]; ring

private theorem fullDualOutput_model_eq_5 (x : Vec 22) :
    ((fullDualOutput.getD 5 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (5 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_6 (x : Vec 22) :
    ((fullDualOutput.getD 6 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (6 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_7 (x : Vec 22) :
    ((fullDualOutput.getD 7 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (7 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_8 (x : Vec 22) :
    ((fullDualOutput.getD 8 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (8 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_9 (x : Vec 22) :
    ((fullDualOutput.getD 9 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (9 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_10 (x : Vec 22) :
    ((fullDualOutput.getD 10 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (10 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_11 (x : Vec 22) :
    ((fullDualOutput.getD 11 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (11 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_12 (x : Vec 22) :
    ((fullDualOutput.getD 12 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (12 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_13 (x : Vec 22) :
    ((fullDualOutput.getD 13 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (13 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_14 (x : Vec 22) :
    ((fullDualOutput.getD 14 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (14 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_15 (x : Vec 22) :
    ((fullDualOutput.getD 15 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (15 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_16 (x : Vec 22) :
    ((fullDualOutput.getD 16 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (16 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_17 (x : Vec 22) :
    ((fullDualOutput.getD 17 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (17 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_18 (x : Vec 22) :
    ((fullDualOutput.getD 18 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (18 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_19 (x : Vec 22) :
    ((fullDualOutput.getD 19 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (19 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_20 (x : Vec 22) :
    ((fullDualOutput.getD 20 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (20 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


private theorem fullDualOutput_model_eq_21 (x : Vec 22) :
    ((fullDualOutput.getD 21 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (21 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3]


/-- The real models carried by `fullDualOutput` are exactly the 22 manuscript
functions in finite-vector coordinates. -/
theorem fullDualOutput_model_eq (x : Vec 22) :
    (fun i : Fin 22 =>
      ((fullDualOutput.getD i.1
        (SoundDual.pointConst 0)).model.value x)) = vectorSystem x := by
  funext i
  fin_cases i
  · exact fullDualOutput_model_eq_0 x
  · exact fullDualOutput_model_eq_1 x
  · exact fullDualOutput_model_eq_2 x
  · exact fullDualOutput_model_eq_3 x
  · exact fullDualOutput_model_eq_4 x
  · exact fullDualOutput_model_eq_5 x
  · exact fullDualOutput_model_eq_6 x
  · exact fullDualOutput_model_eq_7 x
  · exact fullDualOutput_model_eq_8 x
  · exact fullDualOutput_model_eq_9 x
  · exact fullDualOutput_model_eq_10 x
  · exact fullDualOutput_model_eq_11 x
  · exact fullDualOutput_model_eq_12 x
  · exact fullDualOutput_model_eq_13 x
  · exact fullDualOutput_model_eq_14 x
  · exact fullDualOutput_model_eq_15 x
  · exact fullDualOutput_model_eq_16 x
  · exact fullDualOutput_model_eq_17 x
  · exact fullDualOutput_model_eq_18 x
  · exact fullDualOutput_model_eq_19 x
  · exact fullDualOutput_model_eq_20 x
  · exact fullDualOutput_model_eq_21 x

end Romik

end GerverSofa

end

end

end
