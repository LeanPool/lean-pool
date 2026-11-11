/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel
public import LeanPool.ECRuntime.MultiplicativeDrift
public import LeanPool.ECRuntime.Objective

/-!
# One Max

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Potential used for the standard OneMax analysis: number of zero bits. -/
def oneMaxPotential {n : ℕ} (x : BitString n) : ℕ :=
  zeroCount x

/-- The OneMax target is the zero level of the zero-bit potential. -/
def oneMaxTarget (n : ℕ) : Set (BitString n) :=
  potentialTarget (fun x : BitString n => oneMaxPotential x)

@[simp] theorem oneMaxPotential_optimum (n : ℕ) :
    oneMaxPotential (allOnes n) = 0 := by
  simp [oneMaxPotential]

@[simp] theorem allOnes_mem_oneMaxTarget (n : ℕ) :
    allOnes n ∈ oneMaxTarget n := by
  simp [oneMaxTarget, potentialTarget]

/-- Membership in the OneMax target is decidable. -/
instance instDecidablePredOneMaxTarget (n : ℕ) :
    DecidablePred (fun x : BitString n => x ∈ oneMaxTarget n) := by
  intro x
  change Decidable (oneMaxPotential x = 0)
  infer_instance

/-- Zero OneMax potential characterizes the all-one optimum exactly. -/
theorem oneMaxPotential_eq_zero_iff {n : ℕ} (x : BitString n) :
    oneMaxPotential x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hcard : (zeroPositions x).card = 0 := by
      rw [zeroPositions_card]
      simpa [oneMaxPotential] using hx
    have hempty : zeroPositions x = ∅ := Finset.card_eq_zero.mp hcard
    funext i
    cases hxi : x i with
    | false =>
        have himem : i ∈ zeroPositions x := (mem_zeroPositions x i).2 hxi
        rw [hempty] at himem
        simp at himem
    | true =>
        simp [allOnes]
  · intro hx
    subst x
    exact oneMaxPotential_optimum n

/-- The potential-defined target is precisely the singleton optimum. -/
theorem oneMaxTarget_eq_singleton (n : ℕ) :
    oneMaxTarget n = ({allOnes n} : Set (BitString n)) := by
  ext x
  simp [oneMaxTarget, potentialTarget, oneMaxPotential_eq_zero_iff]

/-- Flipping one zero bit and no other bit is a strict OneMax improvement. -/
theorem oneMax_single_zero_flip_improves
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = false) :
    oneMax x < oneMax (mutateWithMask x {i}) := by
  change oneCount x < oneCount (mutateWithMask x {i})
  rw [oneCount_mutate_single_of_false x i hi]
  omega

/-- For the OneMax potential, the same event decreases the potential by exactly one. -/
theorem oneMaxPotential_single_zero_flip
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = false) :
    oneMaxPotential (mutateWithMask x {i}) + 1 = oneMaxPotential x := by
  exact zeroCount_mutate_single_of_false x i hi

/-- A real-valued wrapper useful for the transition-matrix layer. -/
def oneMaxReal {n : ℕ} (x : BitString n) : ℝ :=
  (oneMax x : ℝ)

/-- The all-one string globally maximizes OneMax. -/
theorem oneMaxReal_le_allOnes {n : ℕ} (x : BitString n) :
    oneMaxReal x ≤ oneMaxReal (allOnes n) := by
  simp only [oneMaxReal, oneMax, oneCount_allOnes]
  exact_mod_cast oneCount_le x

/-- Elitist selection for OneMax cannot increase the number of zero bits. -/
theorem oneMaxPotential_selectedAfterMask_le
    {n : ℕ} (x : BitString n) (mask : MutationMask n) :
    oneMaxPotential (selectedAfterMask oneMaxReal x mask) ≤ oneMaxPotential x := by
  unfold selectedAfterMask elitistSelect
  by_cases hacc : oneMaxReal x ≤ oneMaxReal (mutateWithMask x mask)
  · simp only [hacc, ite_true]
    have hcountReal :
        (oneCount x : ℝ) ≤ (oneCount (mutateWithMask x mask) : ℝ) := by
      simpa [oneMaxReal, oneMax] using hacc
    have hcount : oneCount x ≤ oneCount (mutateWithMask x mask) := by
      exact_mod_cast hcountReal
    have hx := oneCount_add_zeroCount x
    have hy := oneCount_add_zeroCount (mutateWithMask x mask)
    unfold oneMaxPotential
    omega
  · simp only [hacc, ite_false]
    exact le_rfl

/-- A simple single-zero mutation is accepted and strictly lowers the OneMax potential. -/
theorem oneMaxPotential_selected_single_zero_flip_lt
    {n : ℕ} (x : BitString n) (i : Fin n) (hi : x i = false) :
    oneMaxPotential (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) <
      oneMaxPotential x := by
  have himprove := oneMax_single_zero_flip_improves x i hi
  have hacc : Accepts oneMaxReal x (mutateWithMask x ({i} : MutationMask n)) := by
    unfold Accepts oneMaxReal
    exact_mod_cast (Nat.le_of_lt himprove)
  rw [selectedAfterMask, elitistSelect_of_accepts oneMaxReal x
    (mutateWithMask x ({i} : MutationMask n)) hacc]
  have hpot := oneMaxPotential_single_zero_flip x i hi
  omega

/-- The finite set of masks that flip exactly one currently-zero bit. -/
def singleZeroMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  (zeroPositions x).image (fun i => ({i} : MutationMask n))

/-- Summing mask weights over `singleZeroMasks` agrees with the earlier coordinate sum. -/
theorem singleZeroMasks_weight_eq {n : ℕ} (p : ℝ) (x : BitString n) :
    (∑ mask ∈ singleZeroMasks x, mutationMaskWeight p mask) =
      singleZeroFlipWeight p x := by
  unfold singleZeroMasks singleZeroFlipWeight
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Finset.singleton_injective hab

/--
The total mass of all strict OneMax improvements is at least the mass of the
simple events that flip one zero bit and no other bit.
-/
theorem oneMax_progress_mass_lower_bound
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    (oneMaxPotential x : ℝ) * (p * (1 - p) ^ (n - 1)) ≤
      finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x) := by
  calc
    (oneMaxPotential x : ℝ) * (p * (1 - p) ^ (n - 1)) =
        singleZeroFlipWeight p x := by
      symm
      simpa [oneMaxPotential] using singleZeroFlipWeight_eq p x
    _ = ∑ mask ∈ singleZeroMasks x, mutationMaskWeight p mask := by
      symm
      exact singleZeroMasks_weight_eq p x
    _ ≤ finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x) := by
      apply sum_le_finiteEventMass_of_subset
      · intro mask
        exact mutationMaskWeight_nonneg hp0 hp1 mask
      · intro mask hmask
        rcases Finset.mem_image.mp hmask with ⟨i, hi, himask⟩
        subst mask
        have hzero : x i = false := (mem_zeroPositions x i).mp hi
        exact oneMaxPotential_selected_single_zero_flip_lt x i hzero

/-- Real-valued version of the zero-count potential, used by generic drift theorems. -/
def oneMaxPotentialReal {n : ℕ} (x : BitString n) : ℝ :=
  (oneMaxPotential x : ℝ)

/-- The real OneMax potential is nonnegative. -/
theorem oneMaxPotentialReal_nonneg {n : ℕ} (x : BitString n) :
    0 ≤ oneMaxPotentialReal x := by
  simp [oneMaxPotentialReal]

/--
The OneMax process has multiplicative drift at least `p(1-p)^(n-1)` with
respect to the zero-count potential.  This is a useful sanity check for the generic
drift API; the fitness-level theorem proved below is sharper for this benchmark.
-/
theorem oneMax_hasMultiplicativeDriftLowerBound
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasMultiplicativeDriftLowerBound (α := BitString n)
      (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
      (oneMaxPotentialReal (n := n))
      (p * (1 - p) ^ (n - 1)) := by
  intro x _hx
  let event : MutationMask n → Prop := fun mask =>
    oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x
  have hAll : ∀ mask : MutationMask n,
      oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) ≤
        oneMaxPotentialReal x := by
    intro mask
    unfold oneMaxPotentialReal
    exact_mod_cast oneMaxPotential_selectedAfterMask_le x mask
  have hEvent : ∀ mask : MutationMask n, event mask →
      oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) + 1 ≤
        oneMaxPotentialReal x := by
    intro mask hmask
    unfold event at hmask
    unfold oneMaxPotentialReal
    have hnat : oneMaxPotential (selectedAfterMask oneMaxReal x mask) + 1 ≤
        oneMaxPotential x := by omega
    exact_mod_cast hnat
  have hweighted := weightedExpectation_add_eventMass_mul_le
    (fun mask : MutationMask n => mutationMaskWeight p mask)
    event
    (fun mask => oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask))
    (oneMaxPotentialReal x) 1
    (fun mask => mutationMaskWeight_nonneg hp0 hp1 mask)
    (mutationMaskWeight_sum n p) hAll hEvent
  have hprogress := oneMax_progress_mass_lower_bound hp0 hp1 x
  have hEV :
      expectedValueAfter (onePlusOneTransition p oneMaxReal) oneMaxPotentialReal x =
        ∑ mask : MutationMask n,
          mutationMaskWeight p mask *
            oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) := by
    unfold expectedValueAfter onePlusOneTransition
    exact pushforwardWeight_expectation
      (fun mask : MutationMask n => mutationMaskWeight p mask)
      (selectedAfterMask oneMaxReal x) oneMaxPotentialReal
  unfold driftAt
  rw [hEV]
  dsimp [event] at hweighted
  simp only [one_mul] at hweighted
  change (p * (1 - p) ^ (n - 1)) * (oneMaxPotential x : ℝ) ≤
    (oneMaxPotential x : ℝ) -
      ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask)
  change (∑ mask : MutationMask n,
      mutationMaskWeight p mask *
        oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask)) +
      finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask => oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x) ≤
      (oneMaxPotential x : ℝ) at hweighted
  nlinarith [hweighted, hprogress]

/-- Per-bad-bit improvement rate supplied by the single-zero-flip events. -/
def oneMaxImprovementRate (n : ℕ) (p : ℝ) : ℝ :=
  p * (1 - p) ^ (n - 1)

/-- The per-bad-bit improvement rate is positive for `0 < p < 1`. -/
theorem oneMaxImprovementRate_pos {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < oneMaxImprovementRate n p := by
  unfold oneMaxImprovementRate
  exact mul_pos hp0 (pow_pos (sub_pos.mpr hp1) _)

/-- The real zero-count target agrees with the earlier natural-valued OneMax target. -/
theorem oneMaxRealTarget_eq_oneMaxTarget (n : ℕ) :
    realPotentialTarget (oneMaxPotentialReal (n := n)) = oneMaxTarget n := by
  ext x
  simp [realPotentialTarget, oneMaxTarget, potentialTarget, oneMaxPotentialReal]

/-- OneMax instantiates the generic multiplicative-drift theorem directly. -/
theorem oneMax_multiplicative_runtimeSup_le
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (oneMaxImprovementRate n p) 1 (oneMaxPotentialReal (n := n)) x) := by
  have hP : IsStochastic
      (onePlusOneTransition (n := n) p (oneMaxReal (n := n))) :=
    onePlusOneTransition_stochastic (n := n) hp0.le hp1.le (oneMaxReal (n := n))
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget (oneMaxPotentialReal (n := n)) →
        (1 : ℝ) ≤ oneMaxPotentialReal z := by
    intro z hz
    have hzNat : oneMaxPotential z ≠ 0 := by
      intro hz0
      apply hz
      simp [realPotentialTarget, oneMaxPotentialReal, hz0]
    have hone : 1 ≤ oneMaxPotential z := Nat.one_le_iff_ne_zero.mpr hzNat
    unfold oneMaxPotentialReal
    exact_mod_cast hone
  have hbound := multiplicativeDrift_runtimeSup_le
    (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
    (oneMaxPotentialReal (n := n))
    (oneMaxImprovementRate n p) 1
    hP (oneMaxImprovementRate_pos hp0 hp1) (by norm_num)
    oneMaxPotentialReal_nonneg hmin
    (by simpa [oneMaxImprovementRate] using
      (oneMax_hasMultiplicativeDriftLowerBound (n := n) hp0.le hp1.le))
    x
  calc
    runtimeSup
        (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
        (oneMaxTarget n) x =
      runtimeSup
        (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
        (realPotentialTarget (oneMaxPotentialReal (n := n))) x := by
          symm
          exact runtimeSup_congr_target
            (onePlusOneTransition (n := n) p (oneMaxReal (n := n)))
            (realPotentialTarget (oneMaxPotentialReal (n := n)))
            (oneMaxTarget n)
            (oneMaxRealTarget_eq_oneMaxTarget n) x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          (oneMaxImprovementRate n p) 1 (oneMaxPotentialReal (n := n)) x) := hbound

/-- A coarser additive-drift certificate for OneMax, useful as a test of the generic theorem. -/
theorem oneMax_additive_finiteHorizonRuntimeBound
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasUniformFiniteHorizonRuntimeBound
      (onePlusOneTransition p oneMaxReal)
      (oneMaxTarget n)
      (additiveDriftRuntime (oneMaxImprovementRate n p) oneMaxPotentialReal) := by
  let rate := oneMaxImprovementRate n p
  have hrate : 0 < rate := oneMaxImprovementRate_pos hp0 hp1
  apply additiveDrift_finiteHorizonBound
      (onePlusOneTransition p oneMaxReal) (oneMaxTarget n)
      oneMaxPotentialReal rate
  · exact onePlusOneTransition_stochastic hp0.le hp1.le oneMaxReal
  · exact hrate
  · exact oneMaxPotentialReal_nonneg
  · intro x hx
    have hx0 : oneMaxPotential x = 0 := by
      simpa [oneMaxTarget, potentialTarget] using hx
    simp [oneMaxPotentialReal, hx0]
  · intro x hx
    have hx0 : oneMaxPotential x ≠ 0 := by
      simpa [oneMaxTarget, potentialTarget] using hx
    have hk : 1 ≤ oneMaxPotential x := Nat.one_le_iff_ne_zero.mpr hx0
    have hkreal : 1 ≤ oneMaxPotentialReal x := by
      unfold oneMaxPotentialReal
      exact_mod_cast hk
    have hmult := oneMax_hasMultiplicativeDriftLowerBound (n := n) hp0.le hp1.le
    have hVpos : 0 < oneMaxPotentialReal x := lt_of_lt_of_le zero_lt_one hkreal
    have hd := hmult x hVpos
    change rate ≤ driftAt (onePlusOneTransition p oneMaxReal) oneMaxPotentialReal x
    change rate * oneMaxPotentialReal x ≤
      driftAt (onePlusOneTransition p oneMaxReal) oneMaxPotentialReal x at hd
    have hlower : rate ≤ rate * oneMaxPotentialReal x := by
      nlinarith [hrate, hkreal]
    exact hlower.trans hd

/--
End-to-end finite-horizon fitness-level bound for OneMax at any mutation rate `0 < p < 1`.
Every truncated expected optimization time is at most `H_k / (p(1-p)^(n-1))`, where
`k` is the number of zero bits in the initial state.
-/
theorem oneMax_finiteHorizonRuntimeBound
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasUniformFiniteHorizonRuntimeBound
      (onePlusOneTransition p oneMaxReal)
      (oneMaxTarget n)
      (harmonicLevelRuntime (oneMaxImprovementRate n p) oneMaxPotential) := by
  have hgeneric := harmonicFitnessLevel_finiteHorizonBound
    (w := fun (_x : BitString n) (mask : MutationMask n) => mutationMaskWeight p mask)
    (step := selectedAfterMask oneMaxReal)
    (V := oneMaxPotential)
    (rate := oneMaxImprovementRate n p)
    (hrate := oneMaxImprovementRate_pos hp0 hp1)
    (hw := fun _x mask => mutationMaskWeight_nonneg hp0.le hp1.le mask)
    (hsum := fun _x => mutationMaskWeight_sum n p)
    (hmono := fun x mask => oneMaxPotential_selectedAfterMask_le x mask)
    (hprogress := fun x hx => by
      simpa [oneMaxImprovementRate] using
        oneMax_progress_mass_lower_bound hp0.le hp1.le x)
  simpa [oneMaxTarget, onePlusOneTransition_eq_finiteRandomTransition] using hgeneric

/-- Pointwise form of the arbitrary-rate finite-horizon OneMax theorem. -/
theorem oneMax_finiteHorizonRuntime_le_harmonic
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℕ) (x : BitString n) :
    finiteHorizonRuntime (onePlusOneTransition p oneMaxReal) (oneMaxTarget n) t x ≤
      harmonicLevelRuntime (oneMaxImprovementRate n p) oneMaxPotential x := by
  exact oneMax_finiteHorizonRuntimeBound hp0 hp1 t x

/--
The elementary improving events used in the classical fitness-level proof have
exact total weight `k * p * (1-p)^(n-1)`, where `k` is the number of zero bits.
-/
theorem oneMax_simple_improvement_weight {n : ℕ} (p : ℝ) (x : BitString n) :
    singleZeroFlipWeight p x =
      (oneMaxPotential x : ℝ) * (p * (1 - p) ^ (n - 1)) := by
  simpa [oneMaxPotential] using singleZeroFlipWeight_eq p x

/-- Standard `(1+1)`-EA mutation rate is positive in every positive dimension. -/
theorem standardMutationRate_pos {n : ℕ} (hn : 0 < n) :
    0 < standardMutationRate n := by
  rw [standardMutationRate, ite_eq_right (Nat.ne_of_gt hn)]
  exact inv_pos.mpr (by exact_mod_cast hn)

/-- Standard mutation rate is strictly below one from dimension two onward. -/
theorem standardMutationRate_lt_one {n : ℕ} (hn : 2 ≤ n) :
    standardMutationRate n < 1 := by
  rw [standardMutationRate, ite_eq_right (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn))]
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  exact inv_lt_one_of_one_lt₀ hn1

/-- The reciprocal single-bit progress rate at `p = 1/n` is at most `e n`. -/
theorem standardImprovementRate_inv_le_en {n : ℕ} (hn : 2 ≤ n) :
    (oneMaxImprovementRate n (standardMutationRate n))⁻¹ ≤
      Real.exp 1 * (n : ℝ) := by
  let m : ℕ := n - 1
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hm_succ : m + 1 = n := by
    dsimp [m]
    omega
  have hnreal_ne : (n : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hnpos)
  have hmreal_ne : (m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hmpos)
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  have hmcast : (m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm_succ
  have hbase : 1 - (n : ℝ)⁻¹ = (m : ℝ) / (n : ℝ) := by
    field_simp [hnreal_ne]
    linarith
  have hratio : (n : ℝ) / (m : ℝ) = 1 + (m : ℝ)⁻¹ := by
    field_simp [hmreal_ne]
    linarith
  have hrate :
      (oneMaxImprovementRate n (standardMutationRate n))⁻¹ =
        (n : ℝ) * (1 + (m : ℝ)⁻¹) ^ m := by
    unfold oneMaxImprovementRate
    rw [hp, show n - 1 = m by rfl, hbase]
    rw [mul_inv_rev, ← inv_pow, inv_inv, inv_div, hratio]
    ring
  rw [hrate]
  calc
    (n : ℝ) * (1 + (m : ℝ)⁻¹) ^ m ≤
        (n : ℝ) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_add_inv_pow_le_exp (n := m))
        (Nat.cast_nonneg n)
    _ = Real.exp 1 * (n : ℝ) := by ring

/-- Standard-rate OneMax already inherits the generic finite-horizon theorem. -/
theorem oneMax_standard_finiteHorizonRuntimeBound
    {n : ℕ} (hn : 2 ≤ n) :
    HasUniformFiniteHorizonRuntimeBound
      (onePlusOneTransition (standardMutationRate n) oneMaxReal)
      (oneMaxTarget n)
      (harmonicLevelRuntime
        (oneMaxImprovementRate n (standardMutationRate n)) oneMaxPotential) := by
  exact oneMax_finiteHorizonRuntimeBound
    (standardMutationRate_pos (by omega))
    (standardMutationRate_lt_one hn)

/-- The classical `e n H_n` upper-bound expression. -/
noncomputable def oneMaxClassicalRuntimeBound (n : ℕ) : ℝ :=
  harmonicRuntimeBound (Real.exp 1) n

/--
If the reciprocal single-bit progress rate is at most `e n`, the finite-horizon
OneMax theorem immediately yields the classical `e n H_n` bound.
-/
theorem oneMax_finiteHorizonRuntime_le_classical_of_rate_bound
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hcoef : (oneMaxImprovementRate n p)⁻¹ ≤ Real.exp 1 * (n : ℝ))
    (t : ℕ) (x : BitString n) :
    finiteHorizonRuntime (onePlusOneTransition p oneMaxReal) (oneMaxTarget n) t x ≤
      oneMaxClassicalRuntimeBound n := by
  have hbase := oneMax_finiteHorizonRuntime_le_harmonic hp0 hp1 t x
  have hpot : oneMaxPotential x ≤ n := by
    simpa [oneMaxPotential] using zeroCount_le x
  have hH : harmonicReal (oneMaxPotential x) ≤ harmonicReal n :=
    harmonicReal_mono hpot
  have hrateInv : 0 ≤ (oneMaxImprovementRate n p)⁻¹ :=
    inv_nonneg.mpr (oneMaxImprovementRate_pos hp0 hp1).le
  calc
    finiteHorizonRuntime (onePlusOneTransition p oneMaxReal) (oneMaxTarget n) t x ≤
        harmonicLevelRuntime (oneMaxImprovementRate n p) oneMaxPotential x := hbase
    _ ≤ (oneMaxImprovementRate n p)⁻¹ * harmonicReal n := by
      unfold harmonicLevelRuntime
      exact mul_le_mul_of_nonneg_left hH hrateInv
    _ ≤ (Real.exp 1 * (n : ℝ)) * harmonicReal n :=
      mul_le_mul_of_nonneg_right hcoef (harmonicReal_nonneg n)
    _ = oneMaxClassicalRuntimeBound n := by
      simp [oneMaxClassicalRuntimeBound, harmonicRuntimeBound, harmonicReal, mul_assoc]

/-- The standard-rate truncated runtime is bounded by `e n H_n`. -/
theorem oneMax_standard_finiteHorizonRuntime_le_classical
    {n : ℕ} (hn : 2 ≤ n) (t : ℕ) (x : BitString n) :
    finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) oneMaxReal)
        (oneMaxTarget n) t x ≤
      oneMaxClassicalRuntimeBound n := by
  exact oneMax_finiteHorizonRuntime_le_classical_of_rate_bound
    (standardMutationRate_pos (by omega))
    (standardMutationRate_lt_one hn)
    (standardImprovementRate_inv_le_en hn)
    t x

/-- The harmonic endpoint already implies the standard `e n (1 + log n)` asymptotic bound. -/
theorem oneMaxClassicalRuntimeBound_le_log (n : ℕ) :
    oneMaxClassicalRuntimeBound n ≤
      Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  unfold oneMaxClassicalRuntimeBound
  exact harmonicRuntimeBound_le_log (Real.exp 1) (Real.exp_pos 1).le n

/-- Fully instantiated standard-rate finite-horizon `e n (1 + log n)` bound. -/
theorem oneMax_standard_finiteHorizonRuntime_le_log
    {n : ℕ} (hn : 2 ≤ n) (t : ℕ) (x : BitString n) :
    finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) oneMaxReal)
        (oneMaxTarget n) t x ≤
      Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  exact (oneMax_standard_finiteHorizonRuntime_le_classical hn t x).trans
    (oneMaxClassicalRuntimeBound_le_log n)

/-- The unrestricted runtime supremum inherits the standard `e n H_n` bound. -/
theorem oneMax_standard_runtimeSup_le_classical
    {n : ℕ} (hn : 2 ≤ n) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) oneMaxReal)
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (oneMaxClassicalRuntimeBound n) := by
  apply runtimeSup_le_of_uniform_bound
  intro t y
  exact oneMax_standard_finiteHorizonRuntime_le_classical hn t y

/-- The unrestricted runtime supremum also satisfies the familiar logarithmic bound. -/
theorem oneMax_standard_runtimeSup_le_log
    {n : ℕ} (hn : 2 ≤ n) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) oneMaxReal)
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  exact (oneMax_standard_runtimeSup_le_classical hn x).trans
    (ENNReal.ofReal_le_ofReal (oneMaxClassicalRuntimeBound_le_log n))

/-- The standard-rate OneMax unrestricted runtime supremum is finite. -/
theorem oneMax_standard_runtimeSup_ne_top
    {n : ℕ} (hn : 2 ≤ n) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) oneMaxReal)
        (oneMaxTarget n) x ≠ ⊤ := by
  have hle := oneMax_standard_runtimeSup_le_classical hn x
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Once `E[T] ≤ e n H_n` is available, this closes the familiar `O(n log n)` estimate. -/
theorem oneMax_runtime_log_endpoint (expectedRuntime : ℝ) (n : ℕ)
    (hRuntime : expectedRuntime ≤ oneMaxClassicalRuntimeBound n) :
    expectedRuntime ≤ Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  exact hRuntime.trans (oneMaxClassicalRuntimeBound_le_log n)

end ECRuntime
