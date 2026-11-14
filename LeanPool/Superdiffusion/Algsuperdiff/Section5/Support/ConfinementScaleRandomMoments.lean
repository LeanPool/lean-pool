/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConfinementScaleMinimality

/-!
# ConfinementScaleRandomMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Moments at the random confinement scale

The displacement bounds are stated at the random confinement scale `m_t`, so
every quantity that enters them is evaluated at a random index.  Two such
quantities need moment bounds: the scale `3^{m_t}` itself, and the error random
variable of the renormalization theorem read at that scale.  Neither is a
moment of any single deterministic object, and this file supplies both, by
summing over the level sets of the random index.

The mechanism is the same in both cases.  Writing `m_0` for the deterministic
lower bound `⌊log₃ L⌋` of the confinement scale, the level sets
`{m_t = m_0 + k}`, `k ∈ ℕ`, cover the sample space up to a null set, they are
disjoint, and the probability of the `k`-th one decays like `3^{-2pk}` by the
minimality estimate.  For the scale itself the value on the level set is the
deterministic number `3^{m_0+k}`, so the integral is a geometric series with
ratio `3^{-p}`.  For a family indexed by the scales, the level set is coupled to
the value by the Cauchy--Schwarz inequality, which spends the moment of order
`2p` of the family and half of the decay of the level set; the remaining half is
again a geometric series with ratio `3^{-p}`.

Both bounds therefore need the moments of the displacement scales at the
exponent `2p` rather than at `p`: halving the admissible range of exponents is
the price of the random index, and it changes only the constant in front of the
range `p ≤ C^{-1} γ^{-1} |log γ|^{-6}`.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. Two arithmetic steps -/

private theorem pow_rpow_comm' (x : ℝ≥0∞) (j : ℕ) (p : ℝ) : (x ^ j) ^ p = (x ^ p) ^ j := by
  rw [← ENNReal.rpow_natCast x j, ← ENNReal.rpow_natCast (x ^ p) j, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  ring_nf

private theorem ofReal_mul_rpow_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal a ^ p * ENNReal.ofReal b ^ (2 * p) = ENNReal.ofReal (a * b ^ (2 : ℕ)) ^ p := by
  rw [ENNReal.ofReal_mul ha, ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.ofReal_pow hb,
    ← ENNReal.rpow_natCast (ENNReal.ofReal b) 2, ← ENNReal.rpow_mul]
  norm_num

private theorem ofReal_mul_rpow_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ} (hp : 0 ≤ p)
    (k : ℕ) :
    ENNReal.ofReal (a * b ^ k) ^ p = ENNReal.ofReal a ^ p * (ENNReal.ofReal b ^ p) ^ k := by
  rw [ENNReal.ofReal_mul ha, ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.ofReal_pow hb,
    pow_rpow_comm']

/-- The geometric series of ratio `3^{-p}`, at every exponent `p ≥ 1`. -/
private theorem geometric_third_le {p : ℝ} (hp : 1 ≤ p) :
    (1 - ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p)⁻¹ ≤ ENNReal.ofReal (3 / 2) := by
  have hle : ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p ≤ ENNReal.ofReal ((3 : ℝ)⁻¹) := by
    calc ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p ≤ ENNReal.ofReal ((3 : ℝ)⁻¹) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (by rw [ENNReal.ofReal_le_one]; norm_num) hp
      _ = ENNReal.ofReal ((3 : ℝ)⁻¹) := ENNReal.rpow_one _
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ((3 : ℝ)⁻¹) ≤ 1 - ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p :=
    tsub_le_tsub_left hle 1
  refine (ENNReal.inv_le_inv.mpr hsub).trans (le_of_eq ?_)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ## 2. The level sets of the random scale -/

/-- The level sets of a measurable integer-valued function bounded below almost
surely decompose every integral against it. -/
private theorem lintegral_eq_tsum_levelSet (mu : Measure Omega) {m : Omega → ℤ}
    (hmmeas : Measurable m) {m0 : ℤ} (hm0 : ∀ᵐ omega ∂mu, m0 ≤ m omega) (g : Omega → ℝ≥0∞) :
    (∫⁻ omega, g omega ∂mu) =
      ∑' k : ℕ, ∫⁻ omega in {omega | m omega = m0 + (k : ℤ)}, g omega ∂mu := by
  have hA : ∀ k : ℕ, MeasurableSet {omega | m omega = m0 + (k : ℤ)} := fun k =>
    hmmeas (measurableSet_singleton (m0 + (k : ℤ)))
  have hd : Pairwise (Function.onFun Disjoint fun k : ℕ => {omega | m omega = m0 + (k : ℤ)}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun omega hi hj => ?_
    simp only [Set.mem_ofPred_eq] at hi hj
    exact hij (by omega)
  have hcover : (⋃ k : ℕ, {omega | m omega = m0 + (k : ℤ)}) =ᵐ[mu] (Set.univ : Set Omega) := by
    rw [MeasureTheory.ae_eq_univ]
    refine measure_mono_null (fun omega homega => ?_) (ae_iff.mp hm0)
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at homega
    simp only [Set.mem_ofPred_eq]
    intro hle
    exact homega (m omega - m0).toNat (by omega)
  rw [← MeasureTheory.setLIntegral_univ g, ← MeasureTheory.setLIntegral_congr hcover,
    MeasureTheory.lintegral_iUnion hA hd]

/-- The Cauchy--Schwarz bound for an integral over a set: half the moment of
order `2p` and half the measure of the set. -/
private theorem setLIntegral_rpow_le (mu : Measure Omega) {f : Omega → ℝ≥0∞}
    (hf : Measurable f) {A : Set Omega} (hA : MeasurableSet A) (p : ℝ) :
    (∫⁻ omega in A, f omega ^ p ∂mu) ≤
      (∫⁻ omega, f omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) * mu A ^ (1 / 2 : ℝ) := by
  have hprod : (∫⁻ omega in A, f omega ^ p ∂mu) =
      ∫⁻ omega, ((fun x => f x ^ p) * A.indicator (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun omega => ?_
    by_cases hmem : omega ∈ A <;> simp [hmem]
  have hg : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hsq : ∀ omega, (A.indicator (fun _ => (1 : ℝ≥0∞)) omega) ^ (2 : ℝ) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) omega := by
    intro omega
    by_cases hmem : omega ∈ A
    · simp [hmem]
    · simp [hmem]
  have hfsq : ∀ omega, ((fun x => f x ^ p) omega) ^ (2 : ℝ) = f omega ^ (2 * p) := by
    intro omega
    rw [← ENNReal.rpow_mul]
    ring_nf
  refine hprod.le.trans ?_
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq mu Real.HolderConjugate.two_two
    (hf.pow_const p).aemeasurable hg.aemeasurable).trans (le_of_eq ?_)
  congr 1
  · rw [one_div]
    congr 1
    exact lintegral_congr fun omega => hfsq omega
  · rw [one_div]
    congr 1
    rw [lintegral_congr fun omega => hsq omega, lintegral_indicator_const hA (1 : ℝ≥0∞),
      one_mul]

/-! ## 3. The moments of the confinement scale -/

/-- **The moments of the confinement scale.**  Minimality bounds `3^{m_t}` by a
single displacement scale, and summing the level sets of the random index
against a uniform moment bound of order `2p` for the displacement scales gives a
moment bound of order `p` for `3^{m_t}`, proportional to the deterministic
factor `L`. -/
theorem lintegral_three_zpow_isConfinementScale_rpow_le (mu : Measure Omega)
    [IsProbabilityMeasure mu] {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k))
    (hSnn : ∀ k omega, 0 ≤ S k omega) {L : ℝ} (hL : 0 < L) {m : Omega → ℤ}
    (hmmeas : Measurable m)
    (hm : ∀ᵐ omega ∂mu,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L (m omega))
    {C p : ℝ} (hC : 1 ≤ C) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal C ^ (2 * p)) :
    (∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu) ≤
      ENNReal.ofReal (2187 / 2 * C ^ (2 : ℕ) * L) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  set m0 : ℤ := Int.log 3 L with hm0def
  have hm0 : ∀ᵐ omega ∂mu, m0 ≤ m omega := by
    filter_upwards [hm] with omega homega
    exact intLog_le_of_isConfinementScale hL homega
  have hlow : (3 : ℝ) ^ m0 ≤ L := by
    rw [hm0def]
    simpa using Int.zpow_log_le_self (b := 3) (r := L) (by norm_num) hL
  have hm0pos : (0 : ℝ) < (3 : ℝ) ^ m0 := zpow_pos (by norm_num) _
  have hA : ∀ k : ℕ, MeasurableSet {omega | m omega = m0 + (k : ℤ)} := fun k =>
    hmmeas (measurableSet_singleton (m0 + (k : ℤ)))
  have hlev := fun k : ℕ =>
    measure_isConfinementScale_eq_le mu hmeas hSnn hL hm hC (by positivity) hmom k
  -- the value of the integrand on each level set
  have hterm : ∀ k : ℕ,
      (∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu) ≤
        ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p *
          (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k := by
    intro k
    have hval : (∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
        ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu) =
        ENNReal.ofReal ((3 : ℝ) ^ (m0 + (k : ℤ))) ^ p * mu {omega | m omega = m0 + (k : ℤ)} := by
      rw [setLIntegral_congr_fun (hA k)
        (fun omega homega => by rw [(homega : m omega = m0 + (k : ℤ))]), setLIntegral_const]
    have hlk := hlev k
    -- the deterministic identity behind the geometric series
    have hupos : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
    have hmk : (3 : ℝ) ^ (m0 + (k : ℤ)) = (3 : ℝ) ^ m0 * (3 : ℝ) ^ (k : ℤ) :=
      zpow_add₀ (by norm_num) _ _
    have hu : (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) = 27 / (3 : ℝ) ^ (k : ℤ) := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    have hinv : ((3 : ℝ)⁻¹) ^ k = ((3 : ℝ) ^ (k : ℤ))⁻¹ := by
      rw [inv_pow, ← zpow_natCast (3 : ℝ) k]
    have hkey : (3 : ℝ) ^ (m0 + (k : ℤ)) * (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ (2 : ℕ) =
        729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0 * ((3 : ℝ)⁻¹) ^ k := by
      rw [hmk, hu, hinv, mul_pow]
      field_simp
      ring
    calc (∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu)
        = ENNReal.ofReal ((3 : ℝ) ^ (m0 + (k : ℤ))) ^ p *
            mu {omega | m omega = m0 + (k : ℤ)} := hval
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (m0 + (k : ℤ))) ^ p *
            ENNReal.ofReal (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ (2 * p) := by gcongr
      _ = ENNReal.ofReal ((3 : ℝ) ^ (m0 + (k : ℤ)) *
            (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ (2 : ℕ)) ^ p :=
          ofReal_mul_rpow_two (by positivity) (by positivity) hp0.le
      _ = ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0 * ((3 : ℝ)⁻¹) ^ k) ^ p := by
          rw [hkey]
      _ = ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p *
            (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k :=
          ofReal_mul_rpow_pow (by positivity) (by norm_num) hp0.le k
  calc (∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu)
      = ∑' k : ℕ, ∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal ((3 : ℝ) ^ (m omega)) ^ p ∂mu :=
        lintegral_eq_tsum_levelSet mu hmmeas hm0 _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p *
          (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p *
          (1 - ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p * ENNReal.ofReal (3 / 2) := by
        gcongr
        exact geometric_third_le hp
    _ ≤ ENNReal.ofReal (729 * C ^ (2 : ℕ) * (3 : ℝ) ^ m0) ^ p * ENNReal.ofReal (3 / 2) ^ p := by
        gcongr
        calc ENNReal.ofReal (3 / 2 : ℝ) = ENNReal.ofReal (3 / 2 : ℝ) ^ (1 : ℝ) :=
              (ENNReal.rpow_one _).symm
          _ ≤ ENNReal.ofReal (3 / 2 : ℝ) ^ p :=
              ENNReal.rpow_le_rpow_of_exponent_le (by rw [ENNReal.one_le_ofReal]; norm_num) hp
    _ ≤ ENNReal.ofReal (2187 / 2 * C ^ (2 : ℕ) * L) ^ p := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0.le
        nlinarith only [hlow, hm0pos, hCpos, sq_nonneg C, hL]

/-! ## 4. Moments of a family at the random scale -/

/-- **The moments of a family at the confinement scale.**  A family of
nonnegative random variables indexed by the scales, with a moment bound of order
`2p` uniform in the scale, has at the random confinement scale a moment bound of
order `p` with the same profile, at the cost of an explicit constant. -/
theorem lintegral_atConfinementScale_rpow_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) (hSnn : ∀ k omega, 0 ≤ S k omega)
    {L : ℝ} (hL : 0 < L) {m : Omega → ℤ} (hmmeas : Measurable m)
    (hm : ∀ᵐ omega ∂mu,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L (m omega))
    {C p : ℝ} (hC : 1 ≤ C) (hp : 1 ≤ p)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal C ^ (2 * p))
    {F : ℤ → Omega → ℝ} (hFmeas : ∀ n, Measurable (F n)) {D : ℝ} (hD : 0 ≤ D)
    (hFmom : ∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (F n omega) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal D ^ (2 * p)) :
    (∫⁻ omega, ENNReal.ofReal (F (m omega) omega) ^ p ∂mu) ≤
      ENNReal.ofReal (81 / 2 * C * D) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  set m0 : ℤ := Int.log 3 L with hm0def
  have hm0 : ∀ᵐ omega ∂mu, m0 ≤ m omega := by
    filter_upwards [hm] with omega homega
    exact intLog_le_of_isConfinementScale hL homega
  have hA : ∀ k : ℕ, MeasurableSet {omega | m omega = m0 + (k : ℤ)} := fun k =>
    hmmeas (measurableSet_singleton (m0 + (k : ℤ)))
  have hlev := fun k : ℕ =>
    measure_isConfinementScale_eq_le mu hmeas hSnn hL hm hC (by positivity) hmom k
  have hterm : ∀ k : ℕ,
      (∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal (F (m omega) omega) ^ p ∂mu) ≤
        ENNReal.ofReal (27 * C * D) ^ p * (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k := by
    intro k
    have hval : (∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
        ENNReal.ofReal (F (m omega) omega) ^ p ∂mu) =
        ∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal (F (m0 + (k : ℤ)) omega) ^ p ∂mu :=
      setLIntegral_congr_fun (hA k)
        (fun omega homega => by rw [(homega : m omega = m0 + (k : ℤ))])
    rw [hval]
    have hcs := setLIntegral_rpow_le mu
      (ENNReal.measurable_ofReal.comp (hFmeas (m0 + (k : ℤ)))) (hA k) p
    refine hcs.trans ?_
    have hfirst : (∫⁻ omega, ENNReal.ofReal (F (m0 + (k : ℤ)) omega) ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal D ^ p := by
      refine (ENNReal.rpow_le_rpow (hFmom (m0 + (k : ℤ))) (by norm_num)).trans (le_of_eq ?_)
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hsecond : (mu {omega | m omega = m0 + (k : ℤ)}) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ p := by
      refine (ENNReal.rpow_le_rpow (hlev k) (by norm_num)).trans (le_of_eq ?_)
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    refine le_trans (mul_le_mul' hfirst hsecond) (le_of_eq ?_)
    have hupos : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
    have hu : (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) = 27 / (3 : ℝ) ^ (k : ℤ) := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    have hinv : ((3 : ℝ)⁻¹) ^ k = ((3 : ℝ) ^ (k : ℤ))⁻¹ := by
      rw [inv_pow, ← zpow_natCast (3 : ℝ) k]
    have hkey : D * (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) = 27 * C * D * ((3 : ℝ)⁻¹) ^ k := by
      rw [hu, hinv]
      field_simp
    calc ENNReal.ofReal D ^ p * ENNReal.ofReal (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ p
        = ENNReal.ofReal (D * (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)))) ^ p := by
          rw [ENNReal.ofReal_mul hD, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      _ = ENNReal.ofReal (27 * C * D * ((3 : ℝ)⁻¹) ^ k) ^ p := by rw [hkey]
      _ = ENNReal.ofReal (27 * C * D) ^ p * (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k :=
          ofReal_mul_rpow_pow (by positivity) (by norm_num) hp0.le k
  calc (∫⁻ omega, ENNReal.ofReal (F (m omega) omega) ^ p ∂mu)
      = ∑' k : ℕ, ∫⁻ omega in {omega | m omega = m0 + (k : ℤ)},
          ENNReal.ofReal (F (m omega) omega) ^ p ∂mu :=
        lintegral_eq_tsum_levelSet mu hmmeas hm0 _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (27 * C * D) ^ p * (ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p) ^ k :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (27 * C * D) ^ p * (1 - ENNReal.ofReal ((3 : ℝ)⁻¹) ^ p)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (27 * C * D) ^ p * ENNReal.ofReal (3 / 2) := by
        gcongr
        exact geometric_third_le hp
    _ ≤ ENNReal.ofReal (27 * C * D) ^ p * ENNReal.ofReal (3 / 2) ^ p := by
        gcongr
        calc ENNReal.ofReal (3 / 2 : ℝ) = ENNReal.ofReal (3 / 2 : ℝ) ^ (1 : ℝ) :=
              (ENNReal.rpow_one _).symm
          _ ≤ ENNReal.ofReal (3 / 2 : ℝ) ^ p :=
              ENNReal.rpow_le_rpow_of_exponent_le (by rw [ENNReal.one_le_ofReal]; norm_num) hp
    _ = ENNReal.ofReal (81 / 2 * C * D) ^ p := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end

end Algsuperdiff.Section5.Support
