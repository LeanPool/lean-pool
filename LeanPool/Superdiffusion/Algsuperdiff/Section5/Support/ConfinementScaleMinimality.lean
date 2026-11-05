/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConfinementScaleMoments

/-!
# ConfinementScaleMinimality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Minimality at the confinement scale, and the level sets of the random scale

The confinement scale `m_t` is the least scale `n` with `L (1 + S_n) ≤ 3^n`.
Its defining inequality bounds the widened scale from above; what bounds the
confinement scale itself from above is *minimality*, the failure of the same
inequality one scale lower.  This file turns that failure into a usable
estimate and then into a bound on the probability of each level set of the
random scale.

The first step is the recursion

`S_{n-1} ≤ S_{n-1} + (1/9) S_n`,

which holds because the widening weight `3^{-2(k-n)}` loses exactly a factor of
nine when the base scale drops by one.  Combining it with the defining
inequality at `m_t` itself, which bounds `L S_{m_t}` by `3^{m_t}`, the failure
one scale lower reads

`3^{m_t - 1} < L (1 + S_{m_t-1} + (1/9) S_{m_t}) ≤ L (1 + S_{m_t-1}) + (1/9) 3^{m_t}`,

and hence `3^{m_t} ≤ (9/2) L (1 + S_{m_t-1})`: the confinement scale is
controlled by a *single* displacement scale, not by the widened supremum.

The scale index is random, so this is not yet a moment bound.  What it gives is
a bound on the probability of the level set `{m_t = n}`: on that event a single
displacement scale is at least `(2/27) 3^{n - m_0} - 1`, where `3^{m_0} ≤ L` is
the deterministic lower bound for the scale, and Chebyshev's inequality at a
uniform moment of the displacement scales turns this into a geometric decay in
`n - m_0`.  That decay is what makes the moments of `3^{m_t}` and of any family
indexed by the random scale summable.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. The recursion for the widened scale -/

/-- **The widening recursion.**  Lowering the base scale by one adds the scale at
the new index and divides the previous widened scale by nine. -/
theorem widenedScale_pred_le (S : ℤ → ℝ) (n : ℤ) :
    widenedScale S (n - 1) ≤
      ENNReal.ofReal (S (n - 1)) + ENNReal.ofReal (9 : ℝ)⁻¹ * widenedScale S n := by
  rw [widenedScale_eq_iSup_nat]
  refine iSup_le fun j => ?_
  cases j with
  | zero =>
      have hval : S (n - 1 + ((0 : ℕ) : ℤ)) * (3 : ℝ) ^ (-2 * ((0 : ℕ) : ℤ)) = S (n - 1) := by
        norm_num
      rw [hval]
      exact le_self_add
  | succ i =>
      have hidx : n - 1 + ((i + 1 : ℕ) : ℤ) = n + (i : ℤ) := by push_cast; ring
      have hexp : (-2 : ℤ) * ((i + 1 : ℕ) : ℤ) = -2 * (i : ℤ) + -2 := by push_cast; ring
      have hval : S (n - 1 + ((i + 1 : ℕ) : ℤ)) * (3 : ℝ) ^ (-2 * ((i + 1 : ℕ) : ℤ)) =
          (9 : ℝ)⁻¹ * (S (n + (i : ℤ)) * (3 : ℝ) ^ (-2 * (i : ℤ))) := by
        rw [hidx, hexp, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring
      rw [hval, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (9 : ℝ)⁻¹)]
      refine le_add_self.trans' ?_
      gcongr
      rw [widenedScale_eq_iSup_nat]
      exact le_iSup (fun j : ℕ => ENNReal.ofReal (S (n + j) * (3 : ℝ) ^ (-2 * (j : ℤ)))) i

/-! ## 2. Minimality -/

/-- **Minimality at the confinement scale.**  Since the scale one below the
confinement scale fails the defining inequality, and the widening recursion
reduces the widened scale there to the single scale `S_{m-1}` plus a ninth of the
widened scale at `m`, the confinement scale obeys
`3^m ≤ (9/2) L (1 + S_{m-1})`. -/
theorem three_zpow_le_of_isConfinementScale {S : ℤ → ℝ} (hSnn : ∀ k, 0 ≤ S k) {L : ℝ}
    (hL : 0 < L) {m : ℤ} (hm : IsConfinementScale (fun n => widenedScale S n) L m) :
    (3 : ℝ) ^ m ≤ 9 / 2 * L * (1 + S (m - 1)) := by
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have h3m1 : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) (m - 1)
  have hdef : ENNReal.ofReal L * (1 + widenedScale S m) ≤ ENNReal.ofReal ((3 : ℝ) ^ m) := hm.1
  have hLne : ENNReal.ofReal L ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hL
  have hfin : widenedScale S m ≠ ⊤ := by
    intro htop
    rw [htop, add_top, ENNReal.mul_top hLne] at hdef
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hdef)
  set sR : ℝ := (widenedScale S m).toReal with hsRdef
  have hsRnn : 0 ≤ sR := ENNReal.toReal_nonneg
  have hsR : ENNReal.ofReal sR = widenedScale S m := ENNReal.ofReal_toReal hfin
  have hreal : L * (1 + sR) ≤ (3 : ℝ) ^ m := by
    refine (ENNReal.ofReal_le_ofReal_iff h3m.le).mp ?_
    rw [ENNReal.ofReal_mul hL.le, ENNReal.ofReal_add zero_le_one hsRnn, ENNReal.ofReal_one, hsR]
    exact hdef
  have hnotmem : (m - 1) ∉ confinementSet (fun n => widenedScale S n) L := by
    intro hmem
    have hle := hm.2 hmem
    omega
  simp only [confinementSet, Set.mem_ofPred_eq, not_le] at hnotmem
  have hpred : widenedScale S (m - 1) ≤ ENNReal.ofReal (S (m - 1) + (9 : ℝ)⁻¹ * sR) := by
    refine (widenedScale_pred_le S m).trans (le_of_eq ?_)
    rw [← hsR, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (9 : ℝ)⁻¹),
      ← ENNReal.ofReal_add (hSnn (m - 1)) (by positivity)]
  have hreal2 : (3 : ℝ) ^ (m - 1) < L * (1 + (S (m - 1) + (9 : ℝ)⁻¹ * sR)) := by
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h3m1.le).mp ?_
    refine lt_of_lt_of_le hnotmem ?_
    rw [ENNReal.ofReal_mul hL.le,
      ENNReal.ofReal_add zero_le_one (add_nonneg (hSnn (m - 1)) (by positivity)),
      ENNReal.ofReal_one]
    gcongr
  have h3 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hLs : L * sR ≤ (3 : ℝ) ^ m := by nlinarith only [hreal, hL, hsRnn]
  linarith only [hreal2, h3, hLs]

/-! ## 3. Measurability of the confinement scale -/

/-- The defining set of the confinement scale is measurable at every fixed
scale. -/
theorem measurableSet_mem_confinementSet {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k))
    (L : ℝ) (n : ℤ) :
    MeasurableSet
      {omega | n ∈ confinementSet (fun j => widenedScale (fun k => S k omega) j) L} := by
  simp only [confinementSet, Set.mem_ofPred_eq]
  exact measurableSet_le
    (measurable_const.mul (measurable_const.add (measurable_widenedScale hmeas n)))
    measurable_const

/-! ## 4. The level sets of the confinement scale -/

/-- The deterministic lower bound for the confinement scale. -/
theorem intLog_le_of_isConfinementScale {S : ℤ → ℝ} {L : ℝ} (hL : 0 < L) {m : ℤ}
    (hm : IsConfinementScale (fun n => widenedScale S n) L m) : Int.log 3 L ≤ m :=
  int_log_le_of_mem_confinementSet hL hm.1

/-- **The probability of a level set of the confinement scale.**  Writing the
scale as `m_0 + k` with `3^{m_0} ≤ L < 3^{m_0+1}`, on the event `{m_t = m_0 + k}`
a single displacement scale is at least `3^{k-3}`, so a uniform moment bound of
order `q` for the displacement scales gives a geometric bound of ratio `3^{-q}`
for the probability of the event. -/
theorem measure_isConfinementScale_eq_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) (hSnn : ∀ k omega, 0 ≤ S k omega)
    {L : ℝ} (hL : 0 < L) {m : Omega → ℤ}
    (hm : ∀ᵐ omega ∂mu,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L (m omega))
    {C q : ℝ} (hC : 1 ≤ C) (hq : 0 < q)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ q ∂mu) ≤ ENNReal.ofReal C ^ q)
    (k : ℕ) :
    mu {omega | m omega = Int.log 3 L + (k : ℤ)} ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ q := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hzp : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) := zpow_pos (by norm_num) _
  by_cases hk : k ≤ 2
  · -- the bound exceeds one, so the trivial bound suffices
    have hge : (1 : ℝ) ≤ C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) := by
      have h1 : (3 : ℝ) ^ (1 : ℤ) ≤ (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) := by
        refine zpow_le_zpow_right₀ (by norm_num) ?_
        omega
      have h3 : (3 : ℝ) ^ (1 : ℤ) = 3 := by norm_num
      nlinarith only [h1, h3, hC, hzp]
    calc mu {omega | m omega = Int.log 3 L + (k : ℤ)} ≤ 1 := prob_le_one
      _ = (1 : ℝ≥0∞) ^ q := (ENNReal.one_rpow q).symm
      _ ≤ ENNReal.ofReal (C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ))) ^ q :=
          ENNReal.rpow_le_rpow (by rwa [ENNReal.one_le_ofReal]) hq.le
  · push Not at hk
    set m0 : ℤ := Int.log 3 L with hm0
    have hlow : (3 : ℝ) ^ m0 ≤ L := by
      rw [hm0]
      simpa using Int.zpow_log_le_self (b := 3) (r := L) (by norm_num) hL
    have hupp : L < (3 : ℝ) ^ (m0 + 1) := by
      rw [hm0]
      simpa using Int.lt_zpow_succ_log_self (b := 3) (r := L) (by norm_num)
    set lam : ℝ := (3 : ℝ) ^ ((k : ℤ) - 3) with hlamdef
    have hlampos : (0 : ℝ) < lam := zpow_pos (by norm_num) _
    -- on the level set a single displacement scale is large
    have hsub : mu {omega | m omega = m0 + (k : ℤ)} ≤
        mu {omega | ENNReal.ofReal lam ^ q ≤
          ENNReal.ofReal (S (m0 + (k : ℤ) - 1) omega) ^ q} := by
      refine measure_mono_ae ?_
      filter_upwards [hm] with omega homega hmem
      have hmk : m omega = m0 + (k : ℤ) := hmem
      rw [hmk] at homega
      have hmin := three_zpow_le_of_isConfinementScale (fun j => hSnn j omega) hL homega
      have hsplit : (3 : ℝ) ^ (m0 + (k : ℤ)) = (3 : ℝ) ^ m0 * (3 : ℝ) ^ (k : ℤ) :=
        zpow_add₀ (by norm_num) _ _
      have h3k : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
      have hm0pos : (0 : ℝ) < (3 : ℝ) ^ m0 := zpow_pos (by norm_num) _
      have hsucc : (3 : ℝ) ^ (m0 + 1) = 3 * (3 : ℝ) ^ m0 := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        ring
      have h33 : (3 : ℝ) ^ (3 : ℤ) = 27 := by norm_num
      have hlam3 : lam * 27 = (3 : ℝ) ^ (k : ℤ) := by
        rw [hlamdef, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), h33]
        field_simp
      have h27 : (27 : ℝ) ≤ (3 : ℝ) ^ (k : ℤ) := by
        have hz : (3 : ℝ) ^ (3 : ℤ) ≤ (3 : ℝ) ^ (k : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        rw [h33] at hz
        exact hz
      have hlamge : (1 : ℝ) ≤ lam := by linarith only [h27, hlam3]
      have hSbig : lam ≤ S (m0 + (k : ℤ) - 1) omega := by
        have hL3 : L < 3 * (3 : ℝ) ^ m0 := by rw [hsucc] at hupp; exact hupp
        have hbig : L / 3 * (3 : ℝ) ^ (k : ℤ) < (3 : ℝ) ^ m0 * (3 : ℝ) ^ (k : ℤ) :=
          mul_lt_mul_of_pos_right (by linarith only [hL3]) h3k
        rw [hsplit] at hmin
        have hchain : L / 3 * (27 * lam) <
            9 / 2 * L * (1 + S (m0 + (k : ℤ) - 1) omega) := by
          rw [show (27 : ℝ) * lam = (3 : ℝ) ^ (k : ℤ) by linarith only [hlam3]]
          linarith only [hbig, hmin]
        have hmul : (9 / 2 * L) * (2 * lam) <
            (9 / 2 * L) * (1 + S (m0 + (k : ℤ) - 1) omega) := by
          linarith only [hchain]
        have h2lam : 2 * lam < 1 + S (m0 + (k : ℤ) - 1) omega :=
          lt_of_mul_lt_mul_left hmul (by linarith only [hL])
        linarith only [h2lam, hlamge]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hSbig) hq.le
    refine hsub.trans ?_
    have hlamne : ENNReal.ofReal lam ^ q ≠ 0 :=
      (ENNReal.rpow_pos (by simpa using hlampos) ENNReal.ofReal_ne_top).ne'
    have hlamtop : ENNReal.ofReal lam ^ q ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
    refine (meas_ge_le_lintegral_div
      (((ENNReal.measurable_ofReal.comp (hmeas (m0 + (k : ℤ) - 1))).pow_const q).aemeasurable)
      hlamne hlamtop).trans ?_
    refine (ENNReal.div_le_div_right (hmom (m0 + (k : ℤ) - 1)) _).trans (le_of_eq ?_)
    have hinvlam : (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) = lam⁻¹ := by
      rw [hlamdef, ← zpow_neg]
      congr 1
      omega
    have hquot : C * (3 : ℝ) ^ ((3 : ℤ) - (k : ℤ)) = C / lam := by
      rw [hinvlam, div_eq_mul_inv]
    rw [hquot, ENNReal.ofReal_rpow_of_nonneg hCpos.le hq.le,
      ENNReal.ofReal_rpow_of_nonneg hlampos.le hq.le,
      ← ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ C / lam) hq.le,
      Real.div_rpow hCpos.le hlampos.le]

/-! ## 5. The measurable choice of the confinement scale -/

open scoped Classical in
/-- **The confinement scale as a function of the sample.**  Where a confinement
scale exists it is unique, and this is that scale; where none exists the value
is `0`.

The value off the existence event is immaterial.  Every statement below about
`confinementScale` is either conditioned on the existence of a confinement scale
at the sample or holds almost surely, and the existence event has full measure
whenever the displacement scales have one uniform moment bound
(`ae_exists_isConfinementScale`); nothing in this development reads the value on
its complement. -/
def confinementScale (S : ℤ → Omega → ℝ) (L : ℝ) (omega : Omega) : ℤ :=
  if h : ∃ m : ℤ,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L m then
    h.choose
  else 0

omit [MeasurableSpace Omega] in
/-- Where a confinement scale exists, the chosen value is one. -/
theorem isConfinementScale_confinementScale {S : ℤ → Omega → ℝ} {L : ℝ} {omega : Omega}
    (h : ∃ m : ℤ, IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L m) :
    IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L
      (confinementScale S L omega) := by
  rw [confinementScale, dite_eq_left h]
  exact h.choose_spec

omit [MeasurableSpace Omega] in
/-- The chosen value is the confinement scale, wherever there is one. -/
theorem confinementScale_eq {S : ℤ → Omega → ℝ} {L : ℝ} {omega : Omega} {m : ℤ}
    (hm : IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L m) :
    confinementScale S L omega = m :=
  isConfinementScale_unique (isConfinementScale_confinementScale ⟨m, hm⟩) hm

omit [MeasurableSpace Omega] in
/-- Where no confinement scale exists the chosen value is `0`. -/
theorem confinementScale_eq_zero {S : ℤ → Omega → ℝ} {L : ℝ} {omega : Omega}
    (h : ¬ ∃ m : ℤ, IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L m) :
    confinementScale S L omega = 0 := by
  rw [confinementScale, dite_eq_right h]

/-- **The chosen confinement scale is measurable.**  Each level set is the event
that the scale is admissible intersected with countably many complements, and
the level set at `0` carries in addition the event that no scale is
admissible. -/
theorem measurable_confinementScale {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k))
    (L : ℝ) : Measurable (confinementScale S L) := by
  set A : ℤ → Set Omega := fun n =>
    {omega | n ∈ confinementSet (fun j => widenedScale (fun k => S k omega) j) L} ∩
      ⋂ j : ℤ, ⋂ _ : j < n,
        {omega | j ∈ confinementSet (fun i => widenedScale (fun k => S k omega) i) L}ᶜ
    with hAdef
  have hAmeas : ∀ n : ℤ, MeasurableSet (A n) := by
    intro n
    refine (measurableSet_mem_confinementSet hmeas L n).inter ?_
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (measurableSet_mem_confinementSet hmeas L j).compl
  have hmemA : ∀ (n : ℤ) (omega : Omega), omega ∈ A n ↔
      IsConfinementScale (fun j => widenedScale (fun k => S k omega) j) L n := by
    intro n omega
    simp only [hAdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hlt⟩
      refine ⟨hn, fun j hj => ?_⟩
      by_contra hcon
      exact hlt j (by omega) hj
    · rintro ⟨hn, hmin⟩
      refine ⟨hn, fun j hj hmem => ?_⟩
      have := hmin hmem
      omega
  refine measurable_to_countable' fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have hset : confinementScale S L ⁻¹' {(0 : ℤ)} = A 0 ∪ (⋃ j : ℤ, A j)ᶜ := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iUnion, not_exists]
      constructor
      · intro hval
        by_cases hex : ∃ m : ℤ,
            IsConfinementScale (fun j => widenedScale (fun k => S k omega) j) L m
        · exact Or.inl ((hmemA 0 omega).mpr (hval ▸ isConfinementScale_confinementScale hex))
        · exact Or.inr fun j hj => hex ⟨j, (hmemA j omega).mp hj⟩
      · rintro (hmem | hnone)
        · exact confinementScale_eq ((hmemA 0 omega).mp hmem)
        · exact confinementScale_eq_zero fun ⟨j, hj⟩ =>
            hnone j ((hmemA j omega).mpr hj)
    rw [hset]
    exact (hAmeas 0).union (MeasurableSet.iUnion hAmeas).compl
  · have hset : confinementScale S L ⁻¹' {n} = A n := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hval
        by_cases hex : ∃ m : ℤ,
            IsConfinementScale (fun j => widenedScale (fun k => S k omega) j) L m
        · exact (hmemA n omega).mpr (hval ▸ isConfinementScale_confinementScale hex)
        · exact absurd (hval.symm.trans (confinementScale_eq_zero hex)) hn
      · intro hmem
        exact confinementScale_eq ((hmemA n omega).mp hmem)
    rw [hset]
    exact hAmeas n

/-- **The chosen confinement scale is almost surely a confinement scale.**  One
uniform moment bound for the displacement scales makes the defining set almost
surely nonempty, and the infimum is then attained. -/
theorem ae_isConfinementScale_confinementScale (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) {C p L : ℝ}
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hL : 0 < L)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p ∂mu) ≤ ENNReal.ofReal C ^ p) :
    ∀ᵐ omega ∂mu,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L
        (confinementScale S L omega) := by
  filter_upwards [ae_exists_isConfinementScale mu hmeas hC hp hL hmom] with omega homega
  exact isConfinementScale_confinementScale homega

end

end Algsuperdiff.Section5.Support
