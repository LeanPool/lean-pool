/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.ZDensityLeg

/-!
# ZAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The witness `Z = max{Z¹, Z²}`, its measurability, and the conditional endpoint

ABK26, §4.2.  The witness is the random
minimal scale of the *disjunction* of the two bad-window families, which is
pointwise the maximum of the two legs (`Algsuperdiff.Probability.minimalScale`).
Three things then come for free, for **every** `omega` and with no
measurability side condition:

* both deterministic clauses (`clauses_of_zWitness_le`) — strictly stronger than
  the frozen statement's `∀ᵐ`;
* the tail at the common rate with the two prefactors added
  (`measure_tail_zWitness_le`).

## The conditional endpoint

`frozen_body_of_slots` is a conditional endpoint.  Its conditional
inputs are exactly

* `hZ1tail` — the `Z¹` leg's tail: Markov on
  `l.minimal.scale.sep` / `e.good.scale.kicking` plus the same centre union
  bound,
* `hZ1clause` — the `Z¹` leg's deterministic clause, and
* `hZ1measurable` — per-window measurability of the `Z¹` bad family.

Everything else in the proposition — the `Z²` leg end to end, the witness, the
measurability, the max tail, and both clauses — is unconditional.

## The `s`-exponent

Every public here reads the regime clause at `s⁹`, i.e. the frozen
`e.scale.sep.cond` with the single numeral `8` replaced by `9`.  See
`ZDensityLeg.lean`'s module docstring: the centre union bound of the `Z²` leg
needs `γ ≤ K(d)⁻¹ c⋆² s⁹ δ²` and the printed clause supplies only `s⁸`, a gap of
one power of the free parameter `s`.  This is the ONLY deviation from the
printed hypotheses; the tail rate, the tolerance `s * Real.sqrt delta`, the
window, the centre set and both displays are byte-identical to the frozen
statement.

## References

* ABK26, `p.minimal.scale.separation.sec4`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The witness -/

/-- **The proposition's random scale** `Z_m(s,δ) = max{Z¹, Z²}`, realised as the
random minimal scale of the disjunction of the two bad-window families. -/
noncomputable def zWitness (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop) : Cutoff.CutoffSample d → ℕ∞ :=
  Probability.minimalScaleEN
    (fun j omega => bad1 j omega ∨ badDensity M s delta hs m j omega)

/-- **The max assembly, as an identity.**  The witness *is* the pointwise maximum
of the two legs. -/
theorem zWitness_eq_max (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop) (omega : Cutoff.CutoffSample d) :
    zWitness M s delta hs m bad1 omega =
      max (Probability.minimalScaleEN bad1 omega)
        (Probability.minimalScaleEN (badDensity M s delta hs m) omega) :=
  Probability.minimalScaleEN_sup bad1 (badDensity M s delta hs m) omega

/-- **`Measurable Z`** (the survey's empty-sweep-1 clause).  It reduces to
per-window measurability of the two bad families; the density leg is proved in
`ZScores.lean`. -/
theorem measurable_zWitness (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop)
    (hb1 : ∀ j : ℕ, MeasurableSet {omega | bad1 j omega}) :
    Measurable (zWitness M s delta hs m bad1) := by
  refine Probability.measurable_minimalScaleEN fun j => ?_
  have hset : {omega : Cutoff.CutoffSample d |
        bad1 j omega ∨ badDensity M s delta hs m j omega}
      = {omega | bad1 j omega} ∪ {omega | badDensity M s delta hs m j omega} := rfl
  rw [hset]
  exact (hb1 j).union (measurableSet_badDensity M s delta hs m j)

/-- The tail event of the witness is the union of the two legs' tail events. -/
theorem tail_set_zWitness (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop) (N : ℕ) :
    {omega | (N : ℕ∞) ≤ zWitness M s delta hs m bad1 omega}
      = {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN bad1 omega} ∪
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badDensity M s delta hs m) omega} := by
  ext omega
  simp only [Set.mem_ofPred_eq, Set.mem_union, zWitness, Probability.minimalScaleEN_sup,
    le_max_iff]

/-! ## 2. Both deterministic clauses -/

/-- **The two deterministic halves, together.**  If the
witness is at most the window length `(m − n).toNat`, then *both* frozen displays
hold at the window `[n, m]`.  This holds for **every** `omega`: no almost-sure
qualifier, no finiteness, no measurability.  The density half is unconditional;
the Cesàro half is exactly `hZ1clause`. -/
theorem clauses_of_zWitness_le (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop)
    (hZ1clause : ∀ (omega : Cutoff.CutoffSample d) (n : ℤ), n ≤ m →
      Probability.minimalScaleEN bad1 omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
      cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta)
    (omega : Cutoff.CutoffSample d) (n : ℤ) (hnm : n ≤ m)
    (h : zWitness M s delta hs m bad1 omega ≤ (((m - n).toNat : ℕ) : ℕ∞)) :
    cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta ∧
      densityScore M s delta hs n m omega ≤ ENNReal.ofReal delta := by
  rw [zWitness_eq_max, max_le_iff] at h
  exact ⟨hZ1clause omega n hnm h.1, densityScore_le_of_minimalScaleEN_le M s delta hs hnm h.2⟩

/-! ## 3. The `Z²` tail in the additive shape -/

/-- **The `Z²` tail at half the prefactor and the un-halved rate** — the shape
that adds to a `Z¹` tail of the same shape and produces the frozen display at the
single constant `C`.

Length-`0` windows are free (`measure ≤ 1 ≤ C/2`), and for `N ≥ 1` the rate
`num/((C/2)γ)` delivered by `measure_tail_badDensity_le` at `C/2` dominates the
displayed `num/(Cγ)`. -/
theorem measure_tail_badDensity_le_half (C : ℝ) (hC : 2 * zTwoConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (N : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badDensity M s delta hs m) omega} ≤
      ENNReal.ofReal
        (C / 2 *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))) := by
  have hz1 : (1 : ℝ) ≤ zTwoConst d := one_le_zTwoConst d
  have hhalf : zTwoConst d ≤ C / 2 := by linarith only [hC]
  have hC1 : (1 : ℝ) ≤ C / 2 := le_trans hz1 hhalf
  have hC0 : (0 : ℝ) < C := by linarith only [hC1]
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hnum0 : (0 : ℝ) ≤ s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (pow_nonneg hs.le 9) (pow_nonneg hcs0.le 2)) (pow_nonneg hd0.le 2)
  have hgamhalf : M.gamma ≤ (C / 2)⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
    refine le_trans hgam (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact pow_le_pow_left₀ (inv_nonneg.2 hC0.le)
        (inv_anti₀ (by linarith only [hC1]) (by linarith only [hC1])) 10
    · exact le_min (pow_nonneg hcs0.le 10)
        (mul_nonneg (mul_nonneg (pow_nonneg hd0.le 2) (pow_nonneg hcs0.le 2))
          (pow_nonneg hs.le 9))
  simpa only [mul_assoc] using
    Probability.measure_exponential_tail_weaken_rate (Cutoff.cutoffSampleLaw M).toMeasure
      (fun k => {omega | (k : ℕ∞) ≤
        Probability.minimalScaleEN (badDensity M s delta hs m) omega})
      (A := C / 2) (C := C) (gamma := M.gamma)
      (numerator := s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ))
      hC1 (by linarith only [hC1]) hgam0 hnum0
      (fun k _ => by simpa only [mul_assoc] using
        measure_tail_badDensity_le (C / 2) hhalf M s delta hs hs4 hd0 hd2 hgamhalf hwin m k) N

/-! ## 4. The max tail at the frozen display -/

/-- **`e.scale.sep.bounds`, at the frozen prefactor-tail shape.**  The tail of
`max{Z¹, Z²}` is the sum of the two legs' tails (`tail_set_zWitness` plus
subadditivity), so two tails at prefactor `C/2` give one at prefactor `C`, with
the rate untouched. -/
theorem measure_tail_zWitness_le (C : ℝ) (hC : 2 * zTwoConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (bad1 : ℕ → Cutoff.CutoffSample d → Prop)
    (hZ1tail : ∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN bad1 omega} ≤
      ENNReal.ofReal
        (C / 2 *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))))
    (N : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ zWitness M s delta hs m bad1 omega} ≤
      ENNReal.ofReal
        (C *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))) := by
  have hz1 : (1 : ℝ) ≤ zTwoConst d := one_le_zTwoConst d
  have hC1 : (1 : ℝ) ≤ C / 2 := by linarith only [hC, hz1]
  have hsum : C / 2 *
        Real.exp
          (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
            (C * M.gamma)) +
      C / 2 *
        Real.exp
          (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
            (C * M.gamma))
      = C *
        Real.exp
          (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
            (C * M.gamma)) := by ring
  have hnn : (0 : ℝ) ≤ C / 2 *
      Real.exp
        (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
          (C * M.gamma)) :=
    mul_nonneg (by linarith only [hC1]) (Real.exp_pos _).le
  rw [tail_set_zWitness]
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add (hZ1tail N)
    (measure_tail_badDensity_le_half C hC M s delta hs hs4 hd0 hd2 hgam hwin m N)) ?_
  rw [← ENNReal.ofReal_add hnn hnn, hsum]

/-! ## 5. The conditional endpoint -/

/-- **The conditional endpoint (abstract `Z¹` leg).**  The full body of the
frozen proposition — the witness, its measurability, the prefactor tail and
both a.e. displays — from the proposition's own parameter ranges and window,
the regime clause at `s⁹` (see the module docstring for the `s⁸ → s⁹`
deviation), and exactly three conditional inputs about the `Z¹` leg:
`hZ1measurable`, `hZ1tail` and `hZ1clause`.

The `Z²` leg, the witness, `Measurable Z`, the max tail and the density display
are all unconditional. -/
theorem frozen_body_of_slots (C : ℝ) (hC : 2 * zTwoConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hsr : s ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hdr : delta ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (hs : 0 < s)
    (bad1 : ℕ → Cutoff.CutoffSample d → Prop)
    (hZ1measurable : ∀ j : ℕ, MeasurableSet {omega | bad1 j omega})
    (hZ1tail : ∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN bad1 omega} ≤
      ENNReal.ofReal
        (C / 2 *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))))
    (hZ1clause : ∀ (omega : Cutoff.CutoffSample d) (n : ℤ), n ≤ m →
      Probability.minimalScaleEN bad1 omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
      cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta) :
    ∃ Z : Cutoff.CutoffSample d → ℕ∞,
      Measurable Z ∧
      (∀ N : ℕ,
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ Z omega} ≤
            ENNReal.ofReal
              (C *
                Real.exp
                  (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
                        delta ^ (2 : ℕ)) /
                    (C * M.gamma)))) ∧
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
          cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta ∧
            densityScore M s delta hs n m omega ≤ ENNReal.ofReal delta := by
  refine ⟨zWitness M s delta hs m bad1, measurable_zWitness M s delta hs m bad1 hZ1measurable,
    fun N => measure_tail_zWitness_le C hC M s delta hs hsr.2 hdr.1 hdr.2 hgam hwin m bad1
      hZ1tail N, ?_⟩
  refine Filter.Eventually.of_forall fun omega => fun n hnm hZ => ?_
  exact clauses_of_zWitness_le M s delta hs m bad1 hZ1clause omega n hnm hZ

/-- The delivered constant is a single `C` with `2 · zTwoConst d ≤ C`; the frozen
`∃ C` is obtained by taking `C := 2 · max (zTwoConst d) (Wave-D's floor)`. -/
theorem frozen_body_of_cesaro_tail (C : ℝ) (hC : 2 * zTwoConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hsr : s ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hdr : delta ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (hs : 0 < s)
    (hZ1tail : ∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤
          Probability.minimalScaleEN (badCesaro M s delta hs m) omega} ≤
      ENNReal.ofReal
        (C / 2 *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma)))) :
    ∃ Z : Cutoff.CutoffSample d → ℕ∞,
      Measurable Z ∧
      (∀ N : ℕ,
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ Z omega} ≤
            ENNReal.ofReal
              (C *
                Real.exp
                  (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
                        delta ^ (2 : ℕ)) /
                    (C * M.gamma)))) ∧
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
          cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta ∧
            densityScore M s delta hs n m omega ≤ ENNReal.ofReal delta :=
  frozen_body_of_slots C hC M s delta hsr hdr hgam hwin m hs (badCesaro M s delta hs m)
    (fun j => measurableSet_badCesaro M s delta hs m j) hZ1tail
    (fun _ _ hnm hZ => cesaroScore_le_of_minimalScaleEN_le M s delta hs hnm hZ)

end

end Algsuperdiff.Section4.Provider.MinimalScale
