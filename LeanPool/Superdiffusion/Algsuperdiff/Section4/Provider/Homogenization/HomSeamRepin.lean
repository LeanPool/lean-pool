/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel

/-!
# HomSeamRepin

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `EthmB(m)` seam, re-pinned: two dominations reduced to ONE bridge

## The seam, and why the printed base exponent has to move

`HomSpineResiduePairing`'s disclosure lists three mismatches between the
coarse-graining bundle's error slots and `EthmB(m)`'s `𝓔` factors: the
coefficient field, the ORDER, and the `q` INDEX.  the sections below settle the
last two at `CoarseGraining`'s carrier, and in doing so FIX the admissible orders:

```text
  slot 1: 𝓔_{s/8,∞,1}(a_L)   →  𝓔_{s/16,∞,2}(a_L)   (q-index, constant 1)
  slot 2: 𝓔_{s/16,∞,2}(a_L)  →  𝓔_{s/32,∞,2}(a_L)   (order, constant √2)
```

The `q`-index step is only available at the HALVED order, so the first slot can
be compared with an `𝓔` factor of order `s/16` and no larger; at the printed `s₁
= s/2` the comparison is FALSE, which is exactly the obstruction measured here.
The move carried here changes nothing but a parameter value: `EthmB(m)` is
instantiated at the BASE exponent

```text
  s':= s/8      (so s₁ = s'/2 = s/16 and s₁/2 = s'/4 = s/32),
```

i.e. the printed formula the §4.5 parameter choices with `s ↦ s/8`, the shape
of `EthmB(m)` untouched (`HomStepEnvelope.ethmB` is already parametrized by its
base exponent, so this is an INSTANTIATION, not a new definition).  The visible
costs are `s'^{-1} = 8 s^{-1}` in the prefactor and the eightfold shrink of the
anchor's admissible `p`-range; the 3-power of the `bounds_mathcal_E_aL`
majorant IMPROVES (`3^{(1/2)(s/16)(m-n)}` in place of `3^{(1/2)(s/2)(m-n)}`).
Both costs are model-independent multiples and are absorbed by the root's
existential constant; the re-pinned Step-1 moment bound is NOT proved here (see
the disclosure).

## Scope

The two domination slots at the re-pinned base are NOT proved here.  They would
need the COEFFICIENT half of the seam: the bundle's slots live at the cutoff
field `a_L` (`Cutoff.coefficientCutoffCoeffOn`), while `EthmB(m)` and all four
printed displays carry the flux-corrected field `ã_{L,m}`, and nothing in this
file asserts a bridge between the two.

CORRECTION: such a bridge is NOT the standing `bounds_mathcal_E_aL` provider
obligation — it is strictly stronger and NOT provable: it would bound the
uncut-`a_L` error by an `L`-free right side, i.e. `sup_L 𝓔(□_m; a_L, σ_m) < ∞`,
which the manuscript never asserts: the print's `bounds_mathcal_E_aL` lemma is
stated at `ã`, and transports the Dirichlet datum to `ã` rather than bounding
`a_L`.  The print-accurate replacements live in `HomSeamFluxCoefficient.lean`
(`seamDom1Flux_of_identification` / `seamDom2Flux_of_identification`, from the
honest `FluxCorrectedParentIdentification` with BOTH sides at `ã`).

Also NOT carried here: the re-pinned Step-1 moment bound
(the anchor's Step-1 factor-moment display is stated at the printed base
`s`; its sibling at `s/8` needs the anchor's `s`-endpoint at `s/32` and
its `p`-range at `64 d |log γ|` — the machine-traced correction of this
file's original `32 d |log γ|`: the binding slot is `homQuarterOf (homSeamBase)
= s/32`, so the scaling is exactly ×8, matching the gauge's `16 → 128`), and
the level chain's absorption of the `√2`
of the second slot — `HomSpineResiduePairing`'s gap pairing takes its
domination at constant one.  `ofReal_one_add_sq_le_of_const` below is the exact
arithmetic that sibling has to consume.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The two `[0,∞]` series facts -/

/-- Cauchy--Schwarz for `ℝ≥0∞`-valued sums over `ℕ`, through Hölder for the
counting measure. -/
private theorem tsum_mul_le_sqrt_mul_sqrt (f g : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, f j * g j) ≤
      (∑' j : ℕ, f j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑' j : ℕ, g j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℕ) hpq
    (f := f) (g := g) measurable_from_top.aemeasurable measurable_from_top.aemeasurable
  simpa only [lintegral_count, Pi.mul_apply] using h

private theorem ennreal_sqrt_mul_sqrt (x : ℝ≥0∞) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)]
  norm_num

private theorem ennreal_sqrt_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **Jensen at a probability weight.**  If the `[0,∞]`-weights sum to `1`, the
weighted average of the square roots is below the square root of the weighted
average. -/
private theorem tsum_weighted_sqrt_le {w R : ℕ → ℝ≥0∞} (hw : (∑' j : ℕ, w j) = 1) :
    (∑' j : ℕ, w j * R j ^ (1 / 2 : ℝ)) ≤ (∑' j : ℕ, w j * R j) ^ (1 / 2 : ℝ) := by
  have hsplit : ∀ j : ℕ, w j * R j ^ (1 / 2 : ℝ) =
      w j ^ (1 / 2 : ℝ) * (w j * R j) ^ (1 / 2 : ℝ) := by
    intro j
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_assoc,
      ennreal_sqrt_mul_sqrt (w j)]
  calc (∑' j : ℕ, w j * R j ^ (1 / 2 : ℝ))
      = ∑' j : ℕ, w j ^ (1 / 2 : ℝ) * (w j * R j) ^ (1 / 2 : ℝ) := tsum_congr hsplit
    _ ≤ (∑' j : ℕ, (w j ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑' j : ℕ, ((w j * R j) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        tsum_mul_le_sqrt_mul_sqrt _ _
    _ = (∑' j : ℕ, w j) ^ (1 / 2 : ℝ) * (∑' j : ℕ, w j * R j) ^ (1 / 2 : ℝ) := by
        congr 1
        · exact congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ))
            (tsum_congr fun j => ennreal_sqrt_sq (w j))
        · exact congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ))
            (tsum_congr fun j => ennreal_sqrt_sq (w j * R j))
    _ = (∑' j : ℕ, w j * R j) ^ (1 / 2 : ℝ) := by
        rw [hw, ENNReal.one_rpow, one_mul]

/-- The geometric weights `c_t 3^{-t j}` are a probability weight on `ℕ`. -/
private theorem tsum_geomWeight_eq_one {t : ℝ} (ht : 0 < t) :
    (∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) *
      ENNReal.ofReal ((3 : ℝ) ^ (-t * (j : ℝ)))) = 1 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hx1 : (3 : ℝ) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num) (z := -t)
      (by linarith only [ht])
  have hx0 : (0 : ℝ) < (3 : ℝ) ^ (-t) := Real.rpow_pos_of_pos h3 _
  have hpow : ∀ j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-t * (j : ℝ))) =
      ENNReal.ofReal ((3 : ℝ) ^ (-t)) ^ j := by
    intro j
    rw [← ENNReal.ofReal_pow hx0.le, ← Real.rpow_natCast ((3 : ℝ) ^ (-t)) j,
      ← Real.rpow_mul h3.le]
  calc (∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-t * (j : ℝ))))
      = ∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-t)) ^ j := tsum_congr fun j => by rw [hpow j]
    _ = ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) *
          ∑' j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-t)) ^ j := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) * (1 - ENNReal.ofReal ((3 : ℝ) ^ (-t)))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ = 1 := by
        have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ((3 : ℝ) ^ (-t)) =
            ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) := by
          rw [ENNReal.ofReal_sub _ hx0.le, ENNReal.ofReal_one]
        rw [hsub]
        refine ENNReal.mul_inv_cancel ?_ ENNReal.ofReal_ne_top
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith only [hx1]

/-- The scale series at a HIGHER order, against the scale series at a lower one:
the only loss is the ratio of the two normalizations. -/
private theorem tsum_geomWeight_order_le {R : ℕ → ℝ≥0∞} {a b K : ℝ} (hb : 0 < b)
    (hab : b ≤ a) (hK0 : 0 ≤ K)
    (hK : 1 - (3 : ℝ) ^ (-a) ≤ K * (1 - (3 : ℝ) ^ (-b))) :
    (∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (j : ℝ))) * R j) ≤
      ENNReal.ofReal K * ∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j := by
  have hb1 : (3 : ℝ) ^ (-b) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num) (z := -b)
      (by linarith only [hb])
  have hb0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-b) := by linarith only [hb1]
  have hterm : ∀ j : ℕ,
      ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) * ENNReal.ofReal ((3 : ℝ) ^ (-a * (j : ℝ))) * R j ≤
        ENNReal.ofReal K * (ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hexp : (3 : ℝ) ^ (-a * (j : ℝ)) ≤ (3 : ℝ) ^ (-b * (j : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h : -a ≤ -b := by linarith only [hab]
      exact mul_le_mul_of_nonneg_right h hj
    have h1 : ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) := by
      rw [← ENNReal.ofReal_mul hK0]
      exact ENNReal.ofReal_le_ofReal hK
    have h2 : ENNReal.ofReal ((3 : ℝ) ^ (-a * (j : ℝ))) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) := ENNReal.ofReal_le_ofReal hexp
    calc ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-a * (j : ℝ))) * R j
        ≤ ENNReal.ofReal K * ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
            ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j :=
          mul_le_mul' (mul_le_mul' h1 h2) le_rfl
      _ = ENNReal.ofReal K * (ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
            ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j) := by ring
  calc (∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (j : ℝ))) * R j)
      ≤ ∑' j : ℕ, ENNReal.ofReal K * (ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal K * ∑' j : ℕ, ENNReal.ofReal (1 - (3 : ℝ) ^ (-b)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-b * (j : ℝ))) * R j := ENNReal.tsum_mul_left

/-! ## 2. The two carrier comparisons -/

section Carrier

variable [NeZero d]

/-- **THE `q`-INDEX STEP, AT CONSTANT EXACTLY ONE.**

`𝓔_{t,∞,1}(□,n; a, σ₀) ≤ 𝓔_{t/2,∞,2}(□,n; a, σ₀)`: `CoarseGraining`'s `q = 1`
truncated parent error at order `t` is below its `q = 2` sibling at HALF that
order, on the same cube, the same truncation, the same coefficient field and
the same scalar comparator.

This is the machine-checked form of the Cauchy--Schwarz step the manuscript
performs between the two printed displays.  The halving is not a slack: at
equal orders the inequality fails. -/
theorem parentTruncatedOne_le_parentTruncatedTwo_half (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0) (t u : FractionalOrder) (htu : u.1 = t.1 / 2) :
    Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 t ≤
      Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 u := by
  have ht : 0 < t.1 := t.2.1
  have he1 : -u.1 * 2 = -t.1 := by rw [htu]; ring
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar_eq_tsum,
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum]
  simp only [he1]
  exact tsum_weighted_sqrt_le (R := fun j : ℕ =>
      Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q (n - (j : ℤ))
        (by omega) a sigma0 hsigma0)
    (tsum_geomWeight_eq_one ht)

/-- **THE ORDER STEP AT `q = 2`.**

`𝓔_{s₁,∞,2} ≤ √K · 𝓔_{s₂,∞,2}` whenever `s₂ ≤ s₁` and the normalization ratio
is below `K`.  The scale sum is monotone in the right direction; the constant is
purely the ratio `c_{s₁,2}/c_{s₂,2}` of the two normalizations. -/
theorem parentTruncatedTwo_le_of_order_le (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0) (s1 s2 : FractionalOrder) {K : ℝ} (hle : s2.1 ≤ s1.1)
    (hK0 : 0 ≤ K)
    (hK : 1 - (3 : ℝ) ^ (-s1.1 * 2) ≤ K * (1 - (3 : ℝ) ^ (-s2.1 * 2))) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 s1 ≤
      ENNReal.ofReal (Real.sqrt K) *
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0
          s2 := by
  have hb : (0 : ℝ) < s2.1 * 2 := by have := s2.2.1; linarith only [this]
  have hab : s2.1 * 2 ≤ s1.1 * 2 := by linarith only [hle]
  have hna : ∀ x : ℝ, -x * 2 = -(x * 2) := fun x => by ring
  have hseries := tsum_geomWeight_order_le
    (R := fun j : ℕ =>
      Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q (n - (j : ℤ))
        (by omega) a sigma0 hsigma0)
    (a := s1.1 * 2) (b := s2.1 * 2) (K := K) hb hab hK0
    (by rw [← hna s1.1, ← hna s2.1]; exact hK)
  simp only [← hna s1.1, ← hna s2.1] at hseries
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum,
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum]
  refine le_trans (ENNReal.rpow_le_rpow hseries (by norm_num)) (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]

/-- The halving instance of the previous theorem: `K = 2` always works, because
`c_{2s,2} = c_{s,2}(1 + 3^{-2s})` and `3^{-2s} ≤ 1`. -/
theorem parentTruncatedTwo_le_sqrtTwo_half (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0) (s1 s2 : FractionalOrder) (hhalf : s2.1 = s1.1 / 2) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 s1 ≤
      ENNReal.ofReal (Real.sqrt 2) *
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0
          s2 := by
  have hs2 : 0 < s2.1 := s2.2.1
  have hle : s2.1 ≤ s1.1 := by rw [hhalf] at hs2 ⊢; linarith only [hs2]
  have hx0 : (0 : ℝ) < (3 : ℝ) ^ (-s2.1 * 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : (3 : ℝ) ^ (-s2.1 * 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num) (z := -s2.1 * 2)
      (by linarith only [hs2])
  have hsq : (3 : ℝ) ^ (-s1.1 * 2) = ((3 : ℝ) ^ (-s2.1 * 2)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s2.1 * 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    rw [hhalf]
    push_cast
    ring
  refine parentTruncatedTwo_le_of_order_le Q n hn a sigma0 hsigma0 s1 s2 hle
    (by norm_num) ?_
  rw [hsq]
  nlinarith [hx0, hx1]

end Carrier

/-! ## 3. The re-pinned base exponent -/

/-- **THE RE-PINNED BASE** `s' = s/8`.  `EthmB(m)` is the printed object at this
base exponent: its first `𝓔` factor is then at `s'/2 = s/16` and its `γ⁵`
factor at `s'/4 = s/32`, which are exactly the two orders the `q`-index and
order steps of sections 1--2 deliver. -/
def homSeamBase (M : ABKModel d) (hs : 0 < homS M) : {s : ℝ // 0 < s} :=
  ⟨homS M / 8, by linarith only [hs]⟩

@[simp] theorem homSeamBase_val (M : ABKModel d) (hs : 0 < homS M) :
    ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ) = homS M / 8 := rfl

/-- The observable depends on its order slot only through the underlying real. -/
theorem fluxCorrectedTwoScaleErrorObservableSup_congr_order (M : ABKModel d) (m n : ℤ)
    {s1 s2 : {s : ℝ // 0 < s}} (h : (s1 : ℝ) = (s2 : ℝ)) :
    fluxCorrectedTwoScaleErrorObservableSup M m n s1 =
      fluxCorrectedTwoScaleErrorObservableSup M m n s2 := by
  have hEq : s1 = s2 := Subtype.ext h
  rw [hEq]

/-! ## 6. The absorption the level chain still owes -/

/-- **THE `√2` IS FREE.**  A domination with a constant `K ≥ 1` enters the gap
leg only through `1 + E²`, where it costs exactly `K²`.  This is the arithmetic
a sibling of `HomSpineResiduePairing`'s gap pairing has to consume in order
to accept the second domination at `√2`; nothing else in the level chain sees
the constant. -/
theorem ofReal_one_add_sq_le_of_const {E K : ℝ} {Ecar : ℝ≥0∞} (hE : 0 ≤ E) (hK : 1 ≤ K)
    (hdom : ENNReal.ofReal E ≤ ENNReal.ofReal K * Ecar) :
    ENNReal.ofReal (1 + E ^ (2 : ℕ)) ≤
      ENNReal.ofReal (K ^ (2 : ℕ)) * (1 + Ecar ^ (2 : ℝ)) := by
  have hsq : (0 : ℝ) ≤ E ^ (2 : ℕ) := pow_nonneg hE 2
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
  have hrw : ENNReal.ofReal (1 + E ^ (2 : ℕ)) = 1 + ENNReal.ofReal E ^ (2 : ℕ) := by
    rw [ENNReal.ofReal_add (by norm_num) hsq, ENNReal.ofReal_one, ENNReal.ofReal_pow hE]
  have hpow : ENNReal.ofReal E ^ (2 : ℕ) ≤ ENNReal.ofReal (K ^ (2 : ℕ)) * Ecar ^ (2 : ℕ) := by
    calc ENNReal.ofReal E ^ (2 : ℕ) ≤ (ENNReal.ofReal K * Ecar) ^ (2 : ℕ) :=
          pow_le_pow_left' hdom 2
      _ = ENNReal.ofReal (K ^ (2 : ℕ)) * Ecar ^ (2 : ℕ) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hK0]
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (K ^ (2 : ℕ)) := by
    have : (1 : ℝ) ≤ K ^ (2 : ℕ) := one_le_pow₀ hK
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal this
  have hcast : Ecar ^ (2 : ℕ) = Ecar ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_natCast Ecar 2]
    norm_num
  rw [hrw, mul_add, mul_one]
  exact add_le_add hone (by rw [← hcast]; exact hpow)

end

end Algsuperdiff.Section4.Provider.Homogenization
