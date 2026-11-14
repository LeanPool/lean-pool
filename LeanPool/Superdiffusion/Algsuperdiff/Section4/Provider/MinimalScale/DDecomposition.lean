/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.AnnularDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.SepEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# DDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `D`-decomposition of `l.minimal.scale.sep`

ABK26, §4.2.  The proof of `l.minimal.scale.sep` opens by applying
`p.mathcalE.annular.decomp` and taking a square root:

```
sup_{L ≥ k} 𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k) · 1_{𝒢(k;s,1)}
  ≤ C (D₁(k) + D₂(k) + D₃(k) + c⋆^{−2}s^{−1}γ|log γ|²)
```



with the three groups.  The remainder is then absorbed into the lemma's own
envelope and the obligation becomes `e.kick.Dees.Dees`.

## What the square root actually does

The anchor `Algsuperdiff.Frozen.Section4.annular_decomposition` states its
clause (i) for the **squared** supremum, with four right-hand groups.  Taking a
square root of a four-term sum costs `√(a+b+c+e) ≤ √a+√b+√c+√e`, and each group
loses a square in a different way:

* the `𝐣`-Hessian group loses its inner square by `∑ aᵢ² ≤ (∑ aᵢ)²` and its outer
  `3^{−½s(k−n)}` halves to `3^{−¼s(k−n)}`.

Every one of these steps is performed **in `ℝ≥0∞`**, where `√(∑ b²) ≤ ∑ b`
needs no summability side condition at all: the four helpers
`tsum_sq_le_sq_tsum`, `sum_sq_le_sq_sum`, `iSup_sq_le_sq_iSup` and
`sq_add_four_le` are unconditional, and the "square root" is taken by comparing
squares (`ENNReal.pow_le_pow_left_iff`) rather than by forming a root.  This is why no
analogue of the real-valued `annular_sqrt_domination`'s `hsum` hypothesis
appears anywhere below.

## Deviations from the printed text

* **The remainder's `s`-exponent is `s^{−3/2}`, not the printed `s^{−1}`.**
  The printed §4.2 remainder `c⋆^{−2}s^{−1}γ|log γ|²` is the exact square root
  of the printed §4.1 second group `C s^{−2}c⋆^{−4}γ²|log γ|⁴`; the anchor
  carries `C s^{−3}c⋆^{−4}γ²|log γ|⁴`, one power of `s` weaker, which is
  precisely the cost of the missing annulus multiplicity.  Its square
  root is `s^{−3/2}`.
* Every statement below carries the window `s ∈ [8γ, 1/4]` verbatim.
* The good event of the display is `𝒢(k;s,1) = goodEventBase M Ccg k s 1`, while
  the anchor's clause (i) is gated by `𝒢₀(k) ∩ 𝒢₁(k;s,√c⋆ γ^{−1/2})` only
  (resolution A6b).  `goodEventBase_subset_anchorEvent` proves the inclusion —
  the only input is `s ≤ 1`, because the composed event's `𝒢₁` threshold carries
  the extra factor `s·ε = s`.
* `D₁` carries the indicator `1_{𝒢(k;s,1)}` inside, exactly as printed;
  `D₂`, `D₃` and the remainder do not, exactly as printed.

## Main definitions

* `annularHalfSum` — the halved-exponent annular `ℓ¹` sum.
* `dOne`, `dTwo`, `dThree` — the three groups `D₁(k), D₂(k), D₃(k)`, in `ℝ≥0∞`.
* `dRemainder` — the deterministic remainder, in `ℝ` (honest `s^{−3/2}`).

## Main results

* `exists_dDecomposition` — the `√`-split of the anchor's clause (i): the
  `D`-decomposition.
* `dRemainder_le_envelope` —: the remainder is below the lemma's own envelope
  `c⋆^{−1}s^{−7/2}√γ` in the printed regime `γ ≤ C^{−10}c⋆^{10}`.  The
  smallness is D, never assumed.
* `exists_dDecomposition_absorbed` — the two composed: the decomposition with
  the remainder already replaced by the envelope, i.e. the reduction of the
  display to the obligation `e.kick.Dees.Dees`.

## References

* ABK26, `l.minimal.scale.sep`; `p.mathcalE.annular.decomp`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The unconditional `ℓ² ↪ ℓ¹` layer in `ℝ≥0∞`

Four elementary facts.  In `ℝ≥0∞` each of them is unconditional: there is no
summability hypothesis, because an `ℝ≥0∞` sum always exists, and the degenerate
case `∑ = ∞` makes every statement trivially true. -/

/-- **`∑' (f i)² ≤ (∑' f i)²` in `ℝ≥0∞`** — the `ℓ² ↪ ℓ¹` inequality, with no
summability side condition. -/
theorem tsum_sq_le_sq_tsum {iota : Type*} (f : iota → ℝ≥0∞) :
    ∑' i, f i ^ 2 ≤ (∑' i, f i) ^ 2 := by
  have hterm : ∀ i, f i ^ 2 ≤ (∑' j, f j) * f i := by
    intro i
    rw [pow_two]
    exact mul_le_mul_left (ENNReal.le_tsum i) (f i)
  calc ∑' i, f i ^ 2 ≤ ∑' i, (∑' j, f j) * f i := ENNReal.tsum_le_tsum hterm
    _ = (∑' j, f j) * ∑' i, f i := ENNReal.tsum_mul_left
    _ = (∑' i, f i) ^ 2 := (pow_two _).symm

/-- The `Finset` companion of `tsum_sq_le_sq_tsum`. -/
theorem sum_sq_le_sq_sum {iota : Type*} (S : Finset iota) (f : iota → ℝ≥0∞) :
    ∑ i ∈ S, f i ^ 2 ≤ (∑ i ∈ S, f i) ^ 2 := by
  have hterm : ∀ i ∈ S, f i ^ 2 ≤ (∑ j ∈ S, f j) * f i := by
    intro i hi
    rw [pow_two]
    exact mul_le_mul_left (Finset.single_le_sum (fun j _ => zero_le) hi) (f i)
  calc ∑ i ∈ S, f i ^ 2 ≤ ∑ i ∈ S, (∑ j ∈ S, f j) * f i := Finset.sum_le_sum hterm
    _ = (∑ j ∈ S, f j) * ∑ i ∈ S, f i := (Finset.mul_sum _ _ _).symm
    _ = (∑ i ∈ S, f i) ^ 2 := (pow_two _).symm

/-- The supremum companion: a supremum of squares is below the square of the
supremum. -/
theorem iSup_sq_le_sq_iSup {iota : Type*} (f : iota → ℝ≥0∞) :
    (⨆ i, f i ^ 2) ≤ (⨆ i, f i) ^ 2 :=
  iSup_le fun i => ENNReal.pow_le_pow_left (le_iSup f i)

/-- **The four-term square root**, in the form the decomposition uses: the sum of
four squares is below the square of the sum. -/
theorem sq_add_four_le (a b c e : ℝ≥0∞) :
    a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 ≤ (a + b + c + e) ^ 2 := by
  have hstep : ∀ x : ℝ≥0∞, x ≤ a + b + c + e → x ^ 2 ≤ x * (a + b + c + e) := by
    intro x hx
    rw [pow_two]
    exact mul_le_mul_right hx x
  have ha : a ≤ a + b + c + e :=
    le_trans (le_trans (self_le_add_right a b) (self_le_add_right _ c)) (self_le_add_right _ e)
  have hb : b ≤ a + b + c + e :=
    le_trans (le_trans (self_le_add_left b a) (self_le_add_right _ c)) (self_le_add_right _ e)
  have hc : c ≤ a + b + c + e :=
    le_trans (self_le_add_left c (a + b)) (self_le_add_right _ e)
  have he : e ≤ a + b + c + e := self_le_add_left e (a + b + c)
  calc a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2
      ≤ a * (a + b + c + e) + b * (a + b + c + e) + c * (a + b + c + e)
          + e * (a + b + c + e) :=
        add_le_add (add_le_add (add_le_add (hstep a ha) (hstep b hb)) (hstep c hc)) (hstep e he)
    _ = (a + b + c + e) * (a + b + c + e) := by ring
    _ = (a + b + c + e) ^ 2 := (pow_two _).symm

/-! ## 2. Weight arithmetic -/

/-- `(3^y)² = 3^{2y}` — the exponent halving of the annular weights. -/
theorem three_rpow_sq (y : ℝ) : (Real.rpow (3 : ℝ) y) ^ 2 = Real.rpow (3 : ℝ) (2 * y) := by
  have hadd : Real.rpow (3 : ℝ) (y + y) = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) y :=
    Real.rpow_add (by norm_num) y y
  have hy : (2 : ℝ) * y = y + y := by ring
  rw [pow_two, ← hadd, hy]

theorem three_rpow_nonneg (y : ℝ) : (0 : ℝ) ≤ Real.rpow (3 : ℝ) y :=
  Real.rpow_nonneg (by norm_num) y

/-- The squared halved weight is the anchor's weight, in `ℝ≥0∞`. -/
theorem ofReal_three_rpow_half_sq (s x : ℝ) :
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * s * x)) ^ 2
      = ENNReal.ofReal (Real.rpow (3 : ℝ) (-s * x)) := by
  rw [← ENNReal.ofReal_pow (three_rpow_nonneg _), three_rpow_sq]
  congr 2
  ring

/-- The squared quarter weight is the anchor's half weight, in `ℝ≥0∞`. -/
theorem ofReal_three_rpow_quarter_sq (s x : ℝ) :
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * x)) ^ 2
      = ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * s * x)) := by
  rw [← ENNReal.ofReal_pow (three_rpow_nonneg _), three_rpow_sq]
  congr 2
  ring

/-! ## 3. The three groups `D₁`, `D₂`, `D₃` and the remainder -/

/-- **The halved-exponent annular `ℓ¹` sum.**  The anchor's annular group with the
exponent `−s(k−n)` halved to `−½s(k−n)` and the square removed from the lattice
maximum. -/
def annularHalfSum (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : {j : ℤ // j ≤ k}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
      ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
        ENNReal.ofReal
          (annularErrorObservable M n.1 s
            (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega))

/-- **`D₁(k)`**, with the indicator of `𝒢(k;s,1)` inside exactly as printed. -/
def dOne (M : ABKModel d) (Ccg : ℝ) (s : {s : ℝ // 0 < s}) (k : ℤ) :
    Cutoff.CutoffSample d → ℝ≥0∞ :=
  Set.indicator (goodEventBase M Ccg k s 1)
    (fun omega => ENNReal.ofReal (Real.sqrt (s : ℝ)) * annularHalfSum M s k omega)

/-- **`D₂(k)`**: `c⋆^{−1/2}s^{−1}γ^{1/2} ∑_{l ≥ k}
3^{(2−γ)k}‖∇𝐣_l‖_{W^{1,∞}(□_k)}`. -/
def dTwo (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ) :
    Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega =>
    ENNReal.ofReal
        ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma) *
      ∑' l : {l : ℤ // k ≤ l},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ)) *
          shellW1InfGradNorm k (omega.1 l.1))

/-- **`D₃(k)`**: `c⋆^{−1/2}s^{−1}γ^{1/2} ∑_{l ≤ k} 3^{−¼s(k−l)} ∑_{i=l−1}^{k}
3^{(2−γ)i} max_{z ∈ 3^iℤ^d ∩ □_k} ‖𝐣_i‖_{W^{2,∞}(z+□_i)}`. -/
def dThree (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ) :
    Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega =>
    ENNReal.ofReal
        ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma) *
      ∑' n : {n : ℤ // n ≤ k},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          ∑ i ∈ Finset.Icc (n.1 - 1) k,
            ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
              ⨆ v : ↥(latticeCubeSet d i k),
                ENNReal.ofReal
                  (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i))

/-- **The deterministic remainder** `c⋆^{−2}s^{−3/2}γ|log γ|²`, the square root of
the anchor's second group.  The printed §4.2 exponent is `s^{−1}`; see the
module docstring. -/
def dRemainder (M : ABKModel d) (s : {s : ℝ // 0 < s}) : ℝ :=
  ((Disorder.cstar M)⁻¹) ^ 2 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ * M.gamma *
    |Real.log M.gamma| ^ 2

theorem dRemainder_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) :
    0 ≤ dRemainder M s := by
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 s.2
  have h1 : (0 : ℝ) ≤ (((Disorder.cstar M)⁻¹) ^ 2) := sq_nonneg _
  have h2 : (0 : ℝ) ≤ ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ := (inv_pos.2 (pow_pos hs 3)).le
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hgam.le) (sq_nonneg _)

/-! ## 4. The event inclusion -/

/-- **`𝒢(k;s,1) ⊆ 𝒢₀(k) ∩ 𝒢₁(k;s,√c⋆ γ^{−1/2})`** — the gate of the anchor's
clause (i) (resolution A6b).  The composed good event reads `𝒢₁` at the threshold
`s·ε·√c⋆ γ^{−1/2}`, which at `ε = 1` and `s ≤ 1` is below the anchor's. -/
theorem goodEventBase_subset_anchorEvent (M : ABKModel d) (Ccg : ℝ) (k : ℤ)
    (s : {s : ℝ // 0 < s}) (hs1 : (s : ℝ) ≤ 1) :
    goodEventBase M Ccg k s 1 ⊆
      eventG0 M Ccg k ∩
        eventG1 M k (s : ℝ) (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsq : (0 : ℝ) < Real.sqrt (Disorder.cstar M) := Real.sqrt_pos.2 hcs
  have hgsq : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgam
  have hT0 : (0 : ℝ) ≤ (s : ℝ) * 1 * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by
    have h := mul_nonneg (mul_nonneg (mul_nonneg s.2.le zero_le_one) hsq.le)
      (inv_pos.2 hgsq).le
    exact h
  have hTle : (s : ℝ) * 1 * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
      ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by
    have hfac : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
      mul_nonneg hsq.le (inv_pos.2 hgsq).le
    have hstep := mul_le_mul_of_nonneg_right hs1 hfac
    calc (s : ℝ) * 1 * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
        = (s : ℝ) * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by ring
      _ ≤ 1 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := hstep
      _ = Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := one_mul _
  intro omega homega
  exact ⟨goodEventBase_subset_eventG0 M Ccg k s 1 homega,
    eventG1_subset_of_le M k (s : ℝ) hT0 hTle
      (goodEventBase_subset_eventG1 M Ccg k s 1 homega)⟩

/-! ## 5. The `√`-split of the anchor's clause (i) -/

/-- The anchor's annular group is below the square of the halved-exponent sum. -/
theorem anchor_annular_le_sq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑' j : {j : ℤ // j ≤ k}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
            ENNReal.ofReal
              (annularErrorObservable M n.1 s
                (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega) ^ 2))
      ≤ (annularHalfSum M s k omega) ^ 2 := by
  have hterm : ∀ (j : {j : ℤ // j ≤ k}) (n : {n : ℤ // n ≤ j.1 - 1}),
      ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          (⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
            ENNReal.ofReal
              (annularErrorObservable M n.1 s
                (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega) ^ 2))
        ≤ (ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
            ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
              ENNReal.ofReal
                (annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega))) ^ 2 := by
    intro j n
    have hsup : (⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
          ENNReal.ofReal
            (annularErrorObservable M n.1 s
              (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega) ^ 2))
        ≤ (⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
            ENNReal.ofReal
              (annularErrorObservable M n.1 s
                (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega))) ^ 2 := by
      refine le_trans (le_of_eq (iSup_congr fun v => ?_)) (iSup_sq_le_sq_iSup _)
      exact ENNReal.ofReal_pow (annularErrorObservable_nonneg M n.1 s _) 2
    rw [mul_pow, ofReal_three_rpow_half_sq]
    exact mul_le_mul_right hsup _
  refine le_trans (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum (hterm j)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun j => tsum_sq_le_sq_tsum _) ?_
  exact tsum_sq_le_sq_tsum _

/-- The anchor's Hessian group is below the square of the quarter-exponent sum. -/
theorem anchor_hessian_le_sq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑' n : {n : ℤ // n ≤ k},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          ∑ i ∈ Finset.Icc (n.1 - 1) k,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
                ⨆ v : ↥(latticeCubeSet d i k),
                  ENNReal.ofReal
                    (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i))) ^ 2)
      ≤ (∑' n : {n : ℤ // n ≤ k},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
            ∑ i ∈ Finset.Icc (n.1 - 1) k,
              ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
                ⨆ v : ↥(latticeCubeSet d i k),
                  ENNReal.ofReal
                    (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i))) ^ 2 := by
  refine le_trans (ENNReal.tsum_le_tsum fun n => ?_) (tsum_sq_le_sq_tsum _)
  rw [mul_pow, ofReal_three_rpow_quarter_sq]
  exact mul_le_mul_right (sum_sq_le_sq_sum _ _) _

/-! ## 6. The real prefactor algebra of the four square roots -/

/-- `√x ≤ 1 + x` — the one comparison that lets the output constant `1 + C` of the
decomposition dominate the anchor's `√C`. -/
theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h : Real.sqrt x ≤ Real.sqrt ((1 + x) ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have hsq : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    calc x ≤ 1 + 2 * x + x ^ 2 := by linarith only [hx, hsq]
      _ = (1 + x) ^ 2 := by ring
  rwa [Real.sqrt_sq (by linarith only [hx])] at h

/-- The annular prefactor squared: `(√C·√s)² = C·s`. -/
theorem sqrt_mul_sqrt_sq {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (Real.sqrt C * Real.sqrt x) ^ 2 = C * x := by
  rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hx]

/-- The `𝐣`-group prefactor squared: `(√C·c⋆^{−1/2}s^{−1}√γ)² = C s^{−2}c⋆^{−1}γ`. -/
theorem sqrt_mul_pref_sq {C cs sv gam : ℝ} (hC : 0 ≤ C) (hcs : 0 < cs) (hgam : 0 ≤ gam) :
    (Real.sqrt C * ((Real.sqrt cs)⁻¹ * sv⁻¹ * Real.sqrt gam)) ^ 2
      = C * (sv⁻¹ ^ 2) * cs⁻¹ * gam := by
  have hCsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  have hgsq : Real.sqrt gam ^ 2 = gam := Real.sq_sqrt hgam
  have hinv : ((Real.sqrt cs)⁻¹) ^ 2 = cs⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hcs.le]
  calc (Real.sqrt C * ((Real.sqrt cs)⁻¹ * sv⁻¹ * Real.sqrt gam)) ^ 2
      = Real.sqrt C ^ 2 * (((Real.sqrt cs)⁻¹) ^ 2 * (sv⁻¹) ^ 2 * Real.sqrt gam ^ 2) := by ring
    _ = C * (cs⁻¹ * (sv⁻¹) ^ 2 * gam) := by rw [hCsq, hinv, hgsq]
    _ = C * (sv⁻¹ ^ 2) * cs⁻¹ * gam := by ring

/-- The remainder prefactor squared: the square of `√C·c⋆^{−2}s^{−3/2}γ|log γ|²` is
the anchor's second group `C s^{−3}c⋆^{−4}γ²|log γ|⁴`. -/
theorem sqrt_mul_remainder_sq {C cs sv gam lg : ℝ} (hC : 0 ≤ C) (hsv : 0 < sv) :
    (Real.sqrt C * ((cs⁻¹) ^ 2 * ((Real.sqrt sv) ^ 3)⁻¹ * gam * |lg| ^ 2)) ^ 2
      = C * (sv⁻¹ ^ 3) * (cs⁻¹ ^ 4) * gam ^ 2 * |lg| ^ 4 := by
  have hCsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  have hs3 : (((Real.sqrt sv) ^ 3)⁻¹) ^ 2 = sv⁻¹ ^ 3 := by
    rw [inv_pow, inv_pow, ← pow_mul, show (3 : ℕ) * 2 = 2 * 3 from by norm_num, pow_mul,
      Real.sq_sqrt hsv.le]
  calc (Real.sqrt C * ((cs⁻¹) ^ 2 * ((Real.sqrt sv) ^ 3)⁻¹ * gam * |lg| ^ 2)) ^ 2
      = Real.sqrt C ^ 2 *
          (((cs⁻¹) ^ 2) ^ 2 * (((Real.sqrt sv) ^ 3)⁻¹) ^ 2 * gam ^ 2 * (|lg| ^ 2) ^ 2) := by
        ring
    _ = C * ((cs⁻¹) ^ 4 * sv⁻¹ ^ 3 * gam ^ 2 * |lg| ^ 4) := by
        rw [hCsq, hs3]; ring
    _ = C * (sv⁻¹ ^ 3) * (cs⁻¹ ^ 4) * gam ^ 2 * |lg| ^ 4 := by ring

/-! ## 7. THE `D`-D -/

/-- **THE `D`-D OF `l.minimal.scale.sep`.**

There is a dimensional constant `C` such that, in the printed regime
`γ ≤ C^{−10}c⋆^{10}` and on the window `s ∈ [8γ, 1/4]`, for every scale `k`
and almost every sample,

```
sup_{L ≥ k} 𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k) · 1_{𝒢(k;s,1)}
  ≤ C (D₁(k) + D₂(k) + D₃(k) + c⋆^{−2}s^{−3/2}γ|log γ|²) .
```

The three groups are the printed ones at the **halved** geometric exponents;
the remainder's exponent is `s^{−3/2}` rather than the printed `s^{−1}` because
the anchor carries the annulus multiplicity (see the module docstring).

**Hypotheses.**  Exactly the premises of the anchor `annular_decomposition`,
which are the kicking lemma's own premises with the window `s ≤ 1/4` in
place of the printed `1/2`.  No summability, no measurability and no finiteness
hypothesis: the whole `ℓ² ↪ ℓ¹` step happens in `ℝ≥0∞`. -/
theorem exists_dDecomposition (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 4 →
          ∀ k : ℤ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            Set.indicator (goodEventBase M (cgEllipLowerConstant d) k s 1)
                (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega
              ≤ ENNReal.ofReal C *
                (dOne M (cgEllipLowerConstant d) s k omega + dTwo M s k omega +
                  dThree M s k omega + ENNReal.ofReal (dRemainder M s)) := by
  obtain ⟨CA, hCA, hanch⟩ := Algsuperdiff.Frozen.Section4.annular_decomposition d
  refine ⟨1 + CA, by linarith only [hCA], ?_⟩
  intro M hreg s hs8 hs4 k
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs4]
  -- the anchor's regime, from the lemma's stronger one
  have hC1 : (1 : ℝ) ≤ 1 + CA := by linarith only [hCA]
  have hregA : M.gamma ≤ CA⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    have hinv : (1 + CA)⁻¹ ^ 10 ≤ CA⁻¹ := by
      have h1 : (1 + CA)⁻¹ ^ 10 ≤ (1 + CA)⁻¹ := by
        have h2 : (1 + CA)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          exact Or.inr hC1
        calc (1 + CA)⁻¹ ^ 10 = (1 + CA)⁻¹ * (1 + CA)⁻¹ ^ 9 := by ring
          _ ≤ (1 + CA)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h2) (by positivity)
          _ = (1 + CA)⁻¹ := mul_one _
      exact h1.trans (inv_anti₀ hCA (by linarith only [hCA]))
    exact hreg.trans (mul_le_mul_of_nonneg_right hinv (pow_nonneg hcs.le 10))
  filter_upwards [hanch M hregA (s : ℝ) ⟨hs8, hs4⟩ s.2 k] with omega hom
  obtain ⟨hclause, -⟩ := hom
  -- the four square roots, as real prefactors
  set pA : ℝ := Real.sqrt CA with hpAdef
  set pref : ℝ := (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma with hprefdef
  have hpA0 : (0 : ℝ) ≤ pA := Real.sqrt_nonneg CA
  have hpref0 : (0 : ℝ) ≤ pref := by
    have h1 : (0 : ℝ) ≤ (Real.sqrt (Disorder.cstar M))⁻¹ :=
      (inv_nonneg.2 (Real.sqrt_nonneg _))
    exact mul_nonneg (mul_nonneg h1 (inv_nonneg.2 hs0.le)) (Real.sqrt_nonneg _)
  set T1 : ℝ≥0∞ := annularHalfSum M s k omega with hT1def
  set S3 : ℝ≥0∞ := ∑' l : {l : ℤ // k ≤ l},
    ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ)) *
      shellW1InfGradNorm k (omega.1 l.1)) with hS3def
  set T4 : ℝ≥0∞ := ∑' n : {n : ℤ // n ≤ k},
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
      ∑ i ∈ Finset.Icc (n.1 - 1) k,
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
          ⨆ v : ↥(latticeCubeSet d i k),
            ENNReal.ofReal
              (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i)) with hT4def
  set aa : ℝ≥0∞ := ENNReal.ofReal (pA * Real.sqrt (s : ℝ)) * T1 with haadef
  set bb : ℝ≥0∞ := ENNReal.ofReal (pA * dRemainder M s) with hbbdef
  set cc : ℝ≥0∞ := ENNReal.ofReal (pA * pref) * S3 with hccdef
  set ee : ℝ≥0∞ := ENNReal.ofReal (pA * pref) * T4 with heedef
  -- the anchor's right-hand side is below `(aa + bb + cc + ee)²`
  have hsq1 : ENNReal.ofReal (CA * (s : ℝ)) *
      (∑' j : {j : ℤ // j ≤ k}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
            ENNReal.ofReal
              (annularErrorObservable M n.1 s
                (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega) ^ 2))
      ≤ aa ^ 2 := by
    rw [haadef, mul_pow, ← ENNReal.ofReal_pow (mul_nonneg hpA0 (Real.sqrt_nonneg _)),
      hpAdef, sqrt_mul_sqrt_sq hCA.le hs0.le]
    exact mul_le_mul_right (anchor_annular_le_sq M s k omega) _
  have hsq2 : ENNReal.ofReal (CA * ((s : ℝ)⁻¹ ^ (3 : ℕ)) *
      ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) * M.gamma ^ (2 : ℕ) *
      |Real.log M.gamma| ^ (4 : ℕ)) ≤ bb ^ 2 := by
    rw [hbbdef, ← ENNReal.ofReal_pow (mul_nonneg hpA0 (dRemainder_nonneg M s)), hpAdef,
      dRemainder, sqrt_mul_remainder_sq hCA.le hs0]
  have hsq3 : ENNReal.ofReal (CA * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
      S3 ^ 2 ≤ cc ^ 2 := by
    rw [hccdef, mul_pow, ← ENNReal.ofReal_pow (mul_nonneg hpA0 hpref0), hpAdef, hprefdef,
      sqrt_mul_pref_sq hCA.le hcs hgam.le]
  have hsq4 : ENNReal.ofReal (CA * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
      (∑' n : {n : ℤ // n ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (s : ℝ) * ((k - n.1 : ℤ) : ℝ))) *
          ∑ i ∈ Finset.Icc (n.1 - 1) k,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
                ⨆ v : ↥(latticeCubeSet d i k),
                  ENNReal.ofReal
                    (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i))) ^ 2)
      ≤ ee ^ 2 := by
    rw [heedef, mul_pow, ← ENNReal.ofReal_pow (mul_nonneg hpA0 hpref0), hpAdef, hprefdef,
      sqrt_mul_pref_sq hCA.le hcs hgam.le]
    exact mul_le_mul_right (anchor_hessian_le_sq M s k omega) _
  have hanchsq : Set.indicator
      (eventG0 M (cgEllipLowerConstant d) k ∩
        eventG1 M k (s : ℝ) (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (fun omega' => fluxCorrectedErrorObservableSqSup M k s omega') omega
      ≤ (aa + bb + cc + ee) ^ 2 := by
    refine hclause.trans (le_trans ?_ (sq_add_four_le aa bb cc ee))
    exact add_le_add (add_le_add (add_le_add hsq1 hsq2) hsq3) hsq4
  -- read the square root off, term by term in the supremum
  by_cases hmem : omega ∈ goodEventBase M (cgEllipLowerConstant d) k s 1
  · rw [Set.indicator_of_mem hmem]
    have hbig : aa + bb + cc + ee ≤ ENNReal.ofReal (1 + CA) *
        (dOne M (cgEllipLowerConstant d) s k omega + dTwo M s k omega +
          dThree M s k omega + ENNReal.ofReal (dRemainder M s)) := by
      have hd1 : dOne M (cgEllipLowerConstant d) s k omega
          = ENNReal.ofReal (Real.sqrt (s : ℝ)) * T1 := by
        rw [dOne, Set.indicator_of_mem hmem, hT1def]
      have hsplit : ENNReal.ofReal pA *
          (dOne M (cgEllipLowerConstant d) s k omega + dTwo M s k omega +
            dThree M s k omega + ENNReal.ofReal (dRemainder M s)) = aa + bb + cc + ee := by
        rw [hd1, dTwo, dThree, haadef, hbbdef, hccdef, heedef, ← hS3def, ← hT4def,
          ENNReal.ofReal_mul hpA0, ENNReal.ofReal_mul hpA0, ENNReal.ofReal_mul hpA0]
        ring
      rw [← hsplit]
      refine mul_le_mul_left ?_ _
      exact ENNReal.ofReal_le_ofReal (by rw [hpAdef]; exact sqrt_le_one_add hCA.le)
    refine fluxCorrectedErrorObservableSup_le M k s omega fun L hL => ?_
    have hterm : ENNReal.ofReal (fluxCorrectedErrorRepresentative M L k s omega) ^ 2
        ≤ (aa + bb + cc + ee) ^ 2 := by
      have heq : ENNReal.ofReal (fluxCorrectedErrorRepresentative M L k s omega) ^ 2
          = ENNReal.ofReal (fluxCorrectedErrorRepresentative M L k s omega ^ 2) :=
        (ENNReal.ofReal_pow (fluxCorrectedErrorRepresentative_nonneg M L k s omega) 2).symm
      have hle : ENNReal.ofReal (fluxCorrectedErrorRepresentative M L k s omega ^ 2)
          ≤ Set.indicator
              (eventG0 M (cgEllipLowerConstant d) k ∩
                eventG1 M k (s : ℝ)
                  (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
              (fun omega' => fluxCorrectedErrorObservableSqSup M k s omega') omega := by
        rw [Set.indicator_of_mem (goodEventBase_subset_anchorEvent M
          (cgEllipLowerConstant d) k s hs1 hmem)]
        exact le_iSup
          (fun L : {L : ℤ // k ≤ L} =>
            ENNReal.ofReal (fluxCorrectedErrorRepresentative M L.1 k s omega ^ 2)) ⟨L, hL⟩
      rw [heq]
      exact hle.trans hanchsq
    exact ((ENNReal.pow_le_pow_left_iff (two_ne_zero)).1 hterm).trans hbig
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## 8. The remainder absorption -/

/-- **The smallness of `√γ (log γ)²`, D from the printed regime.**  From `γ ≤
C^{−10}c⋆^{10}` with `C ≥ 64` and the standing `c⋆ ≤ 3/2` (never `c⋆ ≤ 1`,
which the frozen tail does not deliver) one gets `√γ (log γ)² ≤ c⋆`.  The
transcendental content is the proved `sqrt_mul_log_sq_le_quarter`; everything
else is a comparison of fourth powers. -/
theorem sqrt_mul_log_sq_le_cstar (M : ABKModel d) {C : ℝ} (hC : 64 ≤ C)
    (hreg : M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10) (hgam1 : M.gamma ≤ 1) :
    Real.sqrt M.gamma * (Real.log M.gamma) ^ 2 ≤ Disorder.cstar M := by
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hquarter : M.gamma ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt M.gamma) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hgam.le]
    norm_num
  -- the fourth power comparison
  have hpow4 : (64 * Real.sqrt (Real.sqrt M.gamma)) ^ 4 ≤ Disorder.cstar M ^ 4 := by
    have hroot4 : Real.sqrt (Real.sqrt M.gamma) ^ 4 = M.gamma := by
      rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul,
        Real.sq_sqrt (Real.sqrt_nonneg M.gamma), Real.sq_sqrt hgam.le]
    have hcpow : Disorder.cstar M ^ 10 ≤ (3 / 2 : ℝ) ^ 6 * Disorder.cstar M ^ 4 := by
      have h6 : Disorder.cstar M ^ 6 ≤ (3 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ hcs.le hcs32 6
      calc Disorder.cstar M ^ 10 = Disorder.cstar M ^ 6 * Disorder.cstar M ^ 4 := by ring
        _ ≤ (3 / 2 : ℝ) ^ 6 * Disorder.cstar M ^ 4 :=
          mul_le_mul_of_nonneg_right h6 (pow_nonneg hcs.le 4)
    have hCinv : C⁻¹ ^ 10 ≤ ((64 : ℝ)⁻¹) ^ 10 :=
      pow_le_pow_left₀ (inv_nonneg.2 (by linarith only [hC]))
        (inv_anti₀ (by norm_num) hC) 10
    have hnum : (64 : ℝ) ^ 4 * (((64 : ℝ)⁻¹) ^ 10 * (3 / 2 : ℝ) ^ 6) ≤ 1 := by norm_num
    rw [mul_pow, hroot4]
    calc (64 : ℝ) ^ 4 * M.gamma ≤ 64 ^ 4 * (C⁻¹ ^ 10 * Disorder.cstar M ^ 10) :=
          mul_le_mul_of_nonneg_left hreg (by norm_num)
      _ ≤ 64 ^ 4 * (((64 : ℝ)⁻¹) ^ 10 * ((3 / 2 : ℝ) ^ 6 * Disorder.cstar M ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul hCinv hcpow (pow_nonneg hcs.le 10)
            (pow_nonneg (inv_nonneg.2 (by norm_num)) 10)
      _ = ((64 : ℝ) ^ 4 * (((64 : ℝ)⁻¹) ^ 10 * (3 / 2 : ℝ) ^ 6)) * Disorder.cstar M ^ 4 := by
          ring
      _ ≤ 1 * Disorder.cstar M ^ 4 :=
          mul_le_mul_of_nonneg_right hnum (pow_nonneg hcs.le 4)
      _ = Disorder.cstar M ^ 4 := one_mul _
  have hroot : 64 * Real.sqrt (Real.sqrt M.gamma) ≤ Disorder.cstar M :=
    le_of_pow_le_pow_left₀ (by norm_num) hcs.le hpow4
  have h64 := Algsuperdiff.Probability.sqrt_mul_log_sq_le_quarter hgam hgam1
  rw [hquarter] at h64
  exact h64.trans hroot

/-- **The remainder absorption.**  The deterministic remainder of the `D`-decomposition is below the
kicking lemma's own envelope `c⋆^{−1}s^{−7/2}√γ`, at the printed regime `γ ≤
C^{−10}c⋆^{10}` and with NO smallness hypothesis: the smallness is derived by
`sqrt_mul_log_sq_le_cstar`.

`s^{−7/2} = ((√s)⁷)⁻¹`, so no `rpow` appears. -/
theorem dRemainder_le_envelope (M : ABKModel d) {C : ℝ} (hC : 64 ≤ C)
    (hreg : M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) (hgam1 : M.gamma ≤ 1) :
    dRemainder M s
      ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * Real.sqrt M.gamma := by
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 s.2
  have hsq1 : Real.sqrt (s : ℝ) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hs1
    rwa [Real.sqrt_one] at h
  have hsmall := sqrt_mul_log_sq_le_cstar M hC hreg hgam1
  set E : ℝ := (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * Real.sqrt M.gamma with hEdef
  have hE0 : (0 : ℝ) ≤ E := by
    rw [hEdef]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hcs.le)
      (inv_nonneg.2 (pow_pos hsq0 7).le)) (Real.sqrt_nonneg _)
  -- the bracket
  have hs4 : (Real.sqrt (s : ℝ)) ^ 4 ≤ 1 := pow_le_one₀ hsq0.le hsq1
  have hbracket : (Disorder.cstar M)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4 *
      (Real.sqrt M.gamma * (Real.log M.gamma) ^ 2) ≤ 1 := by
    have h1 : (Disorder.cstar M)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4 ≤ (Disorder.cstar M)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hs4 (inv_nonneg.2 hcs.le)
    have hX0 : (0 : ℝ) ≤ Real.sqrt M.gamma * (Real.log M.gamma) ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
    have h2 : (Disorder.cstar M)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4 *
        (Real.sqrt M.gamma * (Real.log M.gamma) ^ 2)
        ≤ (Disorder.cstar M)⁻¹ * 1 * Disorder.cstar M :=
      mul_le_mul h1 hsmall hX0 (mul_nonneg (inv_nonneg.2 hcs.le) zero_le_one)
    have h3 : (Disorder.cstar M)⁻¹ * 1 * Disorder.cstar M = 1 := by
      rw [mul_one, inv_mul_cancel₀ hcs.ne']
    linarith only [h2, h3]
  -- the exact factorization
  have hgg : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma := Real.mul_self_sqrt hgam.le
  have hsqne : Real.sqrt (s : ℝ) ≠ 0 := ne_of_gt hsq0
  have hss : ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4
      = ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ := by
    field_simp
  have hkey : dRemainder M s = E * ((Disorder.cstar M)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4 *
      (Real.sqrt M.gamma * (Real.log M.gamma) ^ 2)) := by
    rw [dRemainder, hEdef, sq_abs]
    calc ((Disorder.cstar M)⁻¹) ^ 2 * ((Real.sqrt (s : ℝ)) ^ 3)⁻¹ * M.gamma *
          (Real.log M.gamma) ^ 2
        = (Disorder.cstar M)⁻¹ * (Disorder.cstar M)⁻¹ *
            (((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4) *
            (Real.sqrt M.gamma * Real.sqrt M.gamma) * (Real.log M.gamma) ^ 2 := by
          rw [hss, hgg]; ring
      _ = _ := by ring
  rw [hkey]
  calc E * ((Disorder.cstar M)⁻¹ * (Real.sqrt (s : ℝ)) ^ 4 *
        (Real.sqrt M.gamma * (Real.log M.gamma) ^ 2))
      ≤ E * 1 := mul_le_mul_of_nonneg_left hbracket hE0
    _ = E := mul_one _

/-! ## 9. The reduced obligation `e.kick.Dees.Dees` -/

/-- **The `D`-decomposition with the remainder absorbed.**  The deterministic remainder of
`exists_dDecomposition` is replaced by the kicking lemma's own envelope
`c⋆^{−1}s^{−7/2}√γ`, so that the only remaining obligation is the one the
manuscript labels `e.kick.Dees.Dees`: a bound for the Cesàro average of `D₁
+ D₂ + D₃`.

The smallness needed for the absorption is derived from the printed regime `γ ≤
C^{−10}c⋆^{10}` (via `sqrt_mul_log_sq_le_cstar`), never assumed; the standing
`c⋆ ≤ 3/2` is used in place of the unavailable `c⋆ ≤ 1`. -/
theorem exists_dDecomposition_absorbed (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 4 →
          ∀ k : ℤ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            Set.indicator (goodEventBase M (cgEllipLowerConstant d) k s 1)
                (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega
              ≤ ENNReal.ofReal C *
                (dOne M (cgEllipLowerConstant d) s k omega + dTwo M s k omega +
                  dThree M s k omega +
                  ENNReal.ofReal ((Disorder.cstar M)⁻¹ *
                    ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * Real.sqrt M.gamma)) := by
  obtain ⟨CD, hCD, hdec⟩ := exists_dDecomposition d
  refine ⟨64 + CD, by linarith only [hCD], ?_⟩
  intro M hreg s hs8 hs4 k
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs4]
  have hgam1 : M.gamma ≤ 1 := by linarith only [hs8, hs4]
  have hCDle : CD ≤ 64 + CD := by linarith only []
  have hregD : M.gamma ≤ CD⁻¹ ^ 10 * Disorder.cstar M ^ 10 := by
    refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hcs.le 10))
    exact pow_le_pow_left₀ (inv_nonneg.2 (by linarith only [hCD] : (0 : ℝ) ≤ 64 + CD))
      (inv_anti₀ hCD hCDle) 10
  have henv := dRemainder_le_envelope M (C := 64 + CD) (by linarith only [hCD]) hreg s hs1 hgam1
  filter_upwards [hdec M hregD s hs8 hs4 k] with omega hom
  refine hom.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal hCDle) ?_
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal henv)

end

end Algsuperdiff.Section4.Provider.MinimalScale
