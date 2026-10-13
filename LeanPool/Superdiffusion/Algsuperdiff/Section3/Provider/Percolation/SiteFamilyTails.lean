/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamilyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.AdmissibleGates
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.UnionBounds

/-!
# SiteFamilyTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The per-scale tails of the site family of `l.percolation.bad.clusters`

ABK26's proof of `l.percolation.bad.clusters` asserts, for the scale-resolved
bad events `B_L(z + cu_{m-h})` of `SiteFamily.lean`, the probability bounds

```
P[ B_L(z + cu_{m-h}) ] <= exp( - T^2 3^{(3/2) L} )    for all L in N_0 ,
```

with the manuscript's own rate `T^2 = c_{e.BoscL.prob} E^{-2} gamma^{-1}`.

```
c_{e.BoscL.prob}  ->  badRateConst d / 2 ,
badRateConst d = min( delta_osc(d)^2 / 25 , 1 / 512 ) ,
```

the halving being the absorption of the `<= 10 * 3^{9d}` descendant-tree count
of `e.Bext.def` (exactly the absorption already performed by
`measureReal_badExtended_le_exp`, at the same explicit gate `hEabs`).

## What each level uses

* Level `0` is the union of `B_loc` over the nine-generation tree; each member
  obeys `e.Bloc.prob` at rate `1/512` (`measureReal_badLoc_le`), and
  `badRateConst d <= 1/512`.
* Level `l + 1` is the union of the single-shell oscillation events
  `B_{osc, R.scale + l + 1}(R)` over the same tree; each member obeys
  `e.BoscL.prob` at rate `delta_osc(d)^2/25` with shell offset `l + 1`
  *independently of the generation `i`* (this is the manuscript's own indexing
  `m - h - i + L`), and `badRateConst d <= delta_osc(d)^2 / 25`.

The count is absorbed once, uniformly in `l`, because the per-scale exponent
`3^{(3/2) l}` is at least one.

## The reindexed family

`SiteFamilyBridge.siteBadEvent` shifts the levels by `sepShift d = d` in order
to meet the *literal* separation hypothesis of the proved cutoff range lemma.
The shift costs exactly the factor `3 ^ (-(3/2) * sepShift d)` in the tail
parameter, and nothing else; the resulting parameter is `siteRateSq`.

## Main definitions

* `siteRateBase`: the dimension-only prefactor
  `badRateConst d / 2 * 3 ^ (-(3/2) sepShift d)`.
* `siteRateSq`: the tail parameter `T'^2` of the reindexed family.

## Main results

* `measureReal_badScaleEvent_le_of_gates`: the manuscript's per-scale display
  at the corrected rate from the exact four probability gates.
* `measureReal_siteBadEvent_le_of_gates`: the same after the reindexing, in
  exactly the shape `htail` of the abstract percolation layer.
* The names without `_of_gates` are compatibility wrappers for the packaged
  preliminary admissibility.

## References

* ABK26, `l.percolation.bad.clusters`.
* ABK26, `l.bad.event.probabilities`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## Absorbing the descendant-tree count -/

/-- The absorption step: a multiplicative factor whose logarithm is at most
half the rate is swallowed by half the exponential, uniformly over exponents at
least one. -/
private theorem mul_exp_neg_le_exp_neg_half {A K X : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hlog : Real.log A ≤ K / 2) :
    A * Real.exp (-(K * X)) ≤ Real.exp (-(K / 2 * X)) := by
  have hKX : K / 2 ≤ K / 2 * X := le_mul_of_one_le_right (by linarith) hX
  have hAle : A ≤ Real.exp (K / 2 * X) := by
    calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
      _ ≤ Real.exp (K / 2 * X) := Real.exp_le_exp.2 (le_trans hlog hKX)
  have hcancel : Real.exp (K / 2 * X) * Real.exp (-(K / 2 * X)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsplit : Real.exp (-(K * X)) =
      Real.exp (-(K / 2 * X)) * Real.exp (-(K / 2 * X)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc A * Real.exp (-(K * X))
      = A * Real.exp (-(K / 2 * X)) * Real.exp (-(K / 2 * X)) := by rw [hsplit]; ring
    _ ≤ Real.exp (K / 2 * X) * Real.exp (-(K / 2 * X)) * Real.exp (-(K / 2 * X)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAle (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (-(K / 2 * X)) := by rw [hcancel, one_mul]

/-- The nine-generation descendant tree of `Q` has at most `10 * 3 ^ (9 d)`
members, so a uniform bound on the members is paid at that factor. -/
private theorem measureReal_treeUnion_le (M : ABKModel d) (Q : TriadicCube d)
    (F : TriadicCube d → Set (CutoffSample d)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i ∈ Finset.range 10, ∀ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
      (cutoffSampleLaw M).toMeasure.real (F R) ≤ c) :
    (cutoffSampleLaw M).toMeasure.real
        (⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)), F R) ≤
      10 * (3 : ℝ) ^ (9 * d) * c := by
  classical
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  have hinner : ∀ i ∈ Finset.range 10,
      (cutoffSampleLaw M).toMeasure.real
          (⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)), F R) ≤
        (3 : ℝ) ^ (d * i) * c := by
    intro i hi
    have hk : Q.scale - (i : ℤ) ≤ Q.scale := by omega
    refine le_trans (measureReal_biUnion_finset_le
      (μ := (cutoffSampleLaw M).toMeasure)
      (descendantsAtScale Q (Q.scale - (i : ℤ))) (fun R => F R)) ?_
    have hcard : (descendantsAtScale Q (Q.scale - (i : ℤ))).card = (3 ^ d) ^ i := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk, descendantsAtDepth_card]
      congr 1
      omega
    refine le_trans (Finset.sum_le_sum fun R hR => hF i hi R hR) ?_
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hcast : (((3 ^ d) ^ i : ℕ) : ℝ) = (3 : ℝ) ^ (d * i) := by
      push_cast
      rw [← pow_mul]
    rw [hcast]
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have hmono : ∀ i ∈ Finset.range 10, (3 : ℝ) ^ (d * i) ≤ (3 : ℝ) ^ (9 * d) := by
    intro i hi
    have hi' : i < 10 := Finset.mem_range.1 hi
    have hle : d * i ≤ 9 * d := by
      have h1 : d * i ≤ d * 9 := Nat.mul_le_mul (le_refl d) (by omega)
      rw [Nat.mul_comm 9 d]
      exact h1
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hle
  calc ∑ i ∈ Finset.range 10, (3 : ℝ) ^ (d * i)
      ≤ ∑ _i ∈ Finset.range 10, (3 : ℝ) ^ (9 * d) := Finset.sum_le_sum hmono
    _ = 10 * (3 : ℝ) ^ (9 * d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The counting step and the absorption step, combined. -/
private theorem measureReal_treeUnion_le_exp (M : ABKModel d) (Q : TriadicCube d)
    (F : TriadicCube d → Set (CutoffSample d)) {K X : ℝ} (hK : 0 ≤ K) (hX : 1 ≤ X)
    (hlog : Real.log (10 * (3 : ℝ) ^ (9 * d)) ≤ K / 2)
    (hF : ∀ i ∈ Finset.range 10, ∀ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
      (cutoffSampleLaw M).toMeasure.real (F R) ≤ Real.exp (-(K * X))) :
    (cutoffSampleLaw M).toMeasure.real
        (⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)), F R) ≤
      Real.exp (-(K / 2 * X)) :=
  le_trans (measureReal_treeUnion_le M Q F (Real.exp_pos _).le hF)
    (mul_exp_neg_le_exp_neg_half (by positivity) hK hX hlog)

/-! ## The scale restriction of the admissibility -/

/-- The printed scale restriction `gamma <= E^{-5}` upgrades the manuscript's rate
factor `E^{-2} gamma^{-1}` to `E^3`. -/
theorem cube_le_invSq_mul_gammaInv (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) : E ^ 3 ≤ E⁻¹ ^ 2 * M.gamma⁻¹ := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : E ≠ 0 := ne_of_gt hE0
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hginv : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ hE5 hg, ← hEpow]
    exact hgamma
  have hmul := mul_le_mul_of_nonneg_left hginv (sq_nonneg E⁻¹)
  have heq : E⁻¹ ^ 2 * E ^ (5 : ℕ) = E ^ 3 := by field_simp
  rw [heq] at hmul
  exact hmul

/-! ## The per-scale tails -/

/-- ```
P[ B_l(z + cu_j) ] <= exp( - (badRateConst d / 2) E^{-2} gamma^{-1} 3^{(3/2) l} ) .
```

This direct form exposes exactly the four proof-side gates used by the two
single-cube probability bounds.  In particular it does not package them into
the stronger preliminary admissibility `C <= E * cstar`. -/
theorem measureReal_badScaleEvent_le_of_gates (M : ABKModel d) (Q : TriadicCube d)
    {m : ℤ} {E : ℝ} (hE : 1 ≤ E) (hE4 : 4 ≤ E) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hj : Q.scale ≤ m - 1) (hgamma : M.gamma ≤ E ^ (-5 : ℤ))
    (hEabs : 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) ≤ badRateConst d * E ^ 3)
    (l : ℕ) :
    (cutoffSampleLaw M).toMeasure.real (badScaleEvent M Q l) ≤
      Real.exp (-(badRateConst d / 2 * E⁻¹ ^ 2 * M.gamma⁻¹ *
        (3 : ℝ) ^ ((3 / 2 : ℝ) * (l : ℝ)))) := by
  classical
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : E ≠ 0 := ne_of_gt hE0
  have hkappa : 0 < badRateConst d := badRateConst_pos d
  have hK0 : (0 : ℝ) ≤ badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ := by positivity
  have hlow : E ^ 3 ≤ E⁻¹ ^ 2 * M.gamma⁻¹ := cube_le_invSq_mul_gammaInv M hE hgamma
  have hKlow : badRateConst d * E ^ 3 ≤ badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow hkappa.le
  have hlogA : Real.log (10 * (3 : ℝ) ^ (9 * d)) ≤
      badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ / 2 := by
    have hlog10 : Real.log (10 * (3 : ℝ) ^ (9 * d)) =
        Real.log 10 + 9 * (d : ℝ) * Real.log 3 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      congr 1
      push_cast
      ring
    have hlog1020 : Real.log 10 ≤ Real.log 20 :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [hlog10]
    linarith
  cases l with
  | zero =>
      have heq : badScaleEvent M Q 0 =
          ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
            badLoc M R := rfl
      have hmem : ∀ i ∈ Finset.range 10, ∀ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
          (cutoffSampleLaw M).toMeasure.real (badLoc M R) ≤
            Real.exp (-(badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ * 1)) := by
        intro i hi R hR
        have hk : Q.scale - (i : ℤ) ≤ Q.scale := by omega
        have hscale := scale_eq_sub_of_mem_descendantsAtScale hk hR
        have hRj : R.scale ≤ m - 1 := by omega
        refine le_trans (measureReal_badLoc_le M R hE hE4 hS hRj hgamma) ?_
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        rw [mul_one]
        have hmin : badRateConst d ≤ (1 / 512 : ℝ) := min_le_right _ _
        have h1 : badRateConst d * E⁻¹ ^ 2 ≤ (1 / 512 : ℝ) * E⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      rw [heq]
      refine le_trans (measureReal_treeUnion_le_exp M Q (fun R => badLoc M R) hK0
        le_rfl hlogA hmem) (le_of_eq ?_)
      congr 1
      have h3 : (3 : ℝ) ^ ((3 / 2 : ℝ) * ((0 : ℕ) : ℝ)) = 1 := by
        norm_num
      rw [h3]
      ring
  | succ n =>
      have heq : badScaleEvent M Q (n + 1) =
          ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
            badOscAt M R (R.scale + ((n : ℤ) + 1)) := rfl
      have hX1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((3 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
        refine Real.one_le_rpow (by norm_num) ?_
        positivity
      have hmem : ∀ i ∈ Finset.range 10, ∀ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
          (cutoffSampleLaw M).toMeasure.real (badOscAt M R (R.scale + ((n : ℤ) + 1))) ≤
            Real.exp (-(badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ *
              (3 : ℝ) ^ ((3 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)))) := by
        intro i _ R _
        have hL : R.scale ≤ R.scale + ((n : ℤ) + 1) := by omega
        refine le_trans
          (measureReal_badOscAt_le_printed M R hL hunit hgamma20 hinvSq) ?_
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        have hcast : ((R.scale + ((n : ℤ) + 1) : ℤ) : ℝ) - ((R.scale : ℤ) : ℝ) =
            ((n + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast]
        have hmin : badRateConst d ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2 := min_le_left _ _
        have h1 : badRateConst d * E⁻¹ ^ 2 ≤ (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg _)
        have h2 : badRateConst d * E⁻¹ ^ 2 * M.gamma⁻¹ ≤
            (1 / 25 : ℝ) * deltaOsc d ^ 2 * E⁻¹ ^ 2 * M.gamma⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        exact mul_le_mul_of_nonneg_right h2
          (Real.rpow_pos_of_pos (by norm_num) _).le
      rw [heq]
      refine le_trans (measureReal_treeUnion_le_exp M Q
        (fun R => badOscAt M R (R.scale + ((n : ℤ) + 1))) hK0 hX1 hlogA hmem)
        (le_of_eq ?_)
      congr 1
      ring


/-! ## The reindexed tail parameter -/

/-- The dimension-only prefactor of the reindexed tail parameter: the corrected
rate `badRateConst d / 2`, discounted by the disclosed reindexing shift
`sepShift d`. -/
def siteRateBase (d : ℕ) : ℝ :=
  badRateConst d / 2 * (3 : ℝ) ^ (-(3 / 2 : ℝ) * (sepShift d : ℝ))

theorem siteRateBase_pos (d : ℕ) : 0 < siteRateBase d := by
  rw [siteRateBase]
  have := badRateConst_pos d
  positivity

/-- **The tail parameter `T'^2` of the reindexed site family.**  This is the
manuscript's `T^2 = c E^{-2} gamma^{-1}` at the corrected constant, discounted
by the factor `3 ^ (-(3/2) sepShift d)` that the disclosed reindexing costs. -/
def siteRateSq (M : ABKModel d) (E : ℝ) : ℝ :=
  siteRateBase d * (E⁻¹ ^ 2 * M.gamma⁻¹)

/-- **The tail hypothesis of `l.percolation.bound.general`, discharged for the
reindexed site family** at the exponent `a = 3/2` of the manuscript, from the
raw proof-side gates. -/
theorem measureReal_siteBadEvent_le_of_gates (M : ABKModel d) (base : ℤ) {m : ℤ}
    {E : ℝ} (hE : 1 ≤ E) (hE4 : 4 ≤ E) (hunit : unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hbase : base ≤ m - 1) (hgamma : M.gamma ≤ E ^ (-5 : ℤ))
    (hEabs : 2 * (Real.log 20 + 9 * (d : ℝ) * Real.log 3) ≤ badRateConst d * E ^ 3)
    (l : ℕ) (u : Fin d → ℤ) :
    (cutoffSampleLaw M).toMeasure.real (siteBadEvent M base l u) ≤
      Real.exp (-(siteRateSq M E * (3 : ℝ) ^ ((3 / 2 : ℝ) * (l : ℝ)))) := by
  rw [siteBadEvent]
  split
  · rw [measureReal_empty]
    exact (Real.exp_pos _).le
  · rename_i hlq
    push Not at hlq
    have hQ : (siteCube base u).scale ≤ m - 1 := hbase
    refine le_trans (measureReal_badScaleEvent_le_of_gates M (siteCube base u) hE hE4
      hunit hgamma20 hinvSq hS hQ hgamma hEabs (l - sepShift d)) ?_
    refine Real.exp_le_exp.2 (neg_le_neg (le_of_eq ?_))
    have hq : ((l - sepShift d : ℕ) : ℝ) = (l : ℝ) - (sepShift d : ℝ) :=
      Nat.cast_sub hlq
    have hpow : (3 : ℝ) ^ (-(3 / 2 : ℝ) * (sepShift d : ℝ)) *
        (3 : ℝ) ^ ((3 / 2 : ℝ) * (l : ℝ)) =
        (3 : ℝ) ^ ((3 / 2 : ℝ) * ((l - sepShift d : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num), hq]
      congr 1
      ring
    rw [siteRateSq, siteRateBase, ← hpow]
    ring


end

end Algsuperdiff.Section3.Provider.Percolation
