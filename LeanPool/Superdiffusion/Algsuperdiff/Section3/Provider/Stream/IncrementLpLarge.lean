/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpGain

/-!
# IncrementLpLarge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.kl.bounds.large`: the unconditional head-plus-gain estimate

```
  ⨍_{cu_l} |(k_m - k_n)(x)|^p dx
      <= (C(d) p)^{p/2} A^{p/2}
         + O_{Gamma_{2/p}}( (C(d) p)^{p/2} A^{p/2} 3^{-(d/2)(l-m)} ) ,
      A := min{gamma^{-1}, m-n} 3^{2 gamma m} ,
```

**for every `l`**, with no relation between `l` and `m`: the printed binder
`n < m <= l` is not needed, and neither is the partition-regime binder
`m + c <= l` of the existing `Provider/Stream/IncrementLpGain.lean`. The
`l`-window split is internal to the proof.

## The two ingredients

The existing `IncrementLpGain.streamIncrementLpMass_head_tail` provides the
partition-regime estimate `m + c <= l` conditionally on one abstract input,
`hX0`: a `Gamma_sigma` bound for the *restriction-centered* unit-cube
observable of the partition-normalized law. This module proves that input and
assembles both regimes.

### The centering bookkeeping

`hX0` comes from the existing `e.kmn.bounds` provider at the single scale
`l = m + c`, **centered**.
The passage from the raw bound to the centered bound costs **nothing**:

> `isBigO_sub_const_of_isBigOWith_of_nonneg` — if `X >= 0` obeys
> `X <= O_Psi(K)` and `c ∈ [0, K]`, then `X - c = O_Psi(K)`, *with the same
> constant `K`*.

The honest constant is `1`, not `2`: for `t >= 1` the shifted tail event
`{|X - c| > K t}` is contained in the raw tail event `{X > K t}`, because
(i) upward, `X - c > K t` forces `X > K t + c >= K t` as `c >= 0`, and
(ii) downward, `c - X <= c <= K <= K t`, so the downward branch of the
absolute value is *empty*.  No `Gamma`-constant absorption and no
monotonicity of `Psi` is used; the lemma holds for an arbitrary tail
function `Psi`.  The hypothesis `c <= K` is supplied by
`integral_streamIncrementLpMass_le` — the mean of a nonnegative observable
never exceeds its own `Gamma` scale.

### The transport

`isBigOWith_map_of_isBigOWith_comp` is the push-forward transport in the
direction *opposite* to the existing `isBigOWith_comp_of_isBigO_map`: a tail
bound for `g ∘ F` on the sample space is a tail bound for `g` under
`F_* mu`.  Both are the same preimage identity; the two directions are needed
at the two ends of the argument (`hX0` is stated on the law, `e.kmn.bounds` is
proved on `ShellSeq`).

## The two regimes and the enlarged `C(d)`

* `m + c <= l` (the partition regime).  `streamIncrementLpMass_head_tail` gives
  `mass <= E[mass_{m+c}] + |mass_l - E[mass_{m+c}]|` with the second term in
  `O_{Gamma_{2/p}}` of `gammaSigmaDescendantsAtScaleConst d 0 (2/p) *
  3^{-(d/2)(l-m-c)} * K`.  The identity
  `partitionCardinalityScale_originCube_zero` evaluates CoarseGraining's
  cardinality scale as `3^{-(d/2)(l-m-c)} = 3^{(d/2)c} 3^{-(d/2)(l-m)}`, i.e.
  the printed gain times a dimensional constant.
* `l < m + c` (the complementary regime).  Here the partition is not
  available, and the estimate uses the existing `l`-uniform `e.kmn.bounds` with
  head `0`: since `l - m < c`, the printed gain `3^{-(d/2)(l-m)}` *exceeds*
  `3^{-(d/2)c}`, so the ungained amplitude is dominated by the gained one
  after the same enlargement `3^{(d/2)c}` of `C(d)`.

The tail observable is defined by the *same* case split,
`streamIncrementLpTail`; it is an explicit function of the sample, not an
existential.

## Disclosed conventions and limitations

* The head `streamIncrementLpMassHead` is *literally* the right-hand side of
  the existing `integral_streamIncrementLpMass_le`, i.e. `(gammaMomentConst 2 ·
  C_d · A^{1/2} · p^{1/2})^p = ((gammaMomentConst 2 · C_d)^2 p)^{p/2} A^{p/2}`,
  the corrected head with the source's `C(d)` read as `(2e · C_d)^2`.  The
  `p^{p/2}` that the printed display drops is carried.
* The Orlicz exponent is `2/p`, as printed; the norm-level corollary is its
  `1/p`-th root, so the mass gain `3^{-(d/2)(l-m)}` becomes the norm gain
  `3^{-(d/(2p))(l-m)}` — at `p = 4` the `3^{-(d/8)(l-m)}` of
  `e.wave.influence.bound`.  The mass-level gain exponent is `d/2` for *every*
  `p ≥ 1` (the partition fluctuation is the square root of the cell count, and
  `p` enters only through the Orlicz class and the amplitude).
* **The complementary regime carries no improvement.**  For `l < m + c` the
  conclusion is the existing `l`-uniform `e.kmn.bounds` rewritten at the larger
  amplitude, with the whole mass in the random part; the genuine geometric
  gain exists only in the partition regime `m + c ≤ l`, which is the regime the
  source's binder `m ≤ l` was aiming at.  Stating the theorem for every `l`
  costs only the constant `3^{(d/2)c}` and removes a binder; it does not claim
  decay where none is available.
* `|·|` is `Book.Ch02.matrixOperatorNorm` throughout, as in the existing
  `e.kmn.bounds`.

## Main definitions

* `streamIncrementLpMassHead` — the corrected deterministic head.
* `streamIncrementLpTail` — the random part, defined by the internal window
  split.
* `streamIncrementLpGainConst`, `streamIncrementLpGainScale` — the uniform
  amplitude of the random part.

## Main results

* `isBigO_sub_const_of_isBigOWith_of_nonneg` — the centering bookkeeping.
* `isBigOWith_map_of_isBigOWith_comp` — the push-forward transport.
* `isBigO_gammaSigma_centeredOriginObservable_regFieldLpMassRep` — the local
  Provider for `hX0`.
* `partitionCardinalityScale_originCube_zero` — CoarseGraining's cardinality
  scale as the printed geometric gain.
* `streamIncrementLpMass_head_tail_gain` — the local Provider estimate
  corresponding to corrected `e.kl.bounds.large`, unconditional in `l`.
* `streamIncrementLpNorm_head_tail_gain` — the unsquared Γ₂ of the corrected
  `e.km.kn.Lp`, unconditional in `l` (the squared Γ₁ form is proved in
  `IncrementLpSquared.lean`; no node status is assigned here).

## References

* ABK26, `e.kl.bounds.large`; `e.kmn.bounds`; `e.km.kn.Lp`;
  `p.concentration`; `a.j.frd`.
* `Provider/Stream/IncrementLp.lean` (`e.kmn.bounds` and the mass-to-norm
  interface), `Provider/Stream/IncrementLpGain.lean` (the partition-regime
  head/tail package), `Provider/Stream/IncrementMassRepresentative.lean`
  (the measurable local representative).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Centering a nonnegative weak-Orlicz observable -/

/-- **The centering bookkeeping, at constant `1`.**  Subtracting a constant
`c ∈ [0, K]` from a nonnegative observable with a `Psi` tail at scale `K`
leaves the tail at the *same* scale `K`.

The downward branch of the absolute value contributes nothing: `c - X ≤ c ≤ K`
never exceeds `K t` for `t ≥ 1`; the upward branch is contained in the raw
tail because `c ≥ 0`.  No property of `Psi` is used. -/
theorem isBigO_sub_const_of_isBigOWith_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ} {K c : ℝ}
    (hc0 : 0 ≤ c) (hcK : c ≤ K) (hX0 : ∀ omega, 0 ≤ X omega)
    (hX : IndependentSums.IsBigOWith mu Psi X K) :
    IndependentSums.IsBigO mu Psi (fun omega => X omega - c) K := by
  intro t ht
  have hK : (0 : ℝ) ≤ K := le_trans hc0 hcK
  have hKt : K ≤ K * t := le_mul_of_one_le_right hK ht
  have hsub : IndependentSums.upperTailEvent (fun omega => |X omega - c|) (K * t) ⊆
      IndependentSums.upperTailEvent X (K * t) := by
    intro omega homega
    have h : K * t < |X omega - c| := homega
    rcases abs_cases (X omega - c) with ⟨heq, _⟩ | ⟨heq, _⟩
    · show K * t < X omega
      rw [heq] at h
      linarith
    · exact absurd (h.trans_le (by rw [heq]; linarith [hX0 omega])) (lt_irrefl _)
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hX ht)

/-! ## Transport along a push-forward -/

/-- A `Psi` tail bound for a composition `g ∘ F` on the sample space is the same
bound for `g` under the push-forward law.  This is the direction opposite to the
existing `isBigOWith_comp_of_isBigO_map`. -/
theorem isBigOWith_map_of_isBigOWith_comp {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {F : Omega → RegCoeffField d} (hF : Measurable F)
    {g : RegCoeffField d → ℝ} (hg : Measurable g) {Psi : ℝ → ℝ} {A : ℝ}
    (h : IndependentSums.IsBigOWith mu Psi (fun omega => g (F omega)) A) :
    IndependentSums.IsBigOWith (Measure.map F mu) Psi g A := by
  intro t ht
  have hs : MeasurableSet (IndependentSums.upperTailEvent g (A * t)) :=
    measurableSet_lt measurable_const hg
  have hgoal : (Measure.map F mu).real (IndependentSums.upperTailEvent g (A * t)) =
      mu.real (IndependentSums.upperTailEvent (fun omega => g (F omega)) (A * t)) := by
    rw [Measure.real, Measure.real, Measure.map_apply hF hs]
    rfl
  rw [hgoal]
  exact h ht

/-! ## The deterministic head -/

/-- **The corrected head of `e.kl.bounds.large`**: the right-hand side of the
existing `integral_streamIncrementLpMass_le`, i.e. `(C(d) p)^{p/2} A^{p/2}`
with `A = min{gamma^{-1}, m-n} 3^{2 gamma m}`. -/
def streamIncrementLpMassHead (M : ABKModel d) (p : ℝ) (n m : ℤ) : ℝ :=
  (IndependentSums.gammaMomentConst 2 * streamPointScale M n m * p ^ ((2 : ℝ)⁻¹)) ^ p

theorem streamIncrementLpMassHead_pos (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) : 0 < streamIncrementLpMassHead M p n m := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have ha : (0 : ℝ) < IndependentSums.gammaMomentConst 2 * streamPointScale M n m :=
    mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (streamPointScale_pos M hnm)
  exact Real.rpow_pos_of_pos (mul_pos ha (Real.rpow_pos_of_pos hp0 _)) _

/-- The existing `Gamma_{2/p}` scale of `e.kmn.bounds` is the head times the
universal `e` of the moment-to-tail conversion. -/
theorem streamIncrementLpMassScale_eq_exp_mul_head (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassScale M p n m =
      Real.exp 1 * streamIncrementLpMassHead M p n m := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have ha : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 2 * streamPointScale M n m :=
    (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (streamPointScale_pos M hnm)).le
  rw [streamIncrementLpMassScale, streamIncrementLpMassHead,
    Real.mul_rpow ha (Real.rpow_nonneg hp0.le _), ← Real.rpow_mul hp0.le]
  congr 3
  ring

/-- **The head dominates the mean.**  This is `integral_streamIncrementLpMass_le`
read at the head. -/
theorem integral_streamIncrementLpMass_le_head (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    ∫ omega : ShellSeq d, streamIncrementLpMass p l n m omega ∂M.P.toMeasure ≤
      streamIncrementLpMassHead M p n m :=
  integral_streamIncrementLpMass_le M hp hnm l

/-- The mean is below the `Gamma_{2/p}` scale of `e.kmn.bounds`: the shift
budget of the centering lemma. -/
theorem integral_streamIncrementLpMass_le_massScale (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    ∫ omega : ShellSeq d, streamIncrementLpMass p l n m omega ∂M.P.toMeasure ≤
      streamIncrementLpMassScale M p n m := by
  refine (integral_streamIncrementLpMass_le_head M hp hnm l).trans ?_
  rw [streamIncrementLpMassScale_eq_exp_mul_head M hp hnm]
  exact le_mul_of_one_le_left (streamIncrementLpMassHead_pos M hp hnm).le
    (Real.one_le_exp zero_le_one)

/-! ## Discharging the origin-cube hypothesis `hX0` -/

/-- The unit-cube observable of the partition-normalized law, read at a sample,
is the cube mass of the increment at the single scale `m + c`.

This is the pointwise step that the existing
`integral_regFieldLpMassRep_originCube_zero` performs inside its own proof; it
is restated here (same two rewrites, no drift) because that file exposes only
the integrated form, and the tail argument needs the sample-wise identity. -/
theorem regFieldLpMassRep_originCube_zero_partitionIncrement {p : ℝ} (hp : 0 < p)
    (n m : ℤ) (omega : ShellSeq d) :
    regFieldLpMassRep p (cubeSet (originCube d 0))
        (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
          (finiteShellIncrement omega n m)) =
      streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega := by
  rw [regFieldLpMassRep_cubeSet_smulReg_eq_cubeAverage hp
      (m + (incrementPartitionShift d : ℤ)) (incrementPartitionScale_ne_zero d m) rfl
      (originCube d 0) omega n m,
    streamIncrementLpMass_eq_cubeAverage hp]
  congr 1
  simp

/-- **The `hX0` input of `streamIncrementLpMass_head_tail`, proved locally.**

It applies the existing `e.kmn.bounds` provider at the single scale `l = m + c`,
restriction-centers by its own mean, and transports to the
partition-normalized law. No additional probabilistic input is used. -/
theorem isBigO_gammaSigma_centeredOriginObservable_regFieldLpMassRep (M : ABKModel d)
    {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M n m)
      (Book.Ch04.gammaSigma (2 / p))
      (Book.Ch04.restrictionCenteredOriginObservable
        (partitionStreamIncrementLaw M n m) 0
        (regFieldLpMassRep p)) (streamIncrementLpMassScale M p n m) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hmu0 : ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
        ∂(partitionStreamIncrementLaw M n m) =
      ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
        ∂M.P.toMeasure :=
    integral_regFieldLpMassRep_originCube_zero M hp0 n m
  have hc0 : (0 : ℝ) ≤ ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
      ∂(partitionStreamIncrementLaw M n m) := by
    rw [hmu0]
    exact integral_nonneg fun w => streamIncrementLpMass_nonneg p _ n m w
  have hcK : (∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
      ∂(partitionStreamIncrementLaw M n m)) ≤ streamIncrementLpMassScale M p n m := by
    rw [hmu0]
    exact integral_streamIncrementLpMass_le_massScale M hp hnm _
  have hcent := isBigO_sub_const_of_isBigOWith_of_nonneg (mu := M.P.toMeasure)
    (Psi := IndependentSums.gammaSigma (2 / p)) hc0 hcK
    (fun omega => streamIncrementLpMass_nonneg p _ n m omega)
    (isBigOWith_gammaSigma_streamIncrementLpMass M hp hnm
      (m + (incrementPartitionShift d : ℤ)))
  have hg : Measurable (fun a : RegCoeffField d =>
      |regFieldLpMassRep p (cubeSet (originCube d 0)) a -
        ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
          ∂(partitionStreamIncrementLaw M n m)|) :=
    continuous_abs.measurable.comp ((measurable_regFieldLpMassRep p _).sub measurable_const)
  have hcomp : (fun omega : ShellSeq d =>
      |regFieldLpMassRep p (cubeSet (originCube d 0))
          (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
            (finiteShellIncrement omega n m)) -
        ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
          ∂(partitionStreamIncrementLaw M n m)|) =
      fun omega : ShellSeq d =>
        |streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m omega -
          ∫ b, regFieldLpMassRep p (cubeSet (originCube d 0)) b
            ∂(partitionStreamIncrementLaw M n m)| := by
    funext omega
    rw [regFieldLpMassRep_originCube_zero_partitionIncrement hp0 n m omega]
  have htrans := isBigOWith_map_of_isBigOWith_comp M.P.toMeasure
    (measurable_partitionIncrementField (d := d) n m) hg (by rw [hcomp]; exact hcent)
  rw [partitionStreamIncrementLaw_eq_map]
  exact htrans

/-! ## The geometric partition gain -/

private theorem card_descendantsAtScale_originCube_zero {j : ℤ} (hj : 0 ≤ j) :
    ((descendantsAtScale (originCube d j) 0).card : ℝ) =
      (3 : ℝ) ^ ((d : ℝ) * (j : ℝ)) := by
  have hscale : (0 : ℤ) ≤ (originCube d j).scale := by
    simpa [originCube] using hj
  have htoNat : ((Int.toNat j : ℕ) : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj
  have hcard : (descendantsAtScale (originCube d j) 0).card = (3 ^ d) ^ Int.toNat j := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d j) hscale]
    simpa [originCube] using descendantsAtDepth_card (originCube d j) (Int.toNat j)
  rw [hcard]
  have hcast : (((3 ^ d) ^ Int.toNat j : ℕ) : ℝ) = (3 : ℝ) ^ (d * Int.toNat j) := by
    push_cast
    rw [← pow_mul]
  rw [hcast, ← Real.rpow_natCast (3 : ℝ) (d * Int.toNat j)]
  congr 1
  push_cast [htoNat]
  ring

/-- **CoarseGraining's cardinality fluctuation scale, evaluated.**  The scale-`0`
partition of the origin cube at scale `j ≥ 0` has `3^{dj}` cells, so its
square-root fluctuation factor is the geometric gain `3^{-(d/2)j}`. -/
theorem partitionCardinalityScale_originCube_zero {j : ℤ} (hj : 0 ≤ j) :
    Book.Ch04.partitionCardinalityScale (d := d) 0 j =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * (j : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcard := card_descendantsAtScale_originCube_zero (d := d) hj
  rw [Book.Ch04.partitionCardinalityScale, hcard, div_eq_mul_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_mul h3.le, ← Real.rpow_neg h3.le, ← Real.rpow_add h3]
  congr 1
  ring

/-! ## The uniform amplitude -/

/-- The gain-amplitude constant: the universal `e` of the moment-to-tail
conversion, the partition-normalization loss `3^{(d/2)c}` with `3^c > 2 sqrt
d`, and CoarseGraining's colouring constant (raised to at least `1`, so that
the complementary regime `l < m + c` is covered by the same amplitude).  Note
that at general `p` this is *not* a `C(d)`: the colouring constant
`gammaSigmaDescendantsAtScaleConst d 0 (2/p)` grows like `exp(Θ(p²))`
(dominated by CoarseGraining's `gammaSigmaLogControlConst σ = exp(32/σ²)` at `σ
= 2/p`; the `p^{Θ(p)}` triangle/Γ factors are swamped), so in the printed
`(C·p)^{p/2}` shape the `C` is `e^{Θ(p)}` — exponentially `p`-dependent,
outside the node's stated scope `C = C(d)`.  At the wave consumer's fixed `p = 4` it is a
genuine number.  A `C(d)`-uniform tail constant, if the node needs one at
general `p`, is a separate obligation. -/
def streamIncrementLpGainConst (d : ℕ) (sigma : ℝ) : ℝ :=
  Real.exp 1 * (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
    max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 sigma)

theorem streamIncrementLpGainConst_pos (d : ℕ) (sigma : ℝ) :
    0 < streamIncrementLpGainConst d sigma := by
  rw [streamIncrementLpGainConst]
  exact mul_pos (mul_pos (Real.exp_pos 1) (Real.rpow_pos_of_pos (by norm_num) _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- **The amplitude of the random part**: `streamIncrementLpGainConst`
(NOT a `C(d)` at general `p` — see its disclosure) times `3^{-(d/2)(l-m)}`
times the corrected head. -/
def streamIncrementLpGainScale (M : ABKModel d) (p : ℝ) (l n m : ℤ) : ℝ :=
  streamIncrementLpGainConst d (2 / p) *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) *
    streamIncrementLpMassHead M p n m

theorem streamIncrementLpGainScale_pos (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) (l : ℤ) : 0 < streamIncrementLpGainScale M p l n m :=
  mul_pos (mul_pos (streamIncrementLpGainConst_pos d _)
      (Real.rpow_pos_of_pos (by norm_num) _))
    (streamIncrementLpMassHead_pos M hp hnm)

/-- The partition-regime amplitude of `streamIncrementLpMass_head_tail` is below
the uniform amplitude. -/
theorem partitionScale_le_streamIncrementLpGainScale (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p) *
        Book.Ch04.partitionCardinalityScale (d := d) 0
          (l - (m + (incrementPartitionShift d : ℤ))) *
        streamIncrementLpMassScale M p n m ≤
      streamIncrementLpGainScale M p l n m := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hj : (0 : ℤ) ≤ l - (m + (incrementPartitionShift d : ℤ)) := by omega
  have hsplit : (3 : ℝ) ^ (-((d : ℝ) / 2) *
        ((l - (m + (incrementPartitionShift d : ℤ)) : ℤ) : ℝ)) =
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    rw [← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [partitionCardinalityScale_originCube_zero (d := d) hj, hsplit,
    streamIncrementLpMassScale_eq_exp_mul_head M hp hnm, streamIncrementLpGainScale,
    streamIncrementLpGainConst]
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) * Real.exp 1 *
      streamIncrementLpMassHead M p n m :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _))
      (Real.exp_pos 1).le) (streamIncrementLpMassHead_pos M hp hnm).le
  calc Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p) *
        ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) *
        (Real.exp 1 * streamIncrementLpMassHead M p n m)
      = ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) * Real.exp 1 *
          streamIncrementLpMassHead M p n m) *
          Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p) := by ring
    _ ≤ ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) * Real.exp 1 *
          streamIncrementLpMassHead M p n m) *
          max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hnn
    _ = Real.exp 1 * (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) *
          streamIncrementLpMassHead M p n m := by ring

/-- The complementary-regime amplitude of `e.kmn.bounds` is below the uniform
amplitude: for `l < m + c` the printed gain exceeds `3^{-(d/2)c}`, which the
enlarged constant absorbs. -/
theorem massScale_le_streamIncrementLpGainScale (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m l : ℤ} (hnm : n < m)
    (hsl : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    streamIncrementLpMassScale M p n m ≤ streamIncrementLpGainScale M p l n m := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hlt : (l : ℝ) - (m : ℝ) ≤ (incrementPartitionShift d : ℝ) := by
    have hz : l < m + (incrementPartitionShift d : ℤ) := lt_of_not_ge hsl
    have : (l : ℝ) < (m : ℝ) + (incrementPartitionShift d : ℝ) := by exact_mod_cast hz
    linarith
  have hexpo : (0 : ℝ) ≤ ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) +
      -((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) := by
    have hd : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hfac : (0 : ℝ) ≤ ((d : ℝ) / 2) *
        ((incrementPartitionShift d : ℝ) - ((l : ℝ) - (m : ℝ))) :=
      mul_nonneg hd (by linarith)
    have hexpand : ((d : ℝ) / 2) *
        ((incrementPartitionShift d : ℝ) - ((l : ℝ) - (m : ℝ))) =
      ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) +
        -((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) := by ring
    linarith [hexpand ▸ hfac]
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    rw [← Real.rpow_add h3]
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexpo
    rwa [Real.rpow_zero] at h
  have hmax : (1 : ℝ) ≤ max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) :=
    le_max_left _ _
  have hprod : (1 : ℝ) ≤ (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
      max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    have hrw : (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
        max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) =
        ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) *
          max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) := by ring
    rw [hrw]
    exact one_le_mul_of_one_le_of_one_le hone hmax
  rw [streamIncrementLpMassScale_eq_exp_mul_head M hp hnm, streamIncrementLpGainScale,
    streamIncrementLpGainConst]
  have hexp1 : Real.exp 1 * 1 ≤ Real.exp 1 *
      ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
        max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) :=
    mul_le_mul_of_nonneg_left hprod (Real.exp_pos 1).le
  calc Real.exp 1 * streamIncrementLpMassHead M p n m
      = (Real.exp 1 * 1) * streamIncrementLpMassHead M p n m := by ring
    _ ≤ (Real.exp 1 *
          ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
            max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))) *
          streamIncrementLpMassHead M p n m :=
        mul_le_mul_of_nonneg_right hexp1 (streamIncrementLpMassHead_pos M hp hnm).le
    _ = Real.exp 1 * (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          max 1 (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 (2 / p)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) *
          streamIncrementLpMassHead M p n m := by ring

/-! ## The random part -/

/-- **The random part of `e.kl.bounds.large`**, defined by the internal window
split: in the partition regime `m + c ≤ l` it is the fluctuation of the cube
mass about its scale-`(m+c)` mean; in the complementary regime `l < m + c` it is
the cube mass itself. -/
def streamIncrementLpTail (M : ABKModel d) (p : ℝ) (l n m : ℤ) (omega : ShellSeq d) : ℝ :=
  if m + (incrementPartitionShift d : ℤ) ≤ l then
    |streamIncrementLpMass p l n m omega -
      ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
        ∂M.P.toMeasure|
  else streamIncrementLpMass p l n m omega

theorem streamIncrementLpTail_nonneg (M : ABKModel d) (p : ℝ) (l n m : ℤ)
    (omega : ShellSeq d) : 0 ≤ streamIncrementLpTail M p l n m omega := by
  rw [streamIncrementLpTail]
  split
  · exact abs_nonneg _
  · exact streamIncrementLpMass_nonneg p l n m omega

/-! ## `e.kl.bounds.large` -/

/-- **ABK26's `e.kl.bounds.large`** in the form corrected:

`⨍_{cu_l} |(k_m - k_n)(x)|^p dx ≤ (C(d)p)^{p/2} A^{p/2}
   + O_{Γ_{2/p}}((C(d)p)^{p/2} A^{p/2} 3^{-(d/2)(l-m)})`, `A = min{γ^{-1}, m-n}
     3^{2γm}`,

for every `p ≥ 1`, every `n < m` and **every** `l ∈ ℤ` (the printed `m ≤ l` is
not used).  The three conjuncts are exactly the nonnegativity, the pointwise
mass decomposition and the `Γ_{2/p}` tail bound consumed by
`streamIncrementLpNorm_head_tail_of_mass_head_tail`. -/
theorem streamIncrementLpMass_head_tail_gain (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    (∀ omega : ShellSeq d, 0 ≤ streamIncrementLpTail M p l n m omega) ∧
      (∀ omega : ShellSeq d,
        streamIncrementLpMass p l n m omega ≤
          streamIncrementLpMassHead M p n m + streamIncrementLpTail M p l n m omega) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma (2 / p))
        (streamIncrementLpTail M p l n m) (streamIncrementLpGainScale M p l n m) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨fun omega => streamIncrementLpTail_nonneg M p l n m omega, ?_, ?_⟩
  · intro omega
    rw [streamIncrementLpTail]
    split
    · have hmean : (∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure) ≤ streamIncrementLpMassHead M p n m :=
        integral_streamIncrementLpMass_le_head M hp hnm _
      have habs := le_abs_self (streamIncrementLpMass p l n m omega -
        ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure)
      linarith
    · linarith [(streamIncrementLpMassHead_pos M hp hnm).le]
  · by_cases hsl : m + (incrementPartitionShift d : ℤ) ≤ l
    · have hsigma0 : (0 : ℝ) < 2 / p := by positivity
      have hsigma2 : (2 : ℝ) / p ≤ 2 := by
        rw [div_le_iff₀ hp0]
        linarith
      have hgain := streamIncrementLpMass_head_tail M hp0 hsl hsigma0 hsigma2
        (streamIncrementLpMassScale_pos M hp hnm)
        (isBigO_gammaSigma_centeredOriginObservable_regFieldLpMassRep M hp hnm)
      have htail : streamIncrementLpTail M p l n m = fun omega : ShellSeq d =>
          |streamIncrementLpMass p l n m omega -
            ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
              ∂M.P.toMeasure| := by
        funext omega
        rw [streamIncrementLpTail, ite_eq_left hsl]
      rw [htail]
      exact hgain.2.2.2.mono_scale
        (partitionScale_le_streamIncrementLpGainScale M hp hnm hsl)
    · have htail : streamIncrementLpTail M p l n m = streamIncrementLpMass p l n m := by
        funext omega
        rw [streamIncrementLpTail, ite_eq_right hsl]
      rw [htail]
      exact (isBigOWith_gammaSigma_streamIncrementLpMass M hp hnm l).mono_scale
        (massScale_le_streamIncrementLpGainScale M hp hnm hsl)

/-- **The unsquared Γ₂ precursor of the corrected `e.km.kn.Lp`** (whose printed
display is the squared norm at Γ₁; the squaring step is proved in
`IncrementLpSquared.lean`): the `1/p`-th root of the mass form,

`‖k_m - k_n‖_{L^p(cu_l)} ≤ (C(d)p)^{1/2} A^{1/2}
   + O_{Γ₂}((C(d)p)^{1/2} A^{1/2} 3^{-(d/(2p))(l-m)})`,

for every `p ≥ 1`, every `n < m` and every `l ∈ ℤ`.  At `p = 4` the gain is the
`3^{-(d/8)(l-m)}` of `e.wave.influence.bound`. -/
theorem streamIncrementLpNorm_head_tail_gain (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    (∀ omega : ShellSeq d,
        streamIncrementLpNorm p l n m omega ≤
          streamIncrementLpMassHead M p n m ^ p⁻¹ +
            streamIncrementLpTail M p l n m omega ^ p⁻¹) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => streamIncrementLpTail M p l n m omega ^ p⁻¹)
        (streamIncrementLpGainScale M p l n m ^ p⁻¹) := by
  obtain ⟨hT0, hmass, hT⟩ := streamIncrementLpMass_head_tail_gain M hp hnm l
  exact streamIncrementLpNorm_head_tail_of_mass_head_tail M hp l n m
    (streamIncrementLpMassHead_pos M hp hnm).le
    (streamIncrementLpGainScale_pos M hp hnm l).le hT0 hmass hT

end

end Algsuperdiff.Section3.Provider.Stream
