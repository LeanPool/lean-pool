/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# SeriesTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Two weak-Orlicz devices `§4.1` needs and the ambient library does not have

ABK26, §4.1, `l.good.scales.ratio.lambda`, the `𝒴` tail.  The score field

```
𝒴_n := γ^{-4} Σ_{k=-∞}^{n} 3^{-¼γ(n-k)} max_{z ∈ 3^{k-2}ℤ^d ∩ (□_n∖□_{n-1})} (…)_+
```

is an **infinite** weighted sum of **finite maxima**, and the manuscript asserts
an `𝒪_{Γ_{1/3}}` bound for it.  Two generic devices are needed:

1. `isBigOWith_fmax` — the union-bound (`e.maxy.bound`) lift of a `Γ_σ` tail
   through a finite maximum, with the penalty `c` constrained only by `log(#S)
   ≤ c^σ − 1`.  The ambient library's `isBigOWith_gammaSigma_finset_sup'` is
   not usable here: it requires `2 ≤ S.card` and a nonempty `S`, while the §4.1
   lattice annuli must be allowed to be empty (they are, at the degenerate
   indices), and it uses `Finset.sup'` rather than a `0`-floored maximum.

2. `isBigOWith_wsum` — the **countable** generalized triangle inequality: a
   weighted series of nonnegative atoms with individual `Γ_σ` tails and summable
   weighted scales has a `Γ_σ` tail at the scale
   `gammaTriangleConst σ · Σ_j c_j a_j`.  The ambient library has **no**
   `tsum`-level triangle inequality and no monotone-limit stability for `Γ_σ`
   tails; both were checked exhaustively.  The device supplied here is the
   monotone-limit one: the tail event of the series is the increasing union of
   the tail events of the partial sums, and continuity from below
   (`Monotone.measure_iUnion`) turns the uniform finite-sum bound into the
   series bound.  Nothing is assumed about pointwise convergence: the series is
   formed in `ℝ≥0∞`, where it always exists, and `.toReal` sends the divergent
   sample points to `0`, which only helps the upper tail.

## Scope

Provider material: carrier-neutral local helpers over an abstract probability
space.  Every hypothesis is data about an abstract family; no ABK carrier, model
or standing assumption appears.  No `sorry`, no custom axioms, no
`set_option maxHeartbeats`.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open HCPolySupport.IndependentSums MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. The `0`-floored finite maximum -/

/-- **The `0`-floored maximum of `f` over a `Finset`.**  Total (no nonemptiness
side condition) and nonnegative, matching the sign convention of the
manuscript's lattice maxima, all of whose entries are positive parts. -/
def fmax {iota : Type*} (S : Finset iota) (f : iota → ℝ) : ℝ :=
  ((S.sup fun i => (f i).toNNReal : ℝ≥0) : ℝ)

variable {iota : Type*}

theorem fmax_nonneg (S : Finset iota) (f : iota → ℝ) : 0 ≤ fmax S f :=
  NNReal.coe_nonneg _

@[simp] theorem fmax_empty (f : iota → ℝ) : fmax (∅ : Finset iota) f = 0 := by
  simp [fmax]

theorem le_fmax {S : Finset iota} {f : iota → ℝ} {i : iota} (hi : i ∈ S) :
    f i ≤ fmax S f :=
  le_trans (Real.le_coe_toNNReal (f i))
    (NNReal.coe_le_coe.2 (Finset.le_sup (f := fun j => (f j).toNNReal) hi))

theorem fmax_le {S : Finset iota} {f : iota → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ S, f i ≤ b) : fmax S f ≤ b := by
  have hsup : (S.sup fun i => (f i).toNNReal) ≤ b.toNNReal :=
    Finset.sup_le fun i hi => Real.toNNReal_le_toNNReal (h i hi)
  calc fmax S f ≤ ((b.toNNReal : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hsup
    _ = b := Real.coe_toNNReal b hb

/-- **The converse reading of the `0`-floored maximum.**  Above a nonnegative
level the maximum is attained by a genuine member; this is the direction the
union bound consumes, and the nonnegativity of the level is necessary
(`fmax ∅ f = 0`). -/
theorem exists_lt_of_lt_fmax {S : Finset iota} {f : iota → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : b < fmax S f) : ∃ i ∈ S, b < f i := by
  have h1 : b.toNNReal < S.sup fun i => (f i).toNNReal :=
    (Real.toNNReal_lt_iff_lt_coe hb).2 h
  obtain ⟨i, hi, hlt⟩ := Finset.lt_sup_iff.1 h1
  exact ⟨i, hi, (Real.toNNReal_lt_toNNReal_iff_of_nonneg hb).1 hlt⟩

theorem fmax_insert [DecidableEq iota] (i : iota) (S : Finset iota) (f : iota → ℝ) :
    fmax (insert i S) f = max (max (f i) 0) (fmax S f) := by
  refine le_antisymm ?_ ?_
  · refine fmax_le (le_trans (le_max_right (f i) 0) (le_max_left _ _)) ?_
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_trans (le_max_left (f j) 0) (le_max_left _ _)
    · exact le_trans (le_fmax hj) (le_max_right _ _)
  · refine max_le (max_le (le_fmax (Finset.mem_insert_self i S)) (fmax_nonneg _ _)) ?_
    exact fmax_le (fmax_nonneg _ _) fun j hj => le_fmax (Finset.mem_insert_of_mem hj)

theorem measurable_fmax (S : Finset iota) {f : iota → Omega → ℝ}
    (hf : ∀ i, Measurable (f i)) :
    Measurable fun omega => fmax S (fun i => f i omega) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [fmax_empty] using (measurable_const : Measurable fun _ : Omega => (0 : ℝ))
  | @insert i S _hi ih =>
      simp only [fmax_insert]
      exact ((hf i).max measurable_const).max ih

/-! ## 2. The union-bound lift of a `Γ_σ` tail through a finite maximum -/

/-- **`e.maxy.bound` at an abstract finite index set.**

If every member of a finite family has a `Γ_σ` upper tail at the common scale
`A ≥ 0`, then their `0`-floored maximum has one at the scale `c · A`, for any
`c ≥ 1` with `log(#S) ≤ c^σ − 1`.

No nonemptiness and no lower bound on `#S` is required: at `S = ∅` the maximum
is `0` and the bound is vacuous. -/
theorem isBigOWith_fmax {mu : Measure Omega} [IsFiniteMeasure mu] (S : Finset iota)
    {X : iota → Omega → ℝ} {A c sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hcard : Real.log (S.card : ℝ) ≤ c ^ sigma - 1)
    (hX : ∀ i ∈ S, IsBigOWith mu (gammaSigma sigma) (X i) A) :
    IsBigOWith mu (gammaSigma sigma) (fun omega => fmax S (fun i => X i omega)) (c * A) := by
  classical
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc
  have hct : (1 : ℝ) ≤ c * t := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c * t := mul_le_mul hc ht zero_le_one hc0
  have hlev0 : (0 : ℝ) ≤ c * A * t := mul_nonneg (mul_nonneg hc0 hA) ht0
  have hsplit : c * A * t = A * (c * t) := by ring
  -- the union bound
  have hsub : upperTailEvent (fun omega => fmax S (fun i => X i omega)) (c * A * t)
      ⊆ ⋃ i ∈ S, upperTailEvent (X i) (A * (c * t)) := by
    intro omega homega
    obtain ⟨i, hi, hlt⟩ := exists_lt_of_lt_fmax hlev0 homega
    rw [hsplit] at hlt
    exact Set.mem_iUnion₂.2 ⟨i, hi, hlt⟩
  have hterm : ∀ i ∈ S,
      mu.real (upperTailEvent (X i) (A * (c * t))) ≤ Real.exp (-((c * t) ^ sigma)) := by
    intro i hi
    have := (isBigOWith_gammaSigma_iff (μ := mu) (σ := sigma) (X := X i) (A := A)).1 (hX i hi) hct
    exact this
  have hchain : mu.real (upperTailEvent (fun omega => fmax S (fun i => X i omega)) (c * A * t))
      ≤ (S.card : ℝ) * Real.exp (-((c * t) ^ sigma)) := by
    calc mu.real (upperTailEvent (fun omega => fmax S (fun i => X i omega)) (c * A * t))
        ≤ mu.real (⋃ i ∈ S, upperTailEvent (X i) (A * (c * t))) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ i ∈ S, mu.real (upperTailEvent (X i) (A * (c * t))) := by
          simpa using measureReal_biUnion_finset_le S
            (fun i => upperTailEvent (X i) (A * (c * t)))
      _ ≤ ∑ _i ∈ S, Real.exp (-((c * t) ^ sigma)) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * Real.exp (-((c * t) ^ sigma)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hchain ?_
  -- `#S · exp(−(ct)^σ) ≤ exp(−t^σ)` from `log #S ≤ c^σ − 1 ≤ t^σ (c^σ − 1)`
  rcases Nat.eq_zero_or_pos S.card with hzero | hpos
  · rw [hzero]
    simp only [Nat.cast_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hcardR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hpos
    have hcpow : (1 : ℝ) ≤ c ^ sigma := Real.one_le_rpow hc hsigma.le
    have htpow : (1 : ℝ) ≤ t ^ sigma := Real.one_le_rpow ht hsigma.le
    have hmul : (c * t) ^ sigma = c ^ sigma * t ^ sigma := Real.mul_rpow hc0 ht0
    have hkey : Real.log (S.card : ℝ) ≤ (c * t) ^ sigma - t ^ sigma := by
      have hstep : c ^ sigma - 1 ≤ t ^ sigma * (c ^ sigma - 1) :=
        le_mul_of_one_le_left (by linarith only [hcpow]) htpow
      rw [hmul]
      calc Real.log (S.card : ℝ) ≤ c ^ sigma - 1 := hcard
        _ ≤ t ^ sigma * (c ^ sigma - 1) := hstep
        _ = c ^ sigma * t ^ sigma - t ^ sigma := by ring
    calc (S.card : ℝ) * Real.exp (-((c * t) ^ sigma))
        = Real.exp (Real.log (S.card : ℝ)) * Real.exp (-((c * t) ^ sigma)) := by
          rw [Real.exp_log hcardR]
      _ = Real.exp (Real.log (S.card : ℝ) - (c * t) ^ sigma) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(t ^ sigma)) := by
          refine Real.exp_le_exp.2 ?_
          linarith only [hkey]

/-! ## 3. The `ℝ≥0∞`-formed weighted series -/

/-- **The weighted series of a sequence of nonnegative atoms, formed in
`ℝ≥0∞`.**  Total: no summability side condition, and no junk-value hazard,
because `ℝ≥0∞` sums always exist. -/
def wsumE (T : ℕ → Omega → ℝ) (c : ℕ → ℝ) (omega : Omega) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (c j * T j omega)

/-- The real-valued weighted series; at the sample points where the `ℝ≥0∞` sum
is infinite this is `0`, which only strengthens every upper-tail statement made
about it. -/
def wsum (T : ℕ → Omega → ℝ) (c : ℕ → ℝ) (omega : Omega) : ℝ := (wsumE T c omega).toReal

omit [MeasurableSpace Omega] in
theorem wsum_nonneg (T : ℕ → Omega → ℝ) (c : ℕ → ℝ) (omega : Omega) :
    0 ≤ wsum T c omega := ENNReal.toReal_nonneg

omit [MeasurableSpace Omega] in
/-- **Every single term is below the series** — unconditionally, in `ℝ≥0∞`. -/
theorem le_wsumE (T : ℕ → Omega → ℝ) (c : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    ENNReal.ofReal (c j * T j omega) ≤ wsumE T c omega :=
  ENNReal.le_tsum (f := fun j => ENNReal.ofReal (c j * T j omega)) j

/-- The partial sums of the weighted series. -/
def wpartial (T : ℕ → Omega → ℝ) (c : ℕ → ℝ) (N : ℕ) (omega : Omega) : ℝ :=
  ∑ j ∈ Finset.range N, c j * T j omega

omit [MeasurableSpace Omega] in
theorem wsumE_eq_iSup {T : ℕ → Omega → ℝ} {c : ℕ → ℝ}
    (hT0 : ∀ j omega, 0 ≤ T j omega) (hc : ∀ j, 0 ≤ c j) (omega : Omega) :
    wsumE T c omega = ⨆ N : ℕ, ENNReal.ofReal (wpartial T c N omega) := by
  rw [wsumE, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun N => ?_
  rw [wpartial, ENNReal.ofReal_sum_of_nonneg]
  exact fun j _ => mul_nonneg (hc j) (hT0 j omega)

/-! ### The countable generalized triangle inequality -/

/-- A nonnegative random variable's one-sided `Γ_σ` tail is its symmetric one. -/
private theorem isBigO_of_isBigOWith_of_nonneg {mu : Measure Omega} {Psi : ℝ → ℝ}
    {X : Omega → ℝ} {A : ℝ} (hnn : ∀ omega, 0 ≤ X omega)
    (h : IsBigOWith mu Psi X A) : IsBigO mu Psi X A := by
  have hrw : (fun omega => |X omega|) = X := funext fun omega => abs_of_nonneg (hnn omega)
  change IsBigOWith mu Psi (fun omega => |X omega|) A
  rw [hrw]
  exact h

/-- **The partial sums have a `Γ_σ` tail at a scale uniform in `N`.**  The
ambient library's `Finset` triangle inequality, with the partial scale sums
dominated once and for all by the convergent total. -/
private theorem isBigOWith_wpartial {mu : Measure Omega} [IsFiniteMeasure mu]
    {T : ℕ → Omega → ℝ} {c a : ℕ → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hT0 : ∀ j omega, 0 ≤ T j omega) (hTm : ∀ j, Measurable (T j))
    (hc : ∀ j, 0 < c j) (ha : ∀ j, 0 < a j)
    (hsum : Summable fun j => c j * a j)
    (hT : ∀ j, IsBigOWith mu (gammaSigma sigma) (T j) (a j)) (N : ℕ) :
    IsBigOWith mu (gammaSigma sigma) (wpartial T c N)
      (gammaTriangleConst sigma * ∑' j : ℕ, c j * a j) := by
  classical
  set S : ℝ := ∑' j : ℕ, c j * a j with hS
  have hS0 : 0 < S := by
    rw [hS]
    exact hsum.tsum_pos (fun j => (mul_pos (hc j) (ha j)).le) 0 (mul_pos (hc 0) (ha 0))
  have hSle : ∀ N : ℕ, ∑ j ∈ Finset.range N, c j * a j ≤ S :=
    fun N => hsum.sum_le_tsum _ (fun j _ => (mul_pos (hc j) (ha j)).le)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- the empty partial sum is identically `0`
    subst hN
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have hlev : (0 : ℝ) ≤ gammaTriangleConst sigma * S * t :=
      mul_nonneg (mul_nonneg (gammaTriangleConst_pos (σ := sigma)).le hS0.le) ht0
    have hempty : upperTailEvent (wpartial T c 0) (gammaTriangleConst sigma * S * t)
        = (∅ : Set Omega) := by
      ext omega
      simp only [upperTailEvent, wpartial, Finset.range_zero, Finset.sum_empty,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hlev
    rw [hempty, measureReal_empty]
    have hPsi : (0 : ℝ) < gammaSigma sigma t := Real.exp_pos _
    exact (inv_pos.2 hPsi).le
  · have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.2 (by omega)
    have hbigO : IsBigO mu (gammaSigma sigma) (wpartial T c N)
        (gammaTriangleConst sigma * ∑ j ∈ Finset.range N, c j * a j) := by
      refine isBigO_finset_sum_of_isBigO_gammaSigma (Finset.range N)
        (X := fun j omega => c j * T j omega) (a := fun j => c j * a j)
        hsigma hne (fun j _ => mul_pos (hc j) (ha j)) (fun j _ => ?_)
        (fun j _ => (hTm j).const_mul _)
      exact IsBigO.const_mul (hc j).le (isBigO_of_isBigOWith_of_nonneg (hT0 j) (hT j))
    have hmono : IsBigO mu (gammaSigma sigma) (wpartial T c N)
        (gammaTriangleConst sigma * S) :=
      hbigO.mono_scale
        (mul_le_mul_of_nonneg_left (hSle N) (gammaTriangleConst_pos (σ := sigma)).le)
    exact hmono.of_le fun omega => le_abs_self _

/-- **The countable generalized triangle inequality for `Γ_σ` upper tails.**

For nonnegative measurable atoms `T_j` with `T_j ≤ 𝒪_{Γ_σ}(a_j)`, positive
weights `c_j`, and `Σ_j c_j a_j < ∞`,

```
Σ_j c_j T_j ≤ 𝒪_{Γ_σ} ( gammaTriangleConst σ · Σ_j c_j a_j ) ,
```

the series being the total `ℝ≥0∞` one.

The proof is the monotone-limit device: the tail event of the series is the
increasing union of the tail events of the partial sums (in `ℝ≥0∞`, so the
divergent sample points are handled by `.toReal = 0`, which lies below every
positive level), the partial sums obey the finite triangle inequality at the
`N`-uniform scale, and continuity from below closes it. -/
theorem isBigOWith_wsum {mu : Measure Omega} [IsFiniteMeasure mu]
    {T : ℕ → Omega → ℝ} {c a : ℕ → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hT0 : ∀ j omega, 0 ≤ T j omega) (hTm : ∀ j, Measurable (T j))
    (hc : ∀ j, 0 < c j) (ha : ∀ j, 0 < a j)
    (hsum : Summable fun j => c j * a j)
    (hT : ∀ j, IsBigOWith mu (gammaSigma sigma) (T j) (a j)) :
    IsBigOWith mu (gammaSigma sigma) (wsum T c)
      (gammaTriangleConst sigma * ∑' j : ℕ, c j * a j) := by
  classical
  set S : ℝ := ∑' j : ℕ, c j * a j with hS
  set K : ℝ := gammaTriangleConst sigma * S with hK
  have hS0 : 0 < S := by
    rw [hS]
    exact hsum.tsum_pos (fun j => (mul_pos (hc j) (ha j)).le) 0 (mul_pos (hc 0) (ha 0))
  have hK0 : 0 < K := mul_pos (gammaTriangleConst_pos (σ := sigma)) hS0
  have hpart := isBigOWith_wpartial hsigma hT0 hTm hc ha hsum hT
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hlev0 : (0 : ℝ) ≤ K * t := mul_nonneg hK0.le ht0
  set Ev : ℕ → Set Omega := fun N => upperTailEvent (wpartial T c N) (K * t) with hEv
  -- the partial sums increase, hence so do their tail events
  have hmono : Monotone Ev := by
    refine monotone_nat_of_le_succ fun N omega homega => ?_
    have hstep : wpartial T c N omega ≤ wpartial T c (N + 1) omega := by
      rw [wpartial, wpartial, Finset.sum_range_succ]
      have : 0 ≤ c N * T N omega := mul_nonneg (hc N).le (hT0 N omega)
      linarith only [this]
    exact lt_of_lt_of_le homega hstep
  -- the tail event of the series sits inside the increasing union
  have hsub : upperTailEvent (wsum T c) (K * t) ⊆ ⋃ N : ℕ, Ev N := by
    intro omega homega
    have hlt : K * t < (wsumE T c omega).toReal := homega
    have hne : wsumE T c omega ≠ (⊤ : ℝ≥0∞) := by
      intro htop
      rw [htop] at hlt
      simp only [ENNReal.toReal_top] at hlt
      exact absurd hlt (not_lt.2 hlev0)
    have hE : ENNReal.ofReal (K * t) < wsumE T c omega :=
      (ENNReal.ofReal_lt_iff_lt_toReal hlev0 hne).2 hlt
    rw [wsumE_eq_iSup hT0 (fun j => (hc j).le)] at hE
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hE
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlev0).1 hN
  -- continuity from below
  have hEvbound : ∀ N : ℕ, mu (Ev N) ≤ ENNReal.ofReal (Real.exp (-(t ^ sigma))) := by
    intro N
    have hreal : mu.real (Ev N) ≤ Real.exp (-(t ^ sigma)) :=
      (isBigOWith_gammaSigma_iff (μ := mu) (σ := sigma) (X := wpartial T c N) (A := K)).1
        (hpart N) ht
    have hfin : mu (Ev N) = ENNReal.ofReal (mu.real (Ev N)) :=
      (ENNReal.ofReal_toReal (measure_ne_top mu (Ev N))).symm
    rw [hfin]
    exact ENNReal.ofReal_le_ofReal hreal
  have hunion : mu (⋃ N : ℕ, Ev N) ≤ ENNReal.ofReal (Real.exp (-(t ^ sigma))) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hEvbound
  calc mu.real (upperTailEvent (wsum T c) (K * t))
      ≤ mu.real (⋃ N : ℕ, Ev N) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (ENNReal.ofReal (Real.exp (-(t ^ sigma)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion
    _ = Real.exp (-(t ^ sigma)) := ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- **Measurability of the weighted series.**  The `ℝ≥0∞` sum of measurable
nonnegative terms is measurable, and `.toReal` is measurable. -/
theorem measurable_wsum {T : ℕ → Omega → ℝ} {c : ℕ → ℝ}
    (hTm : ∀ j, Measurable (T j)) : Measurable (wsum T c) := by
  have h : Measurable (wsumE T c) := by
    refine Measurable.tsum fun j => ?_
    exact ((hTm j).const_mul (c j)).ennreal_ofReal
  exact h.ennreal_toReal

end

end Algsuperdiff.Section4.Provider.Proportion
