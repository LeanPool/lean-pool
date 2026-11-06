/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Walk
public import LeanPool.RareSubtreePatterns.RegularVariation.Defs

import LeanPool.RareSubtreePatterns.RegularVariation.Consequences

/-!
# The random-walk toolkit

Source lines 837–883 ("Random walk toolbox"), inventory B06–B10, B14.

The bridge estimates of Sections 3–5 of the paper (forest estimates, microscopicity, bridge
removal, truncation, the Chen–Stein error terms, Theorems 1.1 and 1.2) use only a handful of
facts about the Łukasiewicz walk `S_m = X_1 + ⋯ + X_m` (`Ψ_m(x) = walkProb μ m x`) and its
normalizing sequence `a`. `StableToolkit μ α a` collects exactly these facts, stated as honest
inequalities and limits about `walkProb`, `walkLaw` and `a`. The bridge lemmas of Sections 3–5 take
this structure as their hypothesis; it is **derived** from the paper's standing assumption by

  `PoissonDeclumping.Stable.stableToolkit : StableDomain μ α a → StableToolkit μ α a`

(`Stable/ToolkitProof.lean`), so the final theorems (`MainTheorems.lean`) assume only `(H_α)`.
No field states a conclusion of a paper lemma; each field is a direct consequence of the
(lattice) local limit theorem, of tightness of `S_m / a_m`, or of regular variation of `a`.

## Periodic offspring laws

Periodic laws are **not** excluded. With `d = gcd {i - j : μ_i μ_j > 0}` (the span; `μ_0 > 0`
for critical `μ ≠ δ_1`, so every step is `≡ -1 (mod d)`), `S_m ∈ -m + dℤ` almost surely and the
lattice local limit theorem (source lines 867–876) reads
`sup_{x ∈ -m + dℤ} |a_m Ψ_m(x) - d · p_α(x / a_m)| → 0`, where `p_α` is the density of `Y_α`.
The stable density is *not* introduced: `LatticeLocal μ a d L` records only the three
consequences that the proofs use, with `L = d · p_α(0) > 0`:

* `support`: `Ψ_m(x) ≠ 0 → d ∣ x + m` (compatible endpoints);
* `origin`: `a_n Ψ_n(x) → L` uniformly over compatible `|x| ≤ η a_n` (continuity of `p_α` at
  `0` and `p_α(0) > 0`);
* `equicont`: `|a_n Ψ_n(x) - a_n Ψ_n(y)|` is small uniformly over compatible `x, y` with
  `|x - y| ≤ η a_n` (uniform continuity of `p_α`).

Every uniform statement is restricted to compatible lattice points, so no conditional law at
a zero-probability endpoint is ever used.

## Consequences proved here (from the fields only)

* `StableToolkit.rho_pos`, `rho_lt_one`, `tendsto_atTop`: `0 < 1/α < 1`, `a_n → ∞`.
* `StableToolkit.exists_le_div_of_le_two_mul`: `Ψ_m(x) ≤ C / a_n` whenever `n ≤ 2m`.
* `StableToolkit.exists_eventually_le_sub`: `a_{t-j} ≥ (1 - ε) a_t` for `j ≤ δ t`.
* `StableToolkit.eventually_abs_mul_sub_le`, `eventually_bounds`,
  `eventually_abs_div_sub_one_le`: for total lengths `N_n → ∞`, `m_n = o(N_n)` and
  `z_n = o(a_{N_n})`, `a_{N_n} Ψ_{N_n-j}(x) → L` and `Ψ_{N_n-j}(x) / Ψ_{N_n}(y) → 1` uniformly
  over `j ≤ m_n` and compatible `|x|, |y| ≤ z_n` (the "ratio → 1" step of source lines 965,
  1033, 1236, 1293, 1752, 2067, 2293, and the lower bounds of lines 1647, 1958, 1981).
* `StableToolkit.exists_lower_bound_neg_one`: `Ψ_n(-1) ≥ c / a_n` for **every** `n ≥ 1` with
  `Ψ_n(-1) > 0`, i.e. at every admissible size (Dwass), with one constant `c`.
* `StableToolkit.eventually_walkProb_neg_one_pos_iff`: for large `n`, `Ψ_n(-1) > 0 ↔ d ∣ n - 1`
  (in the aperiodic case `d = 1` all large `n` are admissible).
* `StableToolkit.eventually_walkLaw_tail_le`: if `r_n / a_{M_n} → ∞` then
  `max_{i ≤ M_n} P(|S_i| > r_n) → 0` (the only use of "maximal tightness", lines 1763–1770,
  1912; marginal uniform tightness suffices).
* `isProbabilityMeasure_walkLaw`: each `walkLaw μ m` is a probability measure (a definitional
  fact needed above, recorded as an instance).
-/

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace PoissonDeclumping

/-- The lattice local limit theorem, without the stable density (source lines 860–883,
inventory B09). `d` is the span of the walk (`S_m ∈ -m + dℤ` a.s.) and `L = d · p_α(0)` with
`p_α` the density of `Y_α`.

* `support` (lines 876–879): outside the lattice `-m + dℤ` the probability is zero. Used to show
  that the endpoints met in the proofs are compatible: `P(|𝒯| = m) > 0 → d ∣ m - 1` (via
  Dwass), `S_M ∈ -M + dℤ`, hence `0` is compatible with `n - |𝒯|` and `-1 - S_M` with `n - M`
  at admissible `n` (lines 965, 1033, 1293, 1752, 2067, 2293).
* `origin` (`eq:LL` plus continuity and positivity of `p_α` at `0`): `a_n Ψ_n(x) → L` uniformly
  over compatible `|x| ≤ η a_n`. Used for every lower bound `Ψ_n(k) ≥ c / a_n` (lines 1034,
  1164, 1231, 1329, 1647, 1774, 1981, 2069) and every ratio limit
  `Ψ_{n-m}(x) / Ψ_n(-1) → 1` (lines 965, 1033, 1236, 1293, 1752, 2067, 2293).
* `equicont` (`eq:LL` plus uniform continuity of `p_α`): replaces the Skorokhod/dominated
  convergence endpoint smoothing in the proof of `eq:approx3` (lines 1968–1994, B14); the
  smoothing becomes a deterministic uniform bound. -/
structure LatticeLocal (μ : PMF ℕ) (a : ℕ → ℝ) (d : ℕ) (L : ℝ) : Prop where
  d_pos : 0 < d
  L_pos : 0 < L
  support : ∀ (m : ℕ) (x : ℤ), walkProb μ m x ≠ 0 → (d : ℤ) ∣ x + m
  origin : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℤ,
    (d : ℤ) ∣ x + n → |(x : ℝ)| ≤ η * a n → |a n * walkProb μ n x - L| ≤ ε
  equicont : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x y : ℤ,
    (d : ℤ) ∣ x + n → (d : ℤ) ∣ y + n → |((x - y : ℤ) : ℝ)| ≤ η * a n →
    |a n * walkProb μ n x - a n * walkProb μ n y| ≤ ε

/-- **The random-walk toolkit** used by the bridge estimates of Sections 3–5 (source lines
837–883). A temporary conditional interface: it must be derived from `StableDomain μ α a`.

* `critical`, `nondegenerate`, `alpha_mem`: the standing hypotheses `(H_α)` (lines 705–712),
  copied from `StableDomain` so that bridge lemmas need a single hypothesis.
* `monotone`, `pos`, `regularlyVarying` (lines 846–853, B06/B08): `a` is increasing, positive,
  regularly varying of index `1/α`. Potter bounds, `a_{M_n}/a_n → 0`, `a_{n-o(n)}/a_n → 1`,
  `a_n = o(n)`, `a_n = n^{1/α+o(1)}` and Karamata's sums are theorems of
  `PoissonDeclumping.RegularVariation.*` and are not fields. Used at lines 1087–1105, 1145–1177,
  1218, 1346–1348, 1752, 1896, 1958, 1986, 2244.
* `sup_le` (local bound "following from `eq:LL`", B10): `Ψ_m(x) ≤ C / a_m` for all `m ≥ 1`
  and all `x`. Used at lines 1034, 1140, 1161, 1176, 1340, 1647, 1774, 1983, 2069, 2254.
* `tight` (B07, only in its marginal form): `S_m / a_m` is tight, uniformly in `m ≥ 1`. The
  paper invokes functional convergence (`eq:cvlaw`) for `max_{i ≤ M_n} P(|S_i| > r_n - 1) → 0`
  (lines 1763–1770) and convergence in law of `S_{M_n}/a_{M_n}` (line 1912); both only need
  this. Used through `eventually_walkLaw_tail_le`.
* `lattice`: the lattice local limit theorem, see `LatticeLocal`. -/
structure StableToolkit (μ : PMF ℕ) (α : ℝ) (a : ℕ → ℝ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  alpha_mem : 1 < α ∧ α ≤ 2
  monotone : Monotone a
  pos : ∀ n : ℕ, 1 ≤ n → 0 < a n
  regularlyVarying : RegularlyVaryingSeq (1 / α) a
  sup_le : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ x : ℤ, walkProb μ m x ≤ C / a m
  tight : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m →
    (walkLaw μ m).real {x : ℤ | K * a m < |(x : ℝ)|} ≤ ε
  lattice : ∃ (d : ℕ) (L : ℝ), LatticeLocal μ a d L

instance isProbabilityMeasure_stepLaw (μ : PMF ℕ) : IsProbabilityMeasure (stepLaw μ) := by
  unfold stepLaw
  infer_instance

theorem isProbabilityMeasure_walkLaw' (μ : PMF ℕ) (m : ℕ) :
    IsProbabilityMeasure (walkLaw μ m) := by
  induction m with
  | zero => rw [walkLaw]; infer_instance
  | succ m ih => rw [walkLaw]; infer_instance

instance isProbabilityMeasure_walkLaw (μ : PMF ℕ) (m : ℕ) :
    IsProbabilityMeasure (walkLaw μ m) :=
  isProbabilityMeasure_walkLaw' μ m

/-- `Ψ_m(x) = P(S_m = x)` at a natural time. -/
theorem walkProb_natCast_real (μ : PMF ℕ) (m : ℕ) (x : ℤ) :
    walkProb μ m x = (walkLaw μ m).real {x} := by
  simp [walkProb]

private theorem exists_pos_le_of_finset (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n ∈ s, 0 < f n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ∈ s, c ≤ f n := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  · exact ⟨s.inf' hs f, (Finset.lt_inf'_iff hs).2 hf, fun n hn => Finset.inf'_le f hn⟩

namespace StableToolkit

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

theorem rho_pos (hT : StableToolkit μ α a) : 0 < 1 / α := by
  have := hT.alpha_mem.1
  positivity

theorem rho_lt_one (hT : StableToolkit μ α a) : 1 / α < 1 := by
  have h := hT.alpha_mem.1
  rw [div_lt_one (by linarith)]
  exact h

/-- `a_n → ∞`. -/
theorem tendsto_atTop (hT : StableToolkit μ α a) : Tendsto a atTop atTop :=
  hT.regularlyVarying.tendsto_atTop hT.monotone hT.pos hT.rho_pos

/-- The local bound at comparable times: `Ψ_m(x) ≤ C / a_n` whenever `n ≤ 2m` (lines 1161–1164,
1340, 1647, 1774, 2069: `Ψ_{n-q}`, `Ψ_{n-c}`, `Ψ_{n-m_n}`, `Ψ_{n-2M_n}` are `O(1/a_n)`). -/
theorem exists_le_div_of_le_two_mul (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≤ 2 * m → ∀ x : ℤ,
      walkProb μ m x ≤ C / a n := by
  obtain ⟨C₀, hC₀⟩ := hT.sup_le
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le 2
  refine ⟨max C₀ 0 * C₁, by positivity, fun n m hn hm hnm x => ?_⟩
  have ham : 0 < a m := hT.pos m hm
  have han : 0 < a n := hT.pos n hn
  have h1 : a n ≤ C₁ * a m := hC₁ m n hm (by exact_mod_cast hnm)
  calc walkProb μ m x ≤ C₀ / a m := hC₀ m hm x
    _ ≤ max C₀ 0 / a m := by gcongr; exact le_max_left _ _
    _ = max C₀ 0 * C₁ / (C₁ * a m) := by field_simp
    _ ≤ max C₀ 0 * C₁ / a n := by gcongr

/-- Uniform regular variation below a time: for every `ε > 0` there is `δ > 0` with
`a_{t-j} ≥ (1 - ε) a_t` for all `j ≤ δ t`, for all large `t`. -/
theorem exists_eventually_le_sub (hT : StableToolkit μ α a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ t : ℕ in atTop, ∀ j : ℕ, (j : ℝ) ≤ δ * t →
      (1 - ε) * a t ≤ a (t - j) := by
  have hα := hT.alpha_mem.1
  set e : ℝ := min ε 1 / 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 2 := by have := min_le_right ε 1; linarith
  have heε : 2 * e ≤ ε := by have := min_le_left ε 1; linarith
  set c : ℝ := (1 - e) ^ α with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by linarith) α
  have hc1 : c < 1 := Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
  have hcρ : c ^ (1 / α) = 1 - e := by
    rw [hc, one_div, Real.rpow_rpow_inv (by linarith) (by linarith)]
  refine ⟨1 - c, by linarith, by linarith, ?_⟩
  filter_upwards [hT.regularlyVarying.eventually_bounds hc0 he0, eventually_ge_atTop 1]
    with t ht ht1 j hj
  have hat : 0 < a t := hT.pos t ht1
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hjt : j ≤ t := by
    have : (j : ℝ) ≤ t := by nlinarith
    exact_mod_cast this
  have hfl : ⌊c * t⌋₊ ≤ t - j := by
    apply Nat.floor_le_of_le
    rw [Nat.cast_sub hjt]
    linarith
  have h1 := ht.1
  rw [hcρ, lt_div_iff₀ hat] at h1
  have h2 : a ⌊c * t⌋₊ ≤ a (t - j) := hT.monotone hfl
  have h3 : 1 - ε ≤ (1 - e) * (1 - e) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h3 hat.le]

/-- **Microscopic flatness.** Let `N n → ∞` be a sequence of total lengths, `m_n = o(N_n)` and
`z_n = o(a_{N_n})`. Then `a_{N_n} Ψ_{N_n - j}(x) → L` uniformly over `j ≤ m_n` and
lattice-compatible `|x| ≤ z_n`. (With `N n = n`: `a_n Ψ_{n-j}(x) → L`.) -/
theorem eventually_abs_mul_sub_le (hT : StableToolkit μ α a) {d : ℕ} {L : ℝ}
    (hloc : LatticeLocal μ a d L) {N m : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (N n : ℝ)))
    {z : ℕ → ℝ} (hz : z =o[atTop] (fun n => a (N n))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j : ℕ, j ≤ m n → ∀ x : ℤ, (d : ℤ) ∣ x + ((N n - j : ℕ) : ℤ) →
      |(x : ℝ)| ≤ z n → |a (N n) * walkProb μ ((N n - j : ℕ) : ℤ) x - L| ≤ ε := by
  have hL := hloc.L_pos
  obtain ⟨η, hη, N₀, hN₀⟩ := hloc.origin (ε / 2) (by positivity)
  set ε₂ : ℝ := min (1 / 2) (ε / (4 * (L + ε))) with hε₂
  have hε₂pos : 0 < ε₂ := lt_min (by norm_num) (by positivity)
  have hε₂half : ε₂ ≤ 1 / 2 := min_le_left _ _
  have hε₂ε : ε₂ ≤ ε / (4 * (L + ε)) := min_le_right _ _
  obtain ⟨δ, hδ0, hδ1, hRV⟩ := hT.exists_eventually_le_sub hε₂pos
  have hz' := hz.def (show (0 : ℝ) < η / 2 by positivity)
  have hm' := hm.def (show (0 : ℝ) < min δ (1 / 2) by positivity)
  filter_upwards [hN.eventually hRV, hz', hm', hN.eventually_ge_atTop (2 * N₀ + 1)]
    with n hRVn hzn hmn hn
  intro j hj x hdx hx
  have hn1 : 1 ≤ N n := by omega
  have han : 0 < a (N n) := hT.pos (N n) hn1
  have hmn' : (m n : ℝ) ≤ min δ (1 / 2) * N n := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hmn
  have hjR : (j : ℝ) ≤ m n := by exact_mod_cast hj
  have h2m : 2 * m n ≤ N n := by
    have h2 : ((2 * m n : ℕ) : ℝ) ≤ N n := by
      push_cast
      have hmin := min_le_right δ (1 / 2)
      have hnonnegative : (0 : ℝ) ≤ N n := by positivity
      nlinarith only [hmn', hmin, hnonnegative]
    exact_mod_cast h2
  have hNj : N₀ ≤ N n - j := by omega
  have hj1 : 1 ≤ N n - j := by omega
  have hlow : (1 - ε₂) * a (N n) ≤ a (N n - j) := by
    refine hRVn j ?_
    have hmin := min_le_left δ (1 / 2)
    have hnonnegative : (0 : ℝ) ≤ N n := by positivity
    nlinarith only [hjR, hmn', hmin, hnonnegative]
  have hup : a (N n - j) ≤ a (N n) := hT.monotone (Nat.sub_le _ _)
  have hb : 0 < a (N n - j) := hT.pos _ hj1
  have hzle : z n ≤ η / 2 * a (N n) := by
    have h := hzn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos han] at h
    exact (le_abs_self _).trans h
  have hhalf : a (N n) / 2 ≤ a (N n - j) := by
    nlinarith only [hlow, hε₂half, han]
  have hxη : |(x : ℝ)| ≤ η * a (N n - j) := by
    nlinarith only [hx, hzle, hhalf, hη]
  have hu := hN₀ (N n - j) hNj x hdx hxη
  set B := a (N n - j) with hB
  set A := a (N n) with hA
  set P := walkProb μ ((N n - j : ℕ) : ℤ) x with hP
  have hAB : A / B - 1 ≤ 2 * ε₂ := by
    rw [div_sub_one hb.ne', div_le_iff₀ hb]
    nlinarith only [hlow, hhalf, hε₂pos]
  have hAB0 : 0 ≤ A / B - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]
    linarith
  have hu' : |B * P| ≤ L + ε / 2 := by
    have h := abs_sub_abs_le_abs_sub (B * P) L
    rw [abs_of_pos hL] at h
    linarith
  have key : A * P - L = (A / B - 1) * (B * P) + (B * P - L) := by
    field_simp
    ring
  have hε₂L : ε₂ * (L + ε) ≤ ε / 4 := by
    calc ε₂ * (L + ε) ≤ ε / (4 * (L + ε)) * (L + ε) := by gcongr
      _ = ε / 4 := by field_simp
  rw [key]
  calc |(A / B - 1) * (B * P) + (B * P - L)|
      ≤ |(A / B - 1) * (B * P)| + |B * P - L| := abs_add_le _ _
    _ = (A / B - 1) * |B * P| + |B * P - L| := by rw [abs_mul, abs_of_nonneg hAB0]
    _ ≤ (2 * ε₂) * (L + ε / 2) + ε / 2 := by gcongr
    _ ≤ ε := by nlinarith only [hε₂L, hε₂pos, hε]

/-- Two-sided local bounds `L / (2 a_{N_n}) ≤ Ψ_{N_n - j}(x) ≤ 2L / a_{N_n}`, uniformly over
`j ≤ m_n` (`m_n = o(N_n)`) and compatible `|x| ≤ z_n` (`z_n = o(a_{N_n})`); e.g.
`Ψ_n(k) ≥ c / a_n` for compatible `|k| ≤ z_n` (line 1647). -/
theorem eventually_bounds (hT : StableToolkit μ α a) {d : ℕ} {L : ℝ}
    (hloc : LatticeLocal μ a d L) {N m : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (N n : ℝ)))
    {z : ℕ → ℝ} (hz : z =o[atTop] (fun n => a (N n))) :
    ∀ᶠ n in atTop, ∀ j : ℕ, j ≤ m n → ∀ x : ℤ, (d : ℤ) ∣ x + ((N n - j : ℕ) : ℤ) →
      |(x : ℝ)| ≤ z n →
      L / 2 / a (N n) ≤ walkProb μ ((N n - j : ℕ) : ℤ) x ∧
        walkProb μ ((N n - j : ℕ) : ℤ) x ≤ 2 * L / a (N n) := by
  have hL := hloc.L_pos
  filter_upwards [hT.eventually_abs_mul_sub_le hloc hN hm hz (half_pos hL),
    hN.eventually_ge_atTop 1] with n hn hn1 j hj x hdx hx
  have han : 0 < a (N n) := hT.pos (N n) hn1
  have h := abs_le.1 (hn j hj x hdx hx)
  constructor
  · rw [div_le_iff₀ han]
    linarith
  · rw [le_div_iff₀ han]
    linarith

/-- **Ratio limit at compatible endpoints.** For `N_n → ∞`, `m_n = o(N_n)` and
`z_n = o(a_{N_n})`, `Ψ_{N_n - j}(x) / Ψ_{N_n}(y) → 1` uniformly over `j ≤ m_n` and compatible
`|x|, |y| ≤ z_n` (the lattice factor `d` cancels, lines 877–879). -/
theorem eventually_abs_div_sub_one_le (hT : StableToolkit μ α a) {d : ℕ} {L : ℝ}
    (hloc : LatticeLocal μ a d L) {N m : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (N n : ℝ)))
    {z : ℕ → ℝ} (hz : z =o[atTop] (fun n => a (N n))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ j : ℕ, j ≤ m n → ∀ x y : ℤ, (d : ℤ) ∣ x + ((N n - j : ℕ) : ℤ) →
      (d : ℤ) ∣ y + (N n : ℤ) → |(x : ℝ)| ≤ z n → |(y : ℝ)| ≤ z n →
      |walkProb μ ((N n - j : ℕ) : ℤ) x / walkProb μ (N n : ℤ) y - 1| ≤ ε := by
  have hL := hloc.L_pos
  set ε' : ℝ := min (L / 2) (ε * L / 4) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'1 : ε' ≤ L / 2 := min_le_left _ _
  have hε'2 : ε' ≤ ε * L / 4 := min_le_right _ _
  filter_upwards [hT.eventually_abs_mul_sub_le hloc hN hm hz hε'pos,
    hN.eventually_ge_atTop 1] with n hn hn1 j hj x y hdx hdy hxz hyz
  have han : 0 < a (N n) := hT.pos (N n) hn1
  have hu := abs_le.1 (hn j hj x hdx hxz)
  have hv := abs_le.1 (hn 0 (Nat.zero_le _) y (by simpa using hdy) hyz)
  simp only [Nat.sub_zero] at hv
  set P := walkProb μ ((N n - j : ℕ) : ℤ) x with hP
  set Q := walkProb μ (N n : ℤ) y with hQ
  have hQpos : 0 < Q := by
    have : 0 < a (N n) * Q := by linarith
    exact pos_of_mul_pos_right this han.le
  rw [div_sub_one hQpos.ne', abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos, abs_le]
  constructor <;> nlinarith

/-- **Global lower bound at admissible sizes.** One constant `c > 0` with
`Ψ_n(-1) ≥ c / a_n` for every `n ≥ 1` such that `Ψ_n(-1) > 0` (by Dwass, every admissible
`n`): lines 1164, 1231, 1329 ("`Ψ_n(-1) ≍ 1/a_n`", "`P(|𝒯| = n) ≍ 1/(n a_n)` along admissible
`n`") and the constant of Corollary `cor:pip` (line 1653, "for every `n ≥ 1`"). -/
theorem exists_lower_bound_neg_one (hT : StableToolkit μ α a) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → 0 < walkProb μ n (-1) →
      c / a n ≤ walkProb μ n (-1) := by
  obtain ⟨d, L, hloc⟩ := hT.lattice
  have hL := hloc.L_pos
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] a := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  have hm : (fun _ : ℕ => ((0 : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    simp
  obtain ⟨N₀, hN₀⟩ :=
    (hT.eventually_bounds hloc (N := fun n => n) tendsto_id hm hz).exists_forall_of_atTop
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_le_of_finset
    ((Finset.range N₀).filter fun n => 1 ≤ n ∧ 0 < walkProb μ n (-1))
    (fun n => a n * walkProb μ n (-1)) (by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      exact mul_pos (hT.pos n hn.2.1) hn.2.2)
  refine ⟨min (L / 2) c₀, lt_min (half_pos hL) hc₀, fun n hn hpos => ?_⟩
  have han := hT.pos n hn
  rcases lt_or_ge n N₀ with h | h
  · have h1 := hc₀le n (by simp [h, hn, hpos])
    rw [div_le_iff₀ han]
    have := min_le_right (L / 2) c₀
    linarith
  · have hd : (d : ℤ) ∣ (-1) + ((n - 0 : ℕ) : ℤ) := by
      simpa using hloc.support n (-1) hpos.ne'
    obtain ⟨h1, -⟩ := hN₀ n h 0 le_rfl (-1) hd (by simp)
    simp only [Nat.sub_zero] at h1
    calc min (L / 2) c₀ / a n ≤ L / 2 / a n := by gcongr; exact min_le_left _ _
      _ ≤ _ := h1

/-- **Admissible sizes on the lattice.** For all large `n`, `Ψ_n(-1) > 0` iff `d ∣ n - 1`. In
the aperiodic case (`d = 1`) every large `n` has `Ψ_n(-1) > 0`, i.e. is admissible
(lines 860, 703). -/
theorem eventually_walkProb_neg_one_pos_iff (hT : StableToolkit μ α a) {d : ℕ} {L : ℝ}
    (hloc : LatticeLocal μ a d L) :
    ∀ᶠ n : ℕ in atTop, (0 < walkProb μ n (-1) ↔ (d : ℤ) ∣ (n : ℤ) - 1) := by
  have hL := hloc.L_pos
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] a := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  have hm : (fun _ : ℕ => ((0 : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    simp
  filter_upwards [hT.eventually_bounds hloc (N := fun n => n) tendsto_id hm hz,
    eventually_ge_atTop 1] with n hn hn1
  have han := hT.pos n hn1
  constructor
  · intro hpos
    have h := hloc.support n (-1) hpos.ne'
    rwa [show (-1 : ℤ) + n = n - 1 by ring] at h
  · intro hd
    have hd' : (d : ℤ) ∣ (-1) + ((n - 0 : ℕ) : ℤ) := by
      simpa [show (-1 : ℤ) + n = n - 1 by ring] using hd
    obtain ⟨h1, -⟩ := hn 0 le_rfl (-1) hd' (by simp)
    simp only [Nat.sub_zero] at h1
    exact lt_of_lt_of_le (by positivity) h1

/-- **Uniform tails at small times.** If `r_n / a_{M_n} → ∞` (e.g. `r_n = √(a_{M_n} a_n)`,
`RegularlyVaryingSeq.tendsto_sqrt_div`), then `max_{i ≤ M_n} P(|S_i| > r_n) → 0`. This is the
form in which the paper uses tightness of `(S_{⌊M_n t⌋}/a_{M_n})` (lines 1763–1770) and the
convergence in law of `S_{M_n}/a_{M_n}` (line 1912). -/
theorem eventually_walkLaw_tail_le (hT : StableToolkit μ α a) {M : ℕ → ℕ} {r : ℕ → ℝ}
    (hM : ∀ᶠ n in atTop, 1 ≤ M n) (hr : Tendsto (fun n => r n / a (M n)) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i : ℕ, i ≤ M n → (walkLaw μ i).real {x : ℤ | r n < |(x : ℝ)|} ≤ ε := by
  obtain ⟨K, hK⟩ := hT.tight ε hε
  filter_upwards [hM, hr.eventually_ge_atTop (max K 0)] with n hMn hrn i hi
  have haM : 0 < a (M n) := hT.pos _ hMn
  have hr' : max K 0 * a (M n) ≤ r n := by rwa [le_div_iff₀ haM] at hrn
  have hr0 : 0 ≤ r n := le_trans (by positivity) hr'
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have h0 : (0 : ℤ) ∉ {x : ℤ | r n < |(x : ℝ)|} := by simp; linarith
    have : (walkLaw μ 0).real {x : ℤ | r n < |(x : ℝ)|} = 0 := by
      simp only [walkLaw, Measure.real, Measure.dirac_apply, Set.indicator_of_notMem h0]
      simp
    rw [this]
    exact hε.le
  · refine le_trans (measureReal_mono ?_) (hK i hi1)
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hai : 0 < a i := hT.pos i hi1
    have : K * a i ≤ max K 0 * a (M n) := by
      calc K * a i ≤ max K 0 * a i := by gcongr; exact le_max_left _ _
        _ ≤ max K 0 * a (M n) := by gcongr; exact hT.monotone hi
    linarith

end StableToolkit

end PoissonDeclumping
