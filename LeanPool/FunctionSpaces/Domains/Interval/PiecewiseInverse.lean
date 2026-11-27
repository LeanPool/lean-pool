/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseJackson
public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inverse inequality for dyadic piecewise polynomials

For a piecewise polynomial `a` of level `j` and degree `< r` and every `k`,
`ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p`, with `k - j` truncated at `0`
(`Interval.exists_inverse_ppScheme`). For `0 ≤ h ≤ 2^(-k)` the difference `Δ_h^r a(x)` vanishes
when `x, …, x + rh` lie in one dyadic interval, since there `a` is a polynomial of degree `< r`
(`Interval.higherDiff_eq_zero_of_isPiecewisePoly`). The other points form strips of width `rh`
left of the knots. There Nikolskii's inequality bounds `|a|` by `2^(j/p)` times the local `L_p`
norm of a piece (`Interval.enorm_le_localMass`), and the points `x, …, x + rh` meet only `r + 1`
consecutive pieces (`Interval.floor_add_mul_le`), so each piece is counted at most `r + 1` times
(`Interval.sum_sum_localMass_le`). The same pointwise bound holds for differences of every order
`m ≤ r` (`Interval.enorm_higherDiff_le_of_isPiecewisePoly_of_le`). The strip integral
(`Interval.eLpNorm_le_of_strip`) turns a pointwise bound on the strips into the `L_p` bound
(`Interval.eLpNorm_higherDiff_le_of_pointwise`);
the splines of `FunctionSpaces.Domains.Interval.SplineInverse` use it with their own pointwise
bound, and the step functions in `L_p`, `0 < p ≤ 1`, of
`FunctionSpaces.Wavelets.Examples.DyadicStepsQuasiBanach` with theirs: the strip integral holds
for every `0 < p < ∞`. These local estimates hold for every piecewise polynomial on `[0, ∞)`
(`Interval.IsPiecewisePoly`, `Interval.eLpNorm_higherDiff_le_of_isPiecewisePoly`), so they serve
the periodic extensions of `FunctionSpaces.Domains.Interval.PiecewisePeriodic` as well.

With Jackson's inequality at every level (`Interval.exists_approxError_ppScheme_le`) this is a
modulus compatible with the scheme, of inverse order `θ = 1/p` (`Interval.ppModulusData`), and the
abstract coincidence theorem gives, for
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_ppScheme_iff`). For `0 < s < 1/p` the approximation space of dyadic
piecewise polynomials is therefore the Besov space `B^s_{p,q}[0, 1]` defined by moduli of
smoothness. The bound `s < 1/p` belongs to the method: the indicator of `[0, 1/2)` is a piecewise
polynomial of level `1` with `ω_r(·, t)_p` of order `t^(1/p)`. Higher smoothness needs
piecewise polynomials that are smooth across the knots, that is, splines.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff measurable_higherDiff)
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The **local mass** `∫_{I_{k,m}} |u|^p` of `u` on the dyadic interval `I_{k,m}`. -/
noncomputable def localMass (k : ℕ) (u : ℝ → ℂ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in dyadicIco k m, ‖u x‖ₑ ^ p.toReal

/-- The local masses of a piecewise polynomial add up to at most `‖u‖_p^p`. -/
theorem tsum_localMass_ppFun_le (hp : p ≠ ∞) (k : ℕ) (Q : ℕ → ℂ[X]) :
    ∑' m, localMass p k (ppFun k Q) m ≤ eLpNorm (ppFun k Q) p unitVol ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_rpow_eq (measurable_ppFun k Q).aestronglyMeasurable hp0 hp]
  unfold localMass
  rw [← lintegral_iUnion (measurableSet_dyadicIco k) (pairwise_disjoint_dyadicIco k)]
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  refine (setLIntegral_eq_of_support_subset fun x hx => ?_).symm
  by_contra hx'
  refine hx ?_
  dsimp only
  rw [ppFun_eq_zero Q (fun h => hx' (Ico_subset_Icc_self h)), eNorm_zero,
    ENNReal.zero_rpow_of_pos hq]

/-- `u` is a **piecewise polynomial of level `k` and degree `< r` on `[0, ∞)`**: on every dyadic
interval `I_{k,m}`, `m ∈ ℕ`, it agrees with a polynomial of degree `< r`. The local estimates
below need only this, so they serve the piecewise polynomials on `[0, 1)` and their periodic
extensions alike. -/
def IsPiecewisePoly (r k : ℕ) (u : ℝ → ℂ) : Prop :=
  ∀ m : ℕ, ∃ P ∈ degreeLT ℂ r, ∀ x ∈ dyadicIco k m, u x = polyFun P x

/-- A piecewise polynomial on `[0, 1)`, extended by `0`, is a piecewise polynomial on
`[0, ∞)`. -/
theorem isPiecewisePoly_ppFun {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r) (k : ℕ) :
    IsPiecewisePoly r k (ppFun k Q) := fun m =>
  ⟨_, ite_mem_degreeLT hQ k m, fun _ hx => ppFun_eq_polyFun Q hx⟩

/-- **The norm of a piece is a local mass**: if `u = P` on `I_{k,m}`, then
`‖P‖_{L_p[m 2^(-k), (m + 1) 2^(-k)]} = (∫_{I_{k,m}} |u|^p)^(1/p)`. -/
theorem eLpNorm_piece_eq_localMass (hp : p ≠ ∞) {k m : ℕ} {u : ℝ → ℂ} {P : ℂ[X]}
    (hPu : ∀ x ∈ dyadicIco k m, u x = polyFun P x) :
    eLpNorm (polyFun P) p (volume.restrict (Icc ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k))) =
      localMass p k u m ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hIco : dyadicIco k m = Ico ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k) := by
    rw [dyadicIco, add_div]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (measurable_polyFun _).aestronglyMeasurable,
    localMass, hIco, ← setLIntegral_congr Ico_ae_eq_Icc]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ico :
    MeasurableSet (Ico ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k))) fun x hx => ?_
  have hx' : x ∈ dyadicIco k m := by rw [hIco]; exact hx
  rw [hPu x hx']

/-- **Pointwise bound** for a piecewise polynomial by its local mass (Nikolskii's inequality on
`I_{k,m}`): `|u(y)| ≤ K 2^(k/p) (∫_{I_{k,m}} |u|^p)^(1/p)` for `y ∈ I_{k,m}`. -/
theorem enorm_le_localMass {r k : ℕ} {u : ℝ → ℂ} (hu : IsPiecewisePoly r k u) {K : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hp : p ≠ ∞) (m : ℕ) {y : ℝ} (hy : y ∈ dyadicIco k m) :
    ‖u y‖ₑ ≤ K * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) * localMass p k u m ^ (1 / p.toReal) := by
  obtain ⟨P, hP, hPu⟩ := hu m
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hIco : dyadicIco k m = Ico ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k) := by
    rw [dyadicIco, add_div]
  have hy' : y ∈ Icc ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k) := by
    rw [hIco] at hy
    exact Ico_subset_Icc_self hy
  rw [hPu y hy]
  have h := hK.enorm_le hP _ hL hy'
  rwa [show (1 / (2 : ℝ) ^ k)⁻¹ = 2 ^ k by rw [one_div, inv_inv],
    eLpNorm_piece_eq_localMass hp hPu] at h

/-- **The points `x + i h` meet at most `r + 1` pieces**: for `x ≥ 0`, `h ≥ 0`, `2^j h ≤ 1` and
`i ≤ r`, `⌊2^j (x + i h)⌋ ≤ ⌊2^j x⌋ + r`. -/
theorem floor_add_mul_le {j r i : ℕ} {x h : ℝ} (hx : 0 ≤ x) (hh0 : 0 ≤ h)
    (hjh : (2 : ℝ) ^ j * h ≤ 1) (hi : i ≤ r) : ⌊2 ^ j * (x + i * h)⌋₊ ≤ ⌊2 ^ j * x⌋₊ + r := by
  have hi' : (i : ℝ) ≤ r := by exact_mod_cast hi
  have hle : 2 ^ j * (x + i * h) ≤ 2 ^ j * x + r := by
    have : (2 : ℝ) ^ j * (i * h) ≤ r :=
      calc (2 : ℝ) ^ j * (i * h) = i * (2 ^ j * h) := by ring
        _ ≤ r * 1 := mul_le_mul hi' hjh (by positivity) (Nat.cast_nonneg r)
        _ = r := mul_one _
    linarith
  calc ⌊2 ^ j * (x + i * h)⌋₊ ≤ ⌊2 ^ j * x + (r : ℝ)⌋₊ := Nat.floor_mono hle
    _ = ⌊2 ^ j * x⌋₊ + r := Nat.floor_add_natCast (by positivity) r

omit [Fact (1 ≤ p)] in
/-- One piece is counted in the local mass of `r + 1` consecutive pieces. -/
theorem localMass_le_sum_range (k : ℕ) (u : ℝ → ℂ) (n : ℕ) {r l : ℕ} (hl : l ≤ r) :
    localMass p k u (n + l) ≤ ∑ l' ∈ Finset.range (r + 1), localMass p k u (n + l') :=
  Finset.single_le_sum (f := fun l' => localMass p k u (n + l')) (fun _ _ => zero_le)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hl))

/-- **Inside a piece a difference sees only the piece**: for `h ≥ 0` and `x ≥ 0`: if `u` agrees
with `P` on the dyadic interval `I_{k,n}` of `x`, `n = ⌊2^k x⌋`, and `x + mh` lies left of its
right end, then
`Δ_h^m u(x) = Δ_h^m P(x)`, since `x, x + h, …, x + mh` lie in `I_{k,n}`. -/
theorem higherDiff_eq_of_mem_piece {k m : ℕ} {u : ℝ → ℂ} {P : ℂ[X]} {h x : ℝ}
    (hPu : ∀ y ∈ dyadicIco k ⌊2 ^ k * x⌋₊, u y = polyFun P y) (hh0 : 0 ≤ h) (hx : 0 ≤ x)
    (hgood : x + m * h < ((⌊2 ^ k * x⌋₊ : ℝ) + 1) / 2 ^ k) :
    higherDiff m h u x = higherDiff m h (polyFun P) x := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hfl : (⌊2 ^ k * x⌋₊ : ℝ) ≤ 2 ^ k * x := Nat.floor_le (by positivity)
  rw [higherDiff_apply, higherDiff_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hmem : x + i * h ∈ dyadicIco k ⌊2 ^ k * x⌋₊ := by
    rw [dyadicIco, mem_Ico]
    constructor
    · rw [div_le_iff₀ hpos]
      nlinarith [mul_nonneg (Nat.cast_nonneg i) hh0]
    · calc x + i * h ≤ x + m * h := by nlinarith
        _ < _ := hgood
  rw [hPu _ hmem]

/-- **Differences vanish inside a piece**: if `x, x + h, …, x + rh` lie in the dyadic interval of
`x`, then `Δ_h^r u(x) = 0`, since there `u` is a polynomial of degree `< r`. -/
theorem higherDiff_eq_zero_of_isPiecewisePoly {r k : ℕ} {u : ℝ → ℂ} (hu : IsPiecewisePoly r k u)
    {h x : ℝ} (hh0 : 0 ≤ h) (hx : 0 ≤ x)
    (hgood : x + r * h < ((⌊2 ^ k * x⌋₊ : ℝ) + 1) / 2 ^ k) :
    higherDiff r h u x = 0 := by
  obtain ⟨P, hP, hPu⟩ := hu ⌊2 ^ k * x⌋₊
  rw [higherDiff_eq_of_mem_piece hPu hh0 hx hgood]
  exact congrFun (higherDiff_polynomial hP h) x

/-- **Pointwise bound for differences of order `m ≤ r`**: for `0 ≤ h ≤ 2^(-k)` and `x ≥ 0`,
`|Δ_h^m u(x)| ≤ 2^m K 2^(k/p) (∑_{l ≤ r} M_{n+l})^(1/p)` with `n = ⌊2^k x⌋`, since
`x, …, x + mh` meet only the intervals `I_{k,n}, …, I_{k,n+r}`. -/
theorem enorm_higherDiff_le_of_isPiecewisePoly_of_le {r k m : ℕ} (hmr : m ≤ r) {u : ℝ → ℂ}
    (hu : IsPiecewisePoly r k u) {K : ℝ≥0∞} (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h x : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ k) (hx : 0 ≤ x) :
    ‖higherDiff m h u x‖ₑ ≤ 2 ^ m * (K * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
      (∑ l ∈ Finset.range (r + 1), localMass p k u (⌊2 ^ k * x⌋₊ + l)) ^ (1 / p.toReal)) := by
  have hkh : (2 : ℝ) ^ k * h ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  refine enorm_higherDiff_le_of_forall fun i hi => ?_
  have hi' : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hmr
  have h0 : 0 ≤ 2 ^ k * (x + i * h) := by positivity
  have hm : x + i * h ∈ dyadicIco k ⌊2 ^ k * (x + i * h)⌋₊ :=
    mem_dyadicIco.2 ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩
  have hnm : ⌊2 ^ k * x⌋₊ ≤ ⌊2 ^ k * (x + i * h)⌋₊ := Nat.floor_mono
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh0))
      (by positivity))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
  have hdr : d ≤ r := by have := floor_add_mul_le hx hh0 hkh hi'; omega
  refine (enorm_le_localMass hu hK hp _ hm).trans ?_
  gcongr
  rw [hd]
  exact localMass_le_sum_range k u _ hdr

/-- **Pointwise bound for differences**: for `0 ≤ h ≤ 2^(-k)` and `x ≥ 0`,
`|Δ_h^r u(x)| ≤ 2^r K 2^(k/p) (∑_{l ≤ r} ∫_{I_{k,n+l}} |u|^p)^(1/p)` with `n = ⌊2^k x⌋`, since
`x, …, x + rh` meet only the intervals `I_{k,n}, …, I_{k,n+r}`. -/
theorem enorm_higherDiff_le_of_isPiecewisePoly {r k : ℕ} {u : ℝ → ℂ} (hu : IsPiecewisePoly r k u)
    {K : ℝ≥0∞} (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h)
    (hh : h ≤ 1 / 2 ^ k) (hx : 0 ≤ x) :
    ‖higherDiff r h u x‖ₑ ≤ 2 ^ r * (K * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
      (∑ l ∈ Finset.range (r + 1), localMass p k u (⌊2 ^ k * x⌋₊ + l)) ^ (1 / p.toReal)) :=
  enorm_higherDiff_le_of_isPiecewisePoly_of_le le_rfl hu hK hp hh0 hh hx

/-- The **strip function** of the inverse estimate: `c M_n` at the points `x` of the strip
`[(n + 1) 2^(-j) - rh, (n + 1) 2^(-j))` left of the right end of the dyadic interval
`I_{j,n}` containing `x`, and `0` elsewhere. -/
noncomputable def stripBound (j r : ℕ) (h : ℝ) (c : ℝ≥0∞) (M : ℕ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  if ((⌊2 ^ j * x⌋₊ : ℝ) + 1) / 2 ^ j ≤ x + r * h then c * M ⌊2 ^ j * x⌋₊ else 0

/-- **Integral of the strip function**: the strips have width `rh`, so
`∫_{[0,1]} (strip function) ≤ c rh ∑_{n < 2^j} M_n`. -/
theorem lintegral_stripBound_le (j r : ℕ) (h : ℝ) (c : ℝ≥0∞) (M : ℕ → ℝ≥0∞) :
    ∫⁻ x in Icc (0 : ℝ) 1, stripBound j r h c M x ≤
      c * ENNReal.ofReal (r * h) * ∑ n ∈ Finset.range (2 ^ j), M n := by
  refine (lintegral_Icc_le_sum_dyadicIco _ j).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  calc ∫⁻ x in dyadicIco j n, stripBound j r h c M x
      ≤ ∫⁻ x in dyadicIco j n,
          (Ici (((n : ℝ) + 1) / 2 ^ j - r * h)).indicator (fun _ => c * M n) x := by
        refine setLIntegral_mono' (measurableSet_dyadicIco j n) fun x hx => ?_
        rw [stripBound, floor_eq_of_mem_dyadicIco hx]
        split_ifs with hbad
        · rw [indicator_of_mem (by rw [mem_Ici]; linarith)]
        · exact zero_le
    _ = c * M n * volume (Ici (((n : ℝ) + 1) / 2 ^ j - r * h) ∩ dyadicIco j n) := by
        rw [lintegral_indicator_const measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
    _ ≤ c * M n * ENNReal.ofReal (r * h) := by
        gcongr
        calc volume (Ici (((n : ℝ) + 1) / 2 ^ j - r * h) ∩ dyadicIco j n)
            ≤ volume (Icc (((n : ℝ) + 1) / 2 ^ j - r * h) (((n : ℝ) + 1) / 2 ^ j)) :=
              measure_mono fun x hx => ⟨hx.1, hx.2.2.le⟩
          _ = ENNReal.ofReal (r * h) := by rw [Real.volume_Icc]; congr 1; ring
    _ = c * ENNReal.ofReal (r * h) * M n := by ring

omit [Fact (1 ≤ p)] in
/-- **The strip integral**: for `0 < p < ∞`, if `|F|^p` is bounded by `G^p M_n` on the strip of
width `rh` left of the right end of every dyadic interval `I_{j,n}` and vanishes elsewhere on
`S ⊆ [0, 1]`, and `∑_{n < 2^j} M_n ≤ (r + 1) B^p`, then `‖F‖_{L_p(S)} ≤ G (rh (r + 1))^(1/p) B`. -/
theorem eLpNorm_le_of_strip (hp0 : p ≠ 0) (hp : p ≠ ∞) {F : ℝ → ℂ} {S : Set ℝ}
    (hS : S ⊆ Icc 0 1) (hF : AEStronglyMeasurable F (volume.restrict S)) {j r : ℕ} {h : ℝ}
    {G : ℝ≥0∞} {M : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hpt : ∀ᵐ x ∂volume.restrict S, ‖F x‖ₑ ^ p.toReal ≤ stripBound j r h (G ^ p.toReal) M x)
    (hB : ∑ n ∈ Finset.range (2 ^ j), M n ≤ (r + 1) * B ^ p.toReal) :
    eLpNorm F p (volume.restrict S) ≤
      G * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eLpNorm_le_of_lintegral_le hF hp0 hp ?_
  calc ∫⁻ x in S, ‖F x‖ₑ ^ p.toReal
      ≤ ∫⁻ x in S, stripBound j r h (G ^ p.toReal) M x := lintegral_mono_ae hpt
    _ ≤ ∫⁻ x in Icc (0 : ℝ) 1, stripBound j r h (G ^ p.toReal) M x := lintegral_mono_set hS
    _ ≤ G ^ p.toReal * ENNReal.ofReal (r * h) * ∑ n ∈ Finset.range (2 ^ j), M n :=
        lintegral_stripBound_le j r h _ _
    _ ≤ G ^ p.toReal * ENNReal.ofReal (r * h) * ((r + 1) * B ^ p.toReal) := by gcongr
    _ = (G * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
        ring

/-- **The local inverse estimate from a pointwise bound**: let `u` be a piecewise polynomial of
level `j` on `[0, ∞)`, `S ⊆ [0, 1]` measurable and `h ≥ 0`. If on the strips of width `rh` left
of the knots `|Δ_h^r u(x)| ≤ G (∑_{l ≤ r} ∫_{I_{j,n+l}} |u|^p)^(1/p)`, `n = ⌊2^j x⌋`, for almost
every `x ∈ S`, and these local masses add up to at most `(r + 1) B^p` over `n < 2^j`, then
`‖Δ_h^r u‖_{L_p(S)} ≤ G (rh (r + 1))^(1/p) B`. Off the strips the difference vanishes
(`Interval.higherDiff_eq_zero_of_isPiecewisePoly`). -/
theorem eLpNorm_higherDiff_le_of_pointwise (hp : p ≠ ∞) {r j : ℕ} {u : ℝ → ℂ}
    (hu : IsPiecewisePoly r j u) (hum : Measurable u) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Icc 0 1) {h : ℝ} (hh0 : 0 ≤ h) {G B : ℝ≥0∞}
    (hpt : ∀ᵐ x ∂volume.restrict S, ((⌊2 ^ j * x⌋₊ : ℝ) + 1) / 2 ^ j ≤ x + r * h →
      ‖higherDiff r h u x‖ₑ ≤
        G * (∑ l ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l)) ^ (1 / p.toReal))
    (hB : ∑ n ∈ Finset.range (2 ^ j), ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l) ≤
      (r + 1) * B ^ p.toReal) :
    eLpNorm (higherDiff r h u) p (volume.restrict S) ≤
      G * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eLpNorm_le_of_strip hp0 hp hS (measurable_higherDiff hum r h).aestronglyMeasurable
    (M := fun n => ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l)) ?_ hB
  filter_upwards [hpt, ae_restrict_mem hSm] with x hx hxS
  rw [stripBound]
  split_ifs with hbad
  · calc ‖higherDiff r h u x‖ₑ ^ p.toReal
        ≤ (G * (∑ l ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l)) ^
            (1 / p.toReal)) ^ p.toReal := ENNReal.rpow_le_rpow (hx hbad) hq.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
            ENNReal.rpow_one]
  · push Not at hbad
    rw [higherDiff_eq_zero_of_isPiecewisePoly hu hh0 (hS hxS).1 hbad, eNorm_zero,
      ENNReal.zero_rpow_of_pos hq]

/-- **Bounded overlap**: summing the local masses of `r + 1` consecutive pieces over all starting
pieces counts each piece at most `r + 1` times,
`∑_{n < 2^j} ∑_{l ≤ r} ∫_{I_{j,n+l}} |u|^p ≤ (r + 1) ‖u‖_p^p`. -/
theorem sum_sum_localMass_le (hp : p ≠ ∞) (j r : ℕ) (Q : ℕ → ℂ[X]) :
    ∑ n ∈ Finset.range (2 ^ j), ∑ l ∈ Finset.range (r + 1), localMass p j (ppFun j Q) (n + l) ≤
      (r + 1) * eLpNorm (ppFun j Q) p unitVol ^ p.toReal := by
  rw [Finset.sum_comm]
  calc ∑ l ∈ Finset.range (r + 1), ∑ n ∈ Finset.range (2 ^ j),
        localMass p j (ppFun j Q) (n + l)
      ≤ ∑ l ∈ Finset.range (r + 1), ∑' m, localMass p j (ppFun j Q) m :=
        Finset.sum_le_sum fun l _ => (sum_le_tsum _).trans
          (tsum_comp_le_tsum_of_injective (add_left_injective l) _)
    _ = (r + 1) * ∑' m, localMass p j (ppFun j Q) m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (r + 1) * eLpNorm (ppFun j Q) p unitVol ^ p.toReal := by
        gcongr
        exact tsum_localMass_ppFun_le hp j Q

/-- `2^(jθ) (rh (r + 1))^θ = (r (r + 1) 2^j h)^θ` for `θ ≥ 0`. -/
theorem ofReal_two_pow_rpow_mul_eq (r j : ℕ) (h : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ENNReal.ofReal (2 ^ j) ^ θ * (ENNReal.ofReal (r * h) * (r + 1)) ^ θ =
      (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ θ := by
  have h1 : ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (r * h) =
      (r : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h) := by
    rw [← ENNReal.ofReal_mul (by positivity), show (2 : ℝ) ^ j * (r * h) = r * (2 ^ j * h) by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ, ← mul_assoc, h1]
  congr 1
  push_cast
  ring

/-- **The local inverse estimate** for a piecewise polynomial `u` of level `j` on `[0, ∞)`: if
the local masses of `r + 1` consecutive pieces, summed over the pieces in `[0, 1)`, are at most
`(r + 1) B^p`, then for `0 ≤ h ≤ 2^(-j)`,
`‖Δ_h^r u‖_{L_p[0, 1]} ≤ 2^r K (r (r + 1) 2^j h)^(1/p) B`.
The difference vanishes except on strips of width `rh` left of the knots, and there it is
bounded by the local masses of at most `r + 1` neighbouring pieces. -/
theorem eLpNorm_higherDiff_le_of_isPiecewisePoly {r j : ℕ} {u : ℝ → ℂ}
    (hu : IsPiecewisePoly r j u) (hum : Measurable u) {K : ℝ≥0∞} (hK : NikolskiiBound p r K)
    (hp : p ≠ ∞) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) {B : ℝ≥0∞}
    (hB : ∑ n ∈ Finset.range (2 ^ j), ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l) ≤
      (r + 1) * B ^ p.toReal) :
    eLpNorm (higherDiff r h u) p (volume.restrict (Icc 0 1)) ≤
      2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) *
        B := by
  refine (eLpNorm_higherDiff_le_of_pointwise hp hu hum measurableSet_Icc le_rfl hh0
    (G := 2 ^ r * K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)) ?_ hB).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx _
    exact (enorm_higherDiff_le_of_isPiecewisePoly hu hK hp hh0 hh hx.1).trans_eq (by ring)
  · rw [mul_assoc (2 ^ r * K), ofReal_two_pow_rpow_mul_eq r j h (by positivity)]

/-- **The local inverse estimate on `[0, 1]`** for a piecewise polynomial `u` of level `j`: for
`0 ≤ h ≤ 2^(-j)`,
`‖Δ_h^r u‖_{L_p[0, 1 - rh]} ≤ 2^r K (r (r + 1) 2^j h)^(1/p) ‖u‖_{L_p[0,1]}`. -/
theorem eLpNorm_higherDiff_ppFun_le {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    {K : ℝ≥0∞} (hK : NikolskiiBound p r K) (hp : p ≠ ∞) (j : ℕ) {h : ℝ} (hh0 : 0 ≤ h)
    (hh : h ≤ 1 / 2 ^ j) :
    eLpNorm (higherDiff r h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - r * h))) ≤
      2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) *
        eLpNorm (ppFun j Q) p unitVol :=
  (eLpNorm_Icc_mono _ p le_rfl (by linarith [mul_nonneg (Nat.cast_nonneg r) hh0])).trans
    (eLpNorm_higherDiff_le_of_isPiecewisePoly (isPiecewisePoly_ppFun hQ j)
      (measurable_ppFun j Q) hK hp hh0 hh (sum_sum_localMass_le hp j r Q))

variable (p) in
/-- The constant of the inverse inequality, `2^r (1 + K (r (r + 1))^(1/p))`, with the Nikolskii
constant `K`. -/
noncomputable def ppInverseConst (r : ℕ) (K : ℝ≥0∞) : ℝ≥0∞ :=
  2 ^ r * (1 + K * ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal))

omit [Fact (1 ≤ p)] in
/-- The constant of the inverse inequality is finite. -/
theorem ppInverseConst_ne_top (r : ℕ) {K : ℝ≥0∞} (hK : K ≠ ∞) : ppInverseConst p r K ≠ ∞ :=
  ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.natCast_ne_top _))⟩)

omit [Fact (1 ≤ p)] in
/-- `2^r` is at most the constant of the inverse inequality. -/
theorem two_pow_le_ppInverseConst (r : ℕ) (K : ℝ≥0∞) : 2 ^ r ≤ ppInverseConst p r K :=
  le_mul_of_one_le_right zero_le le_self_add

omit [Fact (1 ≤ p)] in
/-- The local inverse estimate in dyadic form: for `j ≤ k` and `h ≤ 2^(-k)`,
`2^r K (r (r + 1) 2^j h)^(1/p) B ≤ C_B 2^(-(k-j)/p) B`. -/
theorem le_ppInverseConst_mul {r j k : ℕ} (hjk : j ≤ k) (K : ℝ≥0∞) {h : ℝ} (hh : h ≤ 1 / 2 ^ k)
    (B : ℝ≥0∞) :
    2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) * B ≤
      ppInverseConst p r K * dyadicWeight (-(1 / p.toReal)) (k - j) * B := by
  have hθ : 0 ≤ 1 / p.toReal := by positivity
  have hw : (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) ≤
      ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * dyadicWeight (-(1 / p.toReal)) (k - j) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_two_pow_mul_rpow_le hjk hh hθ)
  calc 2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^
        (1 / p.toReal) * B
      ≤ 2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) *
          dyadicWeight (-(1 / p.toReal)) (k - j)) * B :=
        mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl
    _ = 2 ^ r * (K * ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal)) *
          dyadicWeight (-(1 / p.toReal)) (k - j) * B := by ring
    _ ≤ ppInverseConst p r K * dyadicWeight (-(1 / p.toReal)) (k - j) * B := by
        unfold ppInverseConst
        gcongr
        exact le_add_self

/-- **The inverse inequality for dyadic piecewise polynomials**, of order `θ = 1/p`: there is
`C_B < ∞` with `ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for every piecewise polynomial
`a` of level `j` (and `k - j` truncated at `0`). The order `1/p` reflects the jumps at the knots:
a single jump has `ω_r(a, t)_p ≈ t^(1/p)`. -/
theorem exists_inverse_ppScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ ppScheme p r (2 ^ j),
      lpModulus p r a k ≤ CB * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨ppInverseConst p r K, ppInverseConst_ne_top r hK, fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hae⟩ := mem_ppScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le r a k).trans (by gcongr; exact two_pow_le_ppInverseConst r K)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.eNorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpModulus, modulus_congr_ae hae, hnorm, modulus_eq_iSup_nonneg]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    exact (eLpNorm_higherDiff_ppFun_le hQ hKb hp j hh.1 hhj).trans
      (le_ppInverseConst_mul hjk K hh.2 _)

/-! ### The coincidence theorem -/

/-- The modulus `ω_r(f, 2^(-k), [0, 1])_p` is compatible with the scheme of dyadic piecewise
polynomials of degree `< r`, with inverse order `θ = 1/p` and Jackson's inequality at every
level (Whitney's inequality at level `0`). -/
noncomputable def ppModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (ppScheme p r) (1 / p.toReal) :=
  .ofExists (lpModulus p r) (lpModulus_add_le r) (2 ^ r) (by simp) (lpModulus_le r) 0
    ((exists_approxError_ppScheme_le hr hp).imp fun _ h => ⟨h.1, fun f k _ => h.2 f k⟩)
    (exists_inverse_ppScheme hp)

/-- **Approximation by dyadic piecewise polynomials.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < 1/p`, an `f ∈ L_p[0, 1]` lies in the approximation space `A^s_q` of the piecewise
polynomials of degree `< r` on dyadic partitions iff its classical Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` is finite. The bound `s < 1/p` is sharp
for discontinuous pieces; higher smoothness needs smooth splines. -/
theorem memApprox_ppScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (ppScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ :=
  (ppModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs hsp f

end Interval
