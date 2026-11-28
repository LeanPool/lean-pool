/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Ball means of differences for Triebel–Lizorkin spaces

The **ball mean of differences** of order `L` at level `j` is
`d_j f(x) = |B(0, 2^(-j))|⁻¹ ∫_{B(0, 2^(-j))} |Δ^L_h f(x)| dh` (`Rd.ballMeanDiff`), and
`‖f‖_p + ‖ x ↦ ‖(2^(js) d_j f(x))_j‖_{ℓ_q} ‖_p` (`Rd.tlDiffNorm`) is the quasi-norm of
Triebel–Lizorkin type built from it. For `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L` it is equivalent
to the local means quasi-norm of `FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans`, with
explicit constants (`Rd.LocalMeansBump.tlDiffNorm_le_tlLocalMeansNorm`,
`Rd.LocalMeansBump.tlLocalMeansNorm_le_tlDiffNorm`), so `F^s_{p,q}` is described by ball means of
differences (`Rd.memTriebelLizorkin_iff_tlDiffNorm_lt_top`).

The proof is pointwise in `x`. A local mean is a difference of two averaged differences of `f`,
so `|k_{j+r+1} ⋆ f(x)| ≤ C d_j f(x)`, where `r = ⌈R⌉₊` gives `R < 2^r`
(`Rd.LocalMeansBump.enorm_localMean_le_ballMeanDiff`). Conversely, the differences of
`η_i ⋆ g` are bounded by the maximal function of `g`, with the factor `2^(-(j-i)L)` for `i ≤ j`
from the smoothness of `η_i` and the factor `1` for `i > j` from averaging the shifts over the
ball (`Rd.LocalMeansBump.ballMeanDiff_conv_dual_le`); the reproducing formula
`f = ∑_i η_i ⋆ k_i ⋆ f` then gives `d_j f(x) ≤ C ∑_i c_{ji} M(k_i ⋆ f)(x)`
(`Rd.LocalMeansBump.ballMeanDiff_le_tsum_maximal`), and the almost diagonal estimate and the
Fefferman–Stein inequality finish. In the bounds for `η_i ⋆ g`, the **fine levels** are the ball
levels `j ≥ i`, at least the level `i` of the kernel, and the **coarse levels** are the ball
levels `j < i`.
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal Topology Pointwise

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Ball means of differences -/

/-- The **ball mean of differences** of order `L` at level `j`:
`d_j f(x) = |B(0, 2^(-j))|⁻¹ ∫_{B(0, 2^(-j))} |Δ^L_h f(x)| dh`, the mean of the differences of
`f` at `x` over all steps of length less than `2^(-j)`. -/
noncomputable def ballMeanDiff (L j : ℕ) (f : V → ℂ) (x : V) : ℝ≥0∞ :=
  (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ * ∫⁻ h in ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff h)^[L] f x‖ₑ

/-- The radius `2^(-j)` of the balls of the ball means is positive. -/
theorem one_div_two_pow_pos (j : ℕ) : (0 : ℝ) < 1 / 2 ^ j := by positivity

/-- `2^(jn) |B(0, 2^(-j))| = |B(0, 1)|`. -/
theorem two_pow_mul_volume_ball_one_div (j : ℕ) :
    2 ^ (j * finrank ℝ V) * volume (ball (0 : V) (1 / 2 ^ j)) = volume (ball (0 : V) 1) := by
  have h := Measure.addHaar_ball_mul_of_pos volume (0 : V) (r := 2 ^ j) (by positivity) (1 / 2 ^ j)
  rw [ENNReal.ofReal_pow (pow_nonneg zero_le_two j), mul_one_div_cancel (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← pow_mul] at h
  exact h.symm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scaling factor of the steps: `|((-2^(-m))^n)⁻¹| = 2^(mn)`. -/
theorem ofReal_abs_inv_neg_inv_two_pow_pow (m : ℕ) :
    ENNReal.ofReal |((-((2 : ℝ) ^ m)⁻¹) ^ finrank ℝ V)⁻¹| = 2 ^ (m * finrank ℝ V) := by
  rw [abs_inv, abs_pow, abs_neg, abs_inv, abs_of_pos (by positivity), inv_pow, inv_inv,
    ← pow_mul, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- The integral of the differences over the ball is `|B(0, 2^(-j))| d_j f(x)`. -/
theorem setLIntegral_eq_mul_ballMeanDiff (L j : ℕ) (f : V → ℂ) (x : V) :
    ∫⁻ h in ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff h)^[L] f x‖ₑ =
      volume (ball (0 : V) (1 / 2 ^ j)) * ballMeanDiff L j f x := by
  rw [ballMeanDiff, ← mul_assoc, ENNReal.mul_inv_cancel
    (volume_ball_ne_zero (one_div_two_pow_pos j)) (volume_ball_ne_top _), one_mul]

/-- A bound of the differences `|Δ^L_h f(x)| ≤ c` for all steps `‖h‖ < 2^(-j)` bounds the ball
mean: `d_j f(x) ≤ c`. -/
theorem ballMeanDiff_le_of_forall {L j : ℕ} {f : V → ℂ} {x : V} {c : ℝ≥0∞}
    (h : ∀ v ∈ ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff v)^[L] f x‖ₑ ≤ c) :
    ballMeanDiff L j f x ≤ c := by
  rw [ballMeanDiff, ENNReal.inv_mul_le_iff (volume_ball_ne_zero (one_div_two_pow_pos j))
    (volume_ball_ne_top _)]
  calc ∫⁻ v in ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff v)^[L] f x‖ₑ
      ≤ ∫⁻ _ in ball (0 : V) (1 / 2 ^ j), c := setLIntegral_mono' measurableSet_ball h
    _ = volume (ball (0 : V) (1 / 2 ^ j)) * c := by rw [setLIntegral_const, mul_comm]

/-- **Smaller balls**: `d_{j+r} f(x) ≤ 2^(rn) d_j f(x)`, since the ball of radius `2^(-j-r)` lies in
the ball of radius `2^(-j)` and has `2^(-rn)` times its volume. -/
theorem ballMeanDiff_level_add_le (L j r : ℕ) (f : V → ℂ) (x : V) :
    ballMeanDiff L (j + r) f x ≤ 2 ^ (r * finrank ℝ V) * ballMeanDiff L j f x := by
  have hvol : volume (ball (0 : V) (1 / 2 ^ j)) =
      2 ^ (r * finrank ℝ V) * volume (ball (0 : V) (1 / 2 ^ (j + r))) := by
    have h := Measure.addHaar_ball_mul_of_pos volume (0 : V) (r := 2 ^ r) (by positivity)
      (1 / 2 ^ (j + r))
    rw [ENNReal.ofReal_pow (pow_nonneg zero_le_two r), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, ← pow_mul, pow_add,
      show (2 : ℝ) ^ r * (1 / (2 ^ j * 2 ^ r)) = 1 / 2 ^ j by field_simp] at h
    rw [h, pow_add]
  have hsub : ball (0 : V) (1 / 2 ^ (j + r)) ⊆ ball (0 : V) (1 / 2 ^ j) :=
    ball_subset_ball (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ one_le_two (Nat.le_add_right j r)))
  have h2 : (2 : ℝ≥0∞) ^ (r * finrank ℝ V) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ (r * finrank ℝ V) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ballMeanDiff, ballMeanDiff, hvol, ENNReal.mul_inv (Or.inl h2) (Or.inl h2'), ← mul_assoc,
    ← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact mul_le_mul' le_rfl (lintegral_mono_set hsub)

/-- For measurable `f` and fixed `x` the differences `h ↦ |Δ^L_h f(x)|` are measurable. -/
theorem measurable_enorm_higherDiff_step {f : V → ℂ} (hf : Measurable f) (L : ℕ) (x : V) :
    Measurable fun h : V => ‖(fwdDiff h)^[L] f x‖ₑ :=
  (measurable_enorm_higherDiff_uncurry hf L).comp measurable_prodMk_left

/-- The ball means of a measurable function are measurable (Tonelli's theorem, Mathlib's
`Measurable.lintegral_prod_right'`). -/
theorem measurable_ballMeanDiff {f : V → ℂ} (hf : Measurable f) (L j : ℕ) :
    Measurable (ballMeanDiff L j f) :=
  ((measurable_enorm_higherDiff_uncurry hf L).lintegral_prod_right'
    (ν := volume.restrict (ball (0 : V) (1 / 2 ^ j)))).const_mul _

/-- **Ball means of almost everywhere equal functions** agree almost everywhere: at a point `x`
with `f(x) = g(x)` the values `f(x + l h)`, `1 ≤ l ≤ L`, agree for almost every step `h`, since
`h ↦ x + l h` maps null sets to null sets. -/
theorem ballMeanDiff_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[volume] g) (L j : ℕ) :
    ballMeanDiff L j f =ᵐ[volume] ballMeanDiff L j g := by
  filter_upwards [hfg] with x hx
  have hl : ∀ l : ℕ, ∀ᵐ v ∂(volume : Measure V), f (x + (l : ℝ) • v) = g (x + (l : ℝ) • v) := by
    intro l
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · exact Eventually.of_forall fun v => by simpa using hx
    · have hq : QuasiMeasurePreserving (fun v : V => x + (l : ℝ) • v) volume volume :=
        (measurePreserving_add_left volume x).quasiMeasurePreserving.comp
          (Measure.quasiMeasurePreserving_smul volume (by positivity : (l : ℝ) ≠ 0))
      exact hq.ae_eq_comp hfg
  have hv : ∀ᵐ v ∂(volume : Measure V), ‖(fwdDiff v)^[L] f x‖ₑ = ‖(fwdDiff v)^[L] g x‖ₑ := by
    filter_upwards [ae_all_iff.2 hl] with v hv
    rw [higherDiff_apply, higherDiff_apply]
    exact congrArg _ (Finset.sum_congr rfl fun l _ => by rw [hv l])
  rw [ballMeanDiff, ballMeanDiff, lintegral_congr_ae (ae_restrict_of_ae hv)]

/-- **The power of a ball mean** (weighted Jensen inequality): for `1 ≤ P` and measurable `f`,
`(d_j f(x))^P ≤ |B|⁻¹ ∫_B |Δ^L_h f(x)|^P dh` with `B = B(0, 2^(-j))`. -/
theorem ballMeanDiff_rpow_le {f : V → ℂ} (hf : Measurable f) (L j : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (x : V) :
    ballMeanDiff L j f x ^ P ≤ ∫⁻ h in ball (0 : V) (1 / 2 ^ j),
      (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ * ‖(fwdDiff h)^[L] f x‖ₑ ^ P := by
  set B := ball (0 : V) (1 / 2 ^ j)
  have hB0 : volume B ≠ 0 := volume_ball_ne_zero (one_div_two_pow_pos j)
  have hc : (volume B)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hB0
  have hmass : ∫⁻ _ in B, (volume B)⁻¹ = 1 := by
    rw [setLIntegral_const, ENNReal.inv_mul_cancel hB0 (volume_ball_ne_top _)]
  have h := lintegral_mul_rpow_le (μ := volume.restrict B) hP (a := fun _ => (volume B)⁻¹)
    aemeasurable_const (measurable_enorm_higherDiff_step hf L x).aemeasurable
  rw [hmass, ENNReal.one_rpow, one_mul, lintegral_const_mul' _ _ hc] at h
  exact h

/-- **Ball means are bounded in `L_p`**: `‖d_j f‖_p ≤ 2^L ‖f‖_p` for measurable `f` and
`1 ≤ p < ∞`. By `Rd.ballMeanDiff_rpow_le` and Tonelli's theorem,
`∫ (d_j f)^p ≤ |B|⁻¹ ∫_B ‖Δ^L_h f‖_p^p dh`, and `‖Δ^L_h f‖_p ≤ 2^L ‖f‖_p`
(`Rd.eLpNorm_higherDiff_le`). -/
theorem eLpNorm_ballMeanDiff_le_of_measurable {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : V → ℂ} (hf : Measurable f) (L j : ℕ) :
    eLpNorm (ballMeanDiff L j f) p volume ≤ 2 ^ L * eLpNorm f p volume := by
  set B := ball (0 : V) (1 / 2 ^ j)
  set X := 2 ^ L * eLpNorm f p volume
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hP : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hB0 : volume B ≠ 0 := volume_ball_ne_zero (one_div_two_pow_pos j)
  have hc : (volume B)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hB0
  have hD := measurable_enorm_higherDiff_uncurry hf L
  have hstep : ∀ v : V, ∫⁻ x, ‖(fwdDiff v)^[L] f x‖ₑ ^ p.toReal ≤ X ^ p.toReal := fun v => by
    rw [← eLpNorm_rpow_eq (aestronglyMeasurable_higherDiff hf.aestronglyMeasurable L v) hp0 hp]
    exact ENNReal.rpow_le_rpow (eLpNorm_higherDiff_le hf.aestronglyMeasurable hp1 L v) hP.le
  have hint : ∫⁻ x, ballMeanDiff L j f x ^ p.toReal ≤ X ^ p.toReal :=
    calc ∫⁻ x, ballMeanDiff L j f x ^ p.toReal
        ≤ ∫⁻ x, ∫⁻ v in B, (volume B)⁻¹ * ‖(fwdDiff v)^[L] f x‖ₑ ^ p.toReal :=
          lintegral_mono fun x => ballMeanDiff_rpow_le hf L j hP1 x
      _ = ∫⁻ v in B, ∫⁻ x, (volume B)⁻¹ * ‖(fwdDiff v)^[L] f x‖ₑ ^ p.toReal :=
          lintegral_lintegral_swap ((hD.pow_const _).const_mul _).aemeasurable
      _ ≤ ∫⁻ _ in B, (volume B)⁻¹ * X ^ p.toReal := lintegral_mono fun v => by
          rw [lintegral_const_mul' _ _ hc]
          exact mul_le_mul' le_rfl (hstep v)
      _ = X ^ p.toReal := by
          rw [setLIntegral_const, mul_comm, ← mul_assoc,
            ENNReal.mul_inv_cancel hB0 (volume_ball_ne_top _), one_mul]
  rw [← ENNReal.rpow_le_rpow_iff hP,
    eLpNorm_rpow_eq_lintegral hp0 hp (measurable_ballMeanDiff hf L j).aemeasurable]
  exact hint

/-- **Ball means are bounded in `L_p`**: `‖d_j f‖_p ≤ 2^L ‖f‖_p` for almost everywhere strongly
measurable `f` and `1 ≤ p < ∞`, through a measurable representative
(`Rd.ballMeanDiff_congr_ae`). -/
theorem eLpNorm_ballMeanDiff_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (L j : ℕ) :
    eLpNorm (ballMeanDiff L j f) p volume ≤ 2 ^ L * eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (ballMeanDiff_congr_ae hf.ae_eq_mk L j), eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_ballMeanDiff_le_of_measurable hp1 hp hf.stronglyMeasurable_mk.measurable L j

/-- **Subadditivity**: `d_j (f + g)(x) ≤ d_j f(x) + d_j g(x)` for measurable `f` and every `g`.
One summand has to be measurable, since the lower Lebesgue integral of a sum of two
non-measurable functions can exceed the sum of their integrals. -/
theorem ballMeanDiff_add_le {f : V → ℂ} (hf : Measurable f) (g : V → ℂ) (L j : ℕ) (x : V) :
    ballMeanDiff L j (f + g) x ≤ ballMeanDiff L j f x + ballMeanDiff L j g x := by
  rw [ballMeanDiff, ballMeanDiff, ballMeanDiff, ← mul_add]
  gcongr
  calc ∫⁻ v in ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff v)^[L] (f + g) x‖ₑ
      ≤ ∫⁻ v in ball (0 : V) (1 / 2 ^ j),
          (‖(fwdDiff v)^[L] f x‖ₑ + ‖(fwdDiff v)^[L] g x‖ₑ) := lintegral_mono fun v => by
        rw [fwdDiff_iter_add, Pi.add_apply]
        exact eNorm_add_le _ _
    _ = _ := lintegral_add_left' (measurable_enorm_higherDiff_step hf L x).aemeasurable _

/-- The ball means of the zero function vanish. -/
theorem ballMeanDiff_zero (L j : ℕ) (x : V) : ballMeanDiff L j (0 : V → ℂ) x = 0 := by
  simp [ballMeanDiff, higherDiff_apply]

/-- **Subadditivity for finite sums**: `d_j (∑_{i ∈ s} f_i)(x) ≤ ∑_{i ∈ s} d_j f_i(x)` for
measurable `f_i` (Mathlib's `Finset.le_sum_of_subadditive_on_pred`, with measurability as the
predicate closed under sums). -/
theorem ballMeanDiff_finsetSum_le {ι : Type*} {s : Finset ι} {f : ι → V → ℂ}
    (hf : ∀ i ∈ s, Measurable (f i)) (L j : ℕ) (x : V) :
    ballMeanDiff L j (∑ i ∈ s, f i) x ≤ ∑ i ∈ s, ballMeanDiff L j (f i) x :=
  Finset.le_sum_of_subadditive_on_pred (fun F => ballMeanDiff L j F x) Measurable
    (ballMeanDiff_zero L j x).le (fun _ G hF _ => ballMeanDiff_add_le hF G L j x)
    (fun _ _ hF hG => hF.add hG) f hf

/-! ### The ball means quasi-norm -/

section Quasinorm

variable {p : ℝ≥0∞}

/-- The **ball means quasi-norm of Triebel–Lizorkin type**
`‖f‖_p + ‖ x ↦ ‖(2^(js) d_j f(x))_j‖_{ℓ_q} ‖_p` of `f ∈ L_p`, with the ball means of
differences of order `L`: the `ℓ_q` norm at each point, then the `L_p` norm. -/
noncomputable def tlDiffNorm (L : ℕ) (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    ℝ≥0∞ :=
  ‖f‖ₑ + eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x)) p volume

/-- The pointwise `ℓ_q` norm of the weighted ball means is measurable. -/
theorem measurable_lqNorm_ballMeanDiff (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    Measurable fun x => lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x) :=
  measurable_lqNorm_comp (fun j =>
    (measurable_ballMeanDiff (Lp.stronglyMeasurable f).measurable L j).const_mul _) q

end Quasinorm

/-! ### Tools for ball means of convolutions -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A step in the ball `B(0, 2^(-j))` has `‖h‖ ≤ 2^(-j)` in `[0, ∞]`. -/
theorem enorm_le_inv_two_pow_of_mem_ball {j : ℕ} {h : V} (hh : h ∈ ball (0 : V) (1 / 2 ^ j)) :
    ‖h‖ₑ ≤ ((2 : ℝ≥0∞) ^ j)⁻¹ := by
  rw [mem_ball_zero_iff] at hh
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal hh.le).trans_eq ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]

/-- `2^(iL) 2^(-jL) = 2^(-(j-i)L)` for `i ≤ j`. -/
theorem dyadicWeight_mul_dyadicWeight_neg_of_le (L : ℝ) {i j : ℕ} (hij : i ≤ j) :
    dyadicWeight L i * dyadicWeight (-L) j = dyadicWeight (-L) (j - i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left, add_comm i k, ENNReal.dyadicWeight_add_nat, mul_left_comm,
    mul_comm (dyadicWeight L i), ENNReal.dyadicWeight_neg_mul_self, mul_one]

/-- For `l ≥ 1` the steps `v` with `‖x + l v - w‖ < ρ` form a set of measure at most
`|B(0,ρ)|`, a ball of radius `ρ / l`. -/
theorem volume_setOf_dist_add_smul_lt_le {l : ℝ} (hl : 1 ≤ l) (ρ : ℝ) (x w : V) :
    volume {v : V | dist w (x + l • v) < ρ} ≤ volume (ball (0 : V) ρ) := by
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hset : {v : V | dist w (x + l • v) < ρ} = (fun v => l • v) ⁻¹' ball (w - x) ρ := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, mem_ball, dist_eq_norm]
    rw [show w - (x + l • v) = -(l • v - (w - x)) by abel, norm_neg]
  rw [hset, Measure.addHaar_preimage_smul volume hl0.ne', Measure.addHaar_ball_center]
  refine (mul_le_mul' (ENNReal.ofReal_le_one.2 ?_) le_rfl).trans_eq (one_mul _)
  rw [abs_of_pos (inv_pos.2 (pow_pos hl0 _))]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hl)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A point of a moving ball**: for `l ≥ 0`, a step `v ∈ B(0,a)` and points `x, w`,
`1_{B(x + l v, ρ)}(w) G(w) ≤ 1_{B(x, ρ + l a)}(w) G(w) 1_T(v)` with
`T = {v' : dist(w, x + l v') < ρ}`: a point `w` of the ball `B(x + l v, ρ)` lies in
`B(x, ρ + l a)` by the triangle inequality, and `v ∈ T` by definition. -/
theorem indicator_ball_add_smul_le (G : V → ℝ≥0∞) {l : ℝ} (hl0 : 0 ≤ l) {a : ℝ} (ρ : ℝ)
    (x : V) {v : V} (hv : v ∈ ball (0 : V) a) (w : V) :
    (ball (x + l • v) ρ).indicator G w ≤
      (ball x (ρ + l * a)).indicator G w * {v : V | dist w (x + l • v) < ρ}.indicator 1 v := by
  by_cases hw : w ∈ ball (x + l • v) ρ
  · have hwx : w ∈ ball x (ρ + l * a) := by
      rw [mem_ball] at hw ⊢
      rw [mem_ball_zero_iff] at hv
      calc dist w x ≤ dist w (x + l • v) + dist (x + l • v) x := dist_triangle _ _ _
        _ < ρ + l * a := by
          rw [dist_eq_norm (x + l • v), add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hl0]
          exact add_lt_add_of_lt_of_le hw (mul_le_mul_of_nonneg_left hv.le hl0)
    rw [indicator_of_mem hw, indicator_of_mem hwx,
      indicator_of_mem (show v ∈ {v : V | dist w (x + l • v) < ρ} from hw), Pi.one_apply, mul_one]
  · rw [indicator_of_notMem hw]
    exact zero_le

/-- **One point under moving balls**: for `l ≥ 1`, every `a, ρ` and points `x, w`,
`∫_{B(0,a)} 1_{B(x + l v, ρ)}(w) G(w) dv ≤ 1_{B(x, ρ + l a)}(w) G(w) |B(0,ρ)|`: the integrand is
at most `1_{B(x, ρ + l a)}(w) G(w)` times the indicator of the steps `v` whose ball contains `w`
(`Rd.indicator_ball_add_smul_le`), a set of measure at most `|B(0,ρ)|`
(`Rd.volume_setOf_dist_add_smul_lt_le`). -/
theorem setLIntegral_indicator_ball_add_smul_le (G : V → ℝ≥0∞) {l : ℝ} (hl : 1 ≤ l) (a ρ : ℝ)
    (x w : V) :
    ∫⁻ v in ball (0 : V) a, (ball (x + l • v) ρ).indicator G w ≤
      (ball x (ρ + l * a)).indicator G w * volume (ball (0 : V) ρ) := by
  have hT : MeasurableSet {v : V | dist w (x + l • v) < ρ} :=
    (isOpen_lt (continuous_const.dist (continuous_const.add (continuous_id.const_smul l)))
      continuous_const).measurableSet
  calc ∫⁻ v in ball (0 : V) a, (ball (x + l • v) ρ).indicator G w
      ≤ ∫⁻ v in ball (0 : V) a, (ball x (ρ + l * a)).indicator G w *
          {v : V | dist w (x + l • v) < ρ}.indicator 1 v :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          indicator_ball_add_smul_le G (zero_le_one.trans hl) ρ x hv w
    _ ≤ ∫⁻ v, (ball x (ρ + l * a)).indicator G w *
          {v : V | dist w (x + l • v) < ρ}.indicator 1 v := setLIntegral_le_lintegral _ _
    _ = (ball x (ρ + l * a)).indicator G w * volume {v : V | dist w (x + l • v) < ρ} := by
        rw [lintegral_const_mul _ (measurable_one.indicator hT), lintegral_indicator_one hT]
    _ ≤ _ := mul_le_mul' le_rfl (volume_setOf_dist_add_smul_lt_le hl ρ x w)

/-- **Averaging moving balls** (Tonelli): for `l ≥ 1`, every `a, ρ`, `x` and every almost
everywhere measurable `G : V → [0, ∞]`,
`∫_{B(0,a)} ∫_{B(x + l v, ρ)} G(w) dw dv ≤ |B(0,ρ)| ∫_{B(x, ρ + l a)} G`: a point `w` lies in
`B(x + l v, ρ)` only for `v` in a set of measure at most `|B(0,ρ)|`, and only if
`w ∈ B(x, ρ + l a)` (`Rd.setLIntegral_indicator_ball_add_smul_le`). -/
theorem setLIntegral_setLIntegral_ball_le {G : V → ℝ≥0∞} (hG : AEMeasurable G volume) {l : ℝ}
    (hl : 1 ≤ l) (a ρ : ℝ) (x : V) :
    ∫⁻ v in ball (0 : V) a, ∫⁻ w in ball (x + l • v) ρ, G w ≤
      volume (ball (0 : V) ρ) * ∫⁻ w in ball x (ρ + l * a), G w := by
  have hS : MeasurableSet {z : V × V | dist z.2 (x + l • z.1) < ρ} :=
    (isOpen_lt (continuous_snd.dist (continuous_const.add (continuous_fst.const_smul l)))
      continuous_const).measurableSet
  have hmeas : AEMeasurable (Function.uncurry fun v w => (ball (x + l • v) ρ).indicator G w)
      ((volume.restrict (ball (0 : V) a)).prod volume) := by
    have heq : (Function.uncurry fun v w => (ball (x + l • v) ρ).indicator G w) =
        {z : V × V | dist z.2 (x + l • z.1) < ρ}.indicator fun z => G z.2 := by
      funext z
      rfl
    rw [heq]
    exact hG.comp_snd.indicator hS
  calc ∫⁻ v in ball (0 : V) a, ∫⁻ w in ball (x + l • v) ρ, G w
      = ∫⁻ v in ball (0 : V) a, ∫⁻ w, (ball (x + l • v) ρ).indicator G w := by
        simp only [lintegral_indicator measurableSet_ball]
    _ = ∫⁻ w, ∫⁻ v in ball (0 : V) a, (ball (x + l • v) ρ).indicator G w :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ w, (ball x (ρ + l * a)).indicator G w * volume (ball (0 : V) ρ) :=
        lintegral_mono fun w => setLIntegral_indicator_ball_add_smul_le G hl a ρ x w
    _ = volume (ball (0 : V) ρ) * ∫⁻ w in ball x (ρ + l * a), G w := by
        rw [lintegral_mul_const' _ _ (volume_ball_ne_top ρ), lintegral_indicator measurableSet_ball,
          mul_comm]

/-! ### Local means by ball means -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The supremum `sup |b|` of a bump `b` is finite, since a bump is continuous with compact
support. -/
theorem iSup_enorm_lt_top : (⨆ z, ‖b.toFun z‖ₑ) < ∞ := by
  obtain ⟨A, hA⟩ := b.contDiff.continuous.bounded_above_of_compact_support b.hasCompactSupport
  exact iSup_enorm_lt_top_of_bddAbove ⟨A, Set.forall_mem_range.2 hA⟩

/-- The constant `sup |b| |B(0,1)| 2^(rn) (1 + 2^n)` of the bound of the local means by ball
means, with `r = ⌈R⌉₊`, the least natural number at least the radius `R` of the bump `b`. -/
noncomputable def ballMeanConst : ℝ≥0∞ :=
  (⨆ z, ‖b.toFun z‖ₑ) * volume (ball (0 : V) 1) * 2 ^ (⌈b.radius⌉₊ * finrank ℝ V) *
    (1 + 2 ^ finrank ℝ V)

/-- The constant of the bound of the local means by ball means is finite. -/
theorem ballMeanConst_ne_top : b.ballMeanConst ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top b.iSup_enorm_lt_top.ne
    (volume_ball_ne_top 1)) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)

/-- The steps `-2^(-(j+k)) z` with `‖z‖ ≤ R < 2^k` lie in the ball `B(0, 2^(-j))`. -/
theorem smul_closedBall_subset_ball (j : ℕ) {k : ℕ} (hk : b.radius < 2 ^ k) :
    (-((2 : ℝ) ^ (j + k))⁻¹) • closedBall (0 : V) b.radius ⊆ ball (0 : V) (1 / 2 ^ j) := by
  rw [smul_closedBall _ _ b.radius_nonneg, smul_zero]
  refine closedBall_subset_ball ?_
  rw [norm_neg, norm_inv, Real.norm_of_nonneg (by positivity), pow_add, mul_inv, mul_assoc,
    one_div]
  have h2 : ((2 : ℝ) ^ k)⁻¹ * b.radius < 1 := by
    rw [inv_mul_lt_iff₀ (by positivity), mul_one]
    exact hk
  calc ((2 : ℝ) ^ j)⁻¹ * (((2 : ℝ) ^ k)⁻¹ * b.radius) < ((2 : ℝ) ^ j)⁻¹ * 1 :=
        mul_lt_mul_of_pos_left h2 (by positivity)
    _ = ((2 : ℝ) ^ j)⁻¹ := mul_one _

/-- **One averaged difference by a ball mean**: for the bump `b`, `R < 2^k`, every `f`, `x`
and `j`, `∫ |b(z)| |Δ^L_{-2^(-(j+k)) z} f(x)| dz ≤ sup |b| |B(0,1)| 2^(kn) d_j f(x)`. The steps
`-2^(-(j+k)) z`, `‖z‖ ≤ R`, fill a ball inside `B(0, 2^(-j))`, and the change of variables
`h = -2^(-(j+k)) z` (`Rd.setLIntegral_comp_smul`) costs the factor `2^((j+k)n)`. -/
theorem lintegral_enorm_mul_higherDiff_le (L j : ℕ) {k : ℕ} (hk : b.radius < 2 ^ k)
    (f : V → ℂ) (x : V) :
    ∫⁻ z, ‖b.toFun z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ (j + k))⁻¹ • z))^[L] f x‖ₑ ≤
      (⨆ z, ‖b.toFun z‖ₑ) * volume (ball (0 : V) 1) * 2 ^ (k * finrank ℝ V) *
        ballMeanDiff L j f x := by
  have hr : -((2 : ℝ) ^ (j + k))⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (by positivity))
  have hS : (⨆ z, ‖b.toFun z‖ₑ) ≠ ∞ := b.iSup_enorm_lt_top.ne
  have hpt : ∀ z, ‖b.toFun z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ (j + k))⁻¹ • z))^[L] f x‖ₑ ≤
      (closedBall (0 : V) b.radius).indicator (fun z => (⨆ z, ‖b.toFun z‖ₑ) *
        ‖(fwdDiff (-((2 : ℝ) ^ (j + k))⁻¹ • z))^[L] f x‖ₑ) z := fun z => by
    by_cases hz : z ∈ closedBall (0 : V) b.radius
    · rw [indicator_of_mem hz]
      exact mul_le_mul' (le_iSup (fun z => ‖b.toFun z‖ₑ) z) le_rfl
    · rw [indicator_of_notMem hz, b.eq_zero z (by simpa using hz), eNorm_zero, zero_mul]
  calc ∫⁻ z, ‖b.toFun z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ (j + k))⁻¹ • z))^[L] f x‖ₑ
      ≤ ∫⁻ z in closedBall (0 : V) b.radius, (⨆ z, ‖b.toFun z‖ₑ) *
          ‖(fwdDiff (-((2 : ℝ) ^ (j + k))⁻¹ • z))^[L] f x‖ₑ := by
        rw [← lintegral_indicator measurableSet_closedBall]
        exact lintegral_mono hpt
    _ = (⨆ z, ‖b.toFun z‖ₑ) * (ENNReal.ofReal |((-((2 : ℝ) ^ (j + k))⁻¹) ^ finrank ℝ V)⁻¹| *
          ∫⁻ v in (-((2 : ℝ) ^ (j + k))⁻¹) • closedBall (0 : V) b.radius,
            ‖(fwdDiff v)^[L] f x‖ₑ) := by
        rw [lintegral_const_mul' _ _ hS]
        exact congrArg _ (setLIntegral_comp_smul (fun v => ‖(fwdDiff v)^[L] f x‖ₑ) hr _)
    _ ≤ (⨆ z, ‖b.toFun z‖ₑ) * (2 ^ ((j + k) * finrank ℝ V) *
          ∫⁻ v in ball (0 : V) (1 / 2 ^ j), ‖(fwdDiff v)^[L] f x‖ₑ) := by
        rw [ofReal_abs_inv_neg_inv_two_pow_pow]
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (lintegral_mono_set (b.smul_closedBall_subset_ball j hk)))
    _ = _ := by
        rw [setLIntegral_eq_mul_ballMeanDiff, add_mul, pow_add,
          ← two_pow_mul_volume_ball_one_div (V := V) j]
        ring

/-- **Local means by ball means**: let `r = ⌈R⌉₊`, so that `R < 2^r`. For every order `L`,
`1 ≤ p < ∞`, `f ∈ L_p`, almost every `x` and every level `j`,
`|k_{j+r+1} ⋆ f(x)| ≤ C d_j f(x)` with `C = Rd.LocalMeansBump.ballMeanConst`. Since
`k_{J+1} ⋆ f = (f - m_{2^J} ⋆ f) - (f - m_{2^(J+1)} ⋆ f)` with `J = j + r`, and each term
averages differences with steps `-2^(-J) z` or `-2^(-J-1) z`, `‖z‖ ≤ R`
(`Rd.ae_enorm_sub_conv_dilate_momentKernel_le`). -/
theorem enorm_localMean_le_ballMeanDiff {p : ℝ≥0∞} [Fact (1 ≤ p)] (L : ℕ) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ∀ j, ‖conv (b.kernel L (j + ⌈b.radius⌉₊ + 1)) f volume x‖ₑ ≤
      b.ballMeanConst * ballMeanDiff L j f x := by
  have hp1 : 1 ≤ p := Fact.out
  have hr : b.radius < 2 ^ ⌈b.radius⌉₊ :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_two_pow_self)
  have hr1 : b.radius < 2 ^ (⌈b.radius⌉₊ + 1) :=
    hr.trans (pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self _))
  refine ae_all_iff.2 fun j => ?_
  filter_upwards [sub_conv_ae hp1 hp (b.integrable_scaled L (j + ⌈b.radius⌉₊ + 1))
      (b.integrable_scaled L (j + ⌈b.radius⌉₊)) (Lp.memLp f),
    ae_enorm_sub_conv_dilate_momentKernel_le hp1 hp b.integrable b.integral_eq_one
      (Lp.memLp f) L (c := (2 : ℝ) ^ (j + ⌈b.radius⌉₊)) (by positivity),
    ae_enorm_sub_conv_dilate_momentKernel_le hp1 hp b.integrable b.integral_eq_one
      (Lp.memLp f) L (c := (2 : ℝ) ^ (j + (⌈b.radius⌉₊ + 1))) (by positivity)]
    with x hx hx1 hx2
  have hk : b.kernel L (j + ⌈b.radius⌉₊ + 1) =
      b.scaled L (j + ⌈b.radius⌉₊ + 1) - b.scaled L (j + ⌈b.radius⌉₊) := rfl
  have hsplit : ∀ a c d : ℂ, c - d = (a - d) - (a - c) := fun a c d => by ring
  rw [hk, hx, Pi.sub_apply, hsplit ((f : V → ℂ) x)]
  calc _ ≤ ‖(f : V → ℂ) x - conv (b.scaled L (j + ⌈b.radius⌉₊)) f volume x‖ₑ +
        ‖(f : V → ℂ) x - conv (b.scaled L (j + ⌈b.radius⌉₊ + 1)) f volume x‖ₑ := eNorm_sub_le
    _ ≤ (⨆ z, ‖b.toFun z‖ₑ) * volume (ball (0 : V) 1) * 2 ^ (⌈b.radius⌉₊ * finrank ℝ V) *
          ballMeanDiff L j f x + (⨆ z, ‖b.toFun z‖ₑ) * volume (ball (0 : V) 1) *
          2 ^ ((⌈b.radius⌉₊ + 1) * finrank ℝ V) * ballMeanDiff L j f x :=
        add_le_add (hx1.trans (b.lintegral_enorm_mul_higherDiff_le L j hr f x))
          (hx2.trans (b.lintegral_enorm_mul_higherDiff_le L j hr1 f x))
    _ = b.ballMeanConst * ballMeanDiff L j f x := by
        rw [ballMeanConst, add_mul, one_mul, pow_add]
        ring

/-! ### Ball means of the dual kernels -/

/-- The constant `|B(0,1)| max(A_L (2LR + L + 1)^n, 2^L A_0 (2LR + 1)^n (2LR + L + 1)^n)` of
the bound of ball means by local means, with `A_l = Rd.LocalMeansBump.dualDerivConst L l`, the
bound of the derivatives of order `≤ l` of the dual kernels. -/
noncomputable def diffByLocalMeansConst (L : ℕ) : ℝ≥0∞ :=
  volume (ball (0 : V) 1) * max
    (ENNReal.ofReal (b.dualDerivConst L L) *
      ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V)
    (2 ^ L * ENNReal.ofReal (b.dualDerivConst L 0) *
      ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
      ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V)

/-- The constant of the bound of ball means by local means is finite. -/
theorem diffByLocalMeansConst_ne_top (L : ℕ) : b.diffByLocalMeansConst L ≠ ∞ :=
  ENNReal.mul_ne_top (volume_ball_ne_top 1) (max_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)))

/-- **Differences of the dual kernels**: `|Δ^L_h η_i(y)| ≤ A_L 2^(in) 2^(iL) ‖h‖^L` with
`A_L = Rd.LocalMeansBump.dualDerivConst L L`, the case of the step `h` without dilation in
`Rd.LocalMeansBump.enorm_higherDiff_dual_le`. -/
theorem enorm_higherDiff_dual_le_mul (L i : ℕ) (h y : V) :
    ‖(fwdDiff h)^[L] (b.dual L i) y‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L L) * 2 ^ (i * finrank ℝ V) * dyadicWeight (L : ℝ) i *
        ‖h‖ₑ ^ L := by
  simpa [ENNReal.dyadicWeight_zero_right, eNorm_neg] using b.enorm_higherDiff_dual_le L L i 0 (-h) y

/-- **Differences of the dual kernels for short steps**: for `i ≤ j` and `‖h‖ < 2^(-j)`,
`|Δ^L_h η_i| ≤ A_L 2^(in) 2^(-(j-i)L) 1_{B(0, (2LR + L + 1) 2^(-i))}`, since `η_i` vanishes
outside `closedBall(0, 2LR 2^(-i))` and the points `y + l h`, `l ≤ L`, move by at most
`L 2^(-j) ≤ L 2^(-i)`. -/
theorem enorm_higherDiff_dual_le_indicator (L : ℕ) {i j : ℕ} (hij : i ≤ j) {h : V}
    (hh : h ∈ ball (0 : V) (1 / 2 ^ j)) (y : V) :
    ‖(fwdDiff h)^[L] (b.dual L i) y‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L L) * 2 ^ (i * finrank ℝ V) *
        dyadicWeight (-(L : ℝ)) (j - i) *
        (ball (0 : V) ((2 * L * b.radius + L + 1) * (1 / 2 ^ i))).indicator 1 y := by
  by_cases hy : y ∈ ball (0 : V) ((2 * L * b.radius + L + 1) * (1 / 2 ^ i))
  · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
    refine (b.enorm_higherDiff_dual_le_mul L i h y).trans ?_
    have hhL : ‖h‖ₑ ^ L ≤ dyadicWeight (-(L : ℝ)) j := by
      rw [ENNReal.dyadicWeight_neg_natCast]
      exact pow_le_pow_left' (enorm_le_inv_two_pow_of_mem_ball hh) L
    calc ENNReal.ofReal (b.dualDerivConst L L) * 2 ^ (i * finrank ℝ V) * dyadicWeight (L : ℝ) i *
          ‖h‖ₑ ^ L
        ≤ ENNReal.ofReal (b.dualDerivConst L L) * 2 ^ (i * finrank ℝ V) *
            (dyadicWeight (L : ℝ) i * dyadicWeight (-(L : ℝ)) j) := by
          rw [← mul_assoc]
          exact mul_le_mul' le_rfl hhL
      _ = _ := by rw [dyadicWeight_mul_dyadicWeight_neg_of_le _ hij]
  · rw [indicator_of_notMem hy, mul_zero, nonpos_iff_eq_zero,
      b.higherDiff_dual_eq_zero L L i ?_, eNorm_zero]
    rw [mem_ball_zero_iff, not_lt] at hy
    rw [mem_ball_zero_iff] at hh
    have hji : (1 : ℝ) / 2 ^ j ≤ 1 / 2 ^ i :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ one_le_two hij)
    have hLh : (L : ℝ) * ‖h‖ ≤ L * (1 / 2 ^ i) :=
      mul_le_mul_of_nonneg_left (hh.le.trans hji) (Nat.cast_nonneg L)
    have hpos : (0 : ℝ) < 1 / 2 ^ i := by positivity
    calc 2 * L * b.radius / 2 ^ i + L * ‖h‖
        ≤ 2 * L * b.radius * (1 / 2 ^ i) + L * (1 / 2 ^ i) := by
          rw [mul_one_div]
          exact add_le_add le_rfl hLh
      _ < (2 * L * b.radius + L + 1) * (1 / 2 ^ i) := by nlinarith
      _ ≤ ‖y‖ := hy

/-- **Ball means of `η_i ⋆ g`, fine levels, one step**: for `i ≤ j`, a locally integrable `g`,
`‖h‖ < 2^(-j)` and every `x`,
`|Δ^L_h (η_i ⋆ g)(x)| ≤ A_L (2LR + L + 1)^n |B(0,1)| 2^(-(j-i)L) M|g|(x)`: the difference moves
onto the kernel (`Rd.higherDiff_conv_apply`), and a kernel bounded by a ball acts below the
maximal function (`Rd.lintegral_mul_le_maximal_of_ball`). -/
theorem enorm_higherDiff_conv_dual_le_of_le (L : ℕ) {i j : ℕ} (hij : i ≤ j) {g : V → ℂ}
    (hg : LocallyIntegrable g volume) {h : V} (hh : h ∈ ball (0 : V) (1 / 2 ^ j)) (x : V) :
    ‖(fwdDiff h)^[L] (conv (b.dual L i) g volume) x‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L L) *
        ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
        dyadicWeight (-(L : ℝ)) (j - i) * maximal (fun y => ‖g y‖ₑ) x := by
  have hc : (0 : ℝ) < 2 * L * b.radius + L + 1 := by
    have := b.radius_nonneg
    positivity
  have hA : ENNReal.ofReal (b.dualDerivConst L L) * 2 ^ (i * finrank ℝ V) *
      dyadicWeight (-(L : ℝ)) (j - i) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) (ENNReal.dyadicWeight_ne_top _ _)
  rw [higherDiff_conv_apply (fun v x => integrable_translate_mul_of_locallyIntegrable
    (b.continuous_dual L i) (b.hasCompactSupport_dual L i) hg v x)]
  refine (enorm_conv_le_lintegral _ _ x).trans ((lintegral_mul_le_maximal_of_ball
    (K := fun y => ‖(fwdDiff h)^[L] (b.dual L i) y‖ₑ) hA
    (b.enorm_higherDiff_dual_le_indicator L hij hh) (mul_pos hc (one_div_two_pow_pos i))
    (fun y => ‖g y‖ₑ) x).trans (le_of_eq ?_))
  rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) hc, ENNReal.ofReal_pow hc.le,
    ← two_pow_mul_volume_ball_one_div (V := V) i]
  ring

/-- **Ball means of `η_i ⋆ g`, fine levels**: for `i ≤ j`, a locally integrable `g` and every
`x`, `d_j(η_i ⋆ g)(x) ≤ C 2^(-(j-i)L) M|g|(x)` with
`C = Rd.LocalMeansBump.diffByLocalMeansConst L`. -/
theorem ballMeanDiff_conv_dual_le_of_le (L : ℕ) {i j : ℕ} (hij : i ≤ j) {g : V → ℂ}
    (hg : LocallyIntegrable g volume) (x : V) :
    ballMeanDiff L j (conv (b.dual L i) g volume) x ≤
      b.diffByLocalMeansConst L * dyadicWeight (-(L : ℝ)) (j - i) *
        maximal (fun y => ‖g y‖ₑ) x := by
  refine (ballMeanDiff_le_of_forall fun h hh =>
    b.enorm_higherDiff_conv_dual_le_of_le L hij hg hh x).trans ?_
  refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
  rw [diffByLocalMeansConst, mul_comm _ (volume (ball (0 : V) 1))]
  exact mul_le_mul' le_rfl (le_max_left _ _)

/-- **The dual kernels are bounded with small support**:
`|η_i| ≤ A_0 2^(in) 1_{B(0, (2LR + 1) 2^(-i))}` with
`A_0 = Rd.LocalMeansBump.dualDerivConst L 0`. -/
theorem enorm_dual_le_indicator (L i : ℕ) (y : V) :
    ‖b.dual L i y‖ₑ ≤ ENNReal.ofReal (b.dualDerivConst L 0) * 2 ^ (i * finrank ℝ V) *
      (ball (0 : V) ((2 * L * b.radius + 1) * (1 / 2 ^ i))).indicator 1 y := by
  by_cases hy : y ∈ ball (0 : V) ((2 * L * b.radius + 1) * (1 / 2 ^ i))
  · rw [indicator_of_mem hy, Pi.one_apply, mul_one]
    have h := b.norm_iteratedFDeriv_dual_le L 0 le_rfl i y
    rw [norm_iteratedFDeriv_zero, add_zero] at h
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
    rw [ENNReal.ofReal_mul (b.dualDerivConst_nonneg L 0), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  · rw [indicator_of_notMem hy, mul_zero, nonpos_iff_eq_zero, b.dual_eq_zero_of_lt L i ?_,
      eNorm_zero]
    rw [mem_ball_zero_iff, not_lt] at hy
    refine lt_of_lt_of_le ?_ hy
    rw [← mul_one_div]
    exact mul_lt_mul_of_pos_right (lt_add_one _) (one_div_two_pow_pos i)

/-- `|η_i ⋆ g(u)| ≤ A_0 2^(in) ∫_{B(u, (2LR + 1) 2^(-i))} |g|` for every `g` and every `u`. -/
theorem enorm_conv_dual_le (L i : ℕ) (g : V → ℂ) (u : V) :
    ‖conv (b.dual L i) g volume u‖ₑ ≤
      ENNReal.ofReal (b.dualDerivConst L 0) * 2 ^ (i * finrank ℝ V) *
        ∫⁻ w in ball u ((2 * L * b.radius + 1) * (1 / 2 ^ i)), ‖g w‖ₑ :=
  (enorm_conv_le_lintegral _ _ u).trans (lintegral_mul_le_setLIntegral_ball
    (K := fun y => ‖b.dual L i y‖ₑ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (b.enorm_dual_le_indicator L i) (fun w => ‖g w‖ₑ) u)

/-- `|η_i ⋆ g(x)| ≤ A_0 (2LR + 1)^n |B(0,1)| M|g|(x)` for every `g` and every `x`. -/
theorem enorm_conv_dual_le_maximal (L i : ℕ) (g : V → ℂ) (x : V) :
    ‖conv (b.dual L i) g volume x‖ₑ ≤ ENNReal.ofReal (b.dualDerivConst L 0) *
      ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
        maximal (fun y => ‖g y‖ₑ) x := by
  have hc : (0 : ℝ) < 2 * L * b.radius + 1 := by
    have := b.radius_nonneg
    positivity
  refine (b.enorm_conv_dual_le L i g x).trans ?_
  calc ENNReal.ofReal (b.dualDerivConst L 0) * 2 ^ (i * finrank ℝ V) *
        ∫⁻ w in ball x ((2 * L * b.radius + 1) * (1 / 2 ^ i)), ‖g w‖ₑ
      ≤ ENNReal.ofReal (b.dualDerivConst L 0) * 2 ^ (i * finrank ℝ V) *
          (volume (ball (0 : V) ((2 * L * b.radius + 1) * (1 / 2 ^ i))) *
            maximal (fun y => ‖g y‖ₑ) x) :=
        mul_le_mul' le_rfl (setLIntegral_ball_le_mul_maximal
          (mul_pos hc (one_div_two_pow_pos i)) _ x)
    _ = _ := by
        rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) hc, ENNReal.ofReal_pow hc.le,
    ← two_pow_mul_volume_ball_one_div (V := V) i]
        ring

/-- **Averages of shifted `η_i ⋆ g`**: for `j ≤ i`, `1 ≤ l ≤ L`, a locally integrable `g` and
every `x`, `⨍_B |η_i ⋆ g(x + l h)| dh ≤ A_0 (2LR + 1)^n (2LR + L + 1)^n |B(0,1)| M|g|(x)`
with `B = B(0, 2^(-j))`: the bound of `|η_i ⋆ g|` by integrals of `|g|` over moving balls
(`Rd.LocalMeansBump.enorm_conv_dual_le`) and the average of those balls
(`Rd.setLIntegral_setLIntegral_ball_le`). -/
theorem laverage_enorm_conv_dual_add_smul_le_of_one_le (L : ℕ) {i j : ℕ} (hji : j ≤ i)
    {g : V → ℂ} (hg : LocallyIntegrable g volume) {l : ℕ} (hl1 : 1 ≤ l) (hlL : l ≤ L) (x : V) :
    ⨍⁻ h in ball (0 : V) (1 / 2 ^ j), ‖conv (b.dual L i) g volume (x + (l : ℝ) • h)‖ₑ ∂volume ≤
      ENNReal.ofReal (b.dualDerivConst L 0) *
        ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
        ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
        maximal (fun y => ‖g y‖ₑ) x := by
  rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
  have hR := b.radius_nonneg
  have hc1 : (0 : ℝ) < 2 * L * b.radius + 1 := by positivity
  have hc2 : (0 : ℝ) < 2 * L * b.radius + L + 1 := by positivity
  have hA : ENNReal.ofReal (b.dualDerivConst L 0) * 2 ^ (i * finrank ℝ V) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hB0 : volume (ball (0 : V) (1 / 2 ^ j)) ≠ 0 := volume_ball_ne_zero (one_div_two_pow_pos j)
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  have hrad : (2 * L * b.radius + 1) * (1 / 2 ^ i) + l * (1 / 2 ^ j) ≤
      (2 * L * b.radius + L + 1) * (1 / 2 ^ j) := by
    have hij : (1 : ℝ) / 2 ^ i ≤ 1 / 2 ^ j :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ one_le_two hji)
    have hlL' : (l : ℝ) ≤ L := by exact_mod_cast hlL
    have hj := one_div_two_pow_pos j
    nlinarith
  calc (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ *
        ∫⁻ h in ball (0 : V) (1 / 2 ^ j), ‖conv (b.dual L i) g volume (x + (l : ℝ) • h)‖ₑ
      ≤ (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ *
          ∫⁻ h in ball (0 : V) (1 / 2 ^ j), ENNReal.ofReal (b.dualDerivConst L 0) *
            2 ^ (i * finrank ℝ V) * ∫⁻ w in ball (x + (l : ℝ) • h)
              ((2 * L * b.radius + 1) * (1 / 2 ^ i)), ‖g w‖ₑ :=
        mul_le_mul' le_rfl (lintegral_mono fun h => b.enorm_conv_dual_le L i g _)
    _ ≤ (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ * (ENNReal.ofReal (b.dualDerivConst L 0) *
          2 ^ (i * finrank ℝ V) *
          (volume (ball (0 : V) ((2 * L * b.radius + 1) * (1 / 2 ^ i))) *
            (volume (ball (0 : V) ((2 * L * b.radius + L + 1) * (1 / 2 ^ j))) *
              maximal (fun y => ‖g y‖ₑ) x))) := by
        rw [lintegral_const_mul' _ _ hA]
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ((setLIntegral_setLIntegral_ball_le
          hg.aestronglyMeasurable.eNorm hl _ _ x).trans (mul_le_mul' le_rfl ?_)))
        exact (lintegral_mono_set (ball_subset_ball hrad)).trans
          (setLIntegral_ball_le_mul_maximal (mul_pos hc2 (one_div_two_pow_pos j)) _ x)
    _ = _ := by
        rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) hc1, ENNReal.ofReal_pow hc1.le,
          Measure.addHaar_ball_mul_of_pos volume (0 : V) hc2, ENNReal.ofReal_pow hc2.le,
          ← two_pow_mul_volume_ball_one_div (V := V) i]
        calc _ = ENNReal.ofReal (b.dualDerivConst L 0) *
              ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
              ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V *
              (2 ^ (i * finrank ℝ V) * volume (ball (0 : V) (1 / 2 ^ i))) *
              maximal (fun y => ‖g y‖ₑ) x *
              ((volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ * volume (ball (0 : V) (1 / 2 ^ j))) := by
              ring
          _ = _ := by rw [ENNReal.inv_mul_cancel hB0 (volume_ball_ne_top _), mul_one]

/-- **Averages of shifted `η_i ⋆ g`, every shift**: for `j ≤ i`, `l ≤ L`, a locally integrable
`g` and every `x`,
`⨍_B |η_i ⋆ g(x + l h)| dh ≤ A_0 (2LR + 1)^n (2LR + L + 1)^n |B(0,1)| M|g|(x)` with
`B = B(0, 2^(-j))`; for `l = 0` the integrand is constant
(`Rd.LocalMeansBump.enorm_conv_dual_le_maximal`). -/
theorem laverage_enorm_conv_dual_add_smul_le (L : ℕ) {i j : ℕ} (hji : j ≤ i) {g : V → ℂ}
    (hg : LocallyIntegrable g volume) {l : ℕ} (hlL : l ≤ L) (x : V) :
    ⨍⁻ h in ball (0 : V) (1 / 2 ^ j), ‖conv (b.dual L i) g volume (x + (l : ℝ) • h)‖ₑ ∂volume ≤
      ENNReal.ofReal (b.dualDerivConst L 0) *
        ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
        ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
        maximal (fun y => ‖g y‖ₑ) x := by
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · have hB0 : volume (ball (0 : V) (1 / 2 ^ j)) ≠ 0 :=
      volume_ball_ne_zero (one_div_two_pow_pos j)
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V := by
      have := b.radius_nonneg
      exact one_le_pow₀ (ENNReal.one_le_ofReal.2 (le_add_of_nonneg_left (by positivity)))
    simp only [Nat.cast_zero, zero_smul, add_zero]
    rw [setLAverage_eq, ENNReal.div_eq_inv_mul, setLIntegral_const, mul_comm _ (volume _),
      ← mul_assoc, ENNReal.inv_mul_cancel hB0 (volume_ball_ne_top _), one_mul]
    refine (b.enorm_conv_dual_le_maximal L i g x).trans ?_
    calc ENNReal.ofReal (b.dualDerivConst L 0) *
          ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
          maximal (fun y => ‖g y‖ₑ) x
        = ENNReal.ofReal (b.dualDerivConst L 0) *
            ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V * 1 * volume (ball (0 : V) 1) *
            maximal (fun y => ‖g y‖ₑ) x := by rw [mul_one]
      _ ≤ _ := by gcongr
  · exact b.laverage_enorm_conv_dual_add_smul_le_of_one_le L hji hg hl1 hlL x

/-- **Ball means of `η_i ⋆ g`, coarse levels**: for `j < i`, a locally integrable `g` and every
`x`, `d_j(η_i ⋆ g)(x) ≤ C M|g|(x)` with `C = Rd.LocalMeansBump.diffByLocalMeansConst L`. The
difference is a sum of `L + 1` shifts `η_i ⋆ g(x + l h)` with binomial weights of sum `2^L`, and
the average of each shift over the ball is bounded by the maximal function
(`Rd.LocalMeansBump.laverage_enorm_conv_dual_add_smul_le`). -/
theorem ballMeanDiff_conv_dual_le_of_lt (L : ℕ) {i j : ℕ} (hji : j < i) {g : V → ℂ}
    (hg : LocallyIntegrable g volume) (x : V) :
    ballMeanDiff L j (conv (b.dual L i) g volume) x ≤
      b.diffByLocalMeansConst L * maximal (fun y => ‖g y‖ₑ) x := by
  set F := conv (b.dual L i) g volume
  set K := ENNReal.ofReal (b.dualDerivConst L 0) *
    ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
    ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V * volume (ball (0 : V) 1) *
    maximal (fun y => ‖g y‖ₑ) x
  have hF : Continuous F := (b.hasCompactSupport_dual L i).continuous_convolution_left
    (ContinuousLinearMap.mul ℂ ℂ) (b.continuous_dual L i) hg
  have hmeas : ∀ l ∈ Finset.range (L + 1), AEMeasurable
      (fun h => (L.choose l : ℝ≥0∞) * ‖F (x + (l : ℝ) • h)‖ₑ)
      (volume.restrict (ball (0 : V) (1 / 2 ^ j))) := fun l _ =>
    ((hF.comp (continuous_const.add (continuous_id.const_smul _))).measurable.eNorm.const_mul
      _).aemeasurable
  calc ballMeanDiff L j F x
      ≤ (volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ * ∫⁻ h in ball (0 : V) (1 / 2 ^ j),
          ∑ l ∈ Finset.range (L + 1), (L.choose l : ℝ≥0∞) * ‖F (x + (l : ℝ) • h)‖ₑ := by
        rw [ballMeanDiff]
        exact mul_le_mul' le_rfl (lintegral_mono fun h => enorm_higherDiff_le_sum L h F x)
    _ = ∑ l ∈ Finset.range (L + 1), (L.choose l : ℝ≥0∞) *
          ((volume (ball (0 : V) (1 / 2 ^ j)))⁻¹ *
            ∫⁻ h in ball (0 : V) (1 / 2 ^ j), ‖F (x + (l : ℝ) • h)‖ₑ) := by
        rw [lintegral_finsetSum' _ hmeas, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
        ring
    _ ≤ ∑ l ∈ Finset.range (L + 1), (L.choose l : ℝ≥0∞) * K :=
        Finset.sum_le_sum fun l hl => mul_le_mul' le_rfl
          (by simpa only [setLAverage_eq, ENNReal.div_eq_inv_mul] using
              b.laverage_enorm_conv_dual_add_smul_le L hji.le hg
                (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) x)
    _ = 2 ^ L * K := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose L
    _ ≤ b.diffByLocalMeansConst L * maximal (fun y => ‖g y‖ₑ) x := by
        rw [diffByLocalMeansConst]
        calc 2 ^ L * K = volume (ball (0 : V) 1) * (2 ^ L * ENNReal.ofReal (b.dualDerivConst L 0) *
              ENNReal.ofReal (2 * L * b.radius + 1) ^ finrank ℝ V *
              ENNReal.ofReal (2 * L * b.radius + L + 1) ^ finrank ℝ V) *
              maximal (fun y => ‖g y‖ₑ) x := by ring
          _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (le_max_right _ _)) le_rfl

/-- **Ball means of `η_i ⋆ g`**: for all levels `i, j`, a locally integrable `g` and every `x`,
`d_j(η_i ⋆ g)(x) ≤ C c_{ji} M|g|(x)` with `c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for
`i > j`, and `C = Rd.LocalMeansBump.diffByLocalMeansConst L`. -/
theorem ballMeanDiff_conv_dual_le (L i j : ℕ) {g : V → ℂ} (hg : LocallyIntegrable g volume)
    (x : V) :
    ballMeanDiff L j (conv (b.dual L i) g volume) x ≤ b.diffByLocalMeansConst L *
      ((if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) * maximal (fun y => ‖g y‖ₑ) x) := by
  split_ifs with hij
  · rw [← mul_assoc]
    exact b.ballMeanDiff_conv_dual_le_of_le L hij hg x
  · rw [one_mul]
    exact b.ballMeanDiff_conv_dual_le_of_lt L (not_le.1 hij) hg x

/-! ### Ball means by local means -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Ball means of the partial sums of the reproducing formula**: for `1 ≤ p < ∞`,
`f ∈ L_p`, all `J, j` and every `x`,
`d_j(m_{2^J} ⋆ m_{2^J} ⋆ f)(x) ≤ C ∑_{i ≤ J} c_{ji} M(k_i ⋆ f)(x)` with
`C = Rd.LocalMeansBump.diffByLocalMeansConst L`, since
`m_{2^J} ⋆ m_{2^J} ⋆ f = ∑_{i ≤ J} η_i ⋆ k_i ⋆ f` at every point
(`Rd.LocalMeansBump.sum_conv_dual_localMean_apply`). -/
theorem ballMeanDiff_partialSum_le (L : ℕ) (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V))
    (J j : ℕ) (x : V) :
    ballMeanDiff L j (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) x ≤
      b.diffByLocalMeansConst L * ∑ i ∈ Finset.range (J + 1),
        (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
          maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) x := by
  have hp1 : 1 ≤ p := Fact.out
  have heq : conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume =
      ∑ i ∈ Finset.range (J + 1), conv (b.dual L i) (b.localMean hp L i f) volume := by
    funext y
    rw [Finset.sum_apply]
    exact (b.sum_conv_dual_localMean_apply hp L J f y).symm
  have hmeas : ∀ i ∈ Finset.range (J + 1),
      Measurable (conv (b.dual L i) (b.localMean hp L i f) volume) := fun i _ =>
    ((b.hasCompactSupport_dual L i).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      (b.continuous_dual L i) ((Lp.memLp _).locallyIntegrable hp1)).measurable
  rw [heq, Finset.mul_sum]
  refine (ballMeanDiff_finsetSum_le hmeas L j x).trans (Finset.sum_le_sum fun i _ => ?_)
  have hM : maximal (fun y => ‖(b.localMean hp L i f : V → ℂ) y‖ₑ) =
      maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) :=
    maximal_congr_ae ((b.localMean_ae_eq hp L i f).mono fun y hy => by simp only [hy])
  rw [← hM]
  exact b.ballMeanDiff_conv_dual_le L i j ((Lp.memLp _).locallyIntegrable hp1) x

/-- The bound of the ball means of `f` through the partial sums: for `1 ≤ p < ∞`, `f ∈ L_p`,
all `J, j` and every `x`,
`d_j f(x) ≤ C ∑_i c_{ji} M(k_i ⋆ f)(x) + d_j(f - m_{2^J} ⋆ m_{2^J} ⋆ f)(x)`, with
`C = Rd.LocalMeansBump.diffByLocalMeansConst L` (subadditivity, `Rd.ballMeanDiff_add_le`, with
the continuous partial sum as the measurable summand). -/
theorem ballMeanDiff_le_tsum_add (L : ℕ) (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V))
    (J j : ℕ) (x : V) :
    ballMeanDiff L j f x ≤ b.diffByLocalMeansConst L * ∑' i,
        (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
          maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) x +
      ballMeanDiff L j ((f : V → ℂ) -
        conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) x := by
  have hp1 : 1 ≤ p := Fact.out
  have hFc : Continuous (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) :=
    (b.hasCompactSupport_scaled L J).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      (b.continuous_scaled L J) ((Lp.memLp _).locallyIntegrable hp1)
  have h1 : ballMeanDiff L j f x = ballMeanDiff L j
      (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume + ((f : V → ℂ) -
        conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume)) x := by
    rw [add_sub_cancel]
  rw [h1]
  refine (ballMeanDiff_add_le hFc.measurable _ L j x).trans (add_le_add ?_ le_rfl)
  refine (b.ballMeanDiff_partialSum_le L hp f J j x).trans (mul_le_mul' le_rfl ?_)
  exact sum_le_tsum _

/-- The remainders of the reproducing formula vanish in the ball means: for `L ≥ 1`,
`1 ≤ p < ∞`, `f ∈ L_p` and every `j`, `‖d_j(f - m_{2^J} ⋆ m_{2^J} ⋆ f)‖_p → 0` as `J → ∞`,
since it is at most `2^L ‖f - m_{2^J} ⋆ m_{2^J} ⋆ f‖_p` (`Rd.eLpNorm_ballMeanDiff_le`) and
`m_{2^J} ⋆ m_{2^J} ⋆ f → f` in `L_p` (`Rd.LocalMeansBump.tendsto_sum_dual_localMean`). -/
theorem tendsto_eLpNorm_ballMeanDiff_sub {L : ℕ} (hL : 1 ≤ L) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    Tendsto (fun J => eLpNorm (ballMeanDiff L j ((f : V → ℂ) -
      conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume)) p volume)
      atTop (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  set H : ℕ → Lp ℂ p (volume : Measure V) := fun J =>
    convLp hp (b.integrable_scaled L J) (convLp hp (b.integrable_scaled L J) f)
  have hH : Tendsto H atTop (𝓝 f) := by
    have h := b.tendsto_sum_dual_localMean hp hL f
    simp_rw [b.sum_dual_localMean hp L] at h
    exact h
  have h0 : Tendsto (fun J => 2 ^ L * ‖H J - f‖ₑ) atTop (𝓝 0) := by
    have h := (hH.sub_const f).eNorm
    rw [sub_self, eNorm_zero] at h
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun J => zero_le)
    fun J => ?_
  have hae : (f : V → ℂ) - conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume
      =ᵐ[volume] ⇑(f - H J) := by
    filter_upwards [Lp.coeFn_sub f (H J), convLp_apply_ae hp (b.integrable_scaled L J)
      (convLp hp (b.integrable_scaled L J) f)] with y hy1 hy2
    rw [hy1, Pi.sub_apply, Pi.sub_apply, hy2]
  have hFc : Continuous (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) :=
    (b.hasCompactSupport_scaled L J).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      (b.continuous_scaled L J) ((Lp.memLp _).locallyIntegrable hp1)
  refine (eLpNorm_ballMeanDiff_le hp1 hp ((Lp.aestronglyMeasurable f).sub
    hFc.aestronglyMeasurable) L j).trans (le_of_eq ?_)
  rw [eLpNorm_congr_ae hae, ← Lp.eNorm_def, eNorm_sub_rev]

/-- **Ball means by local means, pointwise**: for `L ≥ 1`, `1 ≤ p < ∞` and `f ∈ L_p`, almost
everywhere and for all levels `j`, `d_j f(x) ≤ C ∑_i c_{ji} M(k_i ⋆ f)(x)` with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.diffByLocalMeansConst L`. The bound holds for the partial sums of the
reproducing formula at every point, and passes to `f` by
`MeasureTheory.ae_le_of_le_add_of_tendsto_eLpNorm`. -/
theorem ballMeanDiff_le_tsum_maximal {L : ℕ} (hL : 1 ≤ L) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ∀ j, ballMeanDiff L j f x ≤ b.diffByLocalMeansConst L * ∑' i,
      (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) x := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine ae_all_iff.2 fun j => ae_le_of_le_add_of_tendsto_eLpNorm
    (measurable_ballMeanDiff (Lp.stronglyMeasurable f).measurable L j).aemeasurable
    (measurable_const.mul (Measurable.tsum fun i => measurable_const.mul
      (measurable_maximal _))).aemeasurable hp0
    (fun J => Eventually.of_forall fun x => b.ballMeanDiff_le_tsum_add L hp f J j x)
    (b.tendsto_eLpNorm_ballMeanDiff_sub hL hp f j)

/-! ### The characterisation -/

/-- **`L_p` norms by local means**: for `L ≥ 1`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, every `s` and
`f ∈ L_p`, `‖f‖_p ≤ 2 ‖m‖_1 (1 - 2^(-s))⁻¹ ‖f‖^{b,L}_{F^s_{p,q}}`: the reproducing formula
`f = ∑_j η_j ⋆ k_j ⋆ f` with `‖η_j‖_1 ≤ 2 ‖m‖_1` (`ENNReal.enorm_le_of_tendsto_sum`), then
`ℓ_∞(L_p) ≤ L_p(ℓ_∞) ≤ L_p(ℓ_q)` (`MeasureTheory.lqNorm_max_le_eLpNorm_lqNorm`). -/
theorem enorm_le_tlLocalMeansNorm {L : ℕ} (hL : 1 ≤ L) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ *
      b.tlLocalMeansNorm L s q f := by
  have hp1 : 1 ≤ p := Fact.out
  have hmeas := fun j => b.measurable_dyadicWeight_mul_conv_kernel L s j f
  have h1 := ENNReal.enorm_le_of_tendsto_sum (b.tendsto_sum_dual_localMean hp hL f)
    (K := 2 * eLpNorm (momentKernel b.toFun L) 1 volume) (b := fun j => ‖b.localMean hp L j f‖ₑ)
    (fun j => (enorm_convLp_le hp _ _).trans (mul_le_mul' (b.eLpNorm_dual_one_le L j) le_rfl))
    s (q := ∞) le_top
  refine h1.trans (mul_le_mul' le_rfl ?_)
  have heq : ∀ j, dyadicWeight s j * ‖b.localMean hp L j f‖ₑ =
      eLpNorm (fun y => dyadicWeight s j * ‖conv (b.kernel L j) f volume y‖ₑ) p volume :=
    fun j => by
    rw [eLpNorm_const_mul_enorm _ (b.continuous_conv_kernel L j f).aestronglyMeasurable,
      Lp.eNorm_def, eLpNorm_congr_ae (b.localMean_ae_eq hp L j f)]
  simp_rw [heq]
  calc lqNorm ∞ (fun j =>
        eLpNorm (fun y => dyadicWeight s j * ‖conv (b.kernel L j) f volume y‖ₑ) p volume)
      ≤ eLpNorm (fun x => lqNorm ∞ (fun j =>
          dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ)) p volume := by
        have h := lqNorm_max_le_eLpNorm_lqNorm hp1 hp le_top
          fun j => (hmeas j).aemeasurable (μ := volume)
        rwa [max_eq_right le_top] at h
    _ ≤ b.tlLocalMeansNorm L s q f :=
        eLpNorm_mono_eNorm (measurable_lqNorm_comp hmeas ∞).aestronglyMeasurable fun x => by
          simp only [eNorm_eq_self]
          exact ENNReal.lqNorm_le_lqNorm_of_le (zero_lt_one.trans_le hq).ne' le_top _

/-- The constant `2 ‖m‖_1 (1 - 2^(-s))⁻¹ + C A_{s,L} C_{FS}` of the bound of the ball means
quasi-norm by local means: `‖m‖_1` is the `L_1` norm of the moment kernel,
`C = Rd.LocalMeansBump.diffByLocalMeansConst L`, `A_{s,L} = ENNReal.almostDiagonalConst s L` and
`C_{FS} = Rd.feffermanSteinConst V p q`. -/
noncomputable def diffUpperConst (L : ℕ) (p q : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    b.diffByLocalMeansConst L * ENNReal.almostDiagonalConst s L * feffermanSteinConst V p q

/-- The constant of the bound of the ball means quasi-norm by local means is finite for
`1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L`. -/
theorem diffUpperConst_ne_top {L : ℕ} {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    {s : ℝ} (hs : 0 < s) (hsL : s < L) : b.diffUpperConst L p q s ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (eLpNorm_momentKernel_ne_top b.integrable L))
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.diffByLocalMeansConst_ne_top L)
      (ENNReal.almostDiagonalConst_ne_top hs hsL)) (feffermanSteinConst_ne_top hp1 hp hq1)⟩

/-- **The ball means quasi-norm by local means**: for `L ≥ 1`, `1 < p < ∞`, `1 < q ≤ ∞`, every
`s` and `f ∈ L_p`, `‖f‖_p + ‖(2^(js) d_j f)_j‖_{L_p(ℓ_q)} ≤ C ‖f‖^{b,L}_{F^s_{p,q}}` with
`C = Rd.LocalMeansBump.diffUpperConst L p q s`, finite for `0 < s < L`. Pointwise the ball
means are bounded by maximal functions of the local means
(`Rd.LocalMeansBump.ballMeanDiff_le_tsum_maximal`), and the almost diagonal estimate and the
Fefferman–Stein inequality bound those in `L_p(ℓ_q)`. -/
theorem tlDiffNorm_le_tlLocalMeansNorm {L : ℕ} (hL : 1 ≤ L) (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    tlDiffNorm L s q f ≤ b.diffUpperConst L p q s * b.tlLocalMeansNorm L s q f := by
  have h2 : eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x)) p
      volume ≤ b.diffByLocalMeansConst L * ENNReal.almostDiagonalConst s L *
        feffermanSteinConst V p q * b.tlLocalMeansNorm L s q f :=
    eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (measurable_lqNorm_ballMeanDiff L s q f).aemeasurable
      (fun i => (b.measurable_dyadicWeight_mul_conv_kernel L s i f).aemeasurable) (by
        filter_upwards [b.ballMeanDiff_le_tsum_maximal hL hp f] with x hx
        refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq1.le s L hx).trans_eq ?_
        simp only [dyadicWeight_mul_maximal])
  rw [tlDiffNorm, diffUpperConst, add_mul]
  exact add_le_add (b.enorm_le_tlLocalMeansNorm hL hp hq1.le s f) h2

/-- The constant `2 ‖m‖_1 ∑_{j ≤ r} 2^(js) + 2^((r+1)s) C` of the bound of the local means
quasi-norm by ball means, with `r = ⌈R⌉₊` and `C = Rd.LocalMeansBump.ballMeanConst`. -/
noncomputable def diffLowerConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  2 * eLpNorm (momentKernel b.toFun L) 1 volume *
      ∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1), dyadicWeight s j +
    dyadicWeight s (⌈b.radius⌉₊ + 1) * b.ballMeanConst

/-- The constant of the bound of the local means quasi-norm by ball means is finite. -/
theorem diffLowerConst_ne_top (L : ℕ) (s : ℝ) : b.diffLowerConst L s ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (eLpNorm_momentKernel_ne_top b.integrable L))
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.dyadicWeight_ne_top s j),
    ENNReal.mul_ne_top (ENNReal.dyadicWeight_ne_top _ _) b.ballMeanConst_ne_top⟩

/-- **The weighted local means in `L_p`** (Young's inequality):
`‖2^(js) |k_j ⋆ f|‖_p ≤ 2^(js) 2 ‖m‖_1 ‖f‖_p`. -/
theorem eLpNorm_dyadicWeight_mul_conv_kernel_le (L : ℕ) (hp : p ≠ ∞) (s : ℝ) (j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun y => dyadicWeight s j * ‖conv (b.kernel L j) f volume y‖ₑ) p volume ≤
      dyadicWeight s j * (2 * eLpNorm (momentKernel b.toFun L) 1 volume * ‖f‖ₑ) := by
  rw [eLpNorm_const_mul_enorm _ (b.continuous_conv_kernel L j f).aestronglyMeasurable,
    ← eLpNorm_congr_ae (b.localMean_ae_eq hp L j f), ← Lp.eNorm_def]
  exact mul_le_mul' le_rfl
    ((enorm_convLp_le hp _ f).trans (mul_le_mul' (b.eLpNorm_kernel_one_le L j) le_rfl))

/-- **The fine local means by ball means in `ℓ_q`**: with `r = ⌈R⌉₊`, almost everywhere,
`‖(2^((j+r+1)s) |k_{j+r+1} ⋆ f(x)|)_j‖_{ℓ_q} ≤ 2^((r+1)s) C ‖(2^(js) d_j f(x))_j‖_{ℓ_q}` with
`C = Rd.LocalMeansBump.ballMeanConst` (`Rd.LocalMeansBump.enorm_localMean_le_ballMeanDiff`). -/
theorem lqNorm_localMean_shift_le (L : ℕ) (hp : p ≠ ∞) (q : ℝ≥0∞) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, lqNorm q (fun j => dyadicWeight s (j + (⌈b.radius⌉₊ + 1)) *
        ‖conv (b.kernel L (j + (⌈b.radius⌉₊ + 1))) f volume x‖ₑ) ≤
      dyadicWeight s (⌈b.radius⌉₊ + 1) * b.ballMeanConst *
        lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x) := by
  filter_upwards [b.enorm_localMean_le_ballMeanDiff L hp f] with x hx
  rw [← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun j => ?_
  rw [ENNReal.dyadicWeight_add_nat]
  calc dyadicWeight s j * dyadicWeight s (⌈b.radius⌉₊ + 1) *
        ‖conv (b.kernel L (j + (⌈b.radius⌉₊ + 1))) f volume x‖ₑ
      ≤ dyadicWeight s j * dyadicWeight s (⌈b.radius⌉₊ + 1) *
          (b.ballMeanConst * ballMeanDiff L j f x) := mul_le_mul' le_rfl (hx j)
    _ = _ := by ring

/-- **The local means quasi-norm by ball means**: for every order `L`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, every `s` and `f ∈ L_p`,
`‖f‖^{b,L}_{F^s_{p,q}} ≤ C (‖f‖_p + ‖(2^(js) d_j f)_j‖_{L_p(ℓ_q)})` with
`C = Rd.LocalMeansBump.diffLowerConst L s`. The levels `j ≤ r = ⌈R⌉₊` are bounded by Young's
inequality, the levels `j > r` by the ball means
(`Rd.LocalMeansBump.lqNorm_localMean_shift_le`). -/
theorem tlLocalMeansNorm_le_tlDiffNorm (L : ℕ) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) :
    b.tlLocalMeansNorm L s q f ≤ b.diffLowerConst L s * tlDiffNorm L s q f := by
  have hp1 : 1 ≤ p := Fact.out
  have hmeas := fun j => b.measurable_dyadicWeight_mul_conv_kernel L s j f
  have hhead : eLpNorm (fun x => ∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1),
      dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ) p volume ≤
        2 * eLpNorm (momentKernel b.toFun L) 1 volume *
          (∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1), dyadicWeight s j) * ‖f‖ₑ := by
    have hfun : (fun x => ∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1),
        dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ) =
        ∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1),
          fun x => dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ := by
      funext x
      rw [Finset.sum_apply]
    rw [hfun]
    refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun j _ =>
      b.eLpNorm_dyadicWeight_mul_conv_kernel_le L hp s j f).trans_eq ?_)
    rw [← Finset.sum_mul]
    ring
  have htail : eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s (j + (⌈b.radius⌉₊ + 1)) *
      ‖conv (b.kernel L (j + (⌈b.radius⌉₊ + 1))) f volume x‖ₑ)) p volume ≤
        dyadicWeight s (⌈b.radius⌉₊ + 1) * b.ballMeanConst *
          eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x)) p
            volume := by
    refine (eLpNorm_mono_eNorm_ae (measurable_lqNorm_comp
      (fun j => hmeas (j + (⌈b.radius⌉₊ + 1))) q).aestronglyMeasurable (μ := volume) (p := p)
      (g := fun x => dyadicWeight s (⌈b.radius⌉₊ + 1) * b.ballMeanConst *
        lqNorm q (fun j => dyadicWeight s j * ballMeanDiff L j f x))
      ((b.lqNorm_localMean_shift_le L hp q s f).mono fun x hx => ?_)).trans_eq ?_
    · simpa only [eNorm_eq_self] using hx
    · exact eLpNorm_const_mul_ennreal (measurable_lqNorm_ballMeanDiff L s q f).aestronglyMeasurable
  calc b.tlLocalMeansNorm L s q f
      ≤ eLpNorm (fun x => ∑ j ∈ Finset.range (⌈b.radius⌉₊ + 1),
          dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ +
          lqNorm q (fun j => dyadicWeight s (j + (⌈b.radius⌉₊ + 1)) *
            ‖conv (b.kernel L (j + (⌈b.radius⌉₊ + 1))) f volume x‖ₑ)) p volume :=
        eLpNorm_mono_eNorm (b.aemeasurable_lqNorm_conv_kernel L s q f).aestronglyMeasurable
          fun x => by
            simp only [eNorm_eq_self]
            exact ENNReal.lqNorm_le_sum_range_add_shift hq _ _
    _ ≤ _ := eLpNorm_add_le hp1
    _ ≤ _ := add_le_add hhead htail
    _ ≤ b.diffLowerConst L s * tlDiffNorm L s q f := by
        rw [diffLowerConst, tlDiffNorm, add_mul, mul_add, mul_add]
        exact add_le_add le_self_add le_add_self

end LocalMeansBump

/-- **The ball means characterisation of Triebel–Lizorkin spaces**: for `1 < p < ∞`,
`1 < q ≤ ∞`, an order `L` and `0 < s < L`, `f ∈ F^s_{p,q}` iff
`‖f‖_p + ‖(2^(js) d_j f)_j‖_{L_p(ℓ_q)} < ∞`, with the ball means of differences of order `L`.
Both quasi-norms are compared with the local means quasi-norm of the standard bump
(`Rd.LocalMeansBump.std`, `Rd.LocalMeansBump.memTriebelLizorkin_iff_tlLocalMeans`). -/
theorem memTriebelLizorkin_iff_tlDiffNorm_lt_top {p : ℝ≥0∞} [Fact (1 ≤ p)] {L : ℕ}
    (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    {f : Lp ℂ p (volume : Measure V)} :
    MemTriebelLizorkin s q f ↔ tlDiffNorm L s q f < ∞ := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 fun h => by
    rw [h, Nat.cast_zero] at hsL
    linarith
  rw [(LocalMeansBump.std (V := V)).memTriebelLizorkin_iff_tlLocalMeans hp1 hp hq1 hs hsL]
  exact ⟨fun h => ((LocalMeansBump.std (V := V)).tlDiffNorm_le_tlLocalMeansNorm hL hp1 hp hq1 s
      f).trans_lt (ENNReal.mul_lt_top
        ((LocalMeansBump.std (V := V)).diffUpperConst_ne_top hp1 hp hq1 hs hsL).lt_top h),
    fun h => ((LocalMeansBump.std (V := V)).tlLocalMeansNorm_le_tlDiffNorm L hp hq1.le s
      f).trans_lt (ENNReal.mul_lt_top
        ((LocalMeansBump.std (V := V)).diffLowerConst_ne_top L s).lt_top h)⟩

end Rd
