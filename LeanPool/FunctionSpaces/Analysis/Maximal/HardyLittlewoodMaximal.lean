/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.DyadicCubes
public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms
public import LeanPool.FunctionSpaces.Analysis.Lp.LayerCake
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Topology.Semicontinuity.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Hardy–Littlewood maximal function

For `g : V → [0, ∞]` the **Hardy–Littlewood maximal function** is
`M g(x) = sup_{r > 0} |B(0,r)|⁻¹ ∫_{B(x,r)} g` (`Rd.maximal`). It is lower semicontinuous, hence
measurable, for every `g` (`Rd.measurable_maximal`), and it controls convolutions with kernels
bounded by `A 1_{B(0,ρ)}` (`Rd.lintegral_mul_le_maximal_of_ball`), by `A min(1, (ρ/‖y‖)^N)` with
`N > n` (`Rd.lintegral_mul_le_maximal_of_decay`), or by the Peetre weight
`A 2^(jn) (1 + 2^j ‖y‖)^(-N)` (`Rd.lintegral_mul_le_maximal_of_one_add_norm`).

The **weighted weak type `(1,1)`** `∫_{M g > t} w ≤ 5^n t⁻¹ ∫ g M w` holds for all
`g, w ≥ 0` (`Rd.setLIntegral_maximal_gt_le`), by Vitali's covering lemma. With the layer cake
formula for `[0, ∞]`-valued functions
(`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal`) and the integral of `t^(p-2)`
over `(0, 2a)` (`MeasureTheory.lintegral_Ioi_indicator_half_lt_mul_rpow`), both from
`FunctionSpaces.Analysis.Lp.LayerCake`, and Tonelli's theorem
(`Rd.lintegral_Ioi_lintegral_indicator_mul_rpow`) it gives the **weighted strong type**
`∫ (M g)^p w ≤ C_{n,p} ∫ g^p M w` for `1 < p < ∞` (`Rd.lintegral_maximal_rpow_mul_le`) and the
**Hardy–Littlewood maximal theorem** `‖M g‖_p ≤ C_{n,p}^{1/p} ‖g‖_p` (`Rd.eLpNorm_maximal_le`),
with the explicit constant `C_{n,p} = p 2^p 5^n / (p - 1)` (`Rd.maximalConst`). For `p = ∞`,
`M g ≤ ‖g‖_∞` (`Rd.maximal_le_eLpNorm_top`).

Two geometric facts serve the covering arguments: the balls of radius `ρ 2^(-j)` have the volume
`ρ^n |B_1| 2^(-jn)` (`Rd.volume_ball_div_two_pow`, `Rd.volume_closedBall_div_two_pow`), and a set
in `closedBall(c, ρ)` that meets `B(x, r)` for some `x ∉ closedBall(c, 2ρ)` lies in `B(x, 3r)`
(`Metric.subset_ball_three_mul_of_inter_nonempty`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal Topology

namespace Metric

/-- If a set `Q ⊆ closedBall(c, ρ)` meets the ball `B(x, r)` around a point `x ∉ closedBall(c,
2ρ)`, then
`Q ⊆ B(x, 3r)`: a point of `Q` in the ball forces `r > ρ`, so every point of `Q` lies within
`r + 2ρ < 3r` of `x`. -/
theorem subset_ball_three_mul_of_inter_nonempty {α : Type*} [PseudoMetricSpace α] {Q : Set α}
    {c x : α} {ρ r : ℝ} (hQ : Q ⊆ closedBall c ρ) (hx : x ∉ closedBall c (2 * ρ))
    (hne : (Q ∩ ball x r).Nonempty) : Q ⊆ ball x (3 * r) := by
  obtain ⟨y, hyQ, hyB⟩ := hne
  have hy : dist y c ≤ ρ := hQ hyQ
  have hyx : dist y x < r := hyB
  have hxc : 2 * ρ < dist x c := not_le.1 hx
  have h1 : dist x c ≤ dist x y + dist y c := dist_triangle _ _ _
  rw [dist_comm x y] at h1
  intro z hz
  have hz : dist z c ≤ ρ := hQ hz
  have h2 : dist z x ≤ dist z c + dist c y + dist y x :=
    (dist_triangle z y x).trans (add_le_add_left (dist_triangle z c y) _) |>.trans_eq (by ring)
  rw [dist_comm c y] at h2
  rw [mem_ball]
  linarith

end Metric

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Definition and first properties -/

/-- The **Hardy–Littlewood maximal function** of `g : V → [0, ∞]`:
`M g(x) = sup_{r > 0} |B(0,r)|⁻¹ ∫_{B(x,r)} g`, the supremum of the means of `g` over the open
balls centred at `x`. The volume `|B(0,r)| = |B(x,r)|` of the centred ball keeps the factor
independent of `x`. -/
noncomputable def maximal (g : V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (ball (0 : V) r))⁻¹ * ∫⁻ y in ball x r, g y

/-- The ball `B(0,r)` of radius `r > 0` has positive volume. -/
theorem volume_ball_ne_zero {r : ℝ} (hr : 0 < r) : volume (ball (0 : V) r) ≠ 0 :=
  (measure_ball_pos volume (0 : V) hr).ne'

/-- The ball `B(0,r)` has finite volume. -/
theorem volume_ball_ne_top (r : ℝ) : volume (ball (0 : V) r) ≠ ∞ :=
  measure_ball_lt_top.ne

/-- **Volumes of dyadic balls**: a ball of radius `ρ 2^(-j)`, `ρ > 0`, around any centre has
volume `ρ^n |B_1| 2^(-jn)`, where `|B_1|` is the volume of the unit ball. -/
theorem volume_ball_div_two_pow {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) (z : V) :
    volume (ball z (ρ / 2 ^ j)) = ENNReal.ofReal (ρ ^ finrank ℝ V) *
      volume (ball (0 : V) 1) * ENNReal.dyadicWeight (-(finrank ℝ V : ℝ)) j := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), div_eq_mul_one_div, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_one_div_two_pow_pow]
  ring

/-- The volume of the closed ball of radius `d 2^(-j)` is `d^n |B_1| 2^(-jn)` for `d ≥ 0`. -/
theorem volume_closedBall_div_two_pow {d : ℝ} (hd : 0 ≤ d) (j : ℕ) (z : V) :
    volume (closedBall z (d / 2 ^ j)) = ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1) * ENNReal.dyadicWeight (-(finrank ℝ V : ℝ)) j := by
  rw [Measure.addHaar_closedBall _ _ (by positivity), div_eq_mul_one_div, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_one_div_two_pow_pow]
  ring

/-- Every mean over a ball centred at `x` is at most `M g(x)`. -/
theorem le_maximal {r : ℝ} (hr : 0 < r) (g : V → ℝ≥0∞) (x : V) :
    (volume (ball (0 : V) r))⁻¹ * ∫⁻ y in ball x r, g y ≤ maximal g x :=
  le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) =>
    (volume (ball (0 : V) r))⁻¹ * ∫⁻ y in ball x r, g y) r hr

/-- `∫_{B(x,r)} g ≤ |B(0,r)| M g(x)` for every `g : V → [0, ∞]` and every `r > 0`. -/
theorem setLIntegral_ball_le_mul_maximal {r : ℝ} (hr : 0 < r) (g : V → ℝ≥0∞) (x : V) :
    ∫⁻ y in ball x r, g y ≤ volume (ball (0 : V) r) * maximal g x :=
  (ENNReal.inv_mul_le_iff (volume_ball_ne_zero hr) (volume_ball_ne_top r)).1 (le_maximal hr g x)

/-- `M g(x) ≤ c` as soon as `∫_{B(x,r)} g ≤ |B(0,r)| c` for every `r > 0`. -/
theorem maximal_le_of_forall {g : V → ℝ≥0∞} {x : V} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, 0 < r → ∫⁻ y in ball x r, g y ≤ volume (ball (0 : V) r) * c) :
    maximal g x ≤ c :=
  iSup₂_le fun r hr =>
    (ENNReal.inv_mul_le_iff (volume_ball_ne_zero hr) (volume_ball_ne_top r)).2 (h r hr)

/-- The maximal function is **monotone**: `g ≤ h` implies `M g ≤ M h`. -/
theorem maximal_mono {g h : V → ℝ≥0∞} (hgh : g ≤ h) : maximal g ≤ maximal h := fun x =>
  iSup₂_mono fun _ _ => by gcongr with y; exact hgh y

/-- The maximal function is **subadditive**: `M (g + h) ≤ M g + M h`. One summand has to be
measurable, since the lower Lebesgue integral of a sum of two non-measurable functions can exceed
the sum of their integrals. -/
theorem maximal_add_le {g : V → ℝ≥0∞} (hg : AEMeasurable g volume) (h : V → ℝ≥0∞) (x : V) :
    maximal (g + h) x ≤ maximal g x + maximal h x := by
  refine maximal_le_of_forall fun r hr => ?_
  rw [mul_add]
  calc ∫⁻ y in ball x r, (g + h) y
      = (∫⁻ y in ball x r, g y) + ∫⁻ y in ball x r, h y :=
        lintegral_add_left' hg.restrict h
    _ ≤ _ := add_le_add (setLIntegral_ball_le_mul_maximal hr g x)
        (setLIntegral_ball_le_mul_maximal hr h x)

/-- The maximal function is **homogeneous**: `M (c g) = c M g` for a finite constant `c`. -/
theorem maximal_const_mul {c : ℝ≥0∞} (hc : c ≠ ∞) (g : V → ℝ≥0∞) (x : V) :
    maximal (fun y => c * g y) x = c * maximal g x := by
  simp only [maximal, lintegral_const_mul' c _ hc, ENNReal.mul_iSup]
  simp_rw [mul_left_comm c]

/-- If `g ≤ c` almost everywhere, then `M g ≤ c` everywhere. -/
theorem maximal_le_of_ae_le {g : V → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ᵐ y ∂volume, g y ≤ c) (x : V) :
    maximal g x ≤ c := by
  refine maximal_le_of_forall fun r _ => ?_
  calc ∫⁻ y in ball x r, g y ≤ ∫⁻ _ in ball x r, c := lintegral_mono_ae (ae_restrict_of_ae h)
    _ = volume (ball (0 : V) r) * c := by
      rw [setLIntegral_const, Measure.addHaar_ball_center, mul_comm]

/-- The maximal function of a **constant** is that constant. -/
theorem maximal_const (c : ℝ≥0∞) : maximal (fun _ : V => c) = fun _ => c := by
  funext x
  refine le_antisymm (maximal_le_of_ae_le (ae_of_all _ fun _ => le_rfl) x) ?_
  calc c = (volume (ball (0 : V) 1))⁻¹ * ∫⁻ _ in ball x 1, c := by
        rw [setLIntegral_const, Measure.addHaar_ball_center volume x, mul_comm c, ← mul_assoc,
          ENNReal.inv_mul_cancel (volume_ball_ne_zero one_pos) (volume_ball_ne_top 1), one_mul]
    _ ≤ maximal (fun _ => c) x := le_maximal one_pos _ x

/-- Functions that agree almost everywhere have the **same maximal function**. -/
theorem maximal_congr_ae {g h : V → ℝ≥0∞} (hgh : g =ᵐ[volume] h) : maximal g = maximal h := by
  funext x
  simp only [maximal, lintegral_congr_ae (ae_restrict_of_ae hgh)]

/-- Restricting `g` to a set decreases its maximal function: `M (1_s g) ≤ M g`. -/
theorem maximal_indicator_le (s : Set V) (g : V → ℝ≥0∞) : maximal (s.indicator g) ≤ maximal g :=
  maximal_mono (Set.indicator_le_self s g)

/-- **Monotone convergence** for the maximal function: for an increasing sequence of almost
everywhere measurable `g_N`, `M (sup_N g_N) = sup_N M g_N`. -/
theorem maximal_iSup_of_monotone {g : ℕ → V → ℝ≥0∞} (hg : ∀ N, AEMeasurable (g N) volume)
    (hmono : Monotone g) : maximal (⨆ N, g N) = ⨆ N, maximal (g N) := by
  funext x
  simp only [maximal, iSup_apply]
  rw [iSup_comm]
  refine iSup_congr fun r => ?_
  rw [iSup_comm]
  refine iSup_congr fun _ => ?_
  rw [lintegral_iSup' (fun N => (hg N).restrict)
    (ae_of_all _ fun y _ _ hab => hmono hab y), ENNReal.mul_iSup]

/-- On a space with one point (`n = 0`) every function is its own maximal function: every ball
of positive radius is the whole space, of positive finite volume. -/
theorem maximal_eq_self_of_subsingleton [Subsingleton V] (g : V → ℝ≥0∞) : maximal g = g := by
  funext x
  have hball : ∀ r : ℝ, 0 < r → ∀ z : V, ball z r = univ := fun r hr z =>
    Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y z]; exact mem_ball_self hr
  have hg : g = fun _ => g x := funext fun y => by rw [Subsingleton.elim y x]
  have hterm : ∀ r : ℝ, 0 < r →
      (volume (ball (0 : V) r))⁻¹ * ∫⁻ y in ball x r, g y = g x := fun r hr => by
    rw [hg, setLIntegral_const, hball r hr x, ← hball r hr 0, mul_comm (g x), ← mul_assoc,
      ENNReal.inv_mul_cancel (volume_ball_ne_zero hr) (volume_ball_ne_top r), one_mul]
  refine le_antisymm (iSup₂_le fun r hr => (hterm r hr).le) ?_
  exact (hterm 1 one_pos).ge.trans (le_maximal one_pos g x)

/-! ### Measurability by lower semicontinuity -/

/-- For every `g : V → [0, ∞]` and every radius `r`, `x ↦ ∫_{B(x,r)} g` is **lower
semicontinuous**: the ball `B(x₀, r)` is the increasing union of the balls `B(x₀, r - 1/(m+1))`,
and each of them lies in `B(x, r)` for all `x` close to `x₀`. -/
theorem lowerSemicontinuous_setLIntegral_ball (g : V → ℝ≥0∞) (r : ℝ) :
    LowerSemicontinuous fun x => ∫⁻ y in ball x r, g y := by
  intro x₀ a ha
  dsimp only at ha ⊢
  have hU : ball x₀ r = ⋃ m : ℕ, ball x₀ (r - 1 / ((m : ℝ) + 1)) := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.iUnion_subset fun m =>
      ball_subset_ball (by have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
                           linarith))
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_ball.1 hy))
    exact Set.mem_iUnion.2 ⟨m, mem_ball.2 (by linarith)⟩
  have hmono : Monotone fun m : ℕ => ball x₀ (r - 1 / ((m : ℝ) + 1)) := fun m m' hmm' =>
    ball_subset_ball (by gcongr)
  rw [hU, setLIntegral_iUnion_of_directed g hmono.directed_le] at ha
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 ha
  refine Filter.eventually_of_mem (ball_mem_nhds x₀ (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)))
    fun x hx => hm.trans_le (lintegral_mono_set (ball_subset_ball' ?_))
  rw [dist_comm]
  linarith [mem_ball.1 hx]

/-- The maximal function of every `g : V → [0, ∞]` is **lower semicontinuous**, as a supremum of
the lower semicontinuous functions `x ↦ |B(0,r)|⁻¹ ∫_{B(x,r)} g`. -/
theorem lowerSemicontinuous_maximal (g : V → ℝ≥0∞) : LowerSemicontinuous (maximal g) :=
  lowerSemicontinuous_biSup fun r hr =>
    Continuous.comp_lowerSemicontinuous
      (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 (volume_ball_ne_zero hr)))
      (lowerSemicontinuous_setLIntegral_ball g r) fun _ _ h => mul_le_mul_right h _

/-- The maximal function of every `g : V → [0, ∞]` is **measurable**. -/
theorem measurable_maximal (g : V → ℝ≥0∞) : Measurable (maximal g) :=
  (lowerSemicontinuous_maximal g).measurable

/-! ### Kernels with radial majorants -/

/-- **Kernels bounded by a ball, before the maximal function**: if `0 ≤ K ≤ A 1_{B(0,ρ)}`
with `A < ∞`, then `∫ K(y) g(x - y) dy ≤ A ∫_{B(x,ρ)} g` for every `g : V → [0, ∞]`, by the
translation invariance of the Lebesgue measure. -/
theorem lintegral_mul_le_setLIntegral_ball {K : V → ℝ≥0∞} {A : ℝ≥0∞} {ρ : ℝ} (hA : A ≠ ∞)
    (hK : ∀ y, K y ≤ A * (ball (0 : V) ρ).indicator 1 y) (g : V → ℝ≥0∞) (x : V) :
    ∫⁻ y, K y * g (x - y) ≤ A * ∫⁻ y in ball x ρ, g y := by
  have hpt : ∀ y, K y * g (x - y) ≤ A * (ball x ρ).indicator g (x - y) := fun y => by
    by_cases hy : y ∈ ball (0 : V) ρ
    · have hxy : x - y ∈ ball x ρ := by
        rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg]; exact mem_ball_zero_iff.1 hy
      rw [Set.indicator_of_mem hxy]
      have := hK y
      rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one] at this
      gcongr
    · have := hK y
      rw [Set.indicator_of_notMem hy, mul_zero, nonpos_iff_eq_zero] at this
      simp [this]
  calc ∫⁻ y, K y * g (x - y) ≤ ∫⁻ y, A * (ball x ρ).indicator g (x - y) := lintegral_mono hpt
    _ = A * ∫⁻ y in ball x ρ, g y := by
      rw [lintegral_const_mul' A _ hA,
        lintegral_sub_left_eq_self (fun z => (ball x ρ).indicator g z) x,
        lintegral_indicator measurableSet_ball]

/-- **Kernels bounded by a ball.** If `0 ≤ K ≤ A 1_{B(0,ρ)}`, then
`∫ K(y) g(x - y) dy ≤ A |B(0,ρ)| M g(x)` for every `g : V → [0, ∞]` and every kernel `K`
(`Rd.lintegral_mul_le_setLIntegral_ball` and the definition of `M g`). -/
theorem lintegral_mul_le_maximal_of_ball {K : V → ℝ≥0∞} {A : ℝ≥0∞} {ρ : ℝ} (hA : A ≠ ∞)
    (hK : ∀ y, K y ≤ A * (ball (0 : V) ρ).indicator 1 y) (hρ : 0 < ρ) (g : V → ℝ≥0∞) (x : V) :
    ∫⁻ y, K y * g (x - y) ≤ A * volume (ball (0 : V) ρ) * maximal g x :=
  (lintegral_mul_le_setLIntegral_ball hA hK g x).trans (by
    rw [mul_assoc]; gcongr; exact setLIntegral_ball_le_mul_maximal hρ g x)

/-- The dyadic **shell** `{y : ‖y‖ < 2^(i+1) ρ}` for `i = 0` and
`{y : 2^i ρ ≤ ‖y‖ < 2^(i+1) ρ}` for `i ≥ 1`. -/
def dyadicShell (ρ : ℝ) (i : ℕ) : Set V :=
  {y | ‖y‖ < 2 ^ (i + 1) * ρ ∧ (i = 0 ∨ 2 ^ i * ρ ≤ ‖y‖)}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The shells are measurable. -/
theorem measurableSet_dyadicShell (ρ : ℝ) (i : ℕ) :
    MeasurableSet (dyadicShell (V := V) ρ i) := by
  rw [dyadicShell, ofPred_and, ofPred_or]
  exact (measurableSet_lt measurable_norm measurable_const).inter
    ((MeasurableSet.const _).union (measurableSet_le measurable_const measurable_norm))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The shells **cover** `V`: a point with `‖y‖ ≥ ρ` lies in the shell `i` with
`2^i ≤ ‖y‖/ρ < 2^(i+1)`. -/
theorem iUnion_dyadicShell {ρ : ℝ} (hρ : 0 < ρ) : ⋃ i, dyadicShell (V := V) ρ i = univ := by
  refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ?_
  by_cases hy : ‖y‖ < ρ
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [zero_add, pow_one]
    linarith
  · obtain ⟨i, hi1, hi2⟩ := exists_nat_pow_near ((one_le_div hρ).2 (not_lt.1 hy))
      (one_lt_two : (1 : ℝ) < 2)
    exact ⟨i, (div_lt_iff₀ hρ).1 hi2, Or.inr ((le_div_iff₀ hρ).1 hi1)⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A kernel with the bound `A` on `closedBall(0,ρ)` and the bound `A (ρ/‖y‖)^N` outside is at most
`A 2^(-iN)` on the shell `i`. -/
theorem kernel_le_of_mem_dyadicShell {K : V → ℝ≥0∞} {A : ℝ≥0∞} {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hK₁ : ∀ y, ‖y‖ ≤ ρ → K y ≤ A)
    (hK₂ : ∀ y, ρ < ‖y‖ → K y ≤ A * ENNReal.ofReal ((ρ / ‖y‖) ^ N)) {i : ℕ} {y : V}
    (hy : y ∈ dyadicShell ρ i) : K y ≤ A * 2⁻¹ ^ (i * N) := by
  rcases le_or_gt ‖y‖ ρ with h | h
  · have hi : i = 0 := by
      rcases hy.2 with hi | hi
      · exact hi
      · by_contra hne
        have : (2 : ℝ) ≤ 2 ^ i := le_self_pow₀ one_le_two hne
        nlinarith
    simpa [hi] using hK₁ y h
  · refine (hK₂ y h).trans (mul_le_mul_right ?_ A)
    have hpow : (2⁻¹ : ℝ≥0∞) ^ (i * N) = ENNReal.ofReal (((2 : ℝ) ^ i)⁻¹ ^ N) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.inv_pow, ← pow_mul]
    rw [hpow]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ N)
    have hy0 : 0 < ‖y‖ := hρ.trans h
    rw [div_le_iff₀ hy0]
    rcases hy.2 with hi | hi
    · subst hi; simpa using h.le
    · calc ρ = ((2 : ℝ) ^ i)⁻¹ * (2 ^ i * ρ) := by field_simp
        _ ≤ ((2 : ℝ) ^ i)⁻¹ * ‖y‖ := by gcongr

/-- `|B(0, 2^(i+1) ρ)| = 2^((i+1) n) |B(0,ρ)|`. -/
theorem volume_ball_two_pow_mul (i : ℕ) {ρ : ℝ} :
    volume (ball (0 : V) (2 ^ (i + 1) * ρ)) =
      2 ^ ((i + 1) * finrank ℝ V) * volume (ball (0 : V) ρ) := by
  rw [Measure.addHaar_ball_mul_of_pos volume 0 (by positivity), ← pow_mul,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- The geometric sum `∑_i 2^(-iN) 2^((i+1)n) = 2^n (1 - 2^(-(N-n)))⁻¹` for `n ≤ N`. -/
theorem tsum_two_inv_pow_mul_two_pow {n N : ℕ} (hN : n ≤ N) :
    ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i * N) * 2 ^ ((i + 1) * n) = 2 ^ n * (1 - 2⁻¹ ^ (N - n))⁻¹ := by
  have hterm : ∀ i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i * N) * 2 ^ ((i + 1) * n) = 2 ^ n * (2⁻¹ ^ (N - n)) ^ i :=
    fun i => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h2 : (2⁻¹ : ℝ≥0∞) ^ (i * n) * 2 ^ (i * n) = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    rw [Nat.add_sub_cancel_left, mul_add, pow_add, add_mul, one_mul, pow_add, ← pow_mul,
      mul_comm k i]
    calc (2⁻¹ : ℝ≥0∞) ^ (i * n) * 2⁻¹ ^ (i * k) * (2 ^ (i * n) * 2 ^ n)
        = ((2⁻¹ : ℝ≥0∞) ^ (i * n) * 2 ^ (i * n)) * (2 ^ n * 2⁻¹ ^ (i * k)) := by ring
      _ = 2 ^ n * 2⁻¹ ^ (i * k) := by rw [h2, one_mul]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **Kernels with a power tail.** If `K ≤ A` on `closedBall(0,ρ)` and `K(y) ≤ A (ρ/‖y‖)^N`
outside, with
`N > n`, then `∫ K(y) g(x - y) dy ≤ A |B(0,ρ)| 2^n (1 - 2^(-(N-n)))⁻¹ M g(x)` for every
`g : V → [0, ∞]`. The proof covers `V` by the ball `B(0,2ρ)` and the dyadic shells
`2^i ρ ≤ ‖y‖ < 2^(i+1) ρ`, `i ≥ 1`, applies the ball bound on each, and sums a geometric
series. -/
theorem lintegral_mul_le_maximal_of_decay {K : V → ℝ≥0∞} {A : ℝ≥0∞} {ρ : ℝ} {N : ℕ}
    (hN : finrank ℝ V < N) (hA : A ≠ ∞) (hK₁ : ∀ y, ‖y‖ ≤ ρ → K y ≤ A)
    (hK₂ : ∀ y, ρ < ‖y‖ → K y ≤ A * ENNReal.ofReal ((ρ / ‖y‖) ^ N)) (hρ : 0 < ρ)
    (g : V → ℝ≥0∞) (x : V) :
    ∫⁻ y, K y * g (x - y) ≤
      A * volume (ball (0 : V) ρ) * 2 ^ finrank ℝ V * (1 - 2⁻¹ ^ (N - finrank ℝ V))⁻¹ *
        maximal g x := by
  have hshell : ∀ i : ℕ, ∫⁻ y in dyadicShell ρ i, K y * g (x - y) ≤
      A * volume (ball (0 : V) ρ) * maximal g x * (2⁻¹ ^ (i * N) * 2 ^ ((i + 1) * finrank ℝ V)) :=
      fun i => by
    rw [← lintegral_indicator (measurableSet_dyadicShell ρ i)]
    have hAi : A * 2⁻¹ ^ (i * N) ≠ ∞ :=
      ENNReal.mul_ne_top hA (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
    calc ∫⁻ y, (dyadicShell ρ i).indicator (fun y => K y * g (x - y)) y
        = ∫⁻ y, (dyadicShell ρ i).indicator K y * g (x - y) := by
          congr 1; funext y
          by_cases hy : y ∈ dyadicShell ρ i
          · simp [Set.indicator_of_mem hy]
          · simp [Set.indicator_of_notMem hy]
      _ ≤ A * 2⁻¹ ^ (i * N) * volume (ball (0 : V) (2 ^ (i + 1) * ρ)) * maximal g x := by
          refine lintegral_mul_le_maximal_of_ball hAi (fun y => ?_) (by positivity) g x
          by_cases hy : y ∈ dyadicShell ρ i
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (mem_ball_zero_iff.2 hy.1),
              Pi.one_apply, mul_one]
            exact kernel_le_of_mem_dyadicShell hρ hK₁ hK₂ hy
          · simp [Set.indicator_of_notMem hy]
      _ = _ := by rw [volume_ball_two_pow_mul]; ring
  calc ∫⁻ y, K y * g (x - y) = ∫⁻ y in ⋃ i, dyadicShell ρ i, K y * g (x - y) := by
        rw [iUnion_dyadicShell hρ, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ y in dyadicShell ρ i, K y * g (x - y) := lintegral_iUnion_le _ _
    _ ≤ ∑' i : ℕ, A * volume (ball (0 : V) ρ) * maximal g x *
          (2⁻¹ ^ (i * N) * 2 ^ ((i + 1) * finrank ℝ V)) := tsum_le_tsum hshell
    _ = _ := by rw [ENNReal.tsum_mul_left, tsum_two_inv_pow_mul_two_pow hN.le]; ring

variable (V) in
/-- The constant `|B(0,1)| 2^n (1 - 2^(-(N-n)))⁻¹` of the maximal function bound for kernels
with the decay `2^(jn) (1 + 2^j ‖y‖)^(-N)`. -/
noncomputable def decayMaximalConst (N : ℕ) : ℝ≥0∞ :=
  volume (ball (0 : V) 1) * 2 ^ finrank ℝ V * (1 - 2⁻¹ ^ (N - finrank ℝ V))⁻¹

/-- `decayMaximalConst V N` is finite for `N > n`. -/
theorem decayMaximalConst_ne_top {N : ℕ} (hN : finrank ℝ V < N) : decayMaximalConst V N ≠ ∞ := by
  have hlt : (2⁻¹ : ℝ≥0∞) ^ (N - finrank ℝ V) < 1 :=
    pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) (Nat.sub_ne_zero_of_lt hN)
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (volume_ball_ne_top 1)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) (ENNReal.inv_ne_top.2 ?_)
  exact (tsub_pos_iff_lt.2 hlt).ne'

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The tail bound of the Peetre weight: for every `y ≠ 0`,
`(1 + 2^j ‖y‖)^(-N) ≤ (2^(-j)/‖y‖)^N`. -/
theorem inv_one_add_two_pow_mul_pow_le {j N : ℕ} {y : V} (hy0 : 0 < ‖y‖) :
    ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹ ≤ ENNReal.ofReal ((((2 : ℝ) ^ j)⁻¹ / ‖y‖) ^ N) := by
  have h : (((2 : ℝ) ^ j)⁻¹ / ‖y‖) ^ N = ((2 ^ j * ‖y‖) ^ N)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_inv, inv_pow]
  rw [h, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
    ofReal_norm]
  gcongr
  exact le_add_self

/-- **Kernels with Peetre decay.** If `K(y) ≤ A 2^(jn) (1 + 2^j ‖y‖)^(-N)` with `N > n`, then
`∫ K(y) g(x - y) dy ≤ C_{n,N} A M g(x)` for every `g : V → [0, ∞]`, with the constant
`C_{n,N} = decayMaximalConst V N` independent of the level `j`. -/
theorem lintegral_mul_le_maximal_of_one_add_norm {K : V → ℝ≥0∞} {A : ℝ≥0∞} {j N : ℕ}
    (hN : finrank ℝ V < N) (hA : A ≠ ∞)
    (hK : ∀ y, K y ≤ A * 2 ^ (j * finrank ℝ V) * ((1 + 2 ^ j * ‖y‖ₑ) ^ N)⁻¹)
    (g : V → ℝ≥0∞) (x : V) :
    ∫⁻ y, K y * g (x - y) ≤ decayMaximalConst V N * A * maximal g x := by
  have hA' : A * 2 ^ (j * finrank ℝ V) ≠ ∞ :=
    ENNReal.mul_ne_top hA (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hρ : (0 : ℝ) < ((2 : ℝ) ^ j)⁻¹ := by positivity
  have h := lintegral_mul_le_maximal_of_decay hN hA'
    (fun y _ => (hK y).trans (mul_le_of_le_one_right zero_le
      (ENNReal.inv_le_one.2 (one_le_pow₀ le_self_add))))
    (fun y hy => (hK y).trans
      (mul_le_mul_right (inv_one_add_two_pow_mul_pow_le (hρ.trans hy)) _)) hρ g x
  refine h.trans (le_of_eq ?_)
  have hvol : volume (ball (0 : V) ((2 : ℝ) ^ j)⁻¹) =
      (2 ^ (j * finrank ℝ V))⁻¹ * volume (ball (0 : V) 1) := by
    rw [Measure.addHaar_ball_of_pos volume 0 hρ, ENNReal.ofReal_pow hρ.le,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, ENNReal.inv_pow, ENNReal.inv_pow, ← pow_mul]
  have hc : (2 : ℝ≥0∞) ^ (j * finrank ℝ V) * (2 ^ (j * finrank ℝ V))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  rw [hvol, decayMaximalConst]
  calc A * 2 ^ (j * finrank ℝ V) * ((2 ^ (j * finrank ℝ V))⁻¹ * volume (ball (0 : V) 1)) *
        2 ^ finrank ℝ V * (1 - 2⁻¹ ^ (N - finrank ℝ V))⁻¹ * maximal g x
      = (2 ^ (j * finrank ℝ V) * (2 ^ (j * finrank ℝ V))⁻¹) * (volume (ball (0 : V) 1) *
        2 ^ finrank ℝ V * (1 - 2⁻¹ ^ (N - finrank ℝ V))⁻¹ * A * maximal g x) := by ring
    _ = _ := by rw [hc, one_mul]

/-! ### The weighted weak type `(1,1)` -/

/-- For `y ∈ B(b,r)`: `∫_{closedBall(b,4r)} w ≤ 5^n |B(0,r)| M w(y)`, since `closedBall(b,4r) ⊆
B(y,5r)` and
`|B(0,5r)| = 5^n |B(0,r)|`. -/
theorem setLIntegral_closedBall_le_maximal {r : ℝ} (hr : 0 < r) (w : V → ℝ≥0∞) {b y : V}
    (hy : y ∈ ball b r) :
    ∫⁻ z in closedBall b (4 * r), w z ≤
      5 ^ finrank ℝ V * volume (ball (0 : V) r) * maximal w y := by
  have hsub : closedBall b (4 * r) ⊆ ball y (5 * r) := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball] at hy ⊢
    calc dist z y ≤ dist z b + dist b y := dist_triangle _ _ _
      _ < 4 * r + r := by rw [dist_comm b y]; linarith
      _ = 5 * r := by ring
  calc ∫⁻ z in closedBall b (4 * r), w z ≤ ∫⁻ z in ball y (5 * r), w z := lintegral_mono_set hsub
    _ ≤ volume (ball (0 : V) (5 * r)) * maximal w y :=
      setLIntegral_ball_le_mul_maximal (by positivity) w y
    _ = _ := by
      rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) (by norm_num : (0 : ℝ) < 5),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **One ball of the Vitali cover.** If `t |B(0,r)| ≤ ∫_{B(b,r)} g`, then
`t ∫_{closedBall(b,4r)} w ≤ 5^n ∫_{B(b,r)} g M w`: the mass of `w` on the enlarged ball is
spread over
`B(b,r)` with the weight `g`, at the price of `M w`. -/
theorem mul_setLIntegral_closedBall_le {r : ℝ} (hr : 0 < r) {g : V → ℝ≥0∞} (w : V → ℝ≥0∞)
    {b : V} {t : ℝ≥0∞} (hI : t * volume (ball (0 : V) r) ≤ ∫⁻ y in ball b r, g y) :
    t * ∫⁻ z in closedBall b (4 * r), w z ≤
      5 ^ finrank ℝ V * ∫⁻ y in ball b r, g y * maximal w y := by
  have hc : (5 : ℝ≥0∞) ^ finrank ℝ V * volume (ball (0 : V) r) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (volume_ball_ne_top r)
  refine (ENNReal.mul_le_mul_iff_left (volume_ball_ne_zero (V := V) hr) (volume_ball_ne_top r)).1 ?_
  calc t * (∫⁻ z in closedBall b (4 * r), w z) * volume (ball (0 : V) r)
      = (∫⁻ z in closedBall b (4 * r), w z) * (t * volume (ball (0 : V) r)) := by ring
    _ ≤ (∫⁻ z in closedBall b (4 * r), w z) * ∫⁻ y in ball b r, g y := by gcongr
    _ = (∫⁻ y in ball b r, g y) * ∫⁻ z in closedBall b (4 * r), w z := mul_comm _ _
    _ ≤ ∫⁻ y in ball b r, g y * ∫⁻ z in closedBall b (4 * r), w z := lintegral_mul_const_le _ _
    _ ≤ ∫⁻ y in ball b r, g y * (5 ^ finrank ℝ V * volume (ball (0 : V) r) * maximal w y) :=
      setLIntegral_mono' measurableSet_ball fun y hy => by
        gcongr; exact setLIntegral_closedBall_le_maximal hr w hy
    _ = 5 ^ finrank ℝ V * volume (ball (0 : V) r) * ∫⁻ y in ball b r, g y * maximal w y := by
      rw [← lintegral_const_mul' _ _ hc]; congr 1; funext y; ring
    _ = _ := by ring

/-- The points `x` for which the integral of `g` over some ball `B(x,r)` with `0 < r ≤ R` exceeds
`t |B(0,r)|`. These sets exhaust `{M g > t}` as `R → ∞`. -/
def bigBallSet (g : V → ℝ≥0∞) (t : ℝ≥0∞) (R : ℝ) : Set V :=
  {x | ∃ r, 0 < r ∧ r ≤ R ∧ t * volume (ball (0 : V) r) < ∫⁻ y in ball x r, g y}

/-- The sets `bigBallSet g t R` increase with `R`. -/
theorem bigBallSet_mono (g : V → ℝ≥0∞) (t : ℝ≥0∞) : Monotone (bigBallSet g t) :=
  fun _ _ hRR' _ ⟨r, hr0, hrR, hrI⟩ => ⟨r, hr0, hrR.trans hRR', hrI⟩

/-- The level set `{M g > t}` lies in the union of the sets `bigBallSet g t N`, `N ∈ ℕ`. -/
theorem setOf_lt_maximal_subset (g : V → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < maximal g x} ⊆ ⋃ N : ℕ, bigBallSet g t N := fun x hx => by
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 (show t < maximal g x from hx)
  obtain ⟨hr0, hlt⟩ := lt_iSup_iff.1 hr
  rw [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl (volume_ball_ne_zero hr0))
    (Or.inl (volume_ball_ne_top r))] at hlt
  exact Set.mem_iUnion.2 ⟨⌈r⌉₊, r, hr0, Nat.le_ceil r, hlt⟩

/-- **Vitali step.** `t ∫_{E_R} w ≤ 5^n ∫ g M w` for the set `E_R = bigBallSet g t R`: Vitali's
covering lemma selects countably many disjoint balls `B(b, r_b)` from the balls that define
`E_R` such that the balls `closedBall(b, 4 r_b)` cover `E_R`, and each of them is estimated by
`Rd.mul_setLIntegral_closedBall_le`. -/
theorem mul_setLIntegral_bigBallSet_le (g w : V → ℝ≥0∞) (t : ℝ≥0∞) (R : ℝ) :
    t * ∫⁻ x in bigBallSet g t R, w x ≤ 5 ^ finrank ℝ V * ∫⁻ x, g x * maximal w x := by
  have hex : ∀ x ∈ bigBallSet g t R, ∃ r, 0 < r ∧ r ≤ R ∧
      t * volume (ball (0 : V) r) < ∫⁻ y in ball x r, g y := fun x hx => hx
  choose! r hr0 hrR hrI using hex
  obtain ⟨u, hus, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (bigBallSet g t R) id r R hrR 4 (by norm_num)
  have hdisj' : u.PairwiseDisjoint fun b => ball b (r b) :=
    hdisj.mono fun b => ball_subset_closedBall
  have hu : u.Countable := hdisj'.countable_of_isOpen (fun _ _ => isOpen_ball)
    fun b hb => nonempty_ball.2 (hr0 b (hus hb))
  have := hu.to_subtype
  have hcover : bigBallSet g t R ⊆ ⋃ b : u, closedBall (b : V) (4 * r b) := fun a ha => by
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 a ha).le)⟩
  have hball : ∫⁻ x in ⋃ b : u, ball (b : V) (r b), g x * maximal w x =
      ∑' b : u, ∫⁻ x in ball (b : V) (r b), g x * maximal w x :=
    lintegral_iUnion (fun _ => measurableSet_ball) (hdisj'.subtype _ _) _
  calc t * ∫⁻ x in bigBallSet g t R, w x
      ≤ t * ∫⁻ x in ⋃ b : u, closedBall (b : V) (4 * r b), w x :=
        mul_le_mul_right (lintegral_mono_set hcover) t
    _ ≤ t * ∑' b : u, ∫⁻ x in closedBall (b : V) (4 * r b), w x :=
        mul_le_mul_right (lintegral_iUnion_le _ _) t
    _ = ∑' b : u, t * ∫⁻ x in closedBall (b : V) (4 * r b), w x := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, 5 ^ finrank ℝ V * ∫⁻ x in ball (b : V) (r b), g x * maximal w x :=
        tsum_le_tsum fun b =>
          mul_setLIntegral_closedBall_le (hr0 b (hus b.2)) w (hrI b (hus b.2)).le
    _ = 5 ^ finrank ℝ V * ∫⁻ x in ⋃ b : u, ball (b : V) (r b), g x * maximal w x := by
        rw [hball, ENNReal.tsum_mul_left]
    _ ≤ 5 ^ finrank ℝ V * ∫⁻ x, g x * maximal w x :=
        mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **Weighted weak type `(1,1)` of the maximal function** (Fefferman–Stein): for all
`g, w : V → [0, ∞]` and `t > 0`, `∫_{M g > t} w ≤ 5^n t⁻¹ ∫ g M w`. The level set is exhausted
by the sets `Rd.bigBallSet`, whose radii are bounded, and Vitali's covering lemma applies to each
of them. -/
theorem setLIntegral_maximal_gt_le (g w : V → ℝ≥0∞) {t : ℝ≥0∞} (ht0 : 0 < t) :
    ∫⁻ x in {x | t < maximal g x}, w x ≤
      5 ^ finrank ℝ V * t⁻¹ * ∫⁻ x, g x * maximal w x := by
  rcases eq_or_ne t ∞ with rfl | ht
  · simp
  have hmono : Monotone fun N : ℕ => bigBallSet g t N :=
    (bigBallSet_mono g t).comp Nat.mono_cast
  have hle : t * ∫⁻ x in {x | t < maximal g x}, w x ≤
      5 ^ finrank ℝ V * ∫⁻ x, g x * maximal w x := by
    calc t * ∫⁻ x in {x | t < maximal g x}, w x
        ≤ t * ∫⁻ x in ⋃ N : ℕ, bigBallSet g t N, w x :=
          mul_le_mul_right (lintegral_mono_set (setOf_lt_maximal_subset g t)) t
      _ = ⨆ N : ℕ, t * ∫⁻ x in bigBallSet g t N, w x := by
          rw [setLIntegral_iUnion_of_directed w hmono.directed_le, ENNReal.mul_iSup]
      _ ≤ _ := iSup_le fun N => mul_setLIntegral_bigBallSet_le g w t N
  rw [ENNReal.mul_le_iff_le_inv ht0.ne' ht] at hle
  calc _ ≤ t⁻¹ * (5 ^ finrank ℝ V * ∫⁻ x, g x * maximal w x) := hle
    _ = _ := by ring

/-- **Weak type `(1,1)` of the maximal function**: `|{M g > t}| ≤ 5^n t⁻¹ ∫ g` for every
`g : V → [0, ∞]` and `t > 0` (the weight `w = 1`). -/
theorem volume_maximal_gt_le (g : V → ℝ≥0∞) {t : ℝ≥0∞} (ht0 : 0 < t) :
    volume {x | t < maximal g x} ≤ 5 ^ finrank ℝ V * t⁻¹ * ∫⁻ x, g x := by
  have h := setLIntegral_maximal_gt_le g (fun _ => 1) ht0
  rw [maximal_const] at h
  simpa only [setLIntegral_one, mul_one] using h

/-! ### The weighted strong type -/

/-- The constant `C_{n,p} = p 2^p 5^n / (p - 1)` of the strong type bound
`∫ (M g)^p w ≤ C_{n,p} ∫ g^p M w`. -/
noncomputable def maximalConst (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal p * 2 ^ p * 5 ^ n * (ENNReal.ofReal (p - 1))⁻¹

/-- `maximalConst n p` is finite for `p > 1`. -/
theorem maximalConst_ne_top {n : ℕ} {p : ℝ} (hp : 1 < p) : maximalConst n p ≠ ∞ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) ?_
  · exact ENNReal.two_rpow_ne_top _
  · exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne'

/-- **Cutting `g` at the height `s`**: `M g ≤ M (1_{g > s} g) + s` for measurable `g`, since
`g ≤ 1_{g > s} g + s`. -/
theorem maximal_le_maximal_indicator_add {g : V → ℝ≥0∞} (hg : Measurable g) (s : ℝ≥0∞)
    (x : V) : maximal g x ≤ maximal ({y | s < g y}.indicator g) x + s := by
  have hle : g ≤ {y | s < g y}.indicator g + fun _ => s := fun y => by
    by_cases hy : y ∈ {y | s < g y}
    · rw [Pi.add_apply, Set.indicator_of_mem hy]; exact le_self_add
    · rw [Pi.add_apply, Set.indicator_of_notMem hy, zero_add]; exact not_lt.1 hy
  calc maximal g x ≤ maximal ({y | s < g y}.indicator g + fun _ => s) x := maximal_mono hle x
    _ ≤ maximal ({y | s < g y}.indicator g) x + maximal (fun _ => s) x :=
      maximal_add_le ((hg.indicator (measurableSet_lt measurable_const hg)).aemeasurable) _ x
    _ = _ := by rw [maximal_const]

/-- The weighted level sets of `M g` for measurable `g`:
`∫_{M g > s} w ≤ 2 · 5^n s⁻¹ ∫_{g > s/2} g M w` for `s > 0`, by the weighted weak type
applied to `1_{g > s/2} g`. -/
theorem setLIntegral_maximal_gt_le_indicator {g : V → ℝ≥0∞} (hg : Measurable g)
    (w : V → ℝ≥0∞) {s : ℝ≥0∞} (hs0 : 0 < s) :
    ∫⁻ x in {x | s < maximal g x}, w x ≤
      5 ^ finrank ℝ V * 2 * s⁻¹ * ∫⁻ x, {y | s / 2 < g y}.indicator g x * maximal w x := by
  have hsub : {x | s < maximal g x} ⊆
      {x | s / 2 < maximal ({y | s / 2 < g y}.indicator g) x} := fun x (hx : s < _) => by
    change s / 2 < _
    refine lt_of_not_ge fun hle => lt_irrefl s ?_
    calc s < maximal g x := hx
      _ ≤ maximal ({y | s / 2 < g y}.indicator g) x + s / 2 :=
        maximal_le_maximal_indicator_add hg (s / 2) x
      _ ≤ s / 2 + s / 2 := by gcongr
      _ = s := ENNReal.add_halves s
  have hinv : (s / 2)⁻¹ = 2 * s⁻¹ := by
    rw [ENNReal.inv_div (Or.inl ENNReal.ofNat_ne_top) (Or.inl two_ne_zero), div_eq_mul_inv]
  calc ∫⁻ x in {x | s < maximal g x}, w x
      ≤ ∫⁻ x in {x | s / 2 < maximal ({y | s / 2 < g y}.indicator g) x}, w x :=
        lintegral_mono_set hsub
    _ ≤ 5 ^ finrank ℝ V * (s / 2)⁻¹ *
          ∫⁻ x, {y | s / 2 < g y}.indicator g x * maximal w x :=
        setLIntegral_maximal_gt_le _ w (ENNReal.half_pos hs0.ne')
    _ = _ := by rw [hinv]; ring

/-- The integrand of the layer cake formula for `M g` in the measure `w dx`, for measurable `g`
and `t > 0`: `|{M g > t}|_w t^(p-1) ≤ 2 · 5^n (∫_{g > t/2} g M w) t^(p-2)`. -/
theorem withDensity_maximal_gt_mul_le {g : V → ℝ≥0∞} (hg : Measurable g) (w : V → ℝ≥0∞)
    (p : ℝ) {t : ℝ} (ht : 0 < t) :
    volume.withDensity w {x | ENNReal.ofReal t < maximal g x} * ENNReal.ofReal (t ^ (p - 1)) ≤
      5 ^ finrank ℝ V * 2 * ((∫⁻ x, {y | ENNReal.ofReal t / 2 < g y}.indicator g x *
        maximal w x) * ENNReal.ofReal (t ^ (p - 2))) := by
  have hpow : (ENNReal.ofReal t)⁻¹ * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (t ^ (p - 2)) := by
    rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht, Real.rpow_one,
      ENNReal.ofReal_mul ht.le, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top, one_mul]
  rw [withDensity_apply' w]
  calc (∫⁻ x in {x | ENNReal.ofReal t < maximal g x}, w x) * ENNReal.ofReal (t ^ (p - 1))
      ≤ 5 ^ finrank ℝ V * 2 * (ENNReal.ofReal t)⁻¹ *
          (∫⁻ x, {y | ENNReal.ofReal t / 2 < g y}.indicator g x * maximal w x) *
          ENNReal.ofReal (t ^ (p - 1)) := by
        gcongr
        exact setLIntegral_maximal_gt_le_indicator hg w (ENNReal.ofReal_pos.2 ht)
    _ = 5 ^ finrank ℝ V * 2 * ((∫⁻ x, {y | ENNReal.ofReal t / 2 < g y}.indicator g x *
          maximal w x) * ((ENNReal.ofReal t)⁻¹ * ENNReal.ofReal (t ^ (p - 1)))) := by ring
    _ = _ := by rw [hpow]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The function `(t, x) ↦ 1_{g > t/2}(x) g(x)` is measurable on `ℝ × V` for measurable `g`. -/
theorem measurable_indicator_half_lt {g : V → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun q : ℝ × V => {y | ENNReal.ofReal q.1 / 2 < g y}.indicator g q.2 := by
  have h : (fun q : ℝ × V => {y | ENNReal.ofReal q.1 / 2 < g y}.indicator g q.2) =
      {q : ℝ × V | ENNReal.ofReal q.1 / 2 < g q.2}.indicator (fun q => g q.2) := by
    funext q
    by_cases hq : ENNReal.ofReal q.1 / 2 < g q.2
    · rw [Set.indicator_of_mem (show q.2 ∈ {y | ENNReal.ofReal q.1 / 2 < g y} from hq),
        Set.indicator_of_mem (show q ∈ {q : ℝ × V | ENNReal.ofReal q.1 / 2 < g q.2} from hq)]
    · rw [Set.indicator_of_notMem (show q.2 ∉ {y | ENNReal.ofReal q.1 / 2 < g y} from hq),
        Set.indicator_of_notMem (show q ∉ {q : ℝ × V | ENNReal.ofReal q.1 / 2 < g q.2} from hq)]
  rw [h]
  exact (hg.comp measurable_snd).indicator (measurableSet_lt
    ((ENNReal.measurable_ofReal.comp measurable_fst).div_const 2) (hg.comp measurable_snd))

/-- The **Tonelli step** of the strong type bound: for measurable `g, v : V → [0, ∞]` and
`p > 1`, `∫_0^∞ (∫_{g > t/2} g v) t^(p-2) dt = 2^(p-1)/(p-1) ∫ g^p v`. -/
theorem lintegral_Ioi_lintegral_indicator_mul_rpow {g v : V → ℝ≥0∞} (hg : Measurable g)
    (hv : Measurable v) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, {y | ENNReal.ofReal t / 2 < g y}.indicator g x * v x) *
        ENNReal.ofReal (t ^ (p - 2)) =
      2 ^ (p - 1) / ENNReal.ofReal (p - 1) * ∫⁻ x, g x ^ p * v x := by
  have hc : (2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.two_rpow_ne_top _)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hF : AEMeasurable (Function.uncurry fun (t : ℝ) (x : V) =>
      {y | ENNReal.ofReal t / 2 < g y}.indicator g x * v x * ENNReal.ofReal (t ^ (p - 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    (((measurable_indicator_half_lt hg).mul (hv.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _))).aemeasurable
  have hpt : ∀ (t : ℝ) (x : V), {y | ENNReal.ofReal t / 2 < g y}.indicator g x * v x =
      {s : ℝ | ENNReal.ofReal s / 2 < g x}.indicator (fun _ => g x * v x) t := fun t x => by
    by_cases ht : ENNReal.ofReal t / 2 < g x
    · rw [Set.indicator_of_mem (show x ∈ {y | ENNReal.ofReal t / 2 < g y} from ht),
        Set.indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s / 2 < g x} from ht)]
    · rw [Set.indicator_of_notMem (show x ∉ {y | ENNReal.ofReal t / 2 < g y} from ht),
        Set.indicator_of_notMem (show t ∉ {s : ℝ | ENNReal.ofReal s / 2 < g x} from ht), zero_mul]
  simp_rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap hF]
  simp_rw [hpt, lintegral_Ioi_indicator_half_lt_mul_rpow _ _ hp]
  exact lintegral_const_mul' _ _ hc

/-- The **weighted strong type** for measurable `g` and `w`: `∫ (M g)^p w ≤ C_{n,p} ∫ g^p M w`
for `p > 1`, the case of `Rd.lintegral_maximal_rpow_mul_le` before `g` and `w` are replaced by
measurable representatives. -/
theorem lintegral_maximal_rpow_mul_le_of_measurable {g w : V → ℝ≥0∞} (hg : Measurable g)
    (hw : Measurable w) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, maximal g x ^ p * w x ≤ maximalConst (finrank ℝ V) p * ∫⁻ x, g x ^ p * maximal w x := by
  have hc : (5 : ℝ≥0∞) ^ finrank ℝ V * 2 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  calc ∫⁻ x, maximal g x ^ p * w x
      = ∫⁻ x, maximal g x ^ p ∂(volume.withDensity w) := by
        rw [lintegral_withDensity_eq_lintegral_mul volume hw
          ((measurable_maximal g).pow_const p)]
        congr 1; funext x; exact mul_comm _ _
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          volume.withDensity w {x | ENNReal.ofReal t < maximal g x} *
            ENNReal.ofReal (t ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal _ (measurable_maximal g).aemeasurable
          (by linarith)
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), 5 ^ finrank ℝ V * 2 *
          ((∫⁻ x, {y | ENNReal.ofReal t / 2 < g y}.indicator g x * maximal w x) *
            ENNReal.ofReal (t ^ (p - 2))) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun t ht =>
          withDensity_maximal_gt_mul_le hg w p ht) _
    _ = ENNReal.ofReal p * (5 ^ finrank ℝ V * 2 *
          (2 ^ (p - 1) / ENNReal.ofReal (p - 1) * ∫⁻ x, g x ^ p * maximal w x)) := by
        rw [lintegral_const_mul' _ _ hc,
          lintegral_Ioi_lintegral_indicator_mul_rpow hg (measurable_maximal w) hp]
    _ = _ := by
        rw [maximalConst, ENNReal.rpow_eq_mul_rpow_sub_one 2 hp.le, div_eq_mul_inv]; ring

/-- **Weighted strong type of the maximal function** (Fefferman–Stein): for `1 < p < ∞` and
almost everywhere measurable `g, w : V → [0, ∞]`, `∫ (M g)^p w ≤ C_{n,p} ∫ g^p M w` with
`C_{n,p} = p 2^p 5^n / (p - 1)`. The bound holds for every such `g` and `w`, with both sides
possibly infinite. The proof is the layer cake formula in the measure `w dx`, the weighted weak
type for the part of `g` above half the height, and Tonelli's theorem. -/
theorem lintegral_maximal_rpow_mul_le {g w : V → ℝ≥0∞} (hg : AEMeasurable g volume)
    (hw : AEMeasurable w volume) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, maximal g x ^ p * w x ≤ maximalConst (finrank ℝ V) p * ∫⁻ x, g x ^ p * maximal w x := by
  calc ∫⁻ x, maximal g x ^ p * w x = ∫⁻ x, maximal (hg.mk g) x ^ p * hw.mk w x := by
        rw [maximal_congr_ae hg.ae_eq_mk]
        exact lintegral_congr_ae (hw.ae_eq_mk.mono fun x hx => by simp only [hx])
    _ ≤ maximalConst (finrank ℝ V) p * ∫⁻ x, hg.mk g x ^ p * maximal (hw.mk w) x :=
        lintegral_maximal_rpow_mul_le_of_measurable hg.measurable_mk hw.measurable_mk hp
    _ = _ := by
        rw [← maximal_congr_ae hw.ae_eq_mk]
        congr 1
        exact lintegral_congr_ae (hg.ae_eq_mk.mono fun x hx => by simp only [hx])

/-- `C_{n,p} = p 2^p 5^n / (p - 1)` is positive for `p > 0`. -/
theorem maximalConst_ne_zero {n : ℕ} {p : ℝ} (hp : 0 < p) : maximalConst n p ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.2 hp).ne' ?_)
    (pow_ne_zero _ (by norm_num))) (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  exact (ENNReal.rpow_pos (by norm_num) ENNReal.ofNat_ne_top).ne'

/-- The **Hardy–Littlewood maximal theorem**: `‖M g‖_p ≤ C_{n,p}^{1/p} ‖g‖_p` for
`1 < p < ∞` and every `g : V → [0, ∞]` (the weight `w = 1`). -/
theorem eLpNorm_maximal_le (g : V → ℝ≥0∞) {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    eLpNorm (maximal g) p volume ≤
      maximalConst (finrank ℝ V) p.toReal ^ (1 / p.toReal) * eLpNorm g p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpr : 1 < p.toReal := ENNReal.one_lt_toReal hp1 hp
  by_cases hg : AEStronglyMeasurable g volume
  · have h := lintegral_maximal_rpow_mul_le (w := fun _ => (1 : ℝ≥0∞)) hg.aemeasurable
      aemeasurable_const hpr
    rw [maximal_const] at h
    simp only [mul_one] at h
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (measurable_maximal g).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hg]
    simp only [eNorm_eq_self]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact ENNReal.rpow_le_rpow h (by positivity)
  · have hC : maximalConst (finrank ℝ V) p.toReal ^ (1 / p.toReal) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 (maximalConst_ne_zero (zero_lt_one.trans hpr)))
        (maximalConst_ne_top hpr)).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable hg, ENNReal.mul_top hC]
    exact le_top

/-- The maximal function of `g ∈ L_p`, `1 < p < ∞`, is **finite almost everywhere**. -/
theorem maximal_lt_top_ae {g : V → ℝ≥0∞} {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (hgp : eLpNorm g p volume ≠ ∞) : ∀ᵐ x ∂volume, maximal g x < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpr : 0 < p.toReal := zero_lt_one.trans (ENNReal.one_lt_toReal hp1 hp)
  have hlt : eLpNorm (maximal g) p volume ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (maximalConst_ne_top (ENNReal.one_lt_toReal hp1 hp))) hgp) (eLpNorm_maximal_le g hp1 hp)
  have hint : ∫⁻ x, maximal g x ^ p.toReal ≠ ∞ := by
    rw [← eLpNorm_rpow_eq_lintegral hp0 hp (measurable_maximal g).aemeasurable]
    exact ENNReal.rpow_ne_top_of_nonneg hpr.le hlt
  filter_upwards [ae_lt_top ((measurable_maximal g).pow_const _) hint] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hpr).1 hx

/-- The **`p = ∞` bound**: `M g ≤ ‖g‖_∞` everywhere. -/
theorem maximal_le_eLpNorm_top (g : V → ℝ≥0∞) (x : V) : maximal g x ≤ eLpNorm g ∞ volume := by
  by_cases hg : AEStronglyMeasurable g volume
  · rw [eLpNorm_exponent_top hg]
    exact maximal_le_of_ae_le ((ae_le_eLpNormEssSup (f := g)).mono fun y hy => by simpa using hy) x
  · rw [eLpNorm_of_not_aestronglyMeasurable hg]
    exact le_top

end Rd
