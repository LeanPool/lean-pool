/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Campanato.Telescope
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.Topology.MetricSpace.Holder


/-!
# Campanato's characterisation of Hölder continuity

A function whose mean oscillation over balls decays at the rate `r^α` has a representative that is
Hölder continuous with exponent `α`, and the Hölder constant is controlled by the Campanato
constant. This is property (H3) of Fernández-Real and Ros-Oton, *Regularity Theory for Elliptic
PDE*. The `C^{k,α}` scale of Schauder theory rests on it.

Two facts finish the proof. The Lebesgue differentiation theorem identifies `campanatoLimit u`
with `u` almost everywhere, so the limit is a representative. The two-centre comparison
`abs_ballAverage_sub_of_dist_le`, applied at the radius `2 |x - y|`, together with the telescoped
estimate at each of the two centres, bounds `|campanatoLimit u x - campanatoLimit u y|` by
`C · M · |x - y|^α`.

The hypothesis quantifies over balls contained in `B(c, R)`, so the pair estimate needs both
`B(x, 2|x-y|)` and `B(y, 2|x-y|)` inside `B(c, R)`. That holds for `x, y` in the concentric ball
`B(c, ρ)` whenever `5ρ ≤ R`, which is the form `campanato_holderOnWith` takes. Passing from the
concentric ball to all of `B(c, R)` is a separate chaining argument, property (H1') of the same
source, and is not carried out here.
-/

@[expose] public section

open MeasureTheory Set Metric Filter

open scoped NNReal ENNReal Topology

noncomputable section

namespace EllipticPdes.Campanato

variable {d : ℕ}

section AlmostEverywhere

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}

/-- A closed ball and the corresponding open ball agree up to a null set, because a sphere is
Lebesgue null in positive dimension. -/
theorem closedBall_ae_eq_ball (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    Metric.closedBall x r =ᵐ[volume] Metric.ball x r := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [Metric.closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume x r
  · rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall]
    exact measure_empty

/-- **Campanato limit as a representative of `u`.** By the Lebesgue differentiation theorem the
ball means converge to `u` almost everywhere, and by `tendsto_ballAverage_campanatoLimit` they
converge to `campanatoLimit u` everywhere on the open set, so the two agree almost everywhere. -/
theorem campanatoLimit_ae_eq (hd : 0 < d) (hα : 0 < α) (hM : 0 ≤ M) (hΩ : IsOpen Ω)
    (hΩfin : volume Ω ≠ ⊤) (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M) :
    campanatoLimit u =ᵐ[volume.restrict Ω] u := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hΩfin⟩
  have huint : IntegrableOn u Ω volume := hu.integrable (by norm_num)
  have hind : Integrable (Ω.indicator u) volume :=
    huint.integrable_indicator hΩ.measurableSet
  have hloc : LocallyIntegrable (Ω.indicator u) volume := hind.locallyIntegrable
  have hae := (Besicovitch.vitaliFamily
    (volume : Measure (EuclideanSpace ℝ (Fin d)))).ae_tendsto_average hloc
  have hδ : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝[>] 0) :=
    tendsto_pow_atTop_nhdsWithin_zero_of_lt_one (by norm_num) (by norm_num)
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [hae] with x hx hxΩ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε := exists_pow_lt_of_lt_one hε (by norm_num)
  -- The Lebesgue differentiation theorem along the dyadic radii.
  have hcomp : Tendsto
      (fun k : ℕ => ⨍ y in Metric.closedBall x ((1 / 2 : ℝ) ^ k), Ω.indicator u y)
      atTop (𝓝 (Ω.indicator u x)) :=
    hx.comp ((Besicovitch.tendsto_filterAt volume x).comp hδ)
  -- Each closed-ball average is the ball mean, once the ball sits inside `Ω`.
  have heq : ∀ᶠ k in atTop,
      (⨍ y in Metric.closedBall x ((1 / 2 : ℝ) ^ k), Ω.indicator u y)
        = ballAverage u x ((1 / 2 : ℝ) ^ k) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkε : (1 / 2 : ℝ) ^ k < ε :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hN
    have hsubΩ : Metric.closedBall x ((1 / 2 : ℝ) ^ k) ⊆ Ω :=
      (Metric.closedBall_subset_ball hkε).trans hball
    rw [setAverage_congr_fun measurableSet_closedBall
        (Filter.Eventually.of_forall fun y hy => Set.indicator_of_mem (hsubΩ hy) u),
      setAverage_congr (closedBall_ae_eq_ball hd x ((1 / 2 : ℝ) ^ k))]
    rfl
  have h1 : Tendsto (fun k : ℕ => ballAverage u x ((1 / 2 : ℝ) ^ k)) atTop
      (𝓝 (Ω.indicator u x)) := hcomp.congr' heq
  have h2 := tendsto_ballAverage_campanatoLimit hα hM hΩ hu hcamp hxΩ
  rw [tendsto_nhds_unique h2 h1, Set.indicator_of_mem hxΩ]

end AlmostEverywhere

/-- The Hölder constant Campanato's characterisation produces: two telescoped estimates, one at
each centre, plus the two-centre comparison, all evaluated at the radius `2 |x - y|`. -/
def campanatoHolderConst (d : ℕ) (α : ℝ) : ℝ :=
  (2 * campanatoLimitConst d α + campanatoConst d) * 2 ^ α

/-- The Hölder constant is nonnegative. -/
theorem campanatoHolderConst_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ campanatoHolderConst d α := by
  have h1 : (0 : ℝ) ≤ campanatoLimitConst d α := campanatoLimitConst_nonneg hα
  have h2 : (0 : ℝ) ≤ campanatoConst d := campanatoConst_nonneg
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  rw [campanatoHolderConst]
  positivity

section Pair

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}

/-- **Pair estimate.** Two values of the Campanato limit differ by at most
`campanatoHolderConst d α · M · |x - y|^α`, provided the balls of radius `2 |x - y|` about the two
points lie in `Ω`. Both means at that radius are within reach of their limits by the telescoped
estimate, and they are within reach of each other by the two-centre comparison. -/
theorem abs_campanatoLimit_sub_le (hα : 0 < α) (hM : 0 ≤ M) (hΩ : IsOpen Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (hy : y ∈ Ω) (hne : x ≠ y)
    (hxr : Metric.ball x (2 * dist x y) ⊆ Ω) (hyr : Metric.ball y (2 * dist x y) ⊆ Ω) :
    |campanatoLimit u x - campanatoLimit u y|
      ≤ campanatoHolderConst d α * M * dist x y ^ α := by
  have hδ : 0 < dist x y := dist_pos.mpr hne
  have hr : 0 < 2 * dist x y := by linarith
  have h1 := abs_ballAverage_sub_campanatoLimit_le hα hM hΩ hu hcamp hx hr hxr
  have h2 := abs_ballAverage_sub_campanatoLimit_le hα hM hΩ hu hcamp hy hr hyr
  have h3 := abs_ballAverage_sub_of_dist_le hM hu hcamp hr (by linarith) hxr hyr
  have hrα : (2 * dist x y) ^ α = 2 ^ α * dist x y ^ α :=
    Real.mul_rpow (by norm_num) hδ.le
  have h1' : |campanatoLimit u x - ballAverage u x (2 * dist x y)|
      ≤ campanatoLimitConst d α * M * (2 * dist x y) ^ α := by
    rw [abs_sub_comm]; exact h1
  calc |campanatoLimit u x - campanatoLimit u y|
      ≤ |campanatoLimit u x - ballAverage u x (2 * dist x y)|
          + |ballAverage u x (2 * dist x y) - campanatoLimit u y| := abs_sub_le _ _ _
    _ ≤ |campanatoLimit u x - ballAverage u x (2 * dist x y)|
          + (|ballAverage u x (2 * dist x y) - ballAverage u y (2 * dist x y)|
              + |ballAverage u y (2 * dist x y) - campanatoLimit u y|) := by
          gcongr
          exact abs_sub_le _ _ _
    _ ≤ campanatoLimitConst d α * M * (2 * dist x y) ^ α
          + (campanatoConst d * M * (2 * dist x y) ^ α
              + campanatoLimitConst d α * M * (2 * dist x y) ^ α) := by
          exact add_le_add h1' (add_le_add h3 h2)
    _ = campanatoHolderConst d α * M * dist x y ^ α := by
          rw [campanatoHolderConst, hrα]; ring

end Pair

/-- **Campanato's characterisation of Hölder continuity.** Let `u` be square integrable on the ball
`B(c, R)` and suppose its mean oscillation decays at the Campanato rate,

  `∫_{B(x,r)} |u - u_{x,r}|² ≤ M² r^{d + 2α}` for every ball `B(x, r) ⊆ B(c, R)`,

with `0 < α`. Then `campanatoLimit u` is a representative of `u` on every concentric ball
`B(c, ρ)` with `5ρ ≤ R`, and it is Hölder continuous there with exponent `α` and constant
`campanatoHolderConst d α · M`.

The factor `5` comes from the hypothesis: the pair estimate at `x, y ∈ B(c, ρ)` uses the balls
of radius `2 |x - y| < 4ρ` about both points, and those lie in `B(c, R)` exactly when `5ρ ≤ R`. -/
theorem campanato_holderOnWith (hd : 0 < d) {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) {c : EuclideanSpace ℝ (Fin d)} {R ρ : ℝ} (hρ : 0 < ρ)
    (hRρ : 5 * ρ ≤ R) (hu : MemLp u 2 (volume.restrict (Metric.ball c R)))
    (hcamp : CampanatoOn (Metric.ball c R) u α M) :
    campanatoLimit u =ᵐ[volume.restrict (Metric.ball c ρ)] u ∧
      HolderOnWith (Real.toNNReal (campanatoHolderConst d α * M)) (Real.toNNReal α)
        (campanatoLimit u) (Metric.ball c ρ) := by
  have hR : 0 < R := by linarith
  have hρR : ρ ≤ R := by linarith
  have hsubball : Metric.ball c ρ ⊆ Metric.ball c R := Metric.ball_subset_ball hρR
  have hK : 0 ≤ campanatoHolderConst d α * M :=
    mul_nonneg (campanatoHolderConst_nonneg hα) hM
  refine ⟨?_, ?_⟩
  · exact (campanatoLimit_ae_eq hd hα hM Metric.isOpen_ball measure_ball_lt_top.ne hu
      hcamp).filter_mono (ae_mono (Measure.restrict_mono hsubball le_rfl))
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hne
    · simp
    -- The two balls of radius `2 |x - y|` about `x` and `y` lie in `B(c, R)`.
    have hxc : dist x c < ρ := Metric.mem_ball.mp hx
    have hyc : dist y c < ρ := Metric.mem_ball.mp hy
    have hxy : dist x y < 2 * ρ := by
      calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
        _ < ρ + ρ := by rw [dist_comm c y]; linarith
        _ = 2 * ρ := by ring
    have hballsub : ∀ z : EuclideanSpace ℝ (Fin d), dist z c < ρ →
        Metric.ball z (2 * dist x y) ⊆ Metric.ball c R := by
      intro z hz w hw
      rw [Metric.mem_ball] at hw ⊢
      calc dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
        _ < 2 * dist x y + ρ := by linarith
        _ < 2 * (2 * ρ) + ρ := by linarith
        _ = 5 * ρ := by ring
        _ ≤ R := hRρ
    have hbound := abs_campanatoLimit_sub_le hα hM Metric.isOpen_ball hu hcamp
      (hsubball hx) (hsubball hy) hne (hballsub x hxc) (hballsub y hyc)
    -- Transfer the real bound to the extended-distance form `HolderOnWith` states.
    have hαnn : ((Real.toNNReal α : ℝ≥0) : ℝ) = α := Real.coe_toNNReal α hα.le
    have hKnn : ((Real.toNNReal (campanatoHolderConst d α * M) : ℝ≥0) : ℝ)
        = campanatoHolderConst d α * M := Real.coe_toNNReal _ hK
    rw [edist_dist, edist_dist, hαnn,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (Real.toNNReal (campanatoHolderConst d α * M)).coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hKnn, Real.dist_eq]
    exact hbound

end EllipticPdes.Campanato
