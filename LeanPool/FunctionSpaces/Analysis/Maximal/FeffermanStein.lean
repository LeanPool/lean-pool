/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.CalderonZygmund
public import LeanPool.FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal
public import LeanPool.FunctionSpaces.Analysis.Lp.Marcinkiewicz
public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Fefferman–Stein inequality

For `1 < p < ∞`, `1 < q ≤ ∞` and almost everywhere measurable functions `g_j : V → [0, ∞]`,
`j ∈ ℕ`, the **Fefferman–Stein inequality**
`‖ x ↦ ‖(M g_j(x))_j‖_{ℓ_q} ‖_p ≤ C ‖ x ↦ ‖(g_j(x))_j‖_{ℓ_q} ‖_p` holds with the explicit
constant `Rd.feffermanSteinConst` (`Rd.feffermanStein`). The cases:

* `q = ∞` and `q = p` follow from the Hardy–Littlewood maximal theorem one function at a time
  (`Rd.feffermanStein_top`, `Rd.feffermanStein_self`);
* `q < p` follows by duality with the weighted strong type, first for finitely many functions
  (`Rd.lintegral_rpow_sum_maximal_le`) and then by monotone convergence in the number of
  functions (`Rd.lintegral_lqNorm_maximal_rpow_le_of_gt`), with the norm form
  `Rd.feffermanStein_of_gt`;
* `p < q` follows by interpolation between the case `q = p` and the vector-valued weak type
  `(1,1)` (`Rd.volume_lqNorm_maximal_gt_le`, `Rd.lintegral_lqNorm_maximal_rpow_le_of_lt`), with
  the norm form `Rd.feffermanStein_of_lt`.

The weak type rests on the Calderón–Zygmund decomposition of `G = ‖(g_j)_j‖_{ℓ_q}`: off the
enlarged exceptional set, the maximal function of `1_Ω g` is at most `3^n` times the maximal
function of the averages of `g` over the maximal big cubes (`Rd.maximal_indicator_iUnion_le`,
`Rd.maximal_indicator_czSet_le`), and the good parts (`Rd.czGood`) keep the integral
(`Rd.lintegral_czGood`) and have `ℓ_q` norm at most `2^n t` (`Rd.ae_czGood_self_le`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal
open ENNReal (lqNorm)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The maximal function off enlarged sets -/

/-- The integral of `g` over the part of `Q ⊆ closedBall(c, ρ)` in `B(x, r)`, for `x ∉
closedBall(c, 2ρ)`, is at
most `(⨍_Q g) |Q ∩ B(x, 3r)|`: either the two sets are disjoint, or `Q ⊆ B(x, 3r)`. -/
theorem setLIntegral_inter_ball_le {Q : Set V} {c x : V} {ρ r : ℝ} (hQ : Q ⊆ closedBall c ρ)
    (h0 : volume Q ≠ 0) (htop : volume Q ≠ ∞) (g : V → ℝ≥0∞) (hx : x ∉ closedBall c (2 * ρ)) :
    ∫⁻ y in Q ∩ ball x r, g y ≤ (⨍⁻ z in Q, g z ∂volume) * volume (Q ∩ ball x (3 * r)) := by
  rcases (Q ∩ ball x r).eq_empty_or_nonempty with he | hne
  · rw [he, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  rw [Set.inter_eq_left.2 (subset_ball_three_mul_of_inter_nonempty hQ hx hne), setLAverage_eq,
    ENNReal.div_mul_cancel h0 htop]
  exact lintegral_mono_set Set.inter_subset_left

/-- **The maximal function off enlarged sets**: let `Q_i ⊆ closedBall(c_i, ρ_i)` be countably many
measurable sets of positive finite measure and `x` a point outside every `closedBall(c_i,
2ρ_i)`. Then
`M(1_{⋃ Q_i} g)(x) ≤ 3^n M gTilde(x)` for every `g : V → [0, ∞]`, where `gTilde = ∑_i (⨍_{Q_i}
g) 1_{Q_i}`
replaces `g` on each `Q_i` by its mean. A ball `B(x, r)` that meets `Q_i` has radius `r > ρ_i`
and `Q_i ⊆ B(x, 3r)`, so `∫_{B(x,r)} 1_{⋃ Q_i} g ≤ ∫_{B(x,3r)} gTilde`. The bound holds for
arbitrary,
possibly overlapping sets `Q_i` and every `g`. -/
theorem maximal_indicator_iUnion_le {ι : Type*} [Countable ι] (Q : ι → Set V) (c : ι → V)
    (ρ : ι → ℝ) (hQ : ∀ i, Q i ⊆ closedBall (c i) (ρ i)) (hm : ∀ i, MeasurableSet (Q i))
    (h0 : ∀ i, volume (Q i) ≠ 0) (htop : ∀ i, volume (Q i) ≠ ∞) (g : V → ℝ≥0∞) {x : V}
    (hx : ∀ i, x ∉ closedBall (c i) (2 * ρ i)) :
    maximal ((⋃ i, Q i).indicator g) x ≤
      3 ^ finrank ℝ V *
        maximal (fun y => ∑' i, (Q i).indicator (fun _ => ⨍⁻ z in Q i, g z ∂volume) y) x := by
  refine maximal_le_of_forall fun r hr => ?_
  calc ∫⁻ y in ball x r, (⋃ i, Q i).indicator g y
      = ∫⁻ y in ⋃ i, Q i ∩ ball x r, g y := by
        rw [setLIntegral_indicator (MeasurableSet.iUnion hm), Set.iUnion_inter]
    _ ≤ ∑' i, ∫⁻ y in Q i ∩ ball x r, g y := lintegral_iUnion_le _ _
    _ ≤ ∑' i, (⨍⁻ z in Q i, g z ∂volume) * volume (Q i ∩ ball x (3 * r)) :=
        tsum_le_tsum fun i =>
          setLIntegral_inter_ball_le (hQ i) (h0 i) (htop i) g (hx i)
    _ = ∫⁻ y in ball x (3 * r), ∑' i, (Q i).indicator (fun _ => ⨍⁻ z in Q i, g z ∂volume) y := by
        rw [lintegral_tsum fun i => (measurable_const.indicator (hm i)).aemeasurable]
        refine tsum_congr fun i => ?_
        rw [lintegral_indicator_const (hm i), Measure.restrict_apply (hm i)]
    _ ≤ volume (ball (0 : V) (3 * r)) *
          maximal (fun y => ∑' i, (Q i).indicator (fun _ => ⨍⁻ z in Q i, g z ∂volume) y) x :=
        setLIntegral_ball_le_mul_maximal (by positivity) _ x
    _ = volume (ball (0 : V) r) * (3 ^ finrank ℝ V *
          maximal (fun y => ∑' i, (Q i).indicator (fun _ => ⨍⁻ z in Q i, g z ∂volume) y) x) := by
        rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) (by norm_num : (0 : ℝ) < 3),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        ring

/-! ### Averages over the Calderón–Zygmund cubes -/

variable {G : V → ℝ≥0∞} {t : ℝ≥0∞}

/-- The **Calderón–Zygmund averages** of `h : V → [0, ∞]`: on each maximal big cube `Q` of `G`
at height `t` the mean `⨍_Q h`, and `0` outside the exceptional set `Ω`. -/
noncomputable def czAverage (G : V → ℝ≥0∞) (t : ℝ≥0∞) (h : V → ℝ≥0∞) (y : V) : ℝ≥0∞ :=
  ∑' km : czMaximal G t,
    (zcell km.1.1 km.1.2).indicator (fun _ => ⨍⁻ z in zcell km.1.1 km.1.2, h z ∂volume) y

/-- The Calderón–Zygmund averages are measurable. -/
theorem measurable_czAverage (h : V → ℝ≥0∞) : Measurable (czAverage G t h) :=
  Measurable.tsum fun _ => measurable_const.indicator (measurableSet_zcell _ _)

/-- On a maximal big cube `Q`, the Calderón–Zygmund average of `h` is `⨍_Q h`, since the maximal
big cubes are disjoint. -/
theorem czAverage_eq_of_mem {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (hkm : (k, m) ∈ czMaximal G t)
    (h : V → ℝ≥0∞) {x : V} (hx : x ∈ zcell k m) :
    czAverage G t h x = ⨍⁻ z in zcell k m, h z ∂volume := by
  rw [czAverage, tsum_eq_single ⟨(k, m), hkm⟩ fun km hne => ?_]
  · exact Set.indicator_of_mem hx _
  refine Set.indicator_of_notMem (fun hx' => hne ?_) _
  exact subsingleton_czMaximal_mem_zcell (G := G) (t := t) x hx' (show x ∈ zcell k m from hx)

/-- Outside the exceptional set `Ω` the Calderón–Zygmund averages vanish. -/
theorem czAverage_eq_zero_of_notMem (h : V → ℝ≥0∞) {x : V} (hx : x ∉ czSet G t) :
    czAverage G t h x = 0 :=
  tsum_eq_zero_iff.2 fun km =>
    Set.indicator_of_notMem (fun hx' => hx (zcell_subset_czSet km.2 hx')) _

/-- The sum over the maximal big cubes of the integrals of `h : V → [0, ∞]` over the cubes is
the integral of `h` over the exceptional set `Ω`, since the cubes are disjoint. -/
theorem tsum_setLIntegral_czMaximal (h : V → ℝ≥0∞) :
    ∑' km : czMaximal G t, ∫⁻ z in zcell km.1.1 km.1.2, h z = ∫⁻ z in czSet G t, h z := by
  rw [czSet, lintegral_biUnion czMaximal_countable (fun _ _ => measurableSet_zcell _ _)
    czMaximal_pairwiseDisjoint]

/-- **Summing bounds over the maximal big cubes**: if numbers `a_Q ∈ [0, ∞]` indexed by the
maximal big cubes `Q` of `G` at height `t` satisfy `a_Q ≤ c ∫_Q H` for a function
`H : V → [0, ∞]`, then `∑_Q a_Q ≤ c ∫ H`, since the cubes are disjoint
(`Rd.tsum_setLIntegral_czMaximal`). -/
theorem tsum_le_mul_lintegral_of_le_setLIntegral {a : czMaximal G t → ℝ≥0∞} {H : V → ℝ≥0∞}
    (c : ℝ≥0∞) (h : ∀ km, a km ≤ c * ∫⁻ z in zcell km.1.1 km.1.2, H z) :
    ∑' km, a km ≤ c * ∫⁻ z, H z :=
  calc ∑' km, a km ≤ ∑' km : czMaximal G t, c * ∫⁻ z in zcell km.1.1 km.1.2, H z :=
        tsum_le_tsum h
    _ = c * ∫⁻ z in czSet G t, H z := by rw [ENNReal.tsum_mul_left, tsum_setLIntegral_czMaximal]
    _ ≤ c * ∫⁻ z, H z := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **The averages keep the integral**: `∫ czAverage h = ∫_Ω h` for every `h : V → [0, ∞]`, since
`|Q| ⨍_Q h = ∫_Q h` on each of the disjoint maximal big cubes `Q`. -/
theorem lintegral_czAverage (h : V → ℝ≥0∞) :
    ∫⁻ x, czAverage G t h x = ∫⁻ x in czSet G t, h x := by
  simp only [czAverage]
  rw [lintegral_tsum fun _ =>
      (measurable_const.indicator (measurableSet_zcell _ _)).aemeasurable,
    ← tsum_setLIntegral_czMaximal]
  refine tsum_congr fun km => ?_
  rw [lintegral_indicator_const (measurableSet_zcell _ _), setLAverage_eq,
    ENNReal.div_mul_cancel (volume_zcell_pos _ _).ne' (volume_zcell_lt_top _ _).ne]

/-- The Calderón–Zygmund averages of `G` itself are at most `2^n t`
(`Rd.cz_avg_le`). -/
theorem czAverage_self_le (x : V) : czAverage G t G x ≤ 2 ^ finrank ℝ V * t := by
  by_cases hx : x ∈ czSet G t
  · obtain ⟨km, hkm, hxkm⟩ := Set.mem_iUnion₂.1 hx
    rw [czAverage_eq_of_mem hkm G hxkm]
    exact cz_avg_le hkm
  · rw [czAverage_eq_zero_of_notMem G hx]
    exact zero_le

/-- **Positivity of the maximal function off `Ω*`**: for `x` outside the enlarged exceptional
set, `M(1_Ω h)(x) ≤ 3^n M(czAverage h)(x)` for every `h : V → [0, ∞]`, since every maximal big
cube `Q_{k,m}` lies in `closedBall(c_{k,m}, n 2^(-k))` and `Ω*` contains the balls of twice this
radius. -/
theorem maximal_indicator_czSet_le (h : V → ℝ≥0∞) {x : V} (hx : x ∉ czEnlarged G t) :
    maximal ((czSet G t).indicator h) x ≤ 3 ^ finrank ℝ V * maximal (czAverage G t h) x := by
  have := (czMaximal_countable (V := V) (G := G) (t := t)).to_subtype
  have hU : czSet G t = ⋃ km : czMaximal G t, zcell (V := V) km.1.1 km.1.2 :=
    Set.biUnion_eq_iUnion _ _
  rw [hU]
  exact maximal_indicator_iUnion_le (fun km : czMaximal G t => zcell km.1.1 km.1.2)
    (fun km => zcellCenter km.1.1 km.1.2) (fun km => finrank ℝ V / 2 ^ km.1.1)
    (fun _ => zcell_subset_closedBall _ _) (fun _ => measurableSet_zcell _ _)
    (fun _ => (volume_zcell_pos _ _).ne') (fun _ => (volume_zcell_lt_top _ _).ne) h
    fun km hxkm => hx (mem_biUnion km.2 hxkm)

/-- The closed ball of radius `2n 2^(-k)` around the centre of a cube `Q_{k,m}` has volume
`(2n)^n |B(0,1)| |Q_{k,m}|`. -/
theorem volume_closedBall_zcellCenter (k : ℤ) (m : Fin (finrank ℝ V) → ℤ) :
    volume (closedBall (zcellCenter k m) (2 * (finrank ℝ V / 2 ^ k))) =
      (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) * volume (zcell (V := V) k m) := by
  have hpow : (2 * ((finrank ℝ V : ℝ) / 2 ^ k)) ^ finrank ℝ V =
      (2 * (finrank ℝ V : ℝ)) ^ finrank ℝ V * (((2 : ℝ) ^ k)⁻¹) ^ finrank ℝ V := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_pow]
  rw [Measure.addHaar_closedBall _ _ (by positivity), volume_zcell, hpow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_natCast]
  ring

/-- **The measure of the enlarged exceptional set**: `|Ω*| ≤ (2n)^n |B(0,1)| t⁻¹ ∫ G` for every
height `t`, by `Rd.cz_volume_le`. -/
theorem volume_czEnlarged_le :
    volume (czEnlarged G t) ≤
      (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) * (t⁻¹ * ∫⁻ x, G x) := by
  calc volume (czEnlarged G t)
      ≤ ∑' km : czMaximal G t,
          volume (closedBall (zcellCenter (V := V) km.1.1 km.1.2)
            (2 * (finrank ℝ V / 2 ^ km.1.1))) :=
        measure_biUnion_le volume czMaximal_countable _
    _ = ∑' km : czMaximal G t, (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) *
          volume (zcell (V := V) km.1.1 km.1.2) :=
        tsum_congr fun km => volume_closedBall_zcellCenter _ _
    _ = (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) * volume (czSet G t) := by
        rw [ENNReal.tsum_mul_left, czSet, measure_biUnion czMaximal_countable
          czMaximal_pairwiseDisjoint fun _ _ => measurableSet_zcell _ _]
    _ ≤ _ := mul_le_mul_right cz_volume_le _

/-! ### The good part of the Calderón–Zygmund decomposition -/

/-- The **good part** of `h : V → [0, ∞]` in the Calderón–Zygmund decomposition of `G` at height
`t`: `h` outside the exceptional set `Ω`, and its mean `⨍_Q h` on each maximal big cube `Q`. -/
noncomputable def czGood (G : V → ℝ≥0∞) (t : ℝ≥0∞) (h : V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  (czSet G t)ᶜ.indicator h x + czAverage G t h x

/-- The good part of an almost everywhere measurable function is almost everywhere measurable. -/
theorem aemeasurable_czGood {h : V → ℝ≥0∞} (hh : AEMeasurable h volume) :
    AEMeasurable (czGood G t h) volume :=
  (hh.indicator measurableSet_czSet.compl).add (measurable_czAverage h).aemeasurable

/-- **The good part keeps the integral**: `∫ czGood h = ∫ h` for every `h : V → [0, ∞]`, since
`h` is kept outside `Ω` and the averages keep the integral over `Ω` (`Rd.lintegral_czAverage`).
-/
theorem lintegral_czGood (h : V → ℝ≥0∞) : ∫⁻ x, czGood G t h x = ∫⁻ x, h x := by
  simp only [czGood]
  rw [lintegral_add_right' _ (measurable_czAverage h).aemeasurable,
    lintegral_indicator measurableSet_czSet.compl, lintegral_czAverage, add_comm,
    lintegral_add_compl _ measurableSet_czSet]

/-- **The good part of `G` itself is bounded**: in dimension `n ≥ 1`, for an almost everywhere
measurable `G` with finite integral and `0 < t`, the good part of `G` in its own decomposition
at height `t` is at most `2^n t` almost everywhere: off `Ω` it is `G ≤ t`
(`Rd.cz_ae_le_of_notMem`), on a maximal big cube it is the mean `G_Q ≤ 2^n t`. -/
theorem ae_czGood_self_le [Nontrivial V] (hG : AEMeasurable G volume) (hGi : ∫⁻ x, G x ≠ ∞)
    (ht0 : 0 < t) : ∀ᵐ x, czGood G t G x ≤ 2 ^ finrank ℝ V * t := by
  filter_upwards [cz_ae_le_of_notMem hG hGi ht0] with x hx
  by_cases hxΩ : x ∈ czSet G t
  · rw [czGood, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hxΩ), zero_add]
    exact czAverage_self_le x
  · rw [czGood, Set.indicator_of_mem (show x ∈ (czSet G t)ᶜ from hxΩ),
      czAverage_eq_zero_of_notMem _ hxΩ, add_zero]
    exact (hx hxΩ).trans (le_mul_of_one_le_left zero_le (one_le_pow₀ one_le_two))

/-- **The pointwise `ℓ_q` norm of the good parts**: for a family `g_j` of almost everywhere
measurable functions and `1 ≤ q ≤ ∞`, `‖(czGood g_j (x))_j‖_{ℓ_q} ≤ 1_{Ωᶜ} F(x) + czAverage F (x)`
with `F(x) = ‖(g_j(x))_j‖_{ℓ_q}`: off `Ω` both sides are `F(x)`, and on a maximal big cube `Q` the
left side is `‖(⨍_Q g_j)_j‖_{ℓ_q} ≤ ⨍_Q F` (`MeasureTheory.lqNorm_laverage_le`). -/
theorem lqNorm_czGood_le {q : ℝ≥0∞} (hq : 1 ≤ q) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) volume) (x : V) :
    lqNorm q (fun j => czGood G t (g j) x) ≤
      (czSet G t)ᶜ.indicator (fun y => lqNorm q (fun j => g j y)) x +
        czAverage G t (fun y => lqNorm q (fun j => g j y)) x := by
  by_cases hx : x ∈ czSet G t
  · obtain ⟨km, hkm, hxkm⟩ := Set.mem_iUnion₂.1 hx
    have hxc : x ∉ (czSet G t)ᶜ := fun h => h hx
    simp only [czGood, Set.indicator_of_notMem hxc, zero_add, czAverage_eq_of_mem hkm _ hxkm]
    exact lqNorm_laverage_le hq fun j => (hg j).restrict
  · have hxc : x ∈ (czSet G t)ᶜ := hx
    simp only [czGood, Set.indicator_of_mem hxc, czAverage_eq_zero_of_notMem _ hx, add_zero]
    exact le_rfl

/-- **The good parts are bounded**: in dimension `n ≥ 1`, for `1 ≤ q ≤ ∞`, almost everywhere
measurable `g_j` with `F = ‖(g_j)_j‖_{ℓ_q}` integrable, and `0 < t`, the decomposition of `F` at
height `t` has `‖(czGood g_j (x))_j‖_{ℓ_q} ≤ 2^n t` for almost every `x`. -/
theorem ae_lqNorm_czGood_le [Nontrivial V] {q : ℝ≥0∞} (hq : 1 ≤ q) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) volume) (hGi : ∫⁻ x, lqNorm q (fun j => g j x) ≠ ∞)
    (ht0 : 0 < t) :
    ∀ᵐ x, lqNorm q (fun j => czGood (fun y => lqNorm q (fun j => g j y)) t (g j) x) ≤
      2 ^ finrank ℝ V * t := by
  filter_upwards [ae_czGood_self_le (aemeasurable_lqNorm_comp hg q) hGi ht0] with x hx
  exact (lqNorm_czGood_le hq hg x).trans hx

/-- **The integral of the `ℓ_q` norm of the good parts is at most that of the family**:
`∫ ‖(czGood g_j)_j‖_{ℓ_q} ≤ ∫ ‖(g_j)_j‖_{ℓ_q}` for
`1 ≤ q ≤ ∞` and almost everywhere measurable `g_j`, for the decomposition of any `G` at any
height. -/
theorem lintegral_lqNorm_czGood_le {q : ℝ≥0∞} (hq : 1 ≤ q) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, lqNorm q (fun j => czGood G t (g j) x) ≤ ∫⁻ x, lqNorm q (fun j => g j x) :=
  (lintegral_mono fun x => lqNorm_czGood_le hq hg x).trans_eq (lintegral_czGood _)

/-- **The maximal function off `Ω*` is controlled by the good part**: for `x ∉ Ω*` and almost
everywhere measurable `g`, `M g(x) ≤ (1 + 3^n) M(czGood g)(x)`. Split `g = 1_{Ωᶜ} g + 1_Ω g`;
the first part is at most the good part, and `M(1_Ω g)(x) ≤ 3^n M(czAverage g)(x)` by
`Rd.maximal_indicator_czSet_le`. -/
theorem maximal_le_maximal_czGood {g : V → ℝ≥0∞} (hg : AEMeasurable g volume) {x : V}
    (hx : x ∉ czEnlarged G t) :
    maximal g x ≤ (1 + 3 ^ finrank ℝ V) * maximal (czGood G t g) x := by
  have h1 : maximal ((czSet G t)ᶜ.indicator g) x ≤ maximal (czGood G t g) x :=
    maximal_mono (fun y => le_self_add) x
  have h2 : maximal (czAverage G t g) x ≤ maximal (czGood G t g) x :=
    maximal_mono (fun y => le_add_self) x
  calc maximal g x
      = maximal ((czSet G t)ᶜ.indicator g + (czSet G t).indicator g) x := by
        rw [Set.indicator_compl_add_self]
    _ ≤ maximal ((czSet G t)ᶜ.indicator g) x + maximal ((czSet G t).indicator g) x :=
        maximal_add_le (hg.indicator measurableSet_czSet.compl) _ x
    _ ≤ maximal (czGood G t g) x + 3 ^ finrank ℝ V * maximal (czGood G t g) x :=
        add_le_add h1 ((maximal_indicator_czSet_le g hx).trans (mul_le_mul_right h2 _))
    _ = (1 + 3 ^ finrank ℝ V) * maximal (czGood G t g) x := by ring

/-! ### The case `q = p` and the vector-valued weak type -/

/-- **The strong type in integral form**: `∫ (M g)^p ≤ C_{n,p} ∫ g^p` for `p > 1` and almost
everywhere measurable `g : V → [0, ∞]` (`Rd.lintegral_maximal_rpow_mul_le` with `w = 1`). -/
theorem lintegral_maximal_rpow_le {g : V → ℝ≥0∞} (hg : AEMeasurable g volume) {p : ℝ}
    (hp : 1 < p) : ∫⁻ x, maximal g x ^ p ≤ maximalConst (finrank ℝ V) p * ∫⁻ x, g x ^ p := by
  have h := lintegral_maximal_rpow_mul_le (w := fun _ => (1 : ℝ≥0∞)) hg aemeasurable_const hp
  simpa only [maximal_const, mul_one] using h

/-- **The Fefferman–Stein inequality for `q = p` in integral form**: for `1 < q < ∞` and almost
everywhere measurable `g_j : V → [0, ∞]`,
`∫ ‖(M g_j(x))_j‖_{ℓ_q}^q dx ≤ C_{n,q} ∫ ‖(g_j(x))_j‖_{ℓ_q}^q dx`. Both sides are `∑_j ∫ (·)^q`, and
the maximal theorem applies to each `j`. -/
theorem lintegral_lqNorm_maximal_rpow_le {q : ℝ≥0∞} (hq1 : 1 < q) (hq : q ≠ ∞)
    {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, lqNorm q (fun j => maximal (g j) x) ^ q.toReal ≤
      maximalConst (finrank ℝ V) q.toReal * ∫⁻ x, lqNorm q (fun j => g j x) ^ q.toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  simp_rw [ENNReal.lqNorm_rpow hq0 hq]
  rw [lintegral_tsum fun j => (measurable_maximal _).aemeasurable.pow_const _,
    lintegral_tsum fun j => (hg j).pow_const _, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun j =>
    lintegral_maximal_rpow_le (hg j) (ENNReal.one_lt_toReal hq1 hq)

variable (V) in
/-- The constant of the vector-valued weak type `(1,1)`:
`(2n)^n |B(0,1)| + (1 + 3^n)^q 2^(n(q-1)) C_{n,q}`. -/
noncomputable def weakTypeConst (q : ℝ) : ℝ≥0∞ :=
  (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) +
    (1 + 3 ^ finrank ℝ V) ^ q * 2 ^ ((finrank ℝ V : ℝ) * (q - 1)) *
      maximalConst (finrank ℝ V) q

/-- `weakTypeConst V q` is finite for `q > 1`. -/
theorem weakTypeConst_ne_top {q : ℝ} (hq : 1 < q) : weakTypeConst V q ≠ ∞ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _)))
    (volume_ball_ne_top 1), ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_)
    (maximalConst_ne_top hq)⟩
  · exact ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)
  · exact ENNReal.two_rpow_ne_top _

/-- **The `q`-th power of the good parts**: in dimension `n ≥ 1`, for `1 < q < ∞`, almost
everywhere measurable `g_j` with `G = ‖(g_j)_j‖_{ℓ_q}` integrable, and `0 < t`, the good parts
of the decomposition of `G` at height `t` satisfy
`∫ ‖(czGood g_j (x))_j‖_{ℓ_q}^q dx ≤ 2^(n(q-1)) t^(q-1) ∫ G`: their `ℓ_q` norm is bounded by
`2^n t` almost everywhere and has integral at most `∫ G`
(`MeasureTheory.lintegral_rpow_le_mul_lintegral_of_ae_le`). -/
theorem lintegral_lqNorm_czGood_rpow_le [Nontrivial V] {q : ℝ≥0∞} (hq1 : 1 < q) (hq : q ≠ ∞)
    {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume)
    (hGi : ∫⁻ x, lqNorm q (fun j => g j x) ≠ ∞) (ht0 : 0 < t) :
    ∫⁻ x, lqNorm q (fun j => czGood (fun y => lqNorm q (fun j => g j y)) t (g j) x) ^ q.toReal ≤
      2 ^ ((finrank ℝ V : ℝ) * (q.toReal - 1)) * t ^ (q.toReal - 1) *
        ∫⁻ x, lqNorm q (fun j => g j x) := by
  have hr : 1 ≤ q.toReal := (ENNReal.one_lt_toReal hq1 hq).le
  have hpow : ((2 : ℝ≥0∞) ^ finrank ℝ V * t) ^ (q.toReal - 1) =
      2 ^ ((finrank ℝ V : ℝ) * (q.toReal - 1)) * t ^ (q.toReal - 1) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ENNReal.rpow_mul, ENNReal.rpow_natCast]
  have hL : AEMeasurable (fun x =>
      lqNorm q (fun j => czGood (fun y => lqNorm q (fun j => g j y)) t (g j) x)) volume :=
    aemeasurable_lqNorm_comp (fun j => aemeasurable_czGood (hg j)) q
  rw [← hpow]
  exact (lintegral_rpow_le_mul_lintegral_of_ae_le hr hL
    (ae_lqNorm_czGood_le hq1.le hg hGi ht0)).trans
    (mul_le_mul_right (lintegral_lqNorm_czGood_le hq1.le hg) _)

/-- **Chebyshev's inequality for the good parts**: in dimension `n ≥ 1`, for `1 < q < ∞`, almost
everywhere measurable `g_j` with `G = ‖(g_j)_j‖_{ℓ_q}` integrable, and `0 < t < ∞`, let `czGood`
be the good part of the decomposition of `G` at height `t` and `c = 1 + 3^n`. The set where
`c ‖(M(czGood g_j)(x))_j‖_{ℓ_q}` exceeds `t` has measure at most `c^q 2^(n(q-1)) C_{n,q} t⁻¹ ∫ G`,
by the case `q = p` and the bound of the good parts. -/
theorem volume_lt_mul_lqNorm_maximal_czGood_le [Nontrivial V] {q : ℝ≥0∞} (hq1 : 1 < q)
    (hq : q ≠ ∞) {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume)
    (hGi : ∫⁻ x, lqNorm q (fun j => g j x) ≠ ∞) (ht0 : 0 < t) (ht : t ≠ ∞) :
    volume {x | t < (1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
        maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x)} ≤
      (1 + 3 ^ finrank ℝ V) ^ q.toReal * 2 ^ ((finrank ℝ V : ℝ) * (q.toReal - 1)) *
        maximalConst (finrank ℝ V) q.toReal * t⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) := by
  have hr : 1 < q.toReal := ENNReal.one_lt_toReal hq1 hq
  have hc : (1 + 3 ^ finrank ℝ V : ℝ≥0∞) ^ q.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)
  have hL : Measurable fun x => lqNorm q (fun j =>
      maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x) :=
    measurable_lqNorm_comp (fun _ => measurable_maximal _) q
  have hint := (lintegral_lqNorm_maximal_rpow_le hq1 hq
    (fun j => aemeasurable_czGood (G := fun y => lqNorm q (fun j => g j y)) (t := t) (hg j))).trans
    (mul_le_mul_right (lintegral_lqNorm_czGood_rpow_le hq1 hq hg hGi ht0) _)
  have htt : (t ^ q.toReal)⁻¹ * t ^ (q.toReal - 1) = t⁻¹ := by
    rw [ENNReal.rpow_sub _ _ ht0.ne' ht, ENNReal.rpow_one, div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.rpow_pos ht0 ht).ne'
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ht), one_mul]
  calc volume {x | t < (1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
        maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x)}
      ≤ (t ^ q.toReal)⁻¹ * ∫⁻ x, ((1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
          maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x)) ^ q.toReal :=
        measure_lt_le_inv_rpow_mul_lintegral (hL.const_mul _).aemeasurable (by linarith)
          ht0.ne' ht
    _ ≤ (t ^ q.toReal)⁻¹ * ((1 + 3 ^ finrank ℝ V) ^ q.toReal * (maximalConst (finrank ℝ V)
          q.toReal * (2 ^ ((finrank ℝ V : ℝ) * (q.toReal - 1)) * t ^ (q.toReal - 1) *
            ∫⁻ x, lqNorm q (fun j => g j x)))) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hr.le)]
        rw [lintegral_const_mul' _ _ hc]
        gcongr
    _ = _ := by rw [← htt]; ring

/-- **The vector-valued weak type `(1,1)`** of the maximal function (Fefferman–Stein): in
dimension `n ≥ 1`, for `1 < q < ∞`, almost everywhere measurable `g_j : V → [0, ∞]` with
`G = ‖(g_j)_j‖_{ℓ_q}` integrable, and `0 < t < ∞`,
`|{x : ‖(M g_j(x))_j‖_{ℓ_q} > t}| ≤ C t⁻¹ ∫ G` with `C = weakTypeConst V q`. The
Calderón–Zygmund decomposition of `G` at height `t` splits the level set into the enlarged
exceptional set `Ω*`, of measure at most `(2n)^n |B(0,1)| t⁻¹ ∫ G`, and the set where
`(1 + 3^n) ‖(M(czGood g_j))_j‖_{ℓ_q} > t`, which Chebyshev's inequality bounds. -/
theorem volume_lqNorm_maximal_gt_le [Nontrivial V] {q : ℝ≥0∞} (hq1 : 1 < q) (hq : q ≠ ∞)
    (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume)
    (hGi : ∫⁻ x, lqNorm q (fun j => g j x) ≠ ∞) (ht0 : 0 < t) (ht : t ≠ ∞) :
    volume {x | t < lqNorm q (fun j => maximal (g j) x)} ≤
      weakTypeConst V q.toReal * t⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) := by
  have hsub : {x | t < lqNorm q (fun j => maximal (g j) x)} ⊆
      czEnlarged (fun y => lqNorm q (fun j => g j y)) t ∪
        {x | t < (1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
          maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x)} := fun x hx => by
    by_cases hxE : x ∈ czEnlarged (fun y => lqNorm q (fun j => g j y)) t
    · exact Or.inl hxE
    have h : lqNorm q (fun j => maximal (g j) x) ≤ (1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
        maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x) := by
      rw [← ENNReal.lqNorm_const_mul]
      exact ENNReal.lqNorm_mono fun j => maximal_le_maximal_czGood (hg j) hxE
    exact Or.inr (show t < _ from lt_of_lt_of_le hx h)
  calc volume {x | t < lqNorm q (fun j => maximal (g j) x)}
      ≤ volume (czEnlarged (fun y => lqNorm q (fun j => g j y)) t) +
          volume {x | t < (1 + 3 ^ finrank ℝ V) * lqNorm q (fun j =>
            maximal (czGood (fun y => lqNorm q (fun j => g j y)) t (g j)) x)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) *
          (t⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x)) +
        (1 + 3 ^ finrank ℝ V) ^ q.toReal * 2 ^ ((finrank ℝ V : ℝ) * (q.toReal - 1)) *
          maximalConst (finrank ℝ V) q.toReal * t⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) :=
        add_le_add volume_czEnlarged_le
          (volume_lt_mul_lqNorm_maximal_czGood_le hq1 hq hg hGi ht0 ht)
    _ = _ := by rw [weakTypeConst]; ring

/-! ### Interpolation for `p < q` -/

/-- **Splitting a family along a set**: for almost everywhere measurable `g_j`, measurable `S` and
`1 ≤ q ≤ ∞`, `‖(M g_j(x))_j‖_{ℓ_q} ≤ ‖(M(1_S g_j)(x))_j‖_{ℓ_q} + ‖(M(1_{Sᶜ} g_j)(x))_j‖_{ℓ_q}`, by
the subadditivity of `M` and Minkowski's inequality in `ℓ_q`. -/
theorem lqNorm_maximal_le_indicator_add {q : ℝ≥0∞} (hq : 1 ≤ q) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) volume) {S : Set V} (hS : MeasurableSet S) (x : V) :
    lqNorm q (fun j => maximal (g j) x) ≤
      lqNorm q (fun j => maximal (S.indicator (g j)) x) +
        lqNorm q (fun j => maximal (Sᶜ.indicator (g j)) x) := by
  refine (ENNReal.lqNorm_mono fun j => ?_).trans (ENNReal.lqNorm_add_le hq _ _)
  calc maximal (g j) x = maximal (S.indicator (g j) + Sᶜ.indicator (g j)) x := by
        rw [Set.indicator_self_add_compl]
    _ ≤ _ := maximal_add_le ((hg j).indicator hS) _ x

/-- **The two pieces at a level**: in dimension `n ≥ 1`, for `1 < q < ∞`, almost everywhere
measurable `g_j`, a measurable set `S` on which `G = ‖(g_j)_j‖_{ℓ_q}` is integrable, and
`0 < s < ∞`,
`|{‖(M g_j)_j‖_{ℓ_q} > s}| ≤ C (s/2)⁻¹ ∫ 1_S G + ((s/2)^q)⁻¹ C_{n,q} ∫ (1_{Sᶜ} G)^q` with
`C = weakTypeConst V q`: the vector-valued weak type for `1_S g_j` and Chebyshev's inequality
with the case `q = p` for `1_{Sᶜ} g_j`. -/
theorem volume_lqNorm_maximal_gt_le_split [Nontrivial V] {q : ℝ≥0∞} (hq1 : 1 < q) (hq : q ≠ ∞)
    {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume) {S : Set V}
    (hS : MeasurableSet S) (hSi : ∫⁻ x, S.indicator (fun y => lqNorm q (fun j => g j y)) x ≠ ∞)
    {s : ℝ≥0∞} (hs0 : 0 < s) (hs : s ≠ ∞) :
    volume {x | s < lqNorm q (fun j => maximal (g j) x)} ≤
      weakTypeConst V q.toReal * (s / 2)⁻¹ *
          (∫⁻ x, S.indicator (fun y => lqNorm q (fun j => g j y)) x) +
        ((s / 2) ^ q.toReal)⁻¹ * (maximalConst (finrank ℝ V) q.toReal *
          ∫⁻ x, Sᶜ.indicator (fun y => lqNorm q (fun j => g j y)) x ^ q.toReal) := by
  have hs2 : 0 < s / 2 := ENNReal.half_pos hs0.ne'
  have hs2t : s / 2 ≠ ∞ := ENNReal.div_ne_top hs two_ne_zero
  have hr : 1 < q.toReal := ENNReal.one_lt_toReal hq1 hq
  have hsub : {x | s < lqNorm q (fun j => maximal (g j) x)} ⊆
      {x | s / 2 < lqNorm q (fun j => maximal (S.indicator (g j)) x)} ∪
        {x | s / 2 < lqNorm q (fun j => maximal (Sᶜ.indicator (g j)) x)} := fun x hx => by
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    have h := (lqNorm_maximal_le_indicator_add hq1.le hg hS x).trans (add_le_add hnot.1 hnot.2)
    rw [ENNReal.add_halves] at h
    exact absurd hx (not_lt.2 h)
  have h1 := volume_lqNorm_maximal_gt_le hq1 hq (fun j => S.indicator (g j))
    (fun j => (hg j).indicator hS) (by simpa only [ENNReal.lqNorm_indicator] using hSi) hs2 hs2t
  simp only [ENNReal.lqNorm_indicator] at h1
  have hL : Measurable fun x => lqNorm q (fun j => maximal (Sᶜ.indicator (g j)) x) :=
    measurable_lqNorm_comp (fun _ => measurable_maximal _) q
  have h2 : volume {x | s / 2 < lqNorm q (fun j => maximal (Sᶜ.indicator (g j)) x)} ≤
      ((s / 2) ^ q.toReal)⁻¹ * (maximalConst (finrank ℝ V) q.toReal *
        ∫⁻ x, Sᶜ.indicator (fun y => lqNorm q (fun j => g j y)) x ^ q.toReal) := by
    refine (measure_lt_le_inv_rpow_mul_lintegral hL.aemeasurable (by linarith) hs2.ne'
      hs2t).trans ?_
    gcongr
    have := lintegral_lqNorm_maximal_rpow_le hq1 hq fun j => (hg j).indicator hS.compl
    simpa only [ENNReal.lqNorm_indicator] using this
  calc volume {x | s < lqNorm q (fun j => maximal (g j) x)}
      ≤ volume {x | s / 2 < lqNorm q (fun j => maximal (S.indicator (g j)) x)} +
          volume {x | s / 2 < lqNorm q (fun j => maximal (Sᶜ.indicator (g j)) x)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ _ := add_le_add h1 h2

/-- **The level sets of the vector-valued maximal function, weighted**: in dimension `n ≥ 1`,
for `p > 1`, `1 < q < ∞`, measurable `g_j` with `∫ G^p < ∞` for `G = ‖(g_j)_j‖_{ℓ_q}`, and
`τ > 0`, `|{‖(M g_j)_j‖_{ℓ_q} > τ}| τ^(p-1)` is at most
`2 C (∫_{G > τ} G) τ^(p-2) + 2^q C_{n,q} (∫_{G ≤ τ} G^q) τ^(p-1-q)` with
`C = weakTypeConst V q`: `Rd.volume_lqNorm_maximal_gt_le_split` for the set `{G > τ}`, on which
`G` is integrable since `∫_{G > τ} G ≤ τ^(1-p) ∫ G^p`. -/
theorem volume_lqNorm_maximal_gt_mul_rpow_le [Nontrivial V] {p : ℝ} (hp1 : 1 < p) {q : ℝ≥0∞}
    (hq1 : 1 < q) (hq : q ≠ ∞) {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, Measurable (g j))
    (hA : ∫⁻ x, lqNorm q (fun j => g j x) ^ p ≠ ∞) {τ : ℝ} (hτ : 0 < τ) :
    volume {x | ENNReal.ofReal τ < lqNorm q (fun j => maximal (g j) x)} *
        ENNReal.ofReal (τ ^ (p - 1)) ≤
      2 * weakTypeConst V q.toReal *
          ((∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}.indicator
            (fun y => lqNorm q (fun j => g j y)) x) * ENNReal.ofReal (τ ^ (p - 2))) +
        2 ^ q.toReal * maximalConst (finrank ℝ V) q.toReal *
          ((∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}ᶜ.indicator
            (fun y => lqNorm q (fun j => g j y)) x ^ q.toReal) *
              ENNReal.ofReal (τ ^ (p - 1 - q.toReal))) := by
  have hGm := measurable_lqNorm_comp hg q
  have hS : MeasurableSet {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)} :=
    measurableSet_lt measurable_const hGm
  have hc0 : ENNReal.ofReal τ ^ (p - 1) ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hτ)
    ENNReal.ofReal_ne_top).ne'
  have hSi := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hA)
    (lintegral_indicator_lt_le hp1.le (ENNReal.ofReal_pos.2 hτ).ne' ENNReal.ofReal_ne_top
      (fun y => lqNorm q (fun j => g j y)))
  have h := volume_lqNorm_maximal_gt_le_split hq1 hq (fun j => (hg j).aemeasurable) hS hSi
    (ENNReal.ofReal_pos.2 hτ) ENNReal.ofReal_ne_top
  refine (mul_le_mul_left h _).trans_eq ?_
  calc _ = weakTypeConst V q.toReal *
          ((ENNReal.ofReal τ / 2)⁻¹ * ENNReal.ofReal (τ ^ (p - 1))) *
          (∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}.indicator
            (fun y => lqNorm q (fun j => g j y)) x) +
        ((ENNReal.ofReal τ / 2) ^ q.toReal)⁻¹ * ENNReal.ofReal (τ ^ (p - 1)) *
          (maximalConst (finrank ℝ V) q.toReal *
            ∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}ᶜ.indicator
              (fun y => lqNorm q (fun j => g j y)) x ^ q.toReal) := by ring
    _ = _ := by
        rw [ENNReal.inv_half_mul_ofReal_rpow hτ p,
          ENNReal.inv_half_rpow_mul_ofReal_rpow hτ p q.toReal]
        ring

variable (V) in
/-- The constant of the interpolation for `p < q`:
`p (2 C^w_{n,q} / (p - 1) + 2^q C_{n,q} / (q - p))` with `C^w_{n,q} = weakTypeConst V q` and
`C_{n,q} = maximalConst n q`. -/
noncomputable def interpolationConst (p q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal p * (2 * weakTypeConst V q * (ENNReal.ofReal (p - 1))⁻¹ +
    2 ^ q * maximalConst (finrank ℝ V) q * (ENNReal.ofReal (q - p))⁻¹)

/-- `interpolationConst V p q` is finite for `1 < p < q`. -/
theorem interpolationConst_ne_top {p q : ℝ} (hp : 1 < p) (hpq : p < q) :
    interpolationConst V p q ≠ ∞ := by
  have hq : 1 < q := hp.trans hpq
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (weakTypeConst_ne_top hq))
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne')
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.two_rpow_ne_top _) (maximalConst_ne_top hq))
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne')

/-- `interpolationConst V p q` is positive for `0 < p` and `0 < q`. -/
theorem interpolationConst_ne_zero {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    interpolationConst V p q ≠ 0 := by
  refine mul_ne_zero (ENNReal.ofReal_pos.2 hp).ne' (ne_of_gt ?_)
  refine lt_of_lt_of_le ?_ le_add_self
  refine ENNReal.mul_pos (ENNReal.mul_pos
    (ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2) ENNReal.ofNat_ne_top).ne'
    (maximalConst_ne_zero hq)).ne' (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)

/-- **The Fefferman–Stein inequality for `p < q` in integral form, measurable case**: in
dimension `n ≥ 1`, for `1 < p < q < ∞` and measurable `g_j : V → [0, ∞]`,
`∫ ‖(M g_j(x))_j‖_{ℓ_q}^p dx ≤ C ∫ G^p` with `G = ‖(g_j)_j‖_{ℓ_q}` and
`C = interpolationConst V p q`. The layer cake formula, the level estimate
`Rd.volume_lqNorm_maximal_gt_mul_rpow_le` and the two Tonelli steps give it. The bound
`1 < p < q.toReal` forces `q < ∞`. -/
theorem lintegral_lqNorm_maximal_rpow_le_of_lt_of_measurable [Nontrivial V] {p : ℝ}
    {q : ℝ≥0∞} (hp1 : 1 < p) (hpq : p < q.toReal) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, Measurable (g j)) :
    ∫⁻ x, lqNorm q (fun j => maximal (g j) x) ^ p ≤
      interpolationConst V p q.toReal * ∫⁻ x, lqNorm q (fun j => g j x) ^ p := by
  have hq : q ≠ ∞ := (ENNReal.toReal_pos_iff.1 ((zero_lt_one.trans hp1).trans hpq)).2.ne
  have hq1 : 1 < q :=
    (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq).1 (by simpa using hp1.trans hpq)
  have hr : 1 < q.toReal := hp1.trans hpq
  have hGm := measurable_lqNorm_comp hg q
  rcases eq_or_ne (∫⁻ x, lqNorm q (fun j => g j x) ^ p) ∞ with hA | hA
  · rw [hA, ENNReal.mul_top (interpolationConst_ne_zero (by linarith) (by linarith))]
    exact le_top
  have hc1 : 2 * weakTypeConst V q.toReal ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (weakTypeConst_ne_top hr)
  have hc2 : (2 : ℝ≥0∞) ^ q.toReal * maximalConst (finrank ℝ V) q.toReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
      (maximalConst_ne_top hr)
  have hm1 : Measurable fun τ : ℝ =>
      (∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}.indicator
        (fun y => lqNorm q (fun j => g j y)) x) * ENNReal.ofReal (τ ^ (p - 2)) :=
    (Measurable.lintegral_prod_right'
      (measurable_indicator_section (measurableSet_ofReal_lt hGm) hGm)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal volume
    (measurable_lqNorm_comp (fun _ => measurable_maximal _) q).aemeasurable (by linarith)]
  refine (mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi fun τ hτ =>
    volume_lqNorm_maximal_gt_mul_rpow_le hp1 hq1 hq hg hA hτ) _).trans ?_
  rw [lintegral_add_left' (hm1.const_mul _).aemeasurable, lintegral_const_mul' _ _ hc1,
    lintegral_const_mul' _ _ hc2, lintegral_Ioi_lintegral_indicator_lt_mul_rpow hGm hp1]
  calc ENNReal.ofReal p * (2 * weakTypeConst V q.toReal *
        ((ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) ^ p) +
        2 ^ q.toReal * maximalConst (finrank ℝ V) q.toReal * ∫⁻ τ in Ioi (0 : ℝ),
          (∫⁻ x, {y | ENNReal.ofReal τ < lqNorm q (fun j => g j y)}ᶜ.indicator
            (fun y => lqNorm q (fun j => g j y)) x ^ q.toReal) *
              ENNReal.ofReal (τ ^ (p - 1 - q.toReal)))
      ≤ ENNReal.ofReal p * (2 * weakTypeConst V q.toReal *
          ((ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) ^ p) +
        2 ^ q.toReal * maximalConst (finrank ℝ V) q.toReal *
          ((ENNReal.ofReal (q.toReal - p))⁻¹ * ∫⁻ x, lqNorm q (fun j => g j x) ^ p)) := by
        gcongr
        exact lintegral_Ioi_lintegral_indicator_compl_mul_rpow_le hGm (by linarith) hpq
    _ = _ := by rw [interpolationConst]; ring

/-- **The Fefferman–Stein inequality for `p < q` in integral form** (interpolation): in dimension
`n ≥ 1`, for `1 < p < q < ∞` and almost everywhere measurable `g_j : V → [0, ∞]`,
`∫ ‖(M g_j(x))_j‖_{ℓ_q}^p dx ≤ C ∫ ‖(g_j(x))_j‖_{ℓ_q}^p dx` with
`C = interpolationConst V p q`. At each level `τ` the family is split at `{G > τ}`; the
vector-valued weak type `(1,1)` controls the large part and the case `q = p` the small part, as
in Marcinkiewicz's interpolation theorem. -/
theorem lintegral_lqNorm_maximal_rpow_le_of_lt [Nontrivial V] {p q : ℝ≥0∞} (hp1 : 1 < p)
    (hpq : p < q) (hq : q ≠ ∞) (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, lqNorm q (fun j => maximal (g j) x) ^ p.toReal ≤
      interpolationConst V p.toReal q.toReal * ∫⁻ x, lqNorm q (fun j => g j x) ^ p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_lt hpq
  have hmax : ∀ j, maximal (g j) = maximal ((hg j).mk (g j)) := fun j =>
    maximal_congr_ae (hg j).ae_eq_mk
  have hae : ∀ᵐ x ∂volume, ∀ j, g j x = (hg j).mk (g j) x :=
    ae_all_iff.2 fun j => (hg j).ae_eq_mk
  have hint : ∫⁻ x, lqNorm q (fun j => g j x) ^ p.toReal =
      ∫⁻ x, lqNorm q (fun j => (hg j).mk (g j) x) ^ p.toReal :=
    lintegral_congr_ae (hae.mono fun x hx => by simp only [hx])
  simp_rw [hmax]
  rw [hint]
  exact lintegral_lqNorm_maximal_rpow_le_of_lt_of_measurable (ENNReal.one_lt_toReal hp1 hp)
    ((ENNReal.toReal_lt_toReal hp hq).2 hpq) fun j => (hg j).measurable_mk

/-! ### Duality for `q < p` -/

/-- The constant of the duality argument for `q < p`:
`(C_{n,q} C_{n,u'}^{1/u'})^(p/q)` with the exponent `u' = p/(p - q)` conjugate to `u = p/q`. -/
noncomputable def dualityConst (n : ℕ) (p q : ℝ) : ℝ≥0∞ :=
  (maximalConst n q * maximalConst n (p / (p - q)) ^ ((p - q) / p)) ^ (p / q)

/-- `dualityConst n p q` is finite for `1 < q < p`. -/
theorem dualityConst_ne_top {n : ℕ} {p q : ℝ} (hq : 1 < q) (hqp : q < p) :
    dualityConst n p q ≠ ∞ := by
  have hu' : 1 < p / (p - q) := (one_lt_div (by linarith)).2 (by linarith)
  refine ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
    (ENNReal.mul_ne_top (maximalConst_ne_top hq) ?_)
  exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
    (maximalConst_ne_top hu')

/-- `dualityConst n p q` is positive for `0 < q < p`. -/
theorem dualityConst_ne_zero {n : ℕ} {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    dualityConst n p q ≠ 0 := by
  have hu' : 0 < p / (p - q) := div_pos (by linarith) (by linarith)
  refine (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 (mul_ne_zero (maximalConst_ne_zero hq)
    (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 (maximalConst_ne_zero hu'))
      (div_nonneg (by linarith) (by linarith))).ne')) (div_nonneg (by linarith) hq.le)).ne'

/-- **Finiteness for finitely many functions**: for `1 < q < p`, finitely many almost everywhere
measurable `g_j` and `∫ (∑_j g_j^q)^(p/q) < ∞`, also `∫ (∑_j (M g_j)^q)^(p/q) < ∞`: each `g_j^p`
is at most `(∑_j g_j^q)^(p/q)`, the maximal theorem bounds `∫ (M g_j)^p`, and
`(∑_{j ∈ S} a_j)^u ≤ |S|^(u-1) ∑_{j ∈ S} a_j^u`. -/
theorem lintegral_rpow_sum_maximal_ne_top {p q : ℝ} (hq1 : 1 < q) (hqp : q < p) (S : Finset ℕ)
    {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume)
    (hA : ∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ (p / q) ≠ ∞) :
    ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ (p / q) ≠ ∞ := by
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hu : 1 ≤ p / q := (one_le_div hq0).2 hqp.le
  have hpow : ∀ a : ℝ≥0∞, (a ^ q) ^ (p / q) = a ^ p := fun a => by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hq0.ne']
  have hgj : ∀ j ∈ S, ∫⁻ x, g j x ^ p ≠ ∞ := fun j hj =>
    ne_top_of_le_ne_top hA (lintegral_mono fun x => by
      rw [← hpow]
      exact ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun i => g i x ^ q)
        (fun _ _ => zero_le) hj) (by linarith))
  have hMj : ∀ j ∈ S, ∫⁻ x, maximal (g j) x ^ p ≠ ∞ := fun j hj =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (maximalConst_ne_top (hq1.trans hqp)) (hgj j hj))
      (lintegral_maximal_rpow_le (hg j) (hq1.trans hqp))
  have hc : (S.card : ℝ≥0∞) ^ (p / q - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x =>
    ENNReal.rpow_sum_le_const_mul_sum_rpow (s := S) (f := fun j => maximal (g j) x ^ q) hu)
  rw [lintegral_const_mul' _ _ hc, lintegral_finsetSum' S fun j _ =>
    (((measurable_maximal _).pow_const _).pow_const _).aemeasurable]
  simp_rw [hpow]
  exact ENNReal.mul_ne_top hc (ENNReal.sum_ne_top.2 hMj)

/-- **The duality step** for finitely many functions: for `q > 1`, conjugate exponents `u, u'`
and almost everywhere measurable `g_j`, with `H = ∑_{j ∈ S} (M g_j)^q`,
`∫ H^u ≤ C_{n,q} C_{n,u'}^{1/u'} (∫ (∑_{j ∈ S} g_j^q)^u)^{1/u} (∫ H^u)^{1/u'}`. With
`w = H^(u-1)`, `∫ H^u = ∑_j ∫ (M g_j)^q w ≤ C_{n,q} ∫ (∑_j g_j^q) M w` by the weighted strong type,
then Hölder's inequality and the maximal theorem for `w` in `L_{u'}`, where
`∫ w^{u'} = ∫ H^u`. -/
theorem lintegral_rpow_sum_maximal_le_mul {q u u' : ℝ} (hq1 : 1 < q)
    (hu : u.HolderConjugate u') (S : Finset ℕ) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u ≤
      maximalConst (finrank ℝ V) q * maximalConst (finrank ℝ V) u' ^ (1 / u') *
        (∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ u) ^ (1 / u) *
          (∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u) ^ (1 / u') := by
  have hH : Measurable fun x => ∑ j ∈ S, maximal (g j) x ^ q :=
    Finset.measurable_fun_sum S fun j _ => (measurable_maximal _).pow_const _
  have hw : Measurable fun x => (∑ j ∈ S, maximal (g j) x ^ q) ^ (u - 1) := hH.pow_const _
  have hGq : AEMeasurable (fun x => ∑ j ∈ S, g j x ^ q) volume :=
    Finset.aemeasurable_fun_sum S fun j _ => (hg j).pow_const _
  have hu'0 : (0 : ℝ) ≤ 1 / u' := one_div_nonneg.2 hu.symm.pos.le
  have hM : ∫⁻ x, maximal (fun y => (∑ j ∈ S, maximal (g j) y ^ q) ^ (u - 1)) x ^ u' ≤
      maximalConst (finrank ℝ V) u' * ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u := by
    have hww : ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u =
        ∫⁻ x, ((∑ j ∈ S, maximal (g j) x ^ q) ^ (u - 1)) ^ u' := by
      congr 1
      funext x
      rw [← ENNReal.rpow_mul, hu.sub_one_mul_conj]
    rw [hww]
    exact lintegral_maximal_rpow_le hw.aemeasurable hu.symm.lt
  calc ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u
      = ∑ j ∈ S, ∫⁻ x, maximal (g j) x ^ q * (∑ i ∈ S, maximal (g i) x ^ q) ^ (u - 1) := by
        rw [← lintegral_finsetSum' S (f := fun j x =>
          maximal (g j) x ^ q * (∑ i ∈ S, maximal (g i) x ^ q) ^ (u - 1)) fun j _ =>
          (((measurable_maximal _).pow_const _).mul hw).aemeasurable]
        congr 1
        funext x
        rw [← Finset.sum_mul, ← ENNReal.rpow_eq_mul_rpow_sub_one _ hu.lt.le]
    _ ≤ ∑ j ∈ S, maximalConst (finrank ℝ V) q * ∫⁻ x, g j x ^ q *
          maximal (fun y => (∑ i ∈ S, maximal (g i) y ^ q) ^ (u - 1)) x :=
        Finset.sum_le_sum fun j _ => lintegral_maximal_rpow_mul_le (hg j) hw.aemeasurable hq1
    _ = maximalConst (finrank ℝ V) q * ∫⁻ x, (∑ j ∈ S, g j x ^ q) *
          maximal (fun y => (∑ i ∈ S, maximal (g i) y ^ q) ^ (u - 1)) x := by
        rw [← Finset.mul_sum, ← lintegral_finsetSum' S (f := fun j x =>
          g j x ^ q * maximal (fun y => (∑ i ∈ S, maximal (g i) y ^ q) ^ (u - 1)) x) fun j _ =>
          ((hg j).pow_const _).mul (measurable_maximal _).aemeasurable]
        congr 2
        funext x
        rw [Finset.sum_mul]
    _ ≤ maximalConst (finrank ℝ V) q * ((∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ u) ^ (1 / u) *
          (∫⁻ x, maximal (fun y => (∑ i ∈ S, maximal (g i) y ^ q) ^ (u - 1)) x ^ u') ^
            (1 / u')) :=
        mul_le_mul_right (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hu hGq
          (measurable_maximal _).aemeasurable) _
    _ ≤ maximalConst (finrank ℝ V) q * ((∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ u) ^ (1 / u) *
          (maximalConst (finrank ℝ V) u' *
            ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ u) ^ (1 / u')) :=
        mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow hM hu'0) _) _
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hu'0]; ring

/-- **The Fefferman–Stein inequality for `q < p` and finitely many functions**: for `1 < q < p` and
almost everywhere measurable `g_j`, `∫ (∑_{j ∈ S} (M g_j)^q)^(p/q) ≤ C ∫ (∑_{j ∈ S} g_j^q)^(p/q)`
with `C = dualityConst n p q`. The duality step `Rd.lintegral_rpow_sum_maximal_le_mul` with
`u = p/q` and `u' = p/(p - q)` gives `X ≤ K A^{1/u} X^{1/u'}`, and since `X < ∞` the factor
`X^{1/u'}` cancels (`ENNReal.le_rpow_mul_of_le_mul_rpow`). -/
theorem lintegral_rpow_sum_maximal_le {p q : ℝ} (hq1 : 1 < q) (hqp : q < p) (S : Finset ℕ)
    {g : ℕ → V → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, (∑ j ∈ S, maximal (g j) x ^ q) ^ (p / q) ≤
      dualityConst (finrank ℝ V) p q * ∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ (p / q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hpq0 : p - q ≠ 0 := (sub_pos.2 hqp).ne'
  have hconj : (p / q).HolderConjugate (p / (p - q)) := by
    rw [Real.holderConjugate_iff_eq_conjExponent ((one_lt_div hq0).2 hqp)]
    field_simp
  rcases eq_or_ne (∫⁻ x, (∑ j ∈ S, g j x ^ q) ^ (p / q)) ∞ with hA | hA
  · rw [hA, ENNReal.mul_top (dualityConst_ne_zero hq0 hqp)]
    exact le_top
  have h := ENNReal.le_rpow_mul_of_le_mul_rpow hconj
    (lintegral_rpow_sum_maximal_ne_top hq1 hqp S hg hA)
    (lintegral_rpow_sum_maximal_le_mul hq1 hconj S hg)
  rw [one_div_div] at h
  exact h

/-- **The Fefferman–Stein inequality for `q < p` in integral form** (duality): for
`1 < q < p < ∞` and almost everywhere measurable `g_j : V → [0, ∞]`, in every dimension,
`∫ ‖(M g_j(x))_j‖_{ℓ_q}^p dx ≤ C ∫ ‖(g_j(x))_j‖_{ℓ_q}^p dx` with `C = dualityConst n p q`. The
finite partial sums satisfy `Rd.lintegral_rpow_sum_maximal_le`, and monotone convergence passes
to the series. -/
theorem lintegral_lqNorm_maximal_rpow_le_of_gt {p q : ℝ≥0∞} (hq1 : 1 < q) (hqp : q < p)
    (hp : p ≠ ∞) (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    ∫⁻ x, lqNorm q (fun j => maximal (g j) x) ^ p.toReal ≤
      dualityConst (finrank ℝ V) p.toReal q.toReal *
        ∫⁻ x, lqNorm q (fun j => g j x) ^ p.toReal := by
  have hq : q ≠ ∞ := ne_top_of_lt hqp
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hR : 1 < q.toReal := ENNReal.one_lt_toReal hq1 hq
  have hRP : q.toReal < p.toReal := (ENNReal.toReal_lt_toReal hq hp).2 hqp
  have hu : 0 < p.toReal / q.toReal := div_pos (by linarith) (by linarith)
  have hpow : ∀ a : ℕ → ℝ≥0∞, lqNorm q a ^ p.toReal =
      ⨆ J : ℕ, (∑ j ∈ Finset.range J, a j ^ q.toReal) ^ (p.toReal / q.toReal) := fun a => by
    rw [ENNReal.lqNorm_eq_tsum hq0 hq, ← ENNReal.rpow_mul, one_div_mul_eq_div,
      ENNReal.tsum_eq_iSup_nat]
    have h := (ENNReal.orderIsoRpow _ hu).map_iSup fun J : ℕ =>
      ∑ j ∈ Finset.range J, a j ^ q.toReal
    simpa only [ENNReal.orderIsoRpow_apply] using h
  simp_rw [hpow]
  rw [lintegral_iSup (f := fun J x =>
      (∑ j ∈ Finset.range J, maximal (g j) x ^ q.toReal) ^ (p.toReal / q.toReal))
    (fun J => (Finset.measurable_fun_sum _ fun j _ =>
      (measurable_maximal (g j)).pow_const _).pow_const _)
    fun J J' hJ x => ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hJ))
      hu.le]
  refine iSup_le fun J => (lintegral_rpow_sum_maximal_le hR hRP _ hg).trans
    (mul_le_mul_right (lintegral_mono fun x => ?_) _)
  exact le_iSup (fun J : ℕ => (∑ j ∈ Finset.range J, g j x ^ q.toReal) ^
    (p.toReal / q.toReal)) J

/-! ### The Fefferman–Stein inequality -/

/-- **The Fefferman–Stein inequality for `q = ∞`**: for `1 < p < ∞` and every family
`g_j : V → [0, ∞]`, `‖sup_j M g_j‖_p ≤ C_{n,p}^{1/p} ‖sup_j g_j‖_p`, since
`M g_j ≤ M(sup_k g_k)` for every `j`. -/
theorem feffermanStein_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (g : ℕ → V → ℝ≥0∞) :
    eLpNorm (fun x => lqNorm ∞ (fun j => maximal (g j) x)) p volume ≤
      maximalConst (finrank ℝ V) p.toReal ^ (1 / p.toReal) *
        eLpNorm (fun x => lqNorm ∞ (fun j => g j x)) p volume := by
  simp only [ENNReal.lqNorm_top]
  refine (eLpNorm_mono_eNorm
    (Measurable.iSup fun j => measurable_maximal (g j)).aestronglyMeasurable fun x => ?_).trans
    (eLpNorm_maximal_le (fun y => ⨆ j, g j y) hp1 hp)
  simp only [eNorm_eq_self]
  exact iSup_le fun j => maximal_mono (fun y => le_iSup (fun k => g k y) j) x

/-- **The Fefferman–Stein inequality for `q = p`**: for `1 < p < ∞` and almost everywhere
measurable `g_j : V → [0, ∞]`, `‖(M g_j)_j‖_{L_p(ℓ_p)} ≤ C_{n,p}^{1/p} ‖(g_j)_j‖_{L_p(ℓ_p)}`. -/
theorem feffermanStein_self {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (g : ℕ → V → ℝ≥0∞)
    (hg : ∀ j, AEMeasurable (g j) volume) :
    eLpNorm (fun x => lqNorm p (fun j => maximal (g j) x)) p volume ≤
      maximalConst (finrank ℝ V) p.toReal ^ (1 / p.toReal) *
        eLpNorm (fun x => lqNorm p (fun j => g j x)) p volume :=
  eLpNorm_le_rpow_mul_of_lintegral_le (zero_lt_one.trans hp1).ne' hp
    (measurable_lqNorm_comp (fun _ => measurable_maximal _) p).aemeasurable
    (aemeasurable_lqNorm_comp hg p) (lintegral_lqNorm_maximal_rpow_le hp1 hp hg)

/-- **The Fefferman–Stein inequality for `q < p`**: for `1 < q < p < ∞` and almost everywhere
measurable `g_j : V → [0, ∞]`,
`‖(M g_j)_j‖_{L_p(ℓ_q)} ≤ (dualityConst n p q)^{1/p} ‖(g_j)_j‖_{L_p(ℓ_q)}`. -/
theorem feffermanStein_of_gt {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    (hqp : q < p) (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    eLpNorm (fun x => lqNorm q (fun j => maximal (g j) x)) p volume ≤
      dualityConst (finrank ℝ V) p.toReal q.toReal ^ (1 / p.toReal) *
        eLpNorm (fun x => lqNorm q (fun j => g j x)) p volume :=
  eLpNorm_le_rpow_mul_of_lintegral_le (zero_lt_one.trans hp1).ne' hp
    (measurable_lqNorm_comp (fun _ => measurable_maximal _) q).aemeasurable
    (aemeasurable_lqNorm_comp hg q) (lintegral_lqNorm_maximal_rpow_le_of_gt hq1 hqp hp g hg)

/-- **The Fefferman–Stein inequality for `p < q`**: in dimension `n ≥ 1`, for `1 < p < q < ∞` and
almost everywhere measurable `g_j : V → [0, ∞]`,
`‖(M g_j)_j‖_{L_p(ℓ_q)} ≤ (interpolationConst V p q)^{1/p} ‖(g_j)_j‖_{L_p(ℓ_q)}`. -/
theorem feffermanStein_of_lt [Nontrivial V] {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (hpq : p < q) (hq : q ≠ ∞) (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    eLpNorm (fun x => lqNorm q (fun j => maximal (g j) x)) p volume ≤
      interpolationConst V p.toReal q.toReal ^ (1 / p.toReal) *
        eLpNorm (fun x => lqNorm q (fun j => g j x)) p volume :=
  eLpNorm_le_rpow_mul_of_lintegral_le (zero_lt_one.trans hp1).ne' hp
    (measurable_lqNorm_comp (fun _ => measurable_maximal _) q).aemeasurable
    (aemeasurable_lqNorm_comp hg q) (lintegral_lqNorm_maximal_rpow_le_of_lt hp1 hpq hq g hg)

variable (V) in
/-- The constant of the **Fefferman–Stein inequality**: `1` in dimension `0`, otherwise
`C_{n,p}^{1/p}` for `q = ∞` or `q = p`, `(dualityConst n p q)^{1/p}` for `q < p` and
`(interpolationConst V p q)^{1/p}` for `p < q`. -/
noncomputable def feffermanSteinConst (p q : ℝ≥0∞) : ℝ≥0∞ :=
  if finrank ℝ V = 0 then 1
  else if q = ∞ ∨ q = p then maximalConst (finrank ℝ V) p.toReal ^ (1 / p.toReal)
  else if q < p then dualityConst (finrank ℝ V) p.toReal q.toReal ^ (1 / p.toReal)
  else interpolationConst V p.toReal q.toReal ^ (1 / p.toReal)

/-- `feffermanSteinConst V p q` is finite for `1 < p < ∞` and `1 < q ≤ ∞`. -/
theorem feffermanSteinConst_ne_top {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q) :
    feffermanSteinConst V p q ≠ ∞ := by
  have hP : 1 < p.toReal := ENNReal.one_lt_toReal hp1 hp
  have hnn : (0 : ℝ) ≤ 1 / p.toReal := by positivity
  unfold feffermanSteinConst
  split_ifs with h0 h1 h2
  · exact ENNReal.one_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg hnn (maximalConst_ne_top hP)
  · have hq : q ≠ ∞ := ne_top_of_lt h2
    exact ENNReal.rpow_ne_top_of_nonneg hnn (dualityConst_ne_top
      (ENNReal.one_lt_toReal hq1 hq) ((ENNReal.toReal_lt_toReal hq hp).2 h2))
  · obtain ⟨hq, hqp⟩ := not_or.1 h1
    have hpq : p < q := lt_of_le_of_ne (not_lt.1 h2) (Ne.symm hqp)
    exact ENNReal.rpow_ne_top_of_nonneg hnn
      (interpolationConst_ne_top hP ((ENNReal.toReal_lt_toReal hp hq).2 hpq))

/-- **The Fefferman–Stein inequality**: for `1 < p < ∞`, `1 < q ≤ ∞` and almost everywhere
measurable `g_j : V → [0, ∞]`, `j ∈ ℕ`,
`‖ x ↦ ‖(M g_j(x))_j‖_{ℓ_q} ‖_p ≤ C ‖ x ↦ ‖(g_j(x))_j‖_{ℓ_q} ‖_p` with the explicit constant
`C = feffermanSteinConst V p q`. In dimension `0` the maximal function is the identity; otherwise
the cases `q = ∞`, `q = p`, `q < p` (duality) and `p < q` (interpolation) are
`Rd.feffermanStein_top`, `Rd.feffermanStein_self`, `Rd.feffermanStein_of_gt` and
`Rd.feffermanStein_of_lt`. The case `q = 2` is the one behind the Littlewood–Paley description
of the spaces `H^s_p = F^s_{p,2}`. -/
theorem feffermanStein {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    (g : ℕ → V → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    eLpNorm (fun x => lqNorm q (fun j => maximal (g j) x)) p volume ≤
      feffermanSteinConst V p q * eLpNorm (fun x => lqNorm q (fun j => g j x)) p volume := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : finrank ℝ V = 0 := Module.finrank_zero_iff.2 hV
    simp only [feffermanSteinConst, h0, ↓reduceIte, one_mul, maximal_eq_self_of_subsingleton]
    exact le_rfl
  have h0 : finrank ℝ V ≠ 0 := Module.finrank_pos.ne'
  rcases eq_or_ne q ∞ with rfl | hq
  · simpa only [feffermanSteinConst, h0, ↓reduceIte, true_or] using feffermanStein_top hp1 hp g
  rcases eq_or_ne q p with rfl | hqp
  · simpa only [feffermanSteinConst, h0, ↓reduceIte, or_true] using
      feffermanStein_self hp1 hp g hg
  have hor : ¬ (q = ∞ ∨ q = p) := not_or.2 ⟨hq, hqp⟩
  rcases lt_or_gt_of_ne hqp with hlt | hgt
  · simpa only [feffermanSteinConst, h0, hor, hlt, ↓reduceIte] using
      feffermanStein_of_gt hp1 hp hq1 hlt g hg
  · simpa only [feffermanSteinConst, h0, hor, not_lt.2 hgt.le, ↓reduceIte] using
      feffermanStein_of_lt hp1 hp hgt hq g hg

end Rd
