/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientFiber
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientProjection
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakLower
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTailLimit
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Global weak convergence of the gradients in `prop:forced-limit`

The compactness step of `prop:forced-limit` gives weak `L²` convergence of the
forced regularized gradients on the compact sets of an exhaustion of the slab
`ℝ³ × (0,T)`. With the uniform dissipation bound of `lem:forced-energy-bounds`
on the slab, the weak limit is square integrable on the whole slab, and each
coordinate converges weakly against every square-integrable test on the slab.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- In a real inner product space, pairings of a bounded sequence converge
against a limit of tests when they converge against each test of the
approximating sequence. -/
private theorem forcedLerayLimitGradient_tendsto_inner_of_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ℕ → H) (x₀ : H) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hx₀ : ‖x₀‖ ≤ C)
    (y : ℕ → H) (w : H) (hy : Tendsto y atTop (𝓝 w))
    (hconv : ∀ m, Tendsto (fun n => inner ℝ (x n) (y m)) atTop
      (𝓝 (inner ℝ x₀ (y m)))) :
    Tendsto (fun n => inner ℝ (x n) w) atTop (𝓝 (inner ℝ x₀ w)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx₀
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (3 * (C + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hy δ hδ
  have hym : ‖y M - w‖ < δ := by
    simpa [dist_eq_norm] using hM M le_rfl
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv M) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq] at h1 ⊢
  have hsplit : inner ℝ (x n) w - inner ℝ x₀ w =
      inner ℝ (x n) (w - y M) +
        (inner ℝ (x n) (y M) - inner ℝ x₀ (y M)) +
        inner ℝ x₀ (y M - w) := by
    rw [inner_sub_right, inner_sub_right]
    ring
  have hwy : ‖w - y M‖ < δ := by rwa [norm_sub_rev]
  have ha : |inner ℝ (x n) (w - y M)| ≤ C * δ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hx n) hwy.le (norm_nonneg _) hC)
  have hb : |inner ℝ x₀ (y M - w)| ≤ C * δ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hx₀ hym.le (norm_nonneg _) hC)
  have hCδ : C * δ < ε / 3 := by
    have hlt : C < C + 1 := lt_add_one C
    rw [hδdef]
    have hpos : 0 < C + 1 := by positivity
    calc C * (ε / (3 * (C + 1))) = (ε / 3) * (C / (C + 1)) := by
          field_simp
      _ < (ε / 3) * 1 := by
          apply mul_lt_mul_of_pos_left _ (by positivity)
          rw [div_lt_one hpos]
          exact hlt
      _ = ε / 3 := mul_one _
  rw [hsplit]
  calc |inner ℝ (x n) (w - y M) + (inner ℝ (x n) (y M) - inner ℝ x₀ (y M)) +
        inner ℝ x₀ (y M - w)|
      ≤ |inner ℝ (x n) (w - y M)| + |inner ℝ (x n) (y M) - inner ℝ x₀ (y M)| +
          |inner ℝ x₀ (y M - w)| := abs_add_three _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        linarith only [ha, hb, h1, hCδ]
    _ = ε := by ring

/-- The `L²` seminorm is at most `B^{1/2}` when the integral of the square of
the norm is at most `B`. -/
private theorem forcedLerayLimitGradient_eLpNorm_le_of_lintegral
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {ν : Measure α}
    (f : α → E) (hf : AEStronglyMeasurable f ν) (B : ℝ≥0∞)
    (hB : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ≤ B) :
    eLpNorm f 2 ν ≤ B ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hB (by norm_num)

/-- Conversely, an `L²` seminorm bound `B^{1/2}` bounds the integral of the
square of the norm by `B`. -/
private theorem forcedLerayLimitGradient_lintegral_le_of_eLpNorm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {ν : Measure α}
    (f : α → E) (hf : AEStronglyMeasurable f ν) (B : ℝ≥0∞)
    (hB : eLpNorm f 2 ν ≤ B ^ (1 / 2 : ℝ)) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ≤ B := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf] at hB
  simp only [ENNReal.toReal_ofNat] at hB
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).1 hB

/-- The coordinate `(i, j)` of the gradient carrier, as a continuous linear
functional. -/
@[expose]
def forcedLerayLimitGradientCoord (i j : Fin 3) :
    CompactnessGradientFiber →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp
    (PiLp.proj 2 (fun _ : Fin 3 => L2Vec3) i)

private theorem forcedLerayLimitGradientCoord_apply (i j : Fin 3)
    (y : CompactnessGradientFiber) :
    forcedLerayLimitGradientCoord i j y = y i j := rfl

private theorem forcedLerayLimitGradientCoord_toFiber (i j : Fin 3)
    (A : Fin 3 → Vec3) :
    forcedLerayLimitGradientCoord i j (toCompactnessGradientFiber A) = A i j := rfl

private theorem forcedLerayLimitGradient_abs_coord_le (i j : Fin 3)
    (y : CompactnessGradientFiber) : |y i j| ≤ ‖y‖ := by
  calc |y i j| = ‖(y i) j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖y i‖ := PiLp.norm_apply_le (y i) j
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i

/-- The coordinates of the gradient limit, arranged as a matrix field, have
sup norm at most the Hilbert norm of the carrier. -/
private theorem forcedLerayLimitGradient_matrix_norm_le
    (y : CompactnessGradientFiber) :
    ‖(fun (i j : Fin 3) => y i j : Fin 3 → Vec3)‖ ≤ ‖y‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => ?_
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact forcedLerayLimitGradient_abs_coord_le i j y

/-- The pairing of two square-integrable scalar fields is the integral of
their product. -/
private theorem forcedLerayLimitGradient_inner_toLp
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (f g : α → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, Real.inner_apply]

/-- The global gradient clause of `prop:forced-limit` on one slab
`ℝ³ × (0,T)`: weak `L²` convergence of the gradients on the members of an
exhaustion of the slab, with a uniform bound on the slab, gives a
square-integrable limit on the slab and weak convergence of every coordinate
against every square-integrable test on the slab. The limit is the matrix
field of the local weak limit `G`. -/
theorem forcedLerayLimit_globalGradient_outputs
    (T : ℝ)
    (Dseq : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (G : Vec3 × ℝ → CompactnessGradientFiber)
    (K : ℕ → Set (Vec3 × ℝ))
    (hKsubset : ∀ m, K m ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    (hKcover : AECover
      ((volume : Measure (Vec3 × ℝ)).restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) atTop K)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hDenergy : ∀ n,
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖toCompactnessGradientFiber (Dseq n z)‖ₑ ^ (2 : ℝ)) ≤ B)
    (hlocal : ∀ m,
      ∃ hD : ∀ n, MemLp
        (fun z => toCompactnessGradientFiber (Dseq n z)) 2
        (volume.restrict (K m)),
      ∃ hG : MemLp G 2 (volume.restrict (K m)),
      ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict (K m)),
        Tendsto (fun n => inner ℝ
          ((hD n).toLp (fun z => toCompactnessGradientFiber (Dseq n z))) w)
          atTop (nhds (inner ℝ (hG.toLp G) w))) :
    AEStronglyMeasurable (fun z (i j : Fin 3) => G z i j)
        ((volume : Measure (Vec3 × ℝ)).restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      MemLp (fun z (i j : Fin 3) => G z i j) 2
        ((volume : Measure (Vec3 × ℝ)).restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∀ i j, ∀ w : Vec3 × ℝ → ℝ,
        MemLp w 2 ((volume : Measure (Vec3 × ℝ)).restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
        Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          Dseq n z i j * w z) atTop
          (nhds (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            G z i j * w z))) := by
  classical
  set S : Set (Vec3 × ℝ) := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) with hSdef
  set μ : Measure (Vec3 × ℝ) := (volume : Measure (Vec3 × ℝ)).restrict S with hμdef
  have hSmeas : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  have hKmeas : ∀ m, MeasurableSet (K m) := hKcover.measurableSet
  -- the slab agrees almost everywhere with the union of the exhaustion
  have hSU : S =ᵐ[(volume : Measure (Vec3 × ℝ))] ⋃ m, K m := by
    have hUS : (⋃ m, K m) ⊆ S := iUnion_subset hKsubset
    have hae : ∀ᵐ z ∂μ, z ∈ ⋃ m, K m := by
      filter_upwards [hKcover.ae_eventually_mem] with z hz
      obtain ⟨m, hm⟩ := hz.exists
      exact mem_iUnion.2 ⟨m, hm⟩
    have hae' : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), z ∈ S → z ∈ ⋃ m, K m :=
      (ae_restrict_iff' hSmeas).1 hae
    refine (EventuallyLE.antisymm ?_ (Eventually.of_forall fun z hz => hUS hz))
    filter_upwards [hae'] with z hz
    exact hz
  have hμU : μ = (volume : Measure (Vec3 × ℝ)).restrict (⋃ m, K m) :=
    Measure.restrict_congr_set hSU
  have hrestrictK : ∀ m, μ.restrict (K m) = (volume : Measure (Vec3 × ℝ)).restrict (K m) := by
    intro m
    rw [hμdef, Measure.restrict_restrict (hKmeas m),
      inter_eq_left.2 (hKsubset m)]
  -- measurability on the slab from measurability on each member
  have hglobalMeas : ∀ {E : Type} [NormedAddCommGroup E] (F : Vec3 × ℝ → E),
      (∀ m, AEStronglyMeasurable F ((volume : Measure (Vec3 × ℝ)).restrict (K m))) →
      AEStronglyMeasurable F μ := by
    intro E _ F hF
    rw [hμU]
    exact aestronglyMeasurable_iUnion_iff.2 hF
  choose hD hG hweak using hlocal
  have hGmeas : AEStronglyMeasurable G μ :=
    hglobalMeas G fun m => (hG m).aestronglyMeasurable
  have hDmeas : ∀ n, AEStronglyMeasurable
      (fun z => toCompactnessGradientFiber (Dseq n z)) μ :=
    fun n => hglobalMeas _ fun m => (hD m n).aestronglyMeasurable
  -- the uniform bound on each member, and its transfer to the weak limit
  have hDmember : ∀ m n,
      (∫⁻ z in K m, ‖toCompactnessGradientFiber (Dseq n z)‖ₑ ^ (2 : ℝ) ∂μ) ≤ B := by
    intro m n
    refine le_trans ?_ (hDenergy n)
    rw [hrestrictK m]
    exact lintegral_mono_set (hKsubset m)
  have hGmember : ∀ m,
      (∀ n, (∫⁻ z in K m, ‖toCompactnessGradientFiber (Dseq n z)‖ₑ ^ (2 : ℝ) ∂μ) ≤ B) →
      (∫⁻ z in K m, ‖G z‖ₑ ^ (2 : ℝ) ∂μ) ≤ B := by
    intro m hsrc
    rw [hrestrictK m]
    have hbound : ∀ n, eLpNorm (fun z => toCompactnessGradientFiber (Dseq n z)) 2
        ((volume : Measure (Vec3 × ℝ)).restrict (K m)) ≤ B ^ (1 / 2 : ℝ) := by
      intro n
      apply forcedLerayLimitGradient_eLpNorm_le_of_lintegral _ (hD m n).aestronglyMeasurable
      have h := hsrc n
      rwa [hrestrictK m] at h
    have hlim := eLpNorm_le_of_weak_l2_bounded
      (fun n z => toCompactnessGradientFiber (Dseq n z)) ((hG m).toLp G) (hD m)
      (hweak m) (B ^ (1 / 2 : ℝ))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne) hbound
    have hGeq : eLpNorm (fun z => ((hG m).toLp G) z) 2
        ((volume : Measure (Vec3 × ℝ)).restrict (K m)) =
        eLpNorm G 2 ((volume : Measure (Vec3 × ℝ)).restrict (K m)) :=
      eLpNorm_congr_ae (hG m).coeFn_toLp
    rw [hGeq] at hlim
    exact forcedLerayLimitGradient_lintegral_le_of_eLpNorm G (hG m).aestronglyMeasurable B hlim
  have hGslab : (∫⁻ z in S, ‖G z‖ₑ ^ (2 : ℝ)) ≤ B :=
    lerayLimit_lintegral_bound_of_compactExhaustion (μ := volume) S K hKcover
      (fun n z => toCompactnessGradientFiber (Dseq n z)) G B hDmember hGmember
      hGmeas.aemeasurable
  have hGL2 : MemLp G 2 μ := by
    exact (forcedLerayLimitGradient_eLpNorm_le_of_lintegral G hGmeas B hGslab).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)
  have hDL2 : ∀ n, MemLp (fun z => toCompactnessGradientFiber (Dseq n z)) 2 μ := by
    intro n
    exact (forcedLerayLimitGradient_eLpNorm_le_of_lintegral _ (hDmeas n) B
      (hDenergy n)).trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)
  -- the matrix field of the limit
  have hPhi : Continuous (fun (y : CompactnessGradientFiber) (i j : Fin 3) => y i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (forcedLerayLimitGradientCoord i j).continuous
  have hDuMeas : AEStronglyMeasurable (fun z (i j : Fin 3) => G z i j) μ :=
    hPhi.comp_aestronglyMeasurable hGmeas
  have hDuL2 : MemLp (fun z (i j : Fin 3) => G z i j) 2 μ :=
    hGL2.of_le hDuMeas (Eventually.of_forall fun z =>
      forcedLerayLimitGradient_matrix_norm_le (G z))
  refine ⟨hDuMeas, hDuL2, ?_⟩
  intro i j w hw
  let L := forcedLerayLimitGradientCoord i j
  -- the scalar coordinate fields on the slab
  have hcoordD : ∀ n, MemLp (fun z => Dseq n z i j) 2 μ := by
    intro n
    have h := (hDL2 n).continuousLinearMap_comp L
    simpa [L, forcedLerayLimitGradientCoord_toFiber] using h
  have hcoordG : MemLp (fun z => G z i j) 2 μ := by
    have h := hGL2.continuousLinearMap_comp L
    simpa [L, forcedLerayLimitGradientCoord_apply] using h
  set C : ℝ := (B ^ (1 / 2 : ℝ)).toReal with hCdef
  have hBhalf : B ^ (1 / 2 : ℝ) ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne).ne
  have hnormD : ∀ n, ‖(hcoordD n).toLp (fun z => Dseq n z i j)‖ ≤ C := by
    intro n
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_mono hBhalf ?_
    refine le_trans (eLpNorm_mono_ae_real (g := fun z => ‖toCompactnessGradientFiber (Dseq n z)‖)
      (hcoordD n).aestronglyMeasurable (Eventually.of_forall fun z => ?_)) ?_
    · exact (Real.norm_eq_abs _).le.trans
        (forcedLerayLimitGradient_abs_coord_le i j (toCompactnessGradientFiber (Dseq n z)))
    · refine le_trans (le_of_eq ?_) (forcedLerayLimitGradient_eLpNorm_le_of_lintegral _
        (hDmeas n) B (hDenergy n))
      exact eLpNorm_norm _ (hDmeas n)
  have hnormG : ‖hcoordG.toLp (fun z => G z i j)‖ ≤ C := by
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_mono hBhalf ?_
    refine le_trans (eLpNorm_mono_ae_real (g := fun z => ‖G z‖) hcoordG.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)) ?_
    · exact (Real.norm_eq_abs _).le.trans (forcedLerayLimitGradient_abs_coord_le i j (G z))
    · refine le_trans (le_of_eq ?_)
        (forcedLerayLimitGradient_eLpNorm_le_of_lintegral G hGmeas B hGslab)
      exact eLpNorm_norm _ hGmeas
  -- the truncated tests
  have hwK : ∀ m, MemLp ((K m).indicator w) 2 μ := fun m => hw.indicator (hKmeas m)
  have htail : Tendsto (fun m => eLpNorm ((K m).indicator w - w) 2 μ) atTop (𝓝 0) := by
    have hdiff : ∀ m, (K m).indicator w - w = -((K m)ᶜ.indicator w) := by
      intro m
      funext z
      by_cases hz : z ∈ K m <;> simp [hz]
    have hlin : Tendsto (fun m => ∫⁻ z, ‖(K m)ᶜ.indicator w z‖ₑ ^ (2 : ℝ) ∂μ)
        atTop (𝓝 0) := by
      have hlim0 : (∫⁻ _z : Vec3 × ℝ, (0 : ℝ≥0∞) ∂μ) = 0 := lintegral_zero
      rw [← hlim0]
      refine tendsto_lintegral_of_dominated_convergence' (fun z => ‖w z‖ₑ ^ (2 : ℝ))
        (fun m => ((hw.aestronglyMeasurable.indicator (hKmeas m).compl).enorm.pow_const _))
        (fun m => Eventually.of_forall fun z => ?_) ?_ ?_
      · by_cases hz : z ∈ (K m)ᶜ
        · simp [hz]
        · simp only [indicator_of_notMem hz, enorm_zero]
          exact (ENNReal.zero_rpow_of_pos (by norm_num)).le.trans bot_le
      · have hfin := hw.eLpNorm_lt_top
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hw.aestronglyMeasurable] at hfin
        simp only [ENNReal.toReal_ofNat] at hfin
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hfin |>.ne
      · filter_upwards [hKcover.ae_eventually_mem] with z hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hz] with m hm
        simp [hm, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrpow : Tendsto (fun m =>
        (∫⁻ z, ‖(K m)ᶜ.indicator w z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have hc := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlin
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using hc
    refine hrpow.congr' (Eventually.of_forall fun m => ?_)
    dsimp only
    rw [hdiff m, eLpNorm_neg,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (hw.aestronglyMeasurable.indicator (hKmeas m).compl)]
    simp only [ENNReal.toReal_ofNat]
  have hy : Tendsto (fun m => (hwK m).toLp ((K m).indicator w)) atTop (𝓝 (hw.toLp w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ m, ‖(hwK m).toLp ((K m).indicator w) - hw.toLp w‖ =
        (eLpNorm ((K m).indicator w - w) 2 μ).toReal := by
      intro m
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    simp only [hnorm]
    have hc := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
    simpa [Function.comp_def] using hc
  -- convergence against each truncated test, from the local weak limits
  have hconv : ∀ m, Tendsto
      (fun n => inner ℝ ((hcoordD n).toLp (fun z => Dseq n z i j))
        ((hwK m).toLp ((K m).indicator w)))
      atTop (𝓝 (inner ℝ (hcoordG.toLp (fun z => G z i j))
        ((hwK m).toLp ((K m).indicator w)))) := by
    intro m
    have hrewrite : ∀ F : Vec3 × ℝ → ℝ,
        (∫ z, F z * (K m).indicator w z ∂μ) =
          ∫ z, F z * w z ∂((volume : Measure (Vec3 × ℝ)).restrict (K m)) := by
      intro F
      have hind : (fun z => F z * (K m).indicator w z) =
          (K m).indicator (fun z => F z * w z) := by
        funext z
        by_cases hz : z ∈ K m <;> simp [hz]
      rw [hind, integral_indicator (hKmeas m), hrestrictK m]
    simp only [forcedLerayLimitGradient_inner_toLp, hrewrite]
    have hwKm : MemLp w 2 ((volume : Measure (Vec3 × ℝ)).restrict (K m)) := by
      have h := hw.restrict (K m)
      rwa [hrestrictK m] at h
    have hloc := weak_l2_scalar_integral_of_fiber_weak L
      (fun n z => toCompactnessGradientFiber (Dseq n z)) ((hG m).toLp G) (hD m)
      (hweak m) w hwKm
    have hGeq : (∫ z, L (((hG m).toLp G) z) * w z
        ∂((volume : Measure (Vec3 × ℝ)).restrict (K m))) =
        ∫ z, G z i j * w z ∂((volume : Measure (Vec3 × ℝ)).restrict (K m)) := by
      apply integral_congr_ae
      filter_upwards [(hG m).coeFn_toLp] with z hz
      rw [hz]
      rfl
    rw [← hGeq]
    exact hloc
  have hmain := forcedLerayLimitGradient_tendsto_inner_of_approx
    (fun n => (hcoordD n).toLp (fun z => Dseq n z i j))
    (hcoordG.toLp (fun z => G z i j)) C hnormD hnormG
    (fun m => (hwK m).toLp ((K m).indicator w)) (hw.toLp w) hy hconv
  simp only [forcedLerayLimitGradient_inner_toLp] at hmain
  exact hmain

end CKN.Leray

end
