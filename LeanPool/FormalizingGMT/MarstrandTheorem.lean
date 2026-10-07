/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.TangentMeasures.TangentMeasures
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `s`-uniform measures and Marstrand's theorem

Mattila, *Geometry of sets and measures in Euclidean spaces*, Chapter 14, uniform measures
and Marstrand's theorem.:

* Definition 14.8: `IsSUniform`;
* Corollary 14.9: `mattila_14_9`;
* Theorem 14.10 (Marstrand's theorem): `mattila_14_10`;
* Theorem 14.11: `mattila_14_11`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-! ## Definition 14.8 -/

/-- **Mattila, Definition 14.8.** Let `s` be a positive number. A non-zero Radon measure `ν` on
`ℝⁿ` is *`s`-uniform* if there is a positive number `c` such that
`0 < ν (B (x, r)) = c r ^ s < ∞` for `x ∈ spt ν` and `0 < r < ∞`. -/
def IsSUniform (s : ℝ) (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  0 < s ∧ ν.Regular ∧ ν ≠ 0 ∧ ∃ c : ℝ, 0 < c ∧
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r → ν (closedBall x r) = ENNReal.ofReal (c * r ^ s)

/-- The set `A` of Mattila, Corollary 14.9 and Theorem 14.10: the points `a` at which the
`s`-dimensional density `Θ^s(μ, a)` exists and is positive and finite. -/
def positiveFiniteDensityExistsSet (s : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {a | HasDensity μ.toOuterMeasure s a ∧ 0 < dimensionalDensity μ.toOuterMeasure s a ∧
    dimensionalDensity μ.toOuterMeasure s a < ∞}

/-! ## Auxiliary results -/

namespace SUniformAux

/-- A covering comparison: if `μ₁ (B (x, r)) ≤ K μ₂ (B (x, r))` for arbitrarily small `r` at each
point `x ∈ S`, then `μ₁ S ≤ K μ₂ S`. (A consequence of the Besicovitch covering theorem.) -/
lemma measure_le_mul_of_closedBall_le {μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin n))} [SFinite μ₁]
    [μ₂.OuterRegular] {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (h : ∀ x ∈ S, ∀ δ > 0, ∃ r ∈ Ioo 0 δ, μ₁ (closedBall x r) ≤ K * μ₂ (closedBall x r)) :
    μ₁ S ≤ K * μ₂ S := by
  have hU : ∀ U, S ⊆ U → IsOpen U → μ₁ S ≤ K * μ₂ U := by
    intro U hSU hUo
    have hR : ∀ x ∈ S, ∃ ε > 0, ball x ε ⊆ U := fun x hx ↦ Metric.isOpen_iff.1 hUo x (hSU hx)
    choose! R hRpos hRU using hR
    obtain ⟨t, r, htc, htS, hr, hnull, hdisj⟩ :=
      Besicovitch.exists_disjoint_closedBall_covering_ae μ₁
        (fun x ↦ {ρ | μ₁ (closedBall x ρ) ≤ K * μ₂ (closedBall x ρ)}) S
        (fun x hx δ hδ ↦ by
          obtain ⟨ρ, hρ, hρK⟩ := h x hx δ hδ
          exact ⟨ρ, hρK, hρ⟩) R hRpos
    have hsub : ⋃ x ∈ t, closedBall x (r x) ⊆ U := by
      refine iUnion₂_subset fun x hx ↦ ?_
      exact (closedBall_subset_ball (hr x hx).2.2).trans (hRU x (htS hx))
    calc μ₁ S ≤ μ₁ (S \ ⋃ x ∈ t, closedBall x (r x)) + μ₁ (⋃ x ∈ t, closedBall x (r x)) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro y hy
          by_cases hy' : y ∈ ⋃ x ∈ t, closedBall x (r x)
          · exact Or.inr hy'
          · exact Or.inl ⟨hy, hy'⟩
      _ = ∑' x : t, μ₁ (closedBall x (r x)) := by
          rw [hnull, zero_add, measure_biUnion htc hdisj fun _ _ ↦ measurableSet_closedBall]
      _ ≤ ∑' x : t, K * μ₂ (closedBall x (r x)) := ENNReal.tsum_le_tsum fun x ↦ (hr x x.2).1
      _ = K * μ₂ (⋃ x ∈ t, closedBall x (r x)) := by
          rw [ENNReal.tsum_mul_left, measure_biUnion htc hdisj fun _ _ ↦ measurableSet_closedBall]
      _ ≤ K * μ₂ U := by gcongr
  rw [mul_comm, ← ENNReal.div_le_iff hK0 hKtop, Set.measure_eq_iInf_isOpen S μ₂]
  refine le_iInf fun U ↦ le_iInf fun hSU ↦ le_iInf fun hUo ↦ ?_
  rw [ENNReal.div_le_iff hK0 hKtop, mul_comm]
  exact hU U hSU hUo

/-- The Lebesgue measure of a closed ball in `ℝⁿ`. -/
lemma volume_closedBall_eq (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) =
      ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin]

/-- Tangent measures of an `s`-uniform measure at points of its support are `s`-uniform and
have `0` in their support. -/
lemma isSUniform_of_isTangentMeasure {s : ℝ} {ν lam : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ ν.support)
    (htan : IsTangentMeasure ν lam a) :
    IsSUniform s lam ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ lam.support := by
  obtain ⟨hs, hreg, -, c, hc, hball⟩ := hν
  have hbounds : ∀ y ∈ ν.support, ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ENNReal.ofReal (1 * c * ρ ^ s) ≤ ν (closedBall y ρ) ∧
        ν (closedBall y ρ) ≤ ENNReal.ofReal (c * ρ ^ s) := by
    intro y hy ρ hρ _
    rw [hball y hy ρ hρ, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨-, htan'⟩ := mattila_14_7_4 hc one_pos one_pos ν hreg hbounds a ha
  obtain ⟨c', hc'0, hc'top, hc'⟩ := htan' lam htan
  have hdoub := limsup_ball_ratio_lt_top_of_uniform hc one_pos one_pos ha
    (fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2) (fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1)
  refine ⟨⟨hs, htan.1, htan.2.1, c'.toReal, ENNReal.toReal_pos hc'0.ne' hc'top, ?_⟩,
    zero_mem_support_of_isTangentMeasure ν lam hreg a ha hdoub htan⟩
  intro x hx r hr
  obtain ⟨h1, h2⟩ := hc' x hx r hr
  rw [ENNReal.ofReal_one, one_mul] at h1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc'top]
  exact le_antisymm h2 h1

/-- An `s`-uniform measure has tangent measures at every point of its support. -/
lemma exists_isTangentMeasure {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ ν.support) :
    ∃ lam, IsTangentMeasure ν lam a := by
  obtain ⟨-, hreg, -, c, hc, hball⟩ := hν
  have hbounds : ∀ y ∈ ν.support, ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ENNReal.ofReal (1 * c * ρ ^ s) ≤ ν (closedBall y ρ) ∧
        ν (closedBall y ρ) ≤ ENNReal.ofReal (c * ρ ^ s) := by
    intro y hy ρ hρ _
    rw [hball y hy ρ hρ, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  exact (mattila_14_7_4 hc one_pos one_pos ν hreg hbounds a ha).1

/-- There is no `s`-uniform measure on `ℝⁿ` with `s > n`. -/
lemma not_isSUniform_of_lt {s : ℝ} (hs : (n : ℝ) < s) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    ¬ IsSUniform s ν := by
  rintro ⟨hs, hreg, hne, c, hc, hball⟩
  let _ : ν.Regular := hreg
  apply hne
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  have hR : ∀ R : ℝ, ν (ball 0 R) = 0 := by
    intro R
    have hfinvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) R) ≠ ∞ := measure_ball_lt_top.ne
    have hle : ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
        ν (ball 0 R ∩ ν.support) ≤ ε * volume (ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
      intro ε hε0 hεtop
      refine (measure_le_mul_of_closedBall_le hε0 hεtop _ ?_).trans
        (by gcongr; exact inter_subset_left)
      intro x hx δ hδ
      have hεω : 0 < (ε * ω).toReal :=
        ENNReal.toReal_pos (mul_ne_zero hε0 hω0) (ENNReal.mul_ne_top hεtop hωtop)
      have htend : Tendsto (fun r : ℝ ↦ c * r ^ (s - n)) (𝓝[>] 0) (𝓝 0) := by
        have h := (Real.continuousAt_rpow_const 0 (s - n) (Or.inr (by linarith))).tendsto
        rw [Real.zero_rpow (by linarith)] at h
        simpa using (h.mono_left nhdsWithin_le_nhds).const_mul c
      have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), c * r ^ (s - n) < (ε * ω).toReal ∧ r ∈ Ioo 0 δ :=
        (htend.eventually (gt_mem_nhds hεω)).and (Ioo_mem_nhdsGT hδ)
      obtain ⟨r, hr1, hr2⟩ := hev.exists
      refine ⟨r, hr2, ?_⟩
      rw [hball x hx.2 r hr2.1, volume_closedBall_eq x hr2.1.le]
      have hle' : c * r ^ s ≤ (ε * ω).toReal * r ^ n := by
        have : r ^ s = r ^ (s - n) * r ^ n := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hr2.1]; ring_nf
        rw [this, ← mul_assoc]
        have : (0 : ℝ) ≤ r ^ n := by have := hr2.1.le; positivity
        gcongr
      calc ENNReal.ofReal (c * r ^ s) ≤ ENNReal.ofReal ((ε * ω).toReal * r ^ n) :=
            ENNReal.ofReal_le_ofReal hle'
        _ = ε * (ENNReal.ofReal (r ^ n) * ω) := by
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (ENNReal.mul_ne_top hεtop hωtop)]
            ring
    have h0 : ν (ball 0 R ∩ ν.support) = 0 := by
      have htend : Tendsto (fun k : ℕ ↦ (k : ℝ≥0∞)⁻¹ *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) R)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hfinvol)
      refine le_antisymm (ge_of_tendsto htend ?_) (by simp)
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact hle _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
        (ENNReal.inv_ne_top.2 (by exact_mod_cast (show k ≠ 0 by omega)))
    rwa [measure_inter_conull Measure.measure_compl_support] at h0
  have hsub : (univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ ⋃ k : ℕ, ball 0 ((k : ℝ) + 1) := by
    intro x _
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨k, by simp only [mem_ball]; linarith⟩
  exact Measure.measure_univ_eq_zero.mp
    (le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null fun k ↦ hR _)) (by simp))

/-- An open set `G` is `λ`-null for a tangent measure `λ ∈ Tan (μ, a)` as soon as, at all small
scales `r`, the blow-up `T_{a,r}` maps no point of `spt μ` into `G`. (This uses the lower
semicontinuity of weak limits on open sets, Theorem 1.24 (2) in Mattila.) -/
lemma measure_open_eq_zero_of_isTangentMeasure {μ lam : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) {a : EuclideanSpace ℝ (Fin n)} (htan : IsTangentMeasure μ lam a)
    {G : Set (EuclideanSpace ℝ (Fin n))} (hG : IsOpen G)
    (hsmall : ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → ∀ z ∈ μ.support, blowUpMap a r z ∉ G) :
    lam G = 0 := by
  obtain ⟨ρ, hρ, hsm⟩ := hsmall
  obtain ⟨hlam, -, r, c, hr, -, hcfin, hr0, hconv⟩ := htan
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ lam
    (fun i ↦ regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)) hlam).mp hconv
  have hopen := hb.2 G hG
  have hev : ∀ᶠ k in atTop, (c k • μ.map (blowUpMap a (r k))) G = (fun _ ↦ (0 : ℝ≥0∞)) k := by
    filter_upwards [hr0.eventually (gt_mem_nhds hρ)] with k hk
    rw [Measure.smul_apply, Measure.map_apply (measurable_blowUpMap a _) hG.measurableSet,
      smul_eq_mul, measure_eq_zero_of_disjoint_support (V := blowUpMap a (r k) ⁻¹' G)
        (fun y hy hys ↦ hsm (r k) (hr k) hk y hys hy), mul_zero]
  have hlim : liminf (fun k ↦ (c k • μ.map (blowUpMap a (r k))) G) atTop = 0 := by
    rw [liminf_congr hev, liminf_const]
  exact le_antisymm (hopen.trans hlim.le) (by simp)

/-- If the support of an `s`-uniform measure is not all of `ℝⁿ`, then it has an `s`-uniform
tangent measure `λ` with `0 ∈ spt λ ⊆ {x | 0 ≤ x ⬝ e}` for some `e ≠ 0`. -/
lemma exists_halfSpace {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : IsSUniform s ν)
    (hspt : ν.support ≠ univ) :
    ∃ (e : EuclideanSpace ℝ (Fin n)) (lam : Measure (EuclideanSpace ℝ (Fin n))),
      e ≠ 0 ∧ IsSUniform s lam ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ lam.support ∧
      lam.support ⊆ {x | 0 ≤ inner ℝ x e} := by
  obtain ⟨-, hreg, hne, -⟩ := id hν
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).1 hspt
  have hsptne : ν.support.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    apply hne
    have h0 := Measure.measure_compl_support (μ := ν)
    rw [h, compl_empty] at h0
    exact Measure.measure_univ_eq_zero.mp h0
  obtain ⟨y, hy, hdist⟩ := Measure.isClosed_support.exists_infDist_eq_dist hsptne z
  have hd : 0 < dist z y := by
    rw [← hdist]
    exact (Measure.isClosed_support.notMem_iff_infDist_pos hsptne).1 hz
  have hhole : ∀ p, dist p z < dist z y → p ∉ ν.support := by
    intro p hp
    apply Metric.notMem_of_dist_lt_infDist (x := z)
    rw [hdist, dist_comm]
    exact hp
  set e := y - z with he_def
  have hnorm_e : ‖e‖ = dist z y := by rw [he_def, ← dist_eq_norm, dist_comm]
  have he : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm_e
    linarith
  obtain ⟨lam, htan⟩ := exists_isTangentMeasure hν hy
  obtain ⟨hlam, h0⟩ := isSUniform_of_isTangentMeasure hν hy htan
  refine ⟨e, lam, he, hlam, h0, ?_⟩
  intro x hx
  by_contra hneg
  simp only [mem_ofPred_eq, not_le] at hneg
  set η := -inner ℝ x e with hη
  have hηpos : 0 < η := by linarith
  have henorm : 0 < ‖e‖ := norm_pos_iff.2 he
  set ε := η / (2 * ‖e‖) with hε
  have hεpos : 0 < ε := by positivity
  set M := ‖x‖ + ε with hM
  have hMnn : 0 ≤ M := by positivity
  have hzero : lam (ball x ε) = 0 := by
    refine measure_open_eq_zero_of_isTangentMeasure hreg htan isOpen_ball
      ⟨η / (M ^ 2 + 1), by positivity, fun r hr hrρ p hp hpG ↦ ?_⟩
    set w := blowUpMap y r p with hw
    have hp_eq : p - z = e + r • w := by
      rw [hw, blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, he_def]
      abel
    have hwx : ‖w - x‖ < ε := by rw [← dist_eq_norm]; exact hpG
    have hwM : ‖w‖ ≤ M := by
      have := norm_le_norm_add_norm_sub' w x
      rw [hM]
      linarith
    have hinner : inner ℝ e w ≤ -η / 2 := by
      have h1 : inner ℝ e w = inner ℝ x e + inner ℝ (w - x) e := by
        have k1 := inner_sub_left (𝕜 := ℝ) w x e
        have k2 := real_inner_comm e w
        linarith
      have h2 : inner ℝ (w - x) e ≤ ‖w - x‖ * ‖e‖ := real_inner_le_norm _ _
      have h3 : ‖w - x‖ * ‖e‖ ≤ ε * ‖e‖ := by gcongr
      have h4 : ε * ‖e‖ = η / 2 := by rw [hε]; field_simp
      linarith
    have hsq : ‖p - z‖ ^ 2 < (dist z y) ^ 2 := by
      rw [hp_eq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hnorm_e]
      have hrM : r * M ^ 2 < η := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < M ^ 2 + 1)).1 hrρ
        nlinarith
      have hw2 : ‖w‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwM 2
      have k1 : r * inner ℝ e w ≤ r * (-η / 2) := mul_le_mul_of_nonneg_left hinner hr.le
      have k2 : (r * ‖w‖) ^ 2 ≤ r ^ 2 * M ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hw2 (sq_nonneg r)
      have k3 : r ^ 2 * M ^ 2 < r * η := by
        have := mul_lt_mul_of_pos_left hrM hr
        nlinarith
      linarith
    have hlt : dist p z < dist z y := by
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 hd.le hsq
    exact hhole p hlt hp
  exact ((Measure.mem_support_iff_forall x).1 hx _ (ball_mem_nhds x hεpos)).ne' hzero

/-- Points carry no mass for an `s`-uniform measure. -/
lemma measure_singleton_eq_zero {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) (x : EuclideanSpace ℝ (Fin n)) : ν {x} = 0 := by
  obtain ⟨hs, -, -, c, hc, hball⟩ := hν
  by_cases hx : x ∈ ν.support
  · have htend : Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal (c * ρ ^ s)) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto
      rw [Real.zero_rpow hs.ne'] at h
      have h2 : Tendsto (fun ρ : ℝ ↦ c * ρ ^ s) (𝓝[>] 0) (𝓝 (c * 0)) :=
        (h.mono_left nhdsWithin_le_nhds).const_mul c
      rw [mul_zero] at h2
      convert (ENNReal.continuous_ofReal.tendsto 0).comp h2 using 1
      · funext ρ
        rfl
      · simp
    refine le_antisymm (ge_of_tendsto htend ?_) (by simp)
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    rw [← hball x hx ρ hρ]
    exact measure_mono (by simpa using (mem_closedBall_self hρ.le : x ∈ closedBall x ρ))
  · exact measure_eq_zero_of_disjoint_support (fun y hy ↦ by rw [mem_singleton_iff.1 hy]; exact hx)

/-- For an `s`-uniform measure, closed balls of the same radius centred at points of the support
have the same measure (for every real radius). -/
lemma measure_closedBall_eq_of_mem_support {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ν.support)
    (hy : y ∈ ν.support) (t : ℝ) : ν (closedBall x t) = ν (closedBall y t) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [closedBall_eq_empty.2 ht, closedBall_eq_empty.2 ht]
  · rw [closedBall_zero, closedBall_zero, measure_singleton_eq_zero hν,
      measure_singleton_eq_zero hν]
  · obtain ⟨-, -, -, c, -, hball⟩ := hν
    rw [hball x hx t ht, hball y hy t ht]

/-- **Mattila, Chapter 14, Exercise 5** (in the generality needed): for an `s`-uniform measure
`ν` and `x, y ∈ spt ν`, `∫_{B (y, r)} g (|z - y|) dν z = ∫_{B (x, r)} g (|z - x|) dν z` for every
continuous `g`. In particular `∫_{B(y,r)} (r² - |z - y|²) dν z = ∫_{B(r)} (r² - |z|²) dν z` when
`0 ∈ spt ν`. -/
lemma setIntegral_comp_dist_eq {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ν.support)
    (hy : y ∈ ν.support) (r : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ z in closedBall y r, g (dist z y) ∂ν = ∫ z in closedBall x r, g (dist z x) ∂ν := by
  let _ : ν.Regular := hν.2.1
  have hmeas : ∀ p : EuclideanSpace ℝ (Fin n), Measurable (fun z ↦ dist z p) :=
    fun p ↦ (continuous_id.dist continuous_const).measurable
  have _ : IsFiniteMeasure (ν.restrict (closedBall y r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hmapeq : (ν.restrict (closedBall y r)).map (fun z ↦ dist z y) =
      (ν.restrict (closedBall x r)).map (fun z ↦ dist z x) := by
    refine Measure.ext_of_Iic _ _ fun t ↦ ?_
    rw [Measure.map_apply (hmeas y) measurableSet_Iic,
      Measure.map_apply (hmeas x) measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage (hmeas y)),
      Measure.restrict_apply (measurableSet_Iic.preimage (hmeas x))]
    have hpre : ∀ p : EuclideanSpace ℝ (Fin n),
        (fun z ↦ dist z p) ⁻¹' Iic t ∩ closedBall p r = closedBall p (min t r) := by
      intro p
      ext z
      simp
    rw [hpre, hpre, measure_closedBall_eq_of_mem_support hν hy hx]
  rw [← integral_map (hmeas y).aemeasurable hg.aestronglyMeasurable,
    ← integral_map (hmeas x).aemeasurable hg.aestronglyMeasurable, hmapeq]

/-- The first case in the proof of Theorem 14.10: if `spt ν ⊆ {x | 0 ≤ x ⬝ e}` and
`∫_{B(r)} x ⬝ e dν x = 0` for all `r > 0`, then `spt ν ⊆ {x | x ⬝ e = 0}`. -/
lemma support_subset_of_integral_inner_eq_zero {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {e : EuclideanSpace ℝ (Fin n)}
    (hH : ν.support ⊆ {x | 0 ≤ inner ℝ x e})
    (h : ∀ r : ℝ, 0 < r → ∫ z in closedBall 0 r, inner ℝ z e ∂ν = 0) :
    ν.support ⊆ {x | inner ℝ x e = 0} := by
  let _ : ν.Regular := hν.2.1
  intro x₀ hx₀
  by_contra hne
  have hpos : 0 < inner ℝ x₀ e := lt_of_le_of_ne (hH hx₀) (Ne.symm hne)
  set r := ‖x₀‖ + 1 with hr
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin n) ↦ inner ℝ z e :=
    continuous_id.inner continuous_const
  have hint : IntegrableOn (fun z ↦ inner ℝ z e) (closedBall 0 r) ν :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hnn : 0 ≤ᵐ[ν.restrict (closedBall 0 r)] fun z ↦ inner ℝ z e := by
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ z ∂ν, z ∈ ν.support := mem_ae_iff.2 Measure.measure_compl_support
    filter_upwards [this] with z hz using hH hz
  have hzero := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 (h r (by positivity))
  set U := ball (0 : EuclideanSpace ℝ (Fin n)) r ∩ {z | inner ℝ x₀ e / 2 < inner ℝ z e} with hU
  have hUopen : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const hcont)
  have hxU : x₀ ∈ U := ⟨by rw [mem_ball_zero_iff]; linarith, by
    simp only [mem_ofPred_eq]; linarith⟩
  have hUpos : 0 < ν U := (Measure.mem_support_iff_forall x₀).1 hx₀ U (hUopen.mem_nhds hxU)
  have hU0 : ν U = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_closedBall, ae_iff] at hzero
    refine measure_mono_null (fun z hz ↦ ?_) hzero
    simp only [mem_ofPred_eq, Classical.not_imp, Pi.zero_apply]
    refine ⟨ball_subset_closedBall hz.1, ?_⟩
    have := hz.2
    simp only [mem_ofPred_eq] at this
    linarith
  exact hUpos.ne' hU0

/-- The last step of the proof of Theorem 14.10: if `|y ⬝ m| ≤ C |y|²` for all `y ∈ spt ν` near
`0`, then every tangent measure `λ ∈ Tan (ν, 0)` has `spt λ ⊆ {y | y ⬝ m = 0}`. -/
lemma support_tangent_subset_of_estimate {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) {m : EuclideanSpace ℝ (Fin n)} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hest : ∀ y ∈ ν.support, ‖y‖ ≤ δ → |inner ℝ y m| ≤ C * ‖y‖ ^ 2)
    {lam : Measure (EuclideanSpace ℝ (Fin n))} (htan : IsTangentMeasure ν lam 0) :
    lam.support ⊆ {x | inner ℝ x m = 0} := by
  intro x hx
  by_contra hne
  have hxm : 0 < |inner ℝ x m| := abs_pos.2 hne
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hne
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set η := |inner ℝ x m| / (2 * ‖x‖) with hη
  have hηpos : 0 < η := by positivity
  set R := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set G := {z : EuclideanSpace ℝ (Fin n) | ‖z‖ < R} ∩ {z | η * ‖z‖ < |inner ℝ z m|} with hG
  have hGopen : IsOpen G :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (continuous_const.mul continuous_norm) (continuous_id.inner continuous_const).abs)
  have hxG : x ∈ G := by
    refine ⟨by simp only [mem_ofPred_eq]; linarith, ?_⟩
    simp only [mem_ofPred_eq]
    have : η * ‖x‖ = |inner ℝ x m| / 2 := by rw [hη]; field_simp
    linarith
  have hzero : lam G = 0 := by
    refine measure_open_eq_zero_of_isTangentMeasure hν.2.1 htan hGopen
      ⟨min (δ / R) (η / (C * R + 1)), by positivity, fun r hr hrρ z hz hzG ↦ ?_⟩
    have hT : blowUpMap 0 r z = r⁻¹ • z := by simp [blowUpMap]
    rw [hT] at hzG
    obtain ⟨h1, h2⟩ := hzG
    simp only [mem_ofPred_eq, norm_smul, real_inner_smul_left, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, abs_mul] at h1 h2
    have hr1 : r < δ / R := lt_of_lt_of_le hrρ (min_le_left _ _)
    have hr2 : r < η / (C * R + 1) := lt_of_lt_of_le hrρ (min_le_right _ _)
    have hz1 : ‖z‖ < r * R := by
      rw [inv_mul_lt_iff₀ hr] at h1
      exact h1
    have hz2 : η * ‖z‖ < |inner ℝ z m| := by
      have h2' : r⁻¹ * (η * ‖z‖) < r⁻¹ * |inner ℝ z m| := by
        convert h2 using 1; ring
      exact lt_of_mul_lt_mul_left h2' (inv_nonneg.2 hr.le)
    have hzδ : ‖z‖ ≤ δ := by
      have := (lt_div_iff₀ hRpos).1 hr1
      linarith
    have hest' := hest z hz hzδ
    have hCr : C * (r * R) ≤ η := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < C * R + 1)).1 hr2
      nlinarith
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have : C * ‖z‖ ^ 2 ≤ η * ‖z‖ := by
      have h3 : C * ‖z‖ ≤ C * (r * R) := mul_le_mul_of_nonneg_left hz1.le hC
      nlinarith
    linarith
  exact ((Measure.mem_support_iff_forall x).1 hx G (hGopen.mem_nhds hxG)).ne' hzero

/-- An elementary mean value estimate: `(r + t) ^ s - r ^ s ≤ L t` for `0 ≤ t ≤ r`. -/
lemma rpow_add_sub_rpow_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 ≤ t → t ≤ r → (r + t) ^ s - r ^ s ≤ L * t := by
  refine ⟨s * (r ^ (s - 1) + (2 * r) ^ (s - 1)), by positivity, fun t ht0 htr ↦ ?_⟩
  have key := (convex_Icc r (2 * r)).image_sub_le_mul_sub_of_deriv_le (f := fun x : ℝ ↦ x ^ s)
    (C := s * (r ^ (s - 1) + (2 * r) ^ (s - 1)))
    (fun x _ ↦ (Real.continuousAt_rpow_const x s (Or.inr hs.le)).continuousWithinAt)
    (by
      rw [interior_Icc]
      intro x hx
      exact (Real.differentiableAt_rpow_const_of_ne s (by linarith [hx.1])).differentiableWithinAt)
    (by
      rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [Real.deriv_rpow_const]
      refine mul_le_mul_of_nonneg_left ?_ hs.le
      rcases le_total 0 (s - 1) with h | h
      · have := Real.rpow_le_rpow hx0.le hx.2.le h
        have : 0 ≤ r ^ (s - 1) := by positivity
        linarith
      · have := Real.rpow_le_rpow_of_nonpos hr hx.1.le h
        have : 0 ≤ (2 * r) ^ (s - 1) := by positivity
        linarith)
    r ⟨le_rfl, by linarith⟩ (r + t) ⟨by linarith, by linarith⟩ (by linarith)
  simpa using key

/-- The key estimate in the proof of Theorem 14.10: if `0 ∈ spt ν` and `m = ∫_{B(r)} z dν z`,
then `|y ⬝ m| ≤ C |y|²` for `y ∈ spt ν` with `|y| ≤ r`. -/
lemma abs_inner_integral_le {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : IsSUniform s ν) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ν.support) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ ν.support, ‖y‖ ≤ r →
      |inner ℝ y (∫ z in closedBall 0 r, z ∂ν)| ≤ C * ‖y‖ ^ 2 := by
  let _ : ν.Regular := hν.2.1
  obtain ⟨hs, -, -, c, hc, hball⟩ := id hν
  obtain ⟨L, hL0, hL⟩ := rpow_add_sub_rpow_le hs hr
  set B0 := closedBall (0 : EuclideanSpace ℝ (Fin n)) r with hB0
  refine ⟨ν.real B0 + 3 * r * c * L, add_nonneg measureReal_nonneg (by positivity),
    fun y hy hyr ↦ ?_⟩
  set t := ‖y‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg y
  set By := closedBall y r with hBy
  set fy : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ r ^ 2 - ‖z - y‖ ^ 2 with hfy
  have hfyc : Continuous fy := by fun_prop
  have hint : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f → IntegrableOn f K ν :=
    fun K hK f hf ↦ hf.continuousOn.integrableOn_compact hK
  have hK0 : IsCompact B0 := isCompact_closedBall _ _
  have hKy : IsCompact By := isCompact_closedBall _ _
  have hreal : ∀ p ∈ ν.support, ∀ ρ : ℝ, 0 < ρ → ν.real (closedBall p ρ) = c * ρ ^ s := by
    intro p hp ρ hρ
    rw [measureReal_def, hball p hp ρ hρ, ENNReal.toReal_ofReal (by positivity)]
  have hex5 : ∫ z in By, fy z ∂ν = ∫ z in B0, (r ^ 2 - ‖z‖ ^ 2) ∂ν := by
    have := setIntegral_comp_dist_eq hν h0 hy r (g := fun u ↦ r ^ 2 - u ^ 2) (by fun_prop)
    simpa [dist_eq_norm] using this
  have hm : inner ℝ y (∫ z in B0, z ∂ν) = ∫ z in B0, inner ℝ y z ∂ν :=
    (integral_inner (continuous_id.continuousOn.integrableOn_compact hK0) y).symm
  have hpt : ∀ z, 2 * inner ℝ y z = t ^ 2 + fy z - (r ^ 2 - ‖z‖ ^ 2) := by
    intro z
    have h1 := norm_sub_sq_real z y
    have h2 := real_inner_comm y z
    simp only [hfy]
    linarith
  have h2 : 2 * ∫ z in B0, inner ℝ y z ∂ν =
      t ^ 2 * ν.real B0 + ∫ z in B0, fy z ∂ν - ∫ z in By, fy z ∂ν := by
    rw [hex5, ← integral_const_mul]
    simp_rw [hpt]
    rw [integral_sub (hint _ hK0 (fun a ↦ t ^ 2 + fy a) (continuous_const.add hfyc))
        (hint _ hK0 (fun a ↦ r ^ 2 - ‖a‖ ^ 2) (by fun_prop)),
      integral_add (hint _ hK0 (fun _ ↦ t ^ 2) continuous_const) (hint _ hK0 fy hfyc),
      setIntegral_const,
      smul_eq_mul]
    ring
  have hsplit0 := integral_inter_add_sdiff (μ := ν) (f := fy) (s := B0) (t := By)
    measurableSet_closedBall (hint _ hK0 _ hfyc)
  have hsplity := integral_inter_add_sdiff (μ := ν) (f := fy) (s := By) (t := B0)
    measurableSet_closedBall (hint _ hKy _ hfyc)
  rw [inter_comm] at hsplity
  have hbd1 : ∀ z ∈ B0 \ By, ‖fy z‖ ≤ 3 * r * t := by
    rintro z ⟨hz0, hzy⟩
    simp only [hB0, hBy, mem_closedBall, dist_eq_norm, sub_zero, not_le] at hz0 hzy
    have htri : ‖z - y‖ ≤ ‖z‖ + t := norm_sub_le _ _
    simp only [hfy, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [norm_nonneg z]
  have hbd2 : ∀ z ∈ By \ B0, ‖fy z‖ ≤ 3 * r * t := by
    rintro z ⟨hzy, hz0⟩
    simp only [hB0, hBy, mem_closedBall, dist_eq_norm, sub_zero, not_le] at hz0 hzy
    have htri : ‖z‖ ≤ ‖z - y‖ + t := by
      have := norm_add_le (z - y) y
      rwa [sub_add_cancel] at this
    have hlow : r - t ≤ ‖z - y‖ := by linarith
    have hsq : (r - t) ^ 2 ≤ ‖z - y‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlow 2
    simp only [hfy, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [norm_nonneg (z - y)]
  have hfin : ∀ S : Set (EuclideanSpace ℝ (Fin n)), ∀ p : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ,
      S ⊆ closedBall p ρ → ν S < ⊤ :=
    fun S p ρ hS ↦ (measure_mono hS).trans_lt measure_closedBall_lt_top
  have hI1 : |∫ z in B0 \ By, fy z ∂ν| ≤ 3 * r * t * ν.real (B0 \ By) := by
    have := norm_setIntegral_le_of_norm_le_const (hfin _ 0 r sdiff_subset) hbd1
    simpa [Real.norm_eq_abs] using this
  have hI2 : |∫ z in By \ B0, fy z ∂ν| ≤ 3 * r * t * ν.real (By \ B0) := by
    have := norm_setIntegral_le_of_norm_le_const (hfin _ y r sdiff_subset) hbd2
    simpa [Real.norm_eq_abs] using this
  have hmass : ∀ p q : EuclideanSpace ℝ (Fin n), p ∈ ν.support → dist q p ≤ t →
      ν.real (closedBall q r \ closedBall p r) ≤ c * L * t := by
    intro p q hp hqp
    have hsub : closedBall q r \ closedBall p r ⊆ closedBall p (r + t) \ closedBall p r :=
      sdiff_subset_sdiff_left (closedBall_subset_closedBall' (by linarith))
    have hLt := mul_le_mul_of_nonneg_left (hL t ht0 hyr) hc.le
    calc ν.real (closedBall q r \ closedBall p r)
        ≤ ν.real (closedBall p (r + t) \ closedBall p r) :=
          measureReal_mono hsub (hfin _ p (r + t) sdiff_subset).ne
      _ = ν.real (closedBall p (r + t)) - ν.real (closedBall p r) :=
          measureReal_sdiff (closedBall_subset_closedBall (by linarith)) measurableSet_closedBall
            measure_closedBall_lt_top.ne
      _ = c * (r + t) ^ s - c * r ^ s := by
          rw [hreal p hp _ (by linarith), hreal p hp r hr]
      _ ≤ c * L * t := by linarith
  have hM1 : ν.real (B0 \ By) ≤ c * L * t :=
    hmass y 0 hy (by rw [dist_zero_left])
  have hM2 : ν.real (By \ B0) ≤ c * L * t :=
    hmass 0 y h0 (by rw [dist_zero_right])
  have hrt : 0 ≤ 3 * r * t := by positivity
  have hI1' := hI1.trans (mul_le_mul_of_nonneg_left hM1 hrt)
  have hI2' := hI2.trans (mul_le_mul_of_nonneg_left hM2 hrt)
  have hkey : 2 * ∫ z in B0, inner ℝ y z ∂ν =
      t ^ 2 * ν.real B0 + ∫ z in B0 \ By, fy z ∂ν - ∫ z in By \ B0, fy z ∂ν := by
    linarith
  have hnn : 0 ≤ ν.real B0 * t ^ 2 := mul_nonneg measureReal_nonneg (sq_nonneg t)
  rw [hm, abs_le]
  have a1 := abs_le.1 hI1'
  have a2 := abs_le.1 hI2'
  constructor <;> nlinarith

/-- The core of the proof of Theorem 14.10: an `s`-uniform measure `ν` with
`0 ∈ spt ν ⊆ {x | 0 ≤ x ⬝ e}` produces an `s`-uniform measure supported in a hyperplane. -/
lemma exists_hyperplane {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : IsSUniform s ν)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ν.support) {e : EuclideanSpace ℝ (Fin n)}
    (he : e ≠ 0) (hH : ν.support ⊆ {x | 0 ≤ inner ℝ x e}) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (lam : Measure (EuclideanSpace ℝ (Fin n))),
      w ≠ 0 ∧ IsSUniform s lam ∧ lam.support ⊆ {x | inner ℝ x w = 0} := by
  let _ : ν.Regular := hν.2.1
  by_cases hA : ∀ r : ℝ, 0 < r → ∫ z in closedBall (0 : EuclideanSpace ℝ (Fin n)) r, z ∂ν = 0
  · refine ⟨e, ν, he, hν, support_subset_of_integral_inner_eq_zero hν hH fun r hr ↦ ?_⟩
    have hi : Integrable (fun z ↦ z) (ν.restrict (closedBall 0 r)) :=
      continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have := integral_inner (𝕜 := ℝ) hi e
    simp_rw [real_inner_comm e]
    rw [this, hA r hr, inner_zero_right]
  · push Not at hA
    obtain ⟨r, hr, hm⟩ := hA
    obtain ⟨C, hC, hest⟩ := abs_inner_integral_le hν h0 hr
    obtain ⟨lam, htan⟩ := exists_isTangentMeasure hν h0
    exact ⟨_, lam, hm, (isSUniform_of_isTangentMeasure hν h0 htan).1,
      support_tangent_subset_of_estimate hν hC hr hest htan⟩

/-- An `s`-uniform measure on `ℝⁿ⁺¹` supported in a hyperplane gives an `s`-uniform measure on
`ℝⁿ`. -/
lemma exists_isSUniform_of_hyperplane {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    (hν : IsSUniform s ν) {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : w ≠ 0)
    (hV : ν.support ⊆ {x | inner ℝ x w = 0}) :
    ∃ ν' : Measure (EuclideanSpace ℝ (Fin n)), IsSUniform s ν' := by
  classical
  obtain ⟨hs, hreg, hne, c, hc, hball⟩ := hν
  let _ : ν.Regular := hreg
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) := (ℝ ∙ w)ᗮ with hVdef
  have _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hfin : Module.finrank ℝ V = n := Submodule.finrank_orthogonal_span_singleton hw
  set L : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((stdOrthonormalBasis ℝ V).reindex (finCongr hfin)).repr with hL
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
    fun x ↦ L (V.orthogonalProjectionOnto x) with hf
  set h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y ↦ (L.symm y : EuclideanSpace ℝ (Fin (n + 1))) with hh
  have hf_cont : Continuous f := L.continuous.comp (V.orthogonalProjectionOnto).continuous
  have hh_iso : Isometry h := isometry_subtype_coe.comp L.symm.isometry
  have hsptV : ∀ z ∈ ν.support, z ∈ V := fun z hz ↦ by
    rw [hVdef, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact hV hz
  have hhf : ∀ z ∈ ν.support, h (f z) = z := by
    intro z hz
    simp only [hh, hf, LinearIsometryEquiv.symm_apply_apply]
    rw [show V.orthogonalProjectionOnto z = ⟨z, hsptV z hz⟩ from
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z, hsptV z hz⟩]
  have hdist : ∀ z ∈ ν.support, ∀ y, dist (f z) y = dist z (h y) := by
    intro z hz y
    rw [← hh_iso.dist_eq, hhf z hz]
  set ν' := ν.map f with hν'
  have hmapply : ∀ A, MeasurableSet A → ν' A = ν (f ⁻¹' A ∩ ν.support) := by
    intro A hA
    rw [hν', Measure.map_apply hf_cont.measurable hA,
      measure_inter_conull Measure.measure_compl_support]
  have hpre_cball : ∀ y r, f ⁻¹' closedBall y r ∩ ν.support = closedBall (h y) r ∩ ν.support := by
    intro y r
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_closedBall]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [← hdist z h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hdist z h2], h2⟩
  have hpre_ball : ∀ y r, f ⁻¹' ball y r ∩ ν.support = ball (h y) r ∩ ν.support := by
    intro y r
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ball]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [← hdist z h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hdist z h2], h2⟩
  have hν'ball : ∀ y r, ν' (closedBall y r) = ν (closedBall (h y) r) := by
    intro y r
    rw [hmapply _ measurableSet_closedBall, hpre_cball,
      measure_inter_conull Measure.measure_compl_support]
  have hspt' : ∀ y ∈ ν'.support, h y ∈ ν.support := by
    intro y hy
    by_contra hny
    obtain ⟨ε, hε, hεball⟩ :=
      Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl (h y) hny
    have h0 : ν' (ball y ε) = 0 := by
      rw [hmapply _ measurableSet_ball, hpre_ball]
      refine measure_mono_null (fun z hz ↦ ?_) (measure_empty (μ := ν))
      exact hεball hz.1 hz.2
    exact ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hε)).ne' h0
  have hlocfin : IsLocallyFiniteMeasure ν' := by
    refine ⟨fun y ↦ ⟨ball y 1, ball_mem_nhds y one_pos, ?_⟩⟩
    rw [hmapply _ measurableSet_ball, hpre_ball]
    exact lt_of_le_of_lt (measure_mono inter_subset_left) (regular_measure_ball_lt_top hreg _ _)
  refine ⟨ν', hs, Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν', ?_, c, hc,
    ?_⟩
  · intro h0
    apply hne
    have huniv : ν' univ = ν univ := by
      rw [hν', Measure.map_apply hf_cont.measurable MeasurableSet.univ, preimage_univ]
    rw [h0, Measure.coe_zero, Pi.zero_apply] at huniv
    exact Measure.measure_univ_eq_zero.mp huniv.symm
  · intro y hy r hr
    rw [hν'ball]
    exact hball _ (hspt' y hy) r hr

/-- An `s`-uniform measure whose support is not all of `ℝⁿ⁺¹` gives an `s`-uniform measure on
`ℝⁿ`. -/
lemma exists_lower_dim {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    (hν : IsSUniform s ν) (hspt : ν.support ≠ univ) :
    ∃ ν' : Measure (EuclideanSpace ℝ (Fin n)), IsSUniform s ν' := by
  obtain ⟨e, lam, he, hlam, h0, hH⟩ := exists_halfSpace hν hspt
  obtain ⟨w, lam', hw, hlam', hV⟩ := exists_hyperplane hlam h0 he hH
  exact exists_isSUniform_of_hyperplane hlam' hw hV

/-- If there is an `s`-uniform measure on `ℝⁿ`, then `s` is an integer `≤ n`. -/
lemma nat_of_isSUniform : ∀ {n : ℕ} {s : ℝ} {ν : Measure (EuclideanSpace ℝ (Fin n))},
    IsSUniform s ν → ∃ k : ℕ, k ≤ n ∧ s = k := by
  intro n
  induction n with
  | zero =>
    intro s ν hν
    exact absurd hν (not_isSUniform_of_lt (by simpa using hν.1) ν)
  | succ m ih =>
    intro s ν hν
    rcases lt_trichotomy s ((m + 1 : ℕ) : ℝ) with hlt | heq | hgt
    · have hspt : ν.support ≠ univ := by
        obtain ⟨-, hreg, -, c, hc, hball⟩ := hν
        refine support_ne_univ_of_lower_growth hlt ν hreg (ENNReal.ofReal_pos.2 hc) ?_
        intro x hx ρ hρ
        rw [hball x hx ρ hρ, ENNReal.ofReal_mul hc.le]
      obtain ⟨ν', hν'⟩ := exists_lower_dim hν hspt
      obtain ⟨k, hk, rfl⟩ := ih hν'
      exact ⟨k, by omega, rfl⟩
    · exact ⟨m + 1, le_rfl, heq⟩
    · exact absurd hν (not_isSUniform_of_lt hgt ν)

/-- A Radon measure on `ℝⁿ` giving mass `c r ^ n` to every closed ball of radius `r` is a
constant multiple of Lebesgue measure. -/
lemma eq_smul_volume_of_forall_closedBall {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hν : ν.Regular) {c : ℝ} (hc : 0 < c)
    (hball : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ν (closedBall x r) = ENNReal.ofReal (c * r ^ (n : ℝ))) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K ≠ ∞ ∧ ν = K • volume := by
  let _ : ν.Regular := hν
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set K := ENNReal.ofReal c / ω with hK
  have hK0 : K ≠ 0 := ENNReal.div_ne_zero.2 ⟨(ENNReal.ofReal_pos.2 hc).ne', hωtop⟩
  have hKtop : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hω0
  have heq : ∀ x r, 0 < r → ν (closedBall x r) = K * volume (closedBall x r) := by
    intro x r hr
    rw [hball x r hr, volume_closedBall_eq x hr.le, Real.rpow_natCast, ENNReal.ofReal_mul hc.le,
      hK]
    calc ENNReal.ofReal c * ENNReal.ofReal (r ^ n)
        = (ENNReal.ofReal c / ω * ω) * ENNReal.ofReal (r ^ n) := by
          rw [ENNReal.div_mul_cancel hω0 hωtop]
      _ = ENNReal.ofReal c / ω * (ENNReal.ofReal (r ^ n) * ω) := by ring
  have h1 : ∀ S, ν S ≤ K * volume S := fun S ↦
    measure_le_mul_of_closedBall_le hK0 hKtop S
      (fun x _ δ hδ ↦ ⟨δ / 2, ⟨by positivity, by linarith⟩, (heq x _ (by positivity)).le⟩)
  have h2 : ∀ S, volume S ≤ K⁻¹ * ν S := fun S ↦
    measure_le_mul_of_closedBall_le (ENNReal.inv_ne_zero.2 hKtop) (ENNReal.inv_ne_top.2 hK0) S
      (fun x _ δ hδ ↦ ⟨δ / 2, ⟨by positivity, by linarith⟩, by
        rw [heq x _ (by positivity), ← mul_assoc, ENNReal.inv_mul_cancel hK0 hKtop, one_mul]⟩)
  refine ⟨K, pos_iff_ne_zero.2 hK0, hKtop, Measure.ext fun S _ ↦ le_antisymm (h1 S) ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  calc K * volume S ≤ K * (K⁻¹ * ν S) := by gcongr; exact h2 S
    _ = ν S := by rw [← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]

/-- At points where the density exists and is positive and finite, the density ratio of
Lemma 14.7 is `1`, and the point belongs to the set `A` of Lemma 14.7. -/
lemma mem_positiveFiniteDensitySet {s : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ positiveFiniteDensityExistsSet s μ) :
    a ∈ positiveFiniteDensitySet s μ ∧ RatioOfDensities s μ a = 1 := by
  obtain ⟨hHD, hpos, hfin⟩ := ha
  obtain ⟨y, hy⟩ := hHD.exists_tendsto
  have hl : dimensionalLowerDensity μ.toOuterMeasure s a = y := hy.liminf_eq
  have hu : dimensionalUpperDensity μ.toOuterMeasure s a = y := hy.limsup_eq
  have hd : dimensionalDensity μ.toOuterMeasure s a = y :=
    le_antisymm (sInf_le hy) (le_sInf fun y' hy' ↦ (tendsto_nhds_unique hy hy').le)
  rw [hd] at hpos hfin
  refine ⟨⟨by rw [hl]; exact hpos, by rw [hl, hu], by rw [hu]; exact hfin⟩, ?_⟩
  rw [RatioOfDensities, hl, hu]
  exact ENNReal.div_self hpos.ne' hfin.ne

/-- At points of the set `A` of Lemma 14.7 the measures of small balls are comparable to
`ρ ^ s`. -/
lemma ball_bounds_of_mem {s : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ positiveFiniteDensitySet s μ) :
    ∃ p q r₀ : ℝ, 0 < p ∧ 0 < q ∧ 0 < r₀ ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (closedBall a ρ) ≤ ENNReal.ofReal (q * ρ ^ s)) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ)) := by
  obtain ⟨hl, -, hu⟩ := ha
  obtain ⟨α, hα0, hαl⟩ := exists_between hl
  obtain ⟨β, huβ, hβ⟩ := exists_between hu
  have hαtop : α ≠ ∞ := ne_top_of_lt hαl
  have h1 := eventually_gt_of_lower_density_gt s a α hαl
  have h2 := eventually_lt_of_upper_density_lt s a β huβ
  obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h1.and h2)
  have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
  have hαr : 0 < α.toReal := ENNReal.toReal_pos hα0.ne' hαtop
  have hβr : 0 < β.toReal := ENNReal.toReal_pos (lt_of_le_of_lt bot_le huβ).ne' hβ.ne
  have hX : ∀ ρ : ℝ, 0 < ρ → ∀ γ : ℝ≥0∞, γ ≠ ∞ →
      γ * ENNReal.ofReal ((2 * ρ) ^ s) = ENNReal.ofReal (γ.toReal * 2 ^ s * ρ ^ s) := by
    intro ρ hρ γ hγ
    rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hγ,
      Real.mul_rpow zero_le_two hρ.le]
  refine ⟨α.toReal * 2 ^ s, β.toReal * 2 ^ s, r₀, by positivity, by positivity, hr₀, ?_, ?_⟩
  · intro ρ hρ hρr
    have h := (hsub ⟨hρ, hρr⟩).2
    rw [dimensional_density_ratio_closedBall _ _ _ hρ.le] at h
    have hXpos : ENNReal.ofReal ((2 * ρ) ^ s) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [ENNReal.div_lt_iff (Or.inl hXpos) (Or.inl ENNReal.ofReal_ne_top), hX ρ hρ β hβ.ne] at h
    exact h.le
  · intro ρ hρ hρr
    have h := (hsub ⟨hρ, hρr⟩).1
    rw [dimensional_density_ratio_closedBall _ _ _ hρ.le] at h
    rw [ENNReal.lt_div_iff_mul_lt
        (Or.inl (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity))
        (Or.inl ENNReal.ofReal_ne_top),
      hX ρ hρ α hαtop] at h
    exact h.le

end SUniformAux

open SUniformAux

/-! ## Corollary 14.9 -/

/-- **Mattila, Corollary 14.9 (to Lemma 14.7).** Let `s` be a positive number, `μ` a Radon
measure on `ℝⁿ` and `A` the set of points `a ∈ ℝⁿ` such that the density `Θ^s(μ, a)` exists and
is positive and finite. Then for `μ` almost all `a ∈ A` every `ν ∈ Tan (μ, a)` is `s`-uniform
with `0 ∈ spt ν`. -/
theorem mattila_14_9 {s : ℝ} (hs : 0 < s) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensityExistsSet s μ \ E, ∀ ν, IsTangentMeasure μ ν a →
        IsSUniform s ν ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ ν.support := by
  obtain ⟨E, hE0, hE⟩ := mattila_14_7_1 (s := s) μ hμ
  refine ⟨E, hE0, ?_⟩
  rintro a ⟨ha, haE⟩ ν htan
  obtain ⟨ha', hratio⟩ := mem_positiveFiniteDensitySet ha
  obtain ⟨c, hc0, hctop, hc⟩ := hE a ⟨ha', haE⟩ ν htan
  refine ⟨⟨hs, htan.1, htan.2.1, c.toReal, ENNReal.toReal_pos hc0.ne' hctop, ?_⟩, ?_⟩
  · intro x hx r hr
    obtain ⟨h1, h2⟩ := hc x hx r hr
    rw [hratio, one_mul] at h1
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hctop]
    exact le_antisymm h2 h1
  · obtain ⟨p, q, r₀, hp, hq, hr₀, hup, hlo⟩ := ball_bounds_of_mem ha'
    exact zero_mem_support_of_isTangentMeasure μ ν hμ a (mem_support_of_ball_lower_bound hp hr₀ hlo)
      (limsup_ball_ratio_lt_top_of_ball_bounds_at hp hq hr₀ hup hlo) htan

/-! ## Theorem 14.10 (Marstrand's theorem) -/

/-- **Mattila, Theorem 14.10 (Marstrand's theorem).** Let `s` be a positive number. Suppose
that there exists a Radon measure `μ` on `ℝⁿ` such that the density `Θ^s(μ, a)` exists and is
positive and finite in a set of positive `μ` measure. Then `s` is an integer. -/
theorem mattila_14_10 {s : ℝ} (hs : 0 < s) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) (hA : 0 < μ (positiveFiniteDensityExistsSet s μ)) :
    ∃ k : ℕ, s = k := by
  obtain ⟨E, hE0, hE⟩ := mattila_14_9 hs μ hμ
  have hne : (positiveFiniteDensityExistsSet s μ \ E).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have := measure_sdiff_null (s := positiveFiniteDensityExistsSet s μ) hE0
    rw [h, measure_empty] at this
    exact hA.ne this
  obtain ⟨a, ha⟩ := hne
  obtain ⟨ha', -⟩ := mem_positiveFiniteDensitySet ha.1
  obtain ⟨p, q, r₀, hp, hq, hr₀, hup, hlo⟩ := ball_bounds_of_mem ha'
  obtain ⟨-, ν, -, htan, -⟩ := exists_subseq_blowUp_weaklyConverges_tangentMeasure μ hμ a
    (mem_support_of_ball_lower_bound hp hr₀ hlo)
    (limsup_ball_ratio_lt_top_of_ball_bounds_at hp hq hr₀ hup hlo)
    (fun i ↦ 1 / ((i : ℝ) + 1)) (fun i ↦ by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hν, -⟩ := hE a ha ν htan
  obtain ⟨k, -, hk⟩ := nat_of_isSUniform hν
  exact ⟨k, hk⟩

/-! ## Theorem 14.11 -/

/-- **Mattila, Theorem 14.11.** If `ν` is an `n`-uniform measure in `ℝⁿ`, then `ν` is a
constant multiple of the Lebesgue measure `ℒⁿ`. -/
theorem mattila_14_11 (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : IsSUniform (n : ℝ) ν) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K ≠ ∞ ∧ ν = K • volume := by
  obtain ⟨hs, hreg, -, c, hc, hball⟩ := id hν
  by_cases hspt : ν.support = univ
  · exact eq_smul_volume_of_forall_closedBall hreg hc
      (fun x r hr ↦ hball x (hspt ▸ mem_univ x) r hr)
  · exfalso
    cases n with
    | zero => simp at hs
    | succ m =>
      obtain ⟨ν', hν'⟩ := exists_lower_dim hν hspt
      exact not_isSUniform_of_lt (by push_cast; linarith) ν' hν'

end
