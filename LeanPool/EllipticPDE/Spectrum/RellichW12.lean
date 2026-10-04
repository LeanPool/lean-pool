/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.GlobalApproximation
public import LeanPool.EllipticPDE.Extension.LinearOperator
public import LeanPool.EllipticPDE.Spectrum.RellichDischarge
public import LeanPool.EllipticPDE.Embedding.H01Sobolev
public import LeanPool.EllipticPDE.Extension.BallChart
public import LeanPool.EllipticPDE.Regularity.RestrictedDiffQuotient


/-!
# Rellich-Kondrachov on the whole graph space

`EllipticPdes.Sobolev.embL2_isCompact` is the compact embedding of `H₀¹(Ω)` into `L²(Ω)` on a
bounded measurable domain. Its proof extends each class by zero and applies the
Fréchet-Kolmogorov criterion to the extensions, whose translation modulus is bounded by the
gradient because a class in `H₀¹(Ω)` is a limit of test functions. An element of the graph
space `W12 Ω`, the `H¹(Ω)` of this development, has no such approximation: extended by zero it
jumps at the boundary, and the translation modulus is lost.

The extension operator restores it. On a bounded open domain with `C¹` boundary,
`EllipticPdes.Extension.exists_extLinear` puts every element of `W12 Ω` on the whole space, with
compact support in a fixed ball, a weak gradient on `ℝᵈ`, and a bound by the norm of the
element. The whole-space translation estimate for a class with a weak gradient,
`transL2_toLp_sub_le_of_hasWeakGradOn_univ`, proved by mollifying the class and passing the
smooth estimate to the limit, gives the modulus, and the Fréchet-Kolmogorov criterion gives
total boundedness of the extensions. Restricting back to `Ω`, through the restriction map of
the regularity chapter, is continuous, so the image of the unit ball of `W12 Ω` in `L²(Ω)` is
totally bounded and the embedding is compact.

## Main declarations

* `EllipticPdes.Sobolev.transL2_toLp_sub_le_of_hasWeakGradOn_univ`: the translation modulus
  of a whole-space class with an `L²` weak gradient.
* `EllipticPdes.Sobolev.embW12`: the embedding `W12 Ω →L[ℝ] L²(Ω)`.
* `EllipticPdes.Sobolev.embW12_isCompact`: that embedding is compact on a bounded open domain
  with `C¹` boundary.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.7 Theorem 1 (p. 286);
James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem IV.2.10.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn partialD_convolution_eq_of_hasWeakGradOn
  tendsto_eLpNorm_convolution_sub eLpNorm_convolution_le isFiniteMeasure_restrict_of_isBounded
  norm_apply_le)
open EllipticPdes.Extension (HasC1Boundary exists_extLinear SobolevPair hasWeakGradOn_of_mem_W12
  hasC1Boundary_ball)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### The translation modulus of a whole-space Sobolev class -/

/-- The squared `L²` norm of the `L²` class of a function is the integral of the square. -/
theorem norm_toLp_sq_eq_integral_sq {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : MemLp F 2 volume) : ‖hF.toLp F‖ ^ 2 = ∫ x, F x ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

/-- **Translation modulus of a whole-space class with a weak gradient.** A compactly supported
class on `ℝᵈ` with an `L²` weak gradient moves under translation by at most the length of the
translation times the sum of the `L²` norms of its gradient components. The class is
mollified, the smooth estimate `integral_sq_sub_translation_le` applies to each mollification,
whose gradient is the mollified weak gradient and is bounded in `L²` by the weak gradient
itself, and the estimate passes to the `L²` limit. -/
theorem transL2_toLp_sub_le_of_hasWeakGradOn_univ {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hFcs : HasCompactSupport F)
    (hFint : Integrable F volume) (hF : MemLp F 2 volume) (hG : ∀ k, MemLp (G k) 2 volume)
    (hwg : HasWeakGradOn Set.univ F G) (h : EuclideanSpace ℝ (Fin d)) :
    ‖transL2 h (hF.toLp F) - hF.toLp F‖
      ≤ (∑ k, (eLpNorm (G k) 2 volume).toReal) * ‖h‖ := by
  classical
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = 1 / (n + 1 : ℝ) := fun _ => rfl
  have hrIn : ∀ n : ℕ, (φb n).rIn = 1 / (n + 1 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφratio : ∀ᶠ n in atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  set v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => F ⋆[L, volume] (φb n).normed volume with hvdef
  have hFli : LocallyIntegrable F volume := hFint.locallyIntegrable
  have hvsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) := fun n =>
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hFli
      (φb n).contDiff_normed
  have hvcs : ∀ n, HasCompactSupport (v n) := fun n =>
    HasCompactSupport.convolution (L := L) hFcs (φb n).hasCompactSupport_normed
  have hpartial : ∀ (n : ℕ) (k : Fin d),
      partialD k (v n) = (G k ⋆[L, volume] (φb n).normed volume) := by
    intro n k
    funext x
    have h := partialD_convolution_eq_of_hasWeakGradOn MeasurableSet.univ
      hFint.integrableOn hwg (φb n) k (x := x) (subset_univ _)
    simpa only [indicator_univ] using h
  have hρ0 : ∀ n, (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ (φb n).normed volume :=
    fun n x => (φb n).nonneg_normed x
  have hρm : ∀ n, AEStronglyMeasurable ((φb n).normed volume) volume := fun n =>
    ((φb n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous.aestronglyMeasurable
  have hρ1 : ∀ n, ∫ y, (φb n).normed volume y ∂volume = 1 := fun n => (φb n).integral_normed
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  -- the mollifications are in `L²` and converge to the class
  have hvmem : ∀ n, MemLp (v n) 2 volume := fun n =>
    ((hvsmooth n).continuous.memLp_of_hasCompactSupport (hvcs n))
  have hconv := tendsto_eLpNorm_convolution_sub one_le_two (h := F) (by rw [h2]; exact hF)
    hφrOut hφratio
  rw [h2] at hconv
  have htend : Tendsto (fun n => (hvmem n).toLp (v n)) atTop (𝓝 (hF.toLp F)) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine hconv.congr fun n => ?_
    rw [Lp.edist_toLp_toLp]
  -- the modulus of each mollification
  have hmod : ∀ n, ∀ h : EuclideanSpace ℝ (Fin d),
      ‖transL2 h ((hvmem n).toLp (v n)) - (hvmem n).toLp (v n)‖
        ≤ (∑ k, (eLpNorm (G k) 2 volume).toReal) * ‖h‖ := by
    intro n h
    have hsum0 : 0 ≤ ∑ k, (eLpNorm (G k) 2 volume).toReal :=
      Finset.sum_nonneg fun k _ => ENNReal.toReal_nonneg
    refine le_of_sq_le_sq ?_ (mul_nonneg hsum0 (norm_nonneg _))
    rw [norm_sq_transL2_sub]
    have hae : (fun x => (((hvmem n).toLp (v n) : EuclideanSpace ℝ (Fin d) → ℝ) (x + h)
        - ((hvmem n).toLp (v n) : EuclideanSpace ℝ (Fin d) → ℝ) x) ^ 2)
        =ᵐ[volume] fun x => (v n (x + h) - v n x) ^ 2 := by
      have hcomp : ∀ᵐ x ∂volume,
          ((hvmem n).toLp (v n) : EuclideanSpace ℝ (Fin d) → ℝ) (x + h) = v n (x + h) :=
        ((measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae).eventually
          (hvmem n).coeFn_toLp
      filter_upwards [hcomp, (hvmem n).coeFn_toLp] with x h1 h2
      rw [h1, h2]
    rw [integral_congr_ae hae]
    -- the gradient energy of the mollification is bounded by that of the weak gradient
    have hgrad : ∫ x, ‖fderiv ℝ (v n) x‖ ^ 2
        ≤ (∑ k, (eLpNorm (G k) 2 volume).toReal) ^ 2 := by
      have hpt : (fun x => ‖fderiv ℝ (v n) x‖ ^ 2)
          = fun x => ∑ k, (partialD k (v n) x) ^ 2 := by
        funext x
        rw [norm_sq_clm_eq_sum_apply_single (fderiv ℝ (v n) x)]
        rfl
      have hint : ∀ k : Fin d, Integrable (fun x => (partialD k (v n) x) ^ 2) volume := by
        intro k
        have hc : Continuous (partialD k (v n)) :=
          ((hvsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
        have hcs : HasCompactSupport (partialD k (v n)) :=
          (hvcs n).fderiv (𝕜 := ℝ) |>.comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
            T (EuclideanSpace.single k 1)) (by simp)
        exact (hc.fun_pow 2).integrable_of_hasCompactSupport
          (by simpa only [Function.comp_def] using
            hcs.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
      rw [hpt, integral_finsetSum Finset.univ (fun k _ => hint k)]
      refine le_trans (Finset.sum_le_sum fun k _ => ?_)
        (Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => ENNReal.toReal_nonneg)
      -- one component: the mollified gradient is bounded by the gradient in `L²`
      have hmemk : MemLp (partialD k (v n)) 2 volume := by
        have hc : Continuous (partialD k (v n)) :=
          ((hvsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
        have hcs : HasCompactSupport (partialD k (v n)) :=
          (hvcs n).fderiv (𝕜 := ℝ) |>.comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
            T (EuclideanSpace.single k 1)) (by simp)
        exact hc.memLp_of_hasCompactSupport hcs
      rw [← norm_toLp_sq_eq_integral_sq hmemk]
      have hle : eLpNorm (partialD k (v n)) 2 volume ≤ eLpNorm (G k) 2 volume := by
        rw [hpartial n k]
        have := eLpNorm_convolution_le one_le_two (hρ0 n) (hρm n) (hρ1 n)
          (h := G k) (by rw [h2]; exact hG k)
        rwa [h2] at this
      have hnorm : ‖hmemk.toLp (partialD k (v n))‖ ≤ (eLpNorm (G k) 2 volume).toReal := by
        rw [Lp.norm_def]
        refine ENNReal.toReal_mono (hG k).eLpNorm_ne_top ?_
        calc eLpNorm (hmemk.toLp (partialD k (v n))) 2 volume
            = eLpNorm (partialD k (v n)) 2 volume := eLpNorm_congr_ae hmemk.coeFn_toLp
          _ ≤ eLpNorm (G k) 2 volume := hle
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    calc ∫ x, (v n (x + h) - v n x) ^ 2
        ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ (v n) x‖ ^ 2 :=
          integral_sq_sub_translation_le
            ((hvsmooth n).of_le (by exact_mod_cast le_top)) (hvcs n) h
      _ ≤ ‖h‖ ^ 2 * (∑ k, (eLpNorm (G k) 2 volume).toReal) ^ 2 :=
          mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)
      _ = ((∑ k, (eLpNorm (G k) 2 volume).toReal) * ‖h‖) ^ 2 := by ring
  exact transL2_sub_le_of_tendsto htend hmod h

/-! ### The embedding of the graph space -/

/-- The coordinate-`0` embedding `H¹(Ω) ↪ L²(Ω)`, `U ↦ U 0`, on the graph space `W12 Ω`. -/
def embW12 (Ω : Set (EuclideanSpace ℝ (Fin d))) : W12 Ω →L[ℝ] L2D Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) (0 : Fin (d + 1))).comp (W12 Ω).subtypeL

@[simp] lemma embW12_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : W12 Ω) :
    embW12 Ω U = (U : H1amb Ω) 0 := by
  simp only [embW12, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, PiLp.proj_apply]

/-- **Rellich-Kondrachov on `H¹(Ω)`** (Evans §5.7 Theorem 1 at `p = q = 2`, Guo Theorem
IV.2.10). On a bounded open domain with `C¹` boundary, the embedding of the graph space
`W12 Ω` into `L²(Ω)` is a compact operator. -/
theorem embW12_isCompact (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) : IsCompactOperator (embW12 Ω) := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨R₀, hR₀⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hsub : closure Ω ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R₀ + 1) :=
    (closure_minimal hR₀ isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  obtain ⟨T, K, hT⟩ := exists_extLinear hd hΩopen hΩb hC1 isOpen_ball hsub (p := 2) one_le_two
  -- the pair an element of the graph space presents to the extension operator
  let w : W12 Ω → SobolevPair d := fun U =>
    (fun x => ((U : H1amb Ω) 0 : L2D Ω) x, fun (k : Fin d) x => ((U : H1amb Ω) k.succ : L2D Ω) x)
  have hw : ∀ U : W12 Ω,
      HasWeakGradOn Set.univ (T (w U)).1 (T (w U)).2 ∧ HasCompactSupport (T (w U)).1 ∧
        tsupport (T (w U)).1 ⊆ ball 0 (R₀ + 1) ∧ Integrable (T (w U)).1 volume ∧
        (∀ k, Integrable ((T (w U)).2 k) volume) ∧
        (∀ y ∈ Ω, (T (w U)).1 y = (w U).1 y) ∧
        eLpNorm (T (w U)).1 2 volume ≤ (K : ℝ≥0∞) * (eLpNorm (w U).1 2 (volume.restrict Ω)
          + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) ∧
        ∀ k, eLpNorm ((T (w U)).2 k) 2 volume ≤ (K : ℝ≥0∞) * (eLpNorm (w U).1 2
          (volume.restrict Ω) + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) := fun U =>
    hT (w U) ((Lp.memLp _).integrable one_le_two) (fun k => (Lp.memLp _).integrable one_le_two)
      (hasWeakGradOn_of_mem_W12 U.2)
  -- the seminorms of the pair are bounded by the norm of the element
  have hN : ∀ U : W12 Ω, eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal ((d + 1) * ‖U‖) := by
    intro U
    have h0 : eLpNorm (w U).1 2 (volume.restrict Ω) = ENNReal.ofReal ‖(U : H1amb Ω) 0‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    have hk : ∀ k : Fin d, eLpNorm ((w U).2 k) 2 (volume.restrict Ω)
        = ENNReal.ofReal ‖(U : H1amb Ω) k.succ‖ := fun k => by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
    rw [h0]
    simp_rw [hk]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
      ← ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hU : ‖U‖ = ‖(U : H1amb Ω)‖ := rfl
    calc ‖(U : H1amb Ω) 0‖ + ∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖
        ≤ ‖U‖ + ∑ _k : Fin d, ‖U‖ := by
          rw [hU]
          exact add_le_add (norm_apply_le _ _) (Finset.sum_le_sum fun k _ => norm_apply_le _ _)
      _ = (d + 1) * ‖U‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hKfin : ∀ U : W12 Ω, (K : ℝ≥0∞) * (eLpNorm (w U).1 2 (volume.restrict Ω)
      + ∑ i, eLpNorm ((w U).2 i) 2 (volume.restrict Ω)) < ⊤ := fun U =>
    ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_of_le_of_lt (hN U) ENNReal.ofReal_lt_top)
  have hMF : ∀ U : W12 Ω, MemLp (T (w U)).1 2 volume := fun U =>
    lt_of_le_of_lt (hw U).2.2.2.2.2.2.1 (hKfin U)
  have hMG : ∀ U : W12 Ω, ∀ k, MemLp ((T (w U)).2 k) 2 volume := fun U k =>
    lt_of_le_of_lt ((hw U).2.2.2.2.2.2.2 k) (hKfin U)
  -- the real bounds on the extension and its gradient
  have hFb : ∀ U : W12 Ω, (eLpNorm (T (w U)).1 2 volume).toReal ≤ K * ((d + 1) * ‖U‖) := by
    intro U
    have : eLpNorm (T (w U)).1 2 volume ≤ (K : ℝ≥0∞) * ENNReal.ofReal ((d + 1) * ‖U‖) :=
      (hw U).2.2.2.2.2.2.1.trans (by gcongr; exact hN U)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at this
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) this)
  have hGb : ∀ U : W12 Ω, ∀ k, (eLpNorm ((T (w U)).2 k) 2 volume).toReal
      ≤ K * ((d + 1) * ‖U‖) := by
    intro U k
    have : eLpNorm ((T (w U)).2 k) 2 volume ≤ (K : ℝ≥0∞) * ENNReal.ofReal ((d + 1) * ‖U‖) :=
      ((hw U).2.2.2.2.2.2.2 k).trans (by gcongr; exact hN U)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at this
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) this)
  -- the extensions of the unit ball, as a family in `L²(ℝᵈ)`
  set Φ : W12 Ω → EucL2 d := fun U => (hMF U).toLp (T (w U)).1 with hΦ
  set S : Set (EucL2 d) := Φ '' closedBall 0 1 with hS
  have hSTB : TotallyBounded S := by
    refine totallyBounded_of_lipschitz_translation S (R := R₀ + 1) (M := K * (d + 1))
      (Λ := d * (K * (d + 1))) ?_ ?_ ?_
    · rintro g ⟨U, hU, rfl⟩
      rw [mem_closedBall, dist_zero_right] at hU
      rw [Lp.norm_def, eLpNorm_congr_ae (hMF U).coeFn_toLp]
      calc (eLpNorm (T (w U)).1 2 volume).toReal ≤ K * ((d + 1) * ‖U‖) := hFb U
        _ ≤ K * ((d + 1) * 1) := by gcongr
        _ = K * (d + 1) := by ring
    · rintro g ⟨U, hU, rfl⟩
      filter_upwards [(hMF U).coeFn_toLp] with x hx hxR
      rw [hx]
      refine image_eq_zero_of_notMem_tsupport fun hc => hxR ?_
      exact ball_subset_closedBall ((hw U).2.2.1 hc)
    · rintro g ⟨U, hU, rfl⟩ h
      rw [mem_closedBall, dist_zero_right] at hU
      refine (transL2_toLp_sub_le_of_hasWeakGradOn_univ (hw U).2.1 (hw U).2.2.2.1 (hMF U)
        (hMG U) (hw U).1 h).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc ∑ k, (eLpNorm ((T (w U)).2 k) 2 volume).toReal
          ≤ ∑ _k : Fin d, K * ((d + 1) * ‖U‖) := Finset.sum_le_sum fun k _ => hGb U k
        _ = d * (K * ((d + 1) * ‖U‖)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ d * (K * ((d + 1) * 1)) := by gcongr
        _ = d * (K * (d + 1)) := by ring
  -- the image of the unit ball in `L²(Ω)` is the restriction of that family
  have himg : embW12 Ω '' closedBall (0 : W12 Ω) 1
      ⊆ Regularity.restrictL2 (Ω := Ω) '' S := by
    rintro f ⟨U, hU, rfl⟩
    refine ⟨Φ U, ⟨U, hU, rfl⟩, ?_⟩
    rw [embW12_apply]
    apply Lp.ext
    have h1 := Regularity.coeFn_restrictL2 (Ω := Ω) (Φ U)
    have h2 : ((hMF U).toLp (T (w U)).1 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (T (w U)).1 := ae_restrict_of_ae (hMF U).coeFn_toLp
    have h3 : (T (w U)).1 =ᵐ[volume.restrict Ω]
        fun x => ((U : H1amb Ω) 0 : L2D Ω) x :=
      (ae_restrict_iff' hΩopen.measurableSet).mpr
        (Eventually.of_forall fun y hy => (hw U).2.2.2.2.2.1 y hy)
    exact (h1.trans h2).trans h3
  have hTB : TotallyBounded (embW12 Ω '' closedBall (0 : W12 Ω) 1) :=
    (hSTB.image (Regularity.restrictL2 (Ω := Ω)).uniformContinuous).subset himg
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall (embW12 Ω).toLinearMap
    one_pos).mpr (hTB.closure.isCompact_of_isClosed isClosed_closure)

/-- **Rellich-Kondrachov on `H¹` of the unit ball**, every hypothesis discharged. -/
theorem embW12_isCompact_ball (hd : 0 < d) :
    IsCompactOperator (embW12 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  embW12_isCompact hd isOpen_ball isBounded_ball (hasC1Boundary_ball hd)

end EllipticPdes.Sobolev
