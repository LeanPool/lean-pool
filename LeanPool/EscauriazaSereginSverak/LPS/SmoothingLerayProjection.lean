/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLeraySpace
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify

/-!
# The Leray projection on `L²(ℝ³; ℝ³)`

The Leray projection used in the proof of `prop:lps-smoothing`: the
orthogonal projection `P` onto the weakly divergence-free fields is a
contraction, is self-adjoint, fixes weakly divergence-free fields, annihilates
gradients of `H¹` functions, and commutes with weak partial derivatives. The last property follows from the commutation
of `P` with convolutions: a weak derivative is moved onto the kernel of a
mollifier and the mollifier is then removed in the limit.
-/

public section

open MeasureTheory Set Filter
open scoped Convolution ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Gradients of `H¹(ℝ³)` functions are orthogonal to the weakly
divergence-free fields (`prop:lps-smoothing`). -/
theorem lpsLeray_gradient_mem_orthogonal {q : Vec3 → ℝ} {G : LpsL2Field}
    (hq : MemLp q 2 volume) (hG : ∀ i, HasWeakPartialDerivOn univ i q (⇑(G i))) :
    G ∈ lpsSolenoidalᗮ := by
  let D : List (Fin 3) → Unit → Vec3 → ℝ := fun α _ =>
    match α with
    | [j] => ⇑(G j)
    | _ => q
  have hfam : ∀ u : Unit, IsSobolevFamilyOn 1 univ q (D · u) := by
    intro u
    refine ⟨EventuallyEq.rfl, ?_, ?_⟩
    · intro α hα
      rw [Measure.restrict_univ]
      match α, hα with
      | [], _ => exact hq
      | [j], _ => exact Lp.memLp (G j)
      | _ :: _ :: _, h => simp at h
    · intro α j hα
      match α, hα with
      | [], _ => exact hG j
      | _ :: _, h => simp at h
  obtain ⟨ψ, hψs, hψc, hψconv, -⟩ := sobolevFamily_smooth_approx hfam
  let T : ℕ → LpsTestFunction := fun n => ⟨ψ n (), hψs n (), hψc n ()⟩
  have hcomp : ∀ j, Tendsto (fun n => (lpsTestGradient (T n)) j) atTop (𝓝 (G j)) := by
    intro j
    have h := Lp.tendsto_Lp_of_tendsto_eLpNorm (fi := atTop)
      (f := fun n => (lpsTestGradient (T n)) j)
      (⇑(G j)) (Lp.memLp (G j)) ?_
    · rwa [Lp.toLp_coeFn] at h
    · refine (hψconv () [j] (by simp)).congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp
        (lpsLeray_memLp_spatialDeriv_test (hψs n ()) (hψc n ()) j)] with x hx
      change wordDeriv [j] (ψ n ()) x - ⇑(G j) x =
        ((lpsLeray_memLp_spatialDeriv_test (hψs n ()) (hψc n ()) j).toLp _) x - ⇑(G j) x
      rw [hx]
      rfl
  have hT : Tendsto (fun n => lpsTestGradient (T n)) atTop (𝓝 G) := by
    have h2 := ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 hcomp)
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using h2
  rw [lpsSolenoidal, Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto hT
    (Eventually.of_forall fun n => Submodule.subset_span (Set.mem_range_self _))

/-- Moving a weak derivative of `g` onto the reflected derivative of a smooth
kernel (`prop:lps-smoothing`). -/
theorem lpsLeray_conv_reflect_spatialDeriv {θ g G : Vec3 → ℝ} {k : Fin 3}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hg : HasWeakPartialDerivOn univ k g G) (x : Vec3) :
    ((fun y => spatialDeriv θ k (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x =
      -((fun y => θ (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x := by
  have hθr : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => θ (-y)) := hθ.comp contDiff_neg
  have h := lpsLeray_conv_spatialDeriv_kernel hθr (lpsLeray_hasCompactSupport_reflect hθc) hg x
  rw [lpsLeray_conv_apply, lpsLeray_conv_apply] at h
  rw [lpsLeray_conv_apply, lpsLeray_conv_apply, ← h, ← integral_neg]
  congr 1
  funext t
  rw [lpsLeray_spatialDeriv_reflect (hθ.differentiable (by simp))]
  ring

/-- Test functions are square integrable (`prop:lps-smoothing`). -/
theorem lpsLeray_memLp_test {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : MemLp φ 2 volume :=
  hφ.continuous.memLp_of_hasCompactSupport hφc

/-- The pairing identity behind the commutation of the Leray projection with
weak derivatives, for one smooth compactly supported kernel `θ`
(`prop:lps-smoothing`). -/
theorem lpsLeray_starProjection_pairing {g G : LpsL2Field} {k : Fin 3}
    (h : ∀ i, HasWeakPartialDerivOn univ k (⇑(g i)) (⇑(G i))) (i : Fin 3)
    {θ : Vec3 → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, (lpsSolenoidal.starProjection g i) x *
        (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] spatialDeriv φ k) x =
      -∫ x, (lpsSolenoidal.starProjection G i) x *
        (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) x := by
  set P := lpsSolenoidal.starProjection
  have hθ0 : Continuous θ := hθ.continuous
  have hθr : Continuous (fun y => θ (-y)) := lpsLeray_continuous_reflect hθ0
  have hθrc : HasCompactSupport (fun y => θ (-y)) := lpsLeray_hasCompactSupport_reflect hθc
  have hdθ : Continuous (spatialDeriv θ k) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdθc : HasCompactSupport (spatialDeriv θ k) := hθc.fderiv_apply (𝕜 := ℝ) (basisVec k)
  have hκ : Continuous (fun y => spatialDeriv θ k (-y)) := lpsLeray_continuous_reflect hdθ
  have hκc : HasCompactSupport (fun y => spatialDeriv θ k (-y)) :=
    lpsLeray_hasCompactSupport_reflect hdθc
  have hφL2 := lpsLeray_memLp_test hφ hφc
  set Φ := hφL2.toLp φ
  -- the derivative moves from the test function onto the kernel
  have hmove : θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] spatialDeriv φ k =
      spatialDeriv θ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ := by
    funext x
    exact (lpsLeray_conv_spatialDeriv_kernel hθ hθc
      (HasWeakPartialDerivOn.of_contDiff (hφ.of_le (by norm_cast))) x).symm
  -- a convolved test function is the convolution operator applied to it
  have hopΦ (η : Vec3 → ℝ) (hη : Continuous η) (hηc : HasCompactSupport η) :
      (lpsLeray_memLp_conv hη hηc hφL2).toLp (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) =
        lpsConvL2 η hη hηc Φ := by
    apply Lp.ext
    have hcongr : η ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑Φ =
        η ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ :=
      convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ) (h1 := EventuallyEq.rfl)
        (h2 := hφL2.coeFn_toLp)
    filter_upwards [MemLp.coeFn_toLp (lpsLeray_memLp_conv hη hηc hφL2),
      lpsConvL2_coeFn η hη hηc Φ] with x hx hy
    rw [hx, hy, hcongr]
  -- the reflected derivative kernel turns `g` into minus the reflected kernel applied to `G`
  have hstep : lpsConvField _ hκ hκc g = -lpsConvField _ hθr hθrc G := by
    ext j : 1
    rw [PiLp.neg_apply, lpsConvField_apply, lpsConvField_apply]
    apply Lp.ext
    filter_upwards [lpsConvL2_coeFn _ hκ hκc (g j),
      Lp.coeFn_neg (lpsConvL2 _ hθr hθrc (G j)), lpsConvL2_coeFn _ hθr hθrc (G j)]
      with x hx hneg hy
    rw [hx, hneg, Pi.neg_apply, hy]
    exact lpsLeray_conv_reflect_spatialDeriv hθ hθc (h j) x
  calc ∫ x, (P g i) x * (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] spatialDeriv φ k) x
      = inner ℝ (P g i) (lpsConvL2 _ hdθ hdθc Φ) := by
        rw [← hopΦ _ hdθ hdθc, lpsLeray_inner_toLp, hmove]
    _ = inner ℝ (lpsConvField _ hκ hκc (P g) i) Φ :=
        (lpsConvL2_inner hκ hκc hdθ hdθc (fun y => by rw [neg_neg]) (P g i) Φ).symm
    _ = -inner ℝ (lpsConvField _ hθr hθrc (P G) i) Φ := by
        rw [← lpsConvField_starProjection, hstep, map_neg, lpsConvField_starProjection,
          PiLp.neg_apply, inner_neg_left]
    _ = -inner ℝ (P G i) (lpsConvL2 θ hθ0 hθc Φ) := by
        rw [lpsConvField_apply,
          lpsConvL2_inner hθr hθrc hθ0 hθc (fun y => by rw [neg_neg]) (P G i) Φ]
    _ = -∫ x, (P G i) x * (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) x := by
        rw [← hopΦ θ hθ0 hθc, lpsLeray_inner_toLp]

/-- Pairing an `L²` function with a mollified `L²` function converges to the
unmollified pairing (`prop:lps-smoothing`). -/
theorem lpsLeray_tendsto_integral_mul_mollify (f : Lp ℝ 2 (volume : Measure Vec3))
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hεpos : ∀ n, 0 < ε n) :
    Tendsto (fun n => ∫ x, f x * mollify ψ (ε n) (hεpos n) x) atTop
      (𝓝 (∫ x, f x * ψ x)) := by
  have hmem : ∀ n, MemLp (mollify ψ (ε n) (hεpos n)) 2 volume := fun n =>
    lpsLeray_memLp_conv (mollifier_contDiff (hεpos n) (n := 0)).continuous
      (mollifier_hasCompactSupport (hεpos n)) hψ
  have hconv := CKN.tendsto_eLpNorm_sub_zero_mollify (p := 2) (by norm_num) (by norm_num)
    hψ hε hεpos
  have hLp : Tendsto (fun n => (hmem n).toLp _) atTop (𝓝 (hψ.toLp ψ)) := by
    apply Lp.tendsto_Lp_of_tendsto_eLpNorm
    refine hconv.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hmem n).coeFn_toLp] with x hx
    rw [Pi.sub_apply, hx]
  have hcont : Continuous (fun v : Lp ℝ 2 (volume : Measure Vec3) => inner ℝ f v) :=
    continuous_const.inner continuous_id
  have hinner := (hcont.tendsto (hψ.toLp ψ)).comp hLp
  simp only [Function.comp_def, lpsLeray_inner_toLp] at hinner
  exact hinner

/-- The Leray projection commutes with weak partial derivatives
(`prop:lps-smoothing`). -/
theorem lpsLeray_starProjection_hasWeakPartialDerivOn {g G : LpsL2Field} {k : Fin 3}
    (h : ∀ i, HasWeakPartialDerivOn univ k (⇑(g i)) (⇑(G i))) (i : Fin 3) :
    HasWeakPartialDerivOn univ k (⇑(lpsSolenoidal.starProjection g i))
      (⇑(lpsSolenoidal.starProjection G i)) := by
  intro φ hφ hφc _
  simp only [Measure.restrict_univ]
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => Nat.one_div_pos_of_nat
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := lpsLeray_tendsto_integral_mul_mollify (lpsSolenoidal.starProjection g i)
    (lpsLeray_memLp_spatialDeriv_test hφ hφc k) hε hεpos
  have hR := (lpsLeray_tendsto_integral_mul_mollify (lpsSolenoidal.starProjection G i)
    (lpsLeray_memLp_test hφ hφc) hε hεpos).neg
  have hid : ∀ n, ∫ x, (lpsSolenoidal.starProjection g i) x *
      mollify (spatialDeriv φ k) (ε n) (hεpos n) x =
      -∫ x, (lpsSolenoidal.starProjection G i) x * mollify φ (ε n) (hεpos n) x := fun n =>
    lpsLeray_starProjection_pairing h i (mollifier_contDiff (hεpos n))
      (mollifier_hasCompactSupport (hεpos n)) hφ hφc
  simp only [← hid] at hR
  exact tendsto_nhds_unique hL hR

/-- The Leray projection used in the proof of `prop:lps-smoothing`: on
`L²(ℝ³; ℝ³)`, realised as three `L²(ℝ³)` components, there is a bounded
operator `P` (the orthogonal projection onto the weakly divergence-free
fields) such that
* `P` is a contraction;
* `P` fixes every weakly divergence-free field;
* `P g` is weakly divergence-free for every `g`;
* `P` annihilates the gradient `G` of every `q ∈ L²(ℝ³)` whose weak gradient
  `G` is square integrable;
* `P` commutes with weak partial derivatives: if every component of `g` has
  weak `k`-th derivative the corresponding component of `G`, then every
  component of `P g` has weak `k`-th derivative the corresponding component of
  `P G`;
* `P` is self-adjoint. -/
theorem lps_leray_exists :
    ∃ P : PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3)) →L[ℝ]
        PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3)),
      (∀ g, ‖P g‖ ≤ ‖g‖) ∧
      (∀ g : PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3)),
        (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∑ i, ∫ x, g i x * spatialDeriv φ i x = 0) → P g = g) ∧
      (∀ (g : PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))) (φ : Vec3 → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∑ i, ∫ x, P g i x * spatialDeriv φ i x = 0) ∧
      (∀ (q : Vec3 → ℝ) (G : PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))),
        MemLp q 2 volume → (∀ i, HasWeakPartialDerivOn univ i q (⇑(G i))) → P G = 0) ∧
      (∀ (g G : PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))) (k : Fin 3),
        (∀ i, HasWeakPartialDerivOn univ k (⇑(g i)) (⇑(G i))) →
          ∀ i, HasWeakPartialDerivOn univ k (⇑(P g i)) (⇑(P G i))) ∧
      (∀ g h, inner ℝ (P g) h = inner ℝ g (P h)) := by
  refine ⟨lpsSolenoidal.starProjection, fun g => lpsSolenoidal.norm_starProjection_apply_le g,
    fun g hg => Submodule.starProjection_eq_self_iff.2 ((mem_lpsSolenoidal_iff g).2 hg),
    fun g => (mem_lpsSolenoidal_iff _).1 (Submodule.starProjection_apply_mem _ g),
    fun q G hq hG => (Submodule.starProjection_apply_eq_zero_iff lpsSolenoidal).2
      (lpsLeray_gradient_mem_orthogonal hq hG),
    fun g G k h i => lpsLeray_starProjection_hasWeakPartialDerivOn h i,
    fun g h => lpsSolenoidal.inner_starProjection_left_eq_right g h⟩

end ESS
