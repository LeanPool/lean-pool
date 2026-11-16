/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Quadratic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.CompactTilt
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Caffarelli.Contact
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Extension
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import Mathlib.Analysis.Calculus.DerivativeTest
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Touching tests and their second-order Taylor bounds

Supporting the convex Monge–Ampère infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2. The declarations retain their original
source hypotheses, dimensional scope and mathematical conclusions.
-/

@[expose] public section

section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma directional_second_deriv_nonneg
    {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x₀ + t • v
  let q : ℝ → ℝ := fun t => ψ (L t)
  let p : ℝ → ℝ := fun t => (fderiv ℝ ψ (L t)) v
  let r : ℝ → ℝ := fun t => q t + q (-t)
  have hL (t : ℝ) : HasDerivAt L v t := by
    simpa [L] using
      ((hasDerivAt_id (𝕜 := ℝ) t).smul_const v).const_add x₀
  have hLcont : Tendsto L (𝓝 0) (𝓝 x₀) := by
    simpa [L] using (hL 0).continuousAt.tendsto
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using
      (continuousAt_neg : ContinuousAt (fun t : ℝ => -t) (0 : ℝ)).tendsto
  have hψevent :
      ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 ψ (L t) :=
    hLcont.eventually (hψ.eventually (by norm_num))
  have hqevent : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt q (p t) t := by
    filter_upwards [hψevent] with t ht
    have h :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)
    simpa only [q, p, Function.comp_def] using h
  have hrderiv : deriv r =ᶠ[𝓝 0] (fun t => p t - p (-t)) := by
    filter_upwards [hqevent, hneg.eventually hqevent] with t ht htneg
    have hn : HasDerivAt (fun s : ℝ => q (-s)) (-p (-t)) t := by
      simpa [Function.comp_def] using
        htneg.comp t (hasDerivAt_id (𝕜 := ℝ) t).neg
    simpa only [r, sub_eq_add_neg] using (ht.fun_add hn).deriv
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ ψ) x₀ :=
    hψ.fderiv_right (m := 1) (n := 2) (by norm_num)
  have hpf : HasFDerivAt (fderiv ℝ ψ)
      (fderiv ℝ (fderiv ℝ ψ) x₀) x₀ :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have hp0 :
      HasDerivAt p (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    have hpf' : HasFDerivAt (fderiv ℝ ψ)
        (fderiv ℝ (fderiv ℝ ψ) x₀) (L 0) := by
      simpa [L] using hpf
    have hcomp := hpf'.comp_hasDerivAt 0 (hL 0)
    have happ := hcomp.clm_apply (hasDerivAt_const (x := (0 : ℝ)) v)
    simpa [p, L, bilinearIteratedFDerivTwo, Function.comp_def] using happ
  have hpneg :
      HasDerivAt (fun t => p (-t))
        (-(bilinearIteratedFDerivTwo ℝ ψ x₀ v v)) 0 := by
    have hp0' : HasDerivAt p
        (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hp0
    simpa [Function.comp_def] using
      hp0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hpdiff :
      HasDerivAt (fun t => p t - p (-t))
        (2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    simpa [two_mul] using hp0.fun_sub hpneg
  have hsecond :
      deriv (deriv r) 0 =
        2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
    calc
      deriv (deriv r) 0 =
          deriv (fun t => p t - p (-t)) 0 := hrderiv.deriv_eq
      _ = 2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := hpdiff.deriv
  have hq0 : HasDerivAt q ((fderiv ℝ ψ x₀) v) 0 := by
    have hψ' : HasFDerivAt ψ (fderiv ℝ ψ x₀) (L 0) := by
      simpa [L] using (hψ.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [q, Function.comp_def] using hψ'.comp_hasDerivAt 0 (hL 0)
  have hqneg0 :
      HasDerivAt (fun t => q (-t)) (-((fderiv ℝ ψ x₀) v)) 0 := by
    have hq0' : HasDerivAt q ((fderiv ℝ ψ x₀) v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hq0
    simpa [Function.comp_def] using
      hq0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hr0 : deriv r 0 = 0 := by
    simpa [r] using (hq0.fun_add hqneg0).deriv
  have hrcont : ContinuousAt r 0 :=
    (hq0.fun_add hqneg0).continuousAt
  have hmin : IsLocalMin r 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t
    have hLt : ∀ᶠ t : ℝ in 𝓝 0, u (L t) ≤ ψ (L t) :=
      hLcont.eventually htouch
    filter_upwards [hLt, hneg.eventually hLt] with t ht htneg
    have hc := hconv.2 (mem_univ (L t)) (mem_univ (L (-t)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmid :
        (1 / 2 : ℝ) • L t + (1 / 2 : ℝ) • L (-t) = x₀ := by
      dsimp [L]
      module
    rw [hmid] at hc
    change u x₀ ≤ (1 / 2 : ℝ) * u (L t) + (1 / 2 : ℝ) * u (L (-t)) at hc
    rw [hcontact] at hc
    have hrzero : r 0 = 2 * ψ x₀ := by
      simp [r, q, L, two_mul]
    rw [hrzero]
    change 2 * ψ x₀ ≤ ψ (L t) + ψ (L (-t))
    linarith
  by_contra hA
  have hA' : bilinearIteratedFDerivTwo ℝ ψ x₀ v v < 0 :=
    lt_of_not_ge hA
  have hmax : IsLocalMax r 0 :=
    isLocalMax_of_deriv_deriv_neg (by linarith [hsecond]) hr0 hrcont
  change ∀ᶠ t : ℝ in 𝓝 0, r t ≤ r 0 at hmax
  change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t at hmin
  have heq : r =ᶠ[𝓝 0] (fun _ : ℝ => r 0) := by
    filter_upwards [hmin, hmax] with t htmin htmax
    exact le_antisymm htmax htmin
  rcases _root_.mem_nhds_iff.mp heq with ⟨s, hs, hso, h0s⟩
  have hderiv : deriv r =ᶠ[𝓝 0] (fun _ : ℝ => 0) := by
    filter_upwards [hso.mem_nhds h0s] with t ht
    have hloc : r =ᶠ[𝓝 t] (fun _ : ℝ => r 0) := by
      filter_upwards [hso.mem_nhds ht] with y hy
      exact hs hy
    simpa using hloc.deriv_eq
  have hz : deriv (deriv r) 0 = 0 := by
    simpa using hderiv.deriv_eq
  linarith

/-- **A `C²` function touching a convex function from above has positive semidefinite Hessian at the
contact point** (viscosity tests). -/
theorem posSemidef_hessianMatrix_of_upper_touch {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (hessianMatrix ψ x₀).PosSemidef := by
  classical
  have hs := hψ.isSymmSndFDerivAt
    (by norm_num : minSmoothness ℝ 2 ≤ 2)
  unfold Matrix.PosSemidef
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa [hessianMatrix, bilinearIteratedFDerivTwo] using
      hs (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
  · intro z
    let v : EuclideanSpace ℝ (Fin n) :=
      z.sum (fun i zi => zi • EuclideanSpace.basisFun (Fin n) ℝ i)
    have hv := directional_second_deriv_nonneg hconv hψ hcontact htouch v
    have hquad :
        z.sum (fun i zi =>
            z.sum (fun j zj =>
              star zi * hessianMatrix ψ x₀ i j * zj)) =
          bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
      simp only [Finsupp.sum, star_trivial, hessianMatrix, bilinearIteratedFDerivTwo,
        EuclideanSpace.basisFun_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, map_sum,
        map_smul, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, v]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hs (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
      ring
    rw [hquad]
    exact hv

end FunctionalInequalities.Analysis

section TaylorHessianBound

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

/-! Second-order Taylor bound with the coordinate Hessian for `C²` test functions. -/

namespace FunctionalInequalities.Analysis

private lemma matrix_quadratic_formula
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin M v⟫ =
      ∑ i, ∑ j, v.ofLp i * (M i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp only [Matrix.mulVec, dotProduct, RCLike.inner_apply, Real.ringHom_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma hessianMatrix_quadratic
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin (hessianMatrix ψ x) v⟫ =
      (fderiv ℝ (fderiv ℝ ψ) x) v v := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x
  let c : Fin n → ℝ := fun i => (b.repr v).ofLp i
  have hv : ∑ i, c i • b i = v := b.sum_repr v
  have hc : ∀ i, c i = v.ofLp i := by
    intro i
    exact (EuclideanSpace.basisFun_repr (Fin n) ℝ v i).symm
  have hentry : ∀ i j, hessianMatrix ψ x i j = H (b i) (b j) := by
    intro i j
    change
      bilinearIteratedFDerivTwo ℝ ψ x (b i) (b j) =
        H (b i) (b j)
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    simpa [H] using iteratedFDeriv_two_apply ψ x ![b i, b j]
  have hfirst :
      H (∑ i, c i • b i) = ∑ i, H (c i • b i) := by
    rw [map_sum]
  have hsecond :
      ∀ i, (H (c i • b i)) (∑ j, c j • b j) =
        ∑ j, (H (c i • b i)) (c j • b j) := by
    intro i
    rw [map_sum]
  have hsum :
      H (∑ i, c i • b i) (∑ j, c j • b j) =
        ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
    calc
      H (∑ i, c i • b i) (∑ j, c j • b j) =
          (∑ i, H (c i • b i)) (∑ j, c j • b j) := by
            rw [hfirst]
      _ = ∑ i, (H (c i • b i)) (∑ j, c j • b j) := by
            rw [sum_apply]
      _ = ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsecond i]
            simp only [map_smul, smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [matrix_quadratic_formula]
  simp_rw [hentry, ← hc]
  rw [← hsum, hv]

private lemma local_taylor_two {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0,
      ∀ x ∈ ball x₀ r,
        |ψ x -
              (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
                (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀))| ≤
          ε * ‖x - x₀‖ ^ 2 := by
  classical
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x₀
  have hsymm : ∀ v w : EuclideanSpace ℝ (Fin n), B v w = B w v := by
    intro v w
    exact hψ.isSymmSndFDerivAt (by norm_num) v w
  rcases hψ.contDiffOn (m := 2) le_rfl (by simp) with ⟨u, hu, hψu⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨ρ, hρ, hρu⟩
  let s : Set (EuclideanSpace ℝ (Fin n)) := ball x₀ ρ
  have hs : Convex ℝ s := convex_ball x₀ ρ
  have hx₀s : x₀ ∈ s := mem_ball_self hρ
  have hψs : ContDiffOn ℝ 2 ψ s := hψu.mono hρu
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (1 / 2 : ℝ) * B (y - x₀) (y - x₀)
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ψ y - ψ x₀ - fderiv ℝ ψ x₀ (y - x₀) - q y
  let dg : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun y =>
    fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt g (dg y) s y := by
    intro y hy
    have hy' : ContDiffAt ℝ 2 ψ y := (hψs y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)
    have hψy : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
      (hy'.differentiableAt (by norm_num)).hasFDerivAt
    have hsub :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - x₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).sub_const x₀
    have hlin := (ContinuousLinearMap.hasFDerivAt (fderiv ℝ ψ x₀)).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hlin
    have hB := (ContinuousLinearMap.hasFDerivAt B).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hB
    have hquad₀ := hB.clm_apply hsub
    simp only [Function.comp_apply] at hquad₀
    have hquad_eq :
      B (y - x₀) ∘SL (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) + B.flip (y - x₀) =
        2 • B (y - x₀) := by
      ext z
      simp only [ContinuousLinearMap.comp_id, add_apply, ContinuousLinearMap.flip_apply,
        smul_apply]
      rw [hsymm z (y - x₀)]
      ring
    rw [hquad_eq] at hquad₀
    have hq : HasFDerivAt q (B (y - x₀)) y := by
      convert hquad₀.const_mul (1 / 2 : ℝ) using 1
      ext z
      norm_num [smul_apply, smul_eq_mul]
      ring
    have hg₀ := ((hψy.sub_const (ψ x₀)).sub hlin).sub hq
    have hg : HasFDerivAt g (dg y) y := by
      convert hg₀ using 1
      rfl
    convert hg.hasFDerivWithinAt (s := s) using 1
  have hB₀ :
    (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)) =o[𝓝 x₀]
      fun y => ‖y - x₀‖ := by
    have hfd : HasFDerivAt (fderiv ℝ ψ) B x₀ := by
      exact
        ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    simpa [B] using hfd.isLittleO.norm_right
  have hB₀' : dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ := by
    rw [Asymptotics.isLittleO_iff] at hB₀ ⊢
    intro c hc
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB₀ hc)
  have hB₀'' : dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 1 := by simpa using hB₀'
  have hg₀ : (fun y => g y - g x₀) =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ (1 + 1) :=
    hs.isLittleO_pow_succ hx₀s hderiv hB₀''
  have hgzero : g x₀ = 0 := by simp [g, q]
  have hg₀' : g =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 2 := by simpa [hgzero, pow_two] using hg₀
  have hev : ∀ᶠ y in 𝓝[s] x₀, ‖g y‖ ≤ ε * ‖y - x₀‖ ^ 2 := by
    have h := Asymptotics.IsLittleO.bound hg₀' hε
    filter_upwards [h] with y hy
    calc
      ‖g y‖ ≤ ε * ‖‖y - x₀‖ ^ 2‖ := hy
      _ = ε * ‖y - x₀‖ ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x₀‖))]
  rcases Metric.mem_nhdsWithin_iff.mp hev with ⟨δ, hδ, hδev⟩
  refine ⟨min ρ δ, lt_min hρ hδ, ?_⟩
  intro x hx
  have hx' : dist x x₀ < min ρ δ := Metric.mem_ball.mp hx
  have hxρ : x ∈ s := Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_left ρ δ))
  have hxδ : x ∈ ball x₀ δ := Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_right ρ δ))
  have hbound : ‖g x‖ ≤ ε * ‖x - x₀‖ ^ 2 := by
    have h := hδev ⟨hxδ, hxρ⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖x - x₀‖))] using h
  have hgexpr :
    g x =
      ψ x -
        (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
          (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀)) := by
    simp [g, q, sub_eq_add_neg]
    ring
  rw [hgexpr] at hbound
  simpa only [Real.norm_eq_abs] using hbound

/-- **Second-order Taylor bound with the coordinate Hessian** (viscosity tests):
for `ψ` twice differentiable at `x₀` (`ContDiffAt ℝ 2`), every `ε > 0` admits `r > 0` with
`|ψ x − ψ x₀ − Dψ(x₀)(x − x₀) − ½ ⟪x − x₀, ∇²ψ(x₀)(x − x₀)⟫| ≤ ε ‖x − x₀‖²` on `ball x₀ r`. -/
theorem exists_taylor_two_hessianMatrix_bound {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin (hessianMatrix ψ x₀) (x - x₀)⟫)| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  rcases local_taylor_two hψ hε with ⟨r, hr, hrbound⟩
  refine ⟨r, hr, ?_⟩
  intro x hx
  rw [hessianMatrix_quadratic]
  exact hrbound x hx

end FunctionalInequalities.Analysis

end TaylorHessianBound

section ViscosityTouchingAssembly

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! Viscosity inequalities for Alexandrov solutions: the determinant of the Hessian of a `C²` test
touching from above (below) is bounded below (above) by the Monge–Ampère density. -/

namespace FunctionalInequalities.Analysis

private lemma touching_positive_parameter {P : ℝ → Prop}
    (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ t > 0, P t := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

private lemma touching_closedBall {n : ℕ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {P : EuclideanSpace ℝ (Fin n) → Prop}
    (hP : ∀ᶠ x in 𝓝 x₀, P x) :
    ∃ r > 0, ∀ x ∈ closedBall x₀ r, P x := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro x hx
  exact hsub (closedBall_subset_ball (by linarith : R / 2 < R) hx)

private lemma touching_posDef_perturbation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∀ᶠ t : ℝ in 𝓝 0, (A + t • 1).PosDef := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < hA.1.eigenvalues i + t :=
    Filter.eventually_all.mpr fun i =>
      continuous_const.continuousAt.eventually_lt
        (continuous_const.add continuous_id).continuousAt
        (by simpa only [add_zero] using hA.eigenvalues_pos i)
  filter_upwards [hev] with t ht
  let e :=
    Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
      hA.1.eigenvectorUnitary
  have he : e (Matrix.diagonal hA.1.eigenvalues) = A := by
    simpa [e] using hA.1.spectral_theorem.symm
  have hid :
      Matrix.diagonal (fun _ : Fin n => t) =
        t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    calc
      Matrix.diagonal (fun _ : Fin n => t) =
          Matrix.diagonal (t • (fun _ : Fin n => (1 : ℝ))) := by
        apply congrArg Matrix.diagonal
        funext i
        exact (mul_one t).symm
      _ = t • 1 := by
        rw [Matrix.diagonal_smul, Matrix.diagonal_one]
  have heq :
      A + t • 1 =
        e (Matrix.diagonal (fun i => hA.1.eigenvalues i + t)) := by
    rw [← Matrix.diagonal_add, hid, map_add, map_smul, map_one, he]
  rw [heq]
  change
    ((hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => hA.1.eigenvalues i + t) *
      star (hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).PosDef
  exact
    (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
      (Matrix.posDef_diagonal_iff.mpr ht)

/-- Actual small positive-definite perturbation and Taylor data, shared by
an actual MA-to-lower-test proof and the actual Perron C2-test source. -/
private lemma touching_lower_quadratic_data {n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hA : (hessianMatrix ψ x₀).PosDef)
    {a : ℝ} (ha : a < (hessianMatrix ψ x₀).det) :
    ∃ ε > 0,
      (hessianMatrix ψ x₀ + (-(4 * ε)) • 1).PosDef ∧
      a < (hessianMatrix ψ x₀ + (-(4 * ε)) • 1).det ∧
      ∃ ρ > 0, ∀ y ∈ ball x₀ ρ,
        |ψ y - quadraticAt (hessianMatrix ψ x₀) x₀
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ ψ x₀)) (ψ x₀) y| ≤ ε * ‖y - x₀‖ ^ 2 := by
  let A := hessianMatrix ψ x₀
  have hdcont : Continuous (fun t : ℝ => (A + (-(4 * t)) • 1).det) :=
    (continuous_const.add
      ((continuous_const.mul continuous_id).neg.smul continuous_const)).matrix_det
  have hdnear : ∀ᶠ t : ℝ in 𝓝 0, a < (A + (-(4 * t)) • 1).det :=
    continuous_const.continuousAt.eventually_lt hdcont.continuousAt (by simpa using ha)
  have htendsto : Tendsto (fun t : ℝ => -(4 * t)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => -(4 * t)) :=
      (continuous_const.mul continuous_id).neg
    simpa only [mul_zero, neg_zero] using hc.tendsto 0
  have hpnear : ∀ᶠ t : ℝ in 𝓝 0, (A + (-(4 * t)) • 1).PosDef :=
    htendsto.eventually (touching_posDef_perturbation hA)
  obtain ⟨ε, hε, hdet, hpd⟩ := touching_positive_parameter (hdnear.and hpnear)
  obtain ⟨ρ, hρ, htaylor⟩ := exists_taylor_two_hessianMatrix_bound hψ hε
  refine ⟨ε, hε, hpd, hdet, ρ, hρ, ?_⟩
  intro y hy
  simpa only [quadraticAt, InnerProductSpace.toDual_symm_apply] using htaylor y hy

private lemma touching_quadratic_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b x : EuclideanSpace ℝ (Fin n)) (c d t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b d x + (c - d) + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  have ha :
      Matrix.toEuclideanLin (A + t • 1) (x - x₀) =
        Matrix.toEuclideanLin A (x - x₀) + t • (x - x₀) := by
    change Matrix.toLpLin 2 2 (A + t • 1) (x - x₀) = _
    rw [map_add, map_smul, Matrix.toLpLin_one]
    rfl
  rw [ha, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

private lemma touching_comparison_set {n : ℕ}
    {v w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : ConvexOn ℝ univ v) (hw : ConvexOn ℝ univ w)
    {x₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hcenter : w x₀ < v x₀)
    (hsphere : ∀ x, ‖x - x₀‖ = r → v x ≤ w x) :
    ∃ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G ∧ G ⊆ ball x₀ r ∧ Bornology.IsBounded G ∧ G.Nonempty ∧
        subgradientImage v G ⊆ subgradientImage w G := by
  have hvc : Continuous v :=
    continuousOn_univ.mp (hv.continuousOn isOpen_univ)
  have hwc : Continuous w :=
    continuousOn_univ.mp (hw.continuousOn isOpen_univ)
  let G : Set (EuclideanSpace ℝ (Fin n)) :=
    ball x₀ r ∩ {x | w x < v x}
  have hGo : IsOpen G := isOpen_ball.inter (isOpen_lt hwc hvc)
  have hGball : G ⊆ ball x₀ r := fun _ hx => hx.1
  have hGb : Bornology.IsBounded G := isBounded_ball.subset hGball
  have hGeq : ∀ x ∈ frontier G, w x = v x := by
    intro x hx
    have hxclG : x ∈ closure G := frontier_subset_closure hx
    have hxclB : x ∈ closedBall x₀ r :=
      closure_minimal
        (fun y hy => ball_subset_closedBall (hGball (show y ∈ G from hy)))
        isClosed_closedBall hxclG
    have hle : w x ≤ v x := by
      apply closure_minimal
        (s := G) (t := {y | w y ≤ v y}) ?_
        (isClosed_le hwc hvc) hxclG
      intro y hy
      change w y ≤ v y
      exact le_of_lt (show w y < v y from hy.2)
    have hxnotG : x ∉ G := by
      rw [hGo.frontier_eq] at hx
      exact hx.2
    by_cases hxb : x ∈ ball x₀ r
    · exact le_antisymm hle
        (le_of_not_gt fun hlt => hxnotG ⟨hxb, hlt⟩)
    · have hnle : ‖x - x₀‖ ≤ r := by
        simpa only [mem_closedBall, dist_eq_norm] using hxclB
      have hnge : r ≤ ‖x - x₀‖ := by
        apply le_of_not_gt
        intro hlt
        apply hxb
        simpa only [mem_ball, dist_eq_norm] using hlt
      exact le_antisymm hle (hsphere x (le_antisymm hnle hnge))
  refine ⟨G, hGo, hGball, hGb, ⟨x₀, mem_ball_self hr, hcenter⟩, ?_⟩
  exact subgradientImage_subset_of_le hw hv hGo hGb
    (fun x hx => le_of_lt (show w x < v x from hx.2)) hGeq

private lemma touching_cancel_volume {n : ℕ}
    {G : Set (EuclideanSpace ℝ (Fin n))}
    (hpos : 0 < volume G) (hfin : volume G < ∞)
    {a b : ℝ} (hb : 0 ≤ b)
    (h : ENNReal.ofReal a * volume G ≤ ENNReal.ofReal b * volume G) :
    a ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  exact
    (ENNReal.mul_le_mul_iff_right (ne_of_gt hpos) (ne_of_lt hfin)).mp
      (by simpa only [mul_comm] using h)

/--
**Upper touching test for an Alexandrov solution** (viscosity inequality): if the subgradient
images of the convex `u` on open subsets of `Ω` carry the density `f`
(`vol (∂u(G)) = ∫_G f`), `f` is continuous at `x₀ ∈ Ω`, and a `C²` function `ψ` touches `u` from
above
at `x₀` (`u ≤ ψ` near `x₀`, `u x₀ = ψ x₀`), then `f x₀ ≤ det ∇²ψ(x₀)` (standard coordinates of
`EuclideanSpace ℝ (Fin n)`, `hessianMatrix ψ x₀ i j = D²ψ(x₀)(eᵢ, eⱼ)`). -/
theorem le_det_hessianMatrix_of_upper_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G →
          G ⊆ Ω →
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
              ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (hessianMatrix ψ x₀).det := by
  classical
  apply le_of_not_gt
  intro hbad
  let A := hessianMatrix ψ x₀
  have hA : A.PosSemidef := posSemidef_hessianMatrix_of_upper_touch hconv hψ hcontact htouch
  change A.det < f x₀ at hbad
  obtain ⟨a, hAa, haf⟩ := exists_between hbad
  have hdcont : Continuous (fun t : ℝ => (A + (4 * t) • 1).det) :=
    (continuous_const.add
        ((continuous_const.mul continuous_id).smul continuous_const)).matrix_det
  have hdnear : ∀ᶠ t : ℝ in 𝓝 0, (A + (4 * t) • 1).det < a :=
    hdcont.continuousAt.eventually_lt continuous_const.continuousAt (by simpa using hAa)
  obtain ⟨ε, hε, hdet⟩ := touching_positive_parameter hdnear
  let M : Matrix (Fin n) (Fin n) ℝ := A + (4 * ε) • 1
  have hM : M.PosDef := by
    dsimp only [M]
    simpa only [add_comm] using
      (Matrix.PosDef.one.smul (show 0 < 4 * ε by positivity)).add_posSemidef hA
  have hMdet : M.det < a := hdet
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x₀)
  let q := quadraticAt A x₀ b (ψ x₀)
  obtain ⟨ρ, hρ, htaylor⟩ := exists_taylor_two_hessianMatrix_bound hψ hε
  have htaylor' (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x₀ ρ) :
    |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    simpa only [q, A, b, quadraticAt, InnerProductSpace.toDual_symm_apply] using htaylor x hx
  have hfnear : ∀ᶠ x in 𝓝 x₀, a < f x := continuous_const.continuousAt.eventually_lt hf haf
  have hnear : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ u x ≤ ψ x ∧ a ≤ f x ∧ |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htouch, hfnear, ball_mem_nhds x₀ hρ] with x hxΩ hxu hxf hxt
    exact ⟨hxΩ, hxu, le_of_lt hxf, htaylor' x hxt⟩
  obtain ⟨r, hr, hlocal⟩ := touching_closedBall hnear
  let w := quadraticAt M x₀ b (ψ x₀ - ε * r ^ 2)
  have hwconv : ConvexOn ℝ univ w := convexOn_quadraticAt hM.posSemidef x₀ b (ψ x₀ - ε * r ^ 2)
  have hwformula (x : EuclideanSpace ℝ (Fin n)) :
    w x = q x - ε * r ^ 2 + 2 * ε * ‖x - x₀‖ ^ 2 := by
    dsimp only [w, M, q]
    rw [touching_quadratic_shift A x₀ b x (ψ x₀ - ε * r ^ 2) (ψ x₀) (4 * ε)]
    ring
  have hwcenter : w x₀ = ψ x₀ - ε * r ^ 2 := by simp [w, quadraticAt]
  have hcenter : w x₀ < u x₀ := by
    rw [hwcenter, hcontact]
    have hpos : 0 < ε * r ^ 2 := mul_pos hε (sq_pos_of_pos hr)
    linarith
  have hsphere : ∀ x, ‖x - x₀‖ = r → u x ≤ w x := by
    intro x hxr
    have hx : x ∈ closedBall x₀ r := by
      simpa only [mem_closedBall, dist_eq_norm, hxr] using (le_refl r)
    have hloc := hlocal x hx
    have he := (abs_le.mp hloc.2.2.2).2
    rw [hxr] at he
    rw [hwformula, hxr]
    nlinarith [hloc.2.1]
  obtain ⟨G, hGo, hGball, hGb, hGne, hcomp⟩ :=
    touching_comparison_set hconv hwconv hr hcenter hsphere
  have hGΩ : G ⊆ Ω := by
    intro x hx
    exact (hlocal x (ball_subset_closedBall (hGball hx))).1
  have hGpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) G :=
    IsOpen.measure_pos volume hGo hGne
  have hGfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) G < ∞ := hGb.measure_lt_top
  have hmul : ENNReal.ofReal a * volume G ≤ ENNReal.ofReal M.det * volume G := by
    calc
      ENNReal.ofReal a * volume G = ∫⁻ x in G, ENNReal.ofReal a ∂volume :=
        (setLIntegral_const G (ENNReal.ofReal a)).symm
      _ ≤ ∫⁻ x in G, ENNReal.ofReal (f x) ∂volume := by
        apply setLIntegral_mono' hGo.measurableSet
        intro x hx
        exact ENNReal.ofReal_mono (hlocal x (ball_subset_closedBall (hGball hx))).2.2.1
      _ = volume (subgradientImage u G) := (hMA G hGo hGΩ).symm
      _ ≤ volume (subgradientImage w G) := measure_mono hcomp
      _ = ENNReal.ofReal M.det * volume G :=
        volume_subgradientImage_quadraticAt hM x₀ b (ψ x₀ - ε * r ^ 2) hGo.measurableSet
  have hcoef : a ≤ M.det := touching_cancel_volume hGpos hGfin hM.det_pos.le hmul
  exact (not_le_of_gt hMdet) hcoef

/-- **Lower touching test for an Alexandrov solution**: with the
same Alexandrov hypothesis, if `ψ ∈ C²` touches `u` from below at `x₀` (`ψ ≤ u` near `x₀`,
`u x₀ = ψ x₀`) and `∇²ψ(x₀)` is positive semidefinite, then `det ∇²ψ(x₀) ≤ f x₀`. -/
theorem det_hessianMatrix_le_of_lower_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hf0 : 0 ≤ f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (hessianMatrix ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (hessianMatrix ψ x₀).det ≤ f x₀ := by
  classical
  apply le_of_not_gt
  intro hbad
  let A := hessianMatrix ψ x₀
  change f x₀ < A.det at hbad
  have hA : A.PosDef :=
    hH.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt hf0 hbad))
  obtain ⟨a, hfa, haA⟩ := exists_between hbad
  have ha0 : 0 ≤ a := le_trans hf0 hfa.le
  obtain ⟨ε, hε, hpd, hdet, ρ, hρ, htaylor⟩ :=
    touching_lower_quadratic_data hψ hA haA
  let M : Matrix (Fin n) (Fin n) ℝ := A + (-(4 * ε)) • 1
  have hM : M.PosDef := hpd
  have hMdet : a < M.det := hdet
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ ψ x₀)
  let q := quadraticAt A x₀ b (ψ x₀)
  have htaylor' (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x₀ ρ) :
      |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    simpa only [q, A, b] using htaylor x hx
  have hfnear : ∀ᶠ x in 𝓝 x₀, f x < a :=
    hf.eventually_lt continuous_const.continuousAt hfa
  have hnear : ∀ᶠ x in 𝓝 x₀,
      x ∈ Ω ∧ ψ x ≤ u x ∧ f x ≤ a ∧
        |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htouch, hfnear, ball_mem_nhds x₀ hρ]
      with x hxΩ hxu hxf hxt
    exact ⟨hxΩ, hxu, le_of_lt hxf, htaylor' x hxt⟩
  obtain ⟨r, hr, hlocal⟩ := touching_closedBall hnear
  let w := quadraticAt M x₀ b (ψ x₀ + ε * r ^ 2)
  have hwconv : ConvexOn ℝ univ w :=
    convexOn_quadraticAt hM.posSemidef x₀ b (ψ x₀ + ε * r ^ 2)
  have hwformula (x : EuclideanSpace ℝ (Fin n)) :
      w x = q x + ε * r ^ 2 - 2 * ε * ‖x - x₀‖ ^ 2 := by
    dsimp only [w, M, q]
    rw [touching_quadratic_shift A x₀ b x
      (ψ x₀ + ε * r ^ 2) (ψ x₀) (-(4 * ε))]
    ring
  have hwcenter : w x₀ = ψ x₀ + ε * r ^ 2 := by
    simp [w, quadraticAt]
  have hcenter : u x₀ < w x₀ := by
    rw [hwcenter, hcontact]
    have hpos : 0 < ε * r ^ 2 := mul_pos hε (sq_pos_of_pos hr)
    linarith
  have hsphere : ∀ x, ‖x - x₀‖ = r → w x ≤ u x := by
    intro x hxr
    have hx : x ∈ closedBall x₀ r := by
      simpa only [mem_closedBall, dist_eq_norm, hxr] using (le_refl r)
    have hloc := hlocal x hx
    have he := (abs_le.mp hloc.2.2.2).1
    rw [hxr] at he
    rw [hwformula, hxr]
    nlinarith [hloc.2.1]
  obtain ⟨G, hGo, hGball, hGb, hGne, hcomp⟩ :=
    touching_comparison_set hwconv hconv hr hcenter hsphere
  have hGΩ : G ⊆ Ω := by
    intro x hx
    exact (hlocal x (ball_subset_closedBall (hGball hx))).1
  have hGpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) G :=
    IsOpen.measure_pos volume hGo hGne
  have hGfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) G < ∞ :=
    hGb.measure_lt_top
  have hmul :
      ENNReal.ofReal M.det * volume G ≤ ENNReal.ofReal a * volume G := by
    calc
      ENNReal.ofReal M.det * volume G =
          volume (subgradientImage w G) :=
        (volume_subgradientImage_quadraticAt hM x₀ b
          (ψ x₀ + ε * r ^ 2) hGo.measurableSet).symm
      _ ≤ volume (subgradientImage u G) := measure_mono hcomp
      _ = ∫⁻ x in G, ENNReal.ofReal (f x) ∂volume := hMA G hGo hGΩ
      _ ≤ ∫⁻ x in G, ENNReal.ofReal a ∂volume := by
        apply setLIntegral_mono' hGo.measurableSet
        intro x hx
        exact ENNReal.ofReal_mono
          (hlocal x (ball_subset_closedBall (hGball hx))).2.2.1
      _ = ENNReal.ofReal a * volume G :=
        setLIntegral_const G (ENNReal.ofReal a)
  have hcoef : M.det ≤ a :=
    touching_cancel_volume hGpos hGfin ha0 hmul
  exact (not_le_of_gt hMdet) hcoef

end FunctionalInequalities.Analysis

end ViscosityTouchingAssembly

namespace FunctionalInequalities.Analysis
open Classical Matrix

/-- A bound on positive-definite quadratic lower tests also bounds the determinant
of every positive-semidefinite C² lower test at the same point. -/
theorem det_hessianMatrix_le_of_quadratic_lower_tests {n : ℕ}
    {U ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hquad :
      ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        A.PosDef → ∀ x ∈ Ω, ∀ b, (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y ≤ U y) → A.det ≤ 1)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hH : (hessianMatrix ψ x₀).PosSemidef) (hcontact : U x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ U x) : (hessianMatrix ψ x₀).det ≤ 1 := by
  apply le_of_not_gt
  intro hbad
  let A := hessianMatrix ψ x₀
  change 1 < A.det at hbad
  have hA : A.PosDef := hH.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hbad))
  obtain ⟨ε, hε, hpd, hdet, ρ, hρ, htaylor⟩ := touching_lower_quadratic_data hψ hA hbad
  let M : Matrix (Fin n) (Fin n) ℝ := A + (-(4 * ε)) • 1
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x₀)
  let q := quadraticAt A x₀ b (ψ x₀)
  have htaylor' (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball x₀ ρ) :
    |ψ y - q y| ≤ ε * ‖y - x₀‖ ^ 2 := by simpa only [q, A, b] using htaylor y hy
  have htest : ∀ᶠ y in 𝓝 x₀, quadraticAt M x₀ b (U x₀) y ≤ U y := by
    filter_upwards [htouch, ball_mem_nhds x₀ hρ] with y hy hball
    have hT := htaylor' y hball
    have hshift : quadraticAt M x₀ b (U x₀) y = q y - 2 * ε * ‖y - x₀‖ ^ 2 := by
      rw [hcontact]
      dsimp only [M, q]
      rw [quadraticAt_shift]
      ring
    rw [hshift]
    have hab := (abs_le.mp hT).1
    have hn : 0 ≤ ε * ‖y - x₀‖ ^ 2 := mul_nonneg hε.le (sq_nonneg _)
    nlinarith only [hab, hy, hn]
  have hd := hquad M hpd x₀ hx₀ b htest
  exact (not_lt_of_ge hd) hdet

end FunctionalInequalities.Analysis
