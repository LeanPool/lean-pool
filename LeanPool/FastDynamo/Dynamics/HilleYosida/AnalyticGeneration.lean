/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.AnalyticSemigroup
public import LeanPool.FastDynamo.Dynamics.HilleYosida.Semigroup
public import LeanPool.FastDynamo.Dynamics.StrongSolutionUniqueness
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import LeanPool.FastDynamo.Operator.StrongHolomorphy

/-!
# Sector-dissipative Hille–Yosida generators generate analytic semigroups

`HilleYosidaRay.isAnalyticSemigroup_of_sectorial`: if a densely defined domain operator `A`
on a complex Hilbert space has a Hille–Yosida ray and its numerical range lies in a shifted
quarter sector,

`|Im ⟪ι d, A d⟫| ≤ ω ‖ι d‖² - Re ⟪ι d, A d⟫`  for every domain element `d`,

then the semigroup `hy.semigroup hdense` it generates is analytic of angle `π/4` in the sense
of `IsAnalyticSemigroup` (Engel–Nagel, Definition II.4.5).  This is the analyticity half of
the paper's Lemma A.1 (`lem:semigroup-spectral-growth`) in abstract form.  The paper obtains
analyticity from the analyticity of the diffusion semigroup and a relative bound of the
remaining terms (Engel–Nagel, Theorem III.2.10); here it is obtained from the sector condition,
by extending the Yosida approximation of the Hille–Yosida construction to complex times.

* **Geometry.**  `closedQuarterSector = {|Im z| ≤ Re z}` contains `openSector (π/4)`
  (`openSector_pi_div_four_subset`) and is a convex cone.
* **Exponential bounds.**  `norm_exp_smul_le_of_sectorial`: a bounded operator `B` with
  `|Im ⟪x, B x⟫| ≤ c ‖x‖² - Re ⟪x, B x⟫` has `‖exp (w B)‖ ≤ exp (c Re w)` on the closed quarter
  sector (energy estimate for the orbit of `w B`, whose numerical range lies in the half-plane
  `Re ≤ c Re w`).
  `HilleYosidaRay.sectorial_yosida`: the sector condition of `A` passes to its Yosida
  approximants `A_s` for large `s`, with `ω` replaced by `ω + 1`.
* **Cauchy estimate.**  `norm_exp_apply_sub_exp_apply_le` compares the exponentials of two
  commuting operators; for the approximants it gives `norm_exp_smul_yosida_sub_le`.
* **The extension.**  `HilleYosidaRay.sectorExtension z` is the strong limit of `exp (z A_s)`;
  the limit is locally uniform in `z` on the closed quarter sector
  (`uniformCauchySeqOn_exp_smul_yosida`,
  `HilleYosidaRay.tendstoLocallyUniformlyOn_sectorExtension`),
  agrees with the semigroup at real times (`HilleYosidaRay.sectorExtension_ofReal`), obeys the
  semigroup law (`HilleYosidaRay.sectorExtension_add`) and is bounded by `exp (c ‖z‖)`
  (`HilleYosidaRay.norm_sectorExtension_le`).  Holomorphy of the orbits follows from
  `TendstoLocallyUniformlyOn.differentiableOn`, holomorphy in the operator norm from
  `differentiableOn_of_forall_apply`.
-/

@[expose] public section

namespace FastDynamo

open Filter Topology NormedSpace

universe u v

/-- The closed quarter-plane sector `{z ∈ ℂ | |Im z| ≤ Re z}` (half-opening `π/4`, vertex
included), on which the approximant exponentials are controlled. -/
def closedQuarterSector : Set ℂ := {z : ℂ | |z.im| ≤ z.re}

/-- The open sector of half-opening `π/4` lies in the closed quarter sector: for
`|θ| < π/4` one has `|sin θ| < cos θ`, because `cos θ ∓ sin θ = √2 cos (θ ± π/4) > 0`. -/
theorem openSector_pi_div_four_subset : openSector (Real.pi / 4) ⊆ closedQuarterSector := by
  rintro z ⟨-, hz⟩
  obtain ⟨h1, h2⟩ := abs_lt.mp hz
  set θ := Complex.arg z
  have hs : 0 < Real.sqrt 2 / 2 := by positivity
  have hp : 0 < Real.cos (θ + Real.pi / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hm : 0 < Real.cos (θ - Real.pi / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_pos]⟩
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four] at hp
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four] at hm
  have hsin : Real.sin θ < Real.cos θ := by nlinarith
  have hsin' : -Real.cos θ < Real.sin θ := by nlinarith
  have hre := Complex.norm_mul_cos_arg z
  have him := Complex.norm_mul_sin_arg z
  change |z.im| ≤ z.re
  rw [← hre, ← him, abs_mul, abs_norm]
  refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (norm_nonneg _)

/-- A nonnegative real multiple of a point of the closed quarter sector lies in it. -/
theorem smul_mem_closedQuarterSector {z : ℂ} (hz : z ∈ closedQuarterSector) {u : ℝ}
    (hu : 0 ≤ u) : (u : ℂ) * z ∈ closedQuarterSector := by
  change |((u : ℂ) * z).im| ≤ ((u : ℂ) * z).re
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_of_nonneg hu]
  exact mul_le_mul_of_nonneg_left hz hu

/-- The closed quarter sector is closed under addition. -/
theorem add_mem_closedQuarterSector {z w : ℂ} (hz : z ∈ closedQuarterSector)
    (hw : w ∈ closedQuarterSector) : z + w ∈ closedQuarterSector := by
  change |(z + w).im| ≤ (z + w).re
  rw [Complex.add_im, Complex.add_re]
  exact (abs_add_le _ _).trans (add_le_add hz hw)

section Exponential

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/--
**Exponential bound from a sector condition.**  If a bounded operator `B` has its numerical
range in the shifted quarter sector, `|Im ⟪x, B x⟫| ≤ c ‖x‖² - Re ⟪x, B x⟫`, then
`‖exp (w B)‖ ≤ exp (c Re w)` for every `w` with `|Im w| ≤ Re w`.

For such `w` the numerical range of `w B` lies in the half-plane `Re ≤ c Re w`, so the
orbit `τ ↦ exp (τ w B) x` obeys the energy estimate
`DomainOperator.norm_embedding_le_exp_of_isForwardStrongSolution` for the bounded domain
operator with identity embedding and operator `w B`; at `τ = 1` this is the claim.
-/
theorem norm_exp_smul_le_of_sectorial (B : X →L[ℂ] X) (c : ℝ)
    (hB : ∀ x : X, |(inner ℂ x (B x)).im| ≤ c * ‖x‖ ^ 2 - (inner ℂ x (B x)).re)
    {w : ℂ} (hw : w ∈ closedQuarterSector) :
    ‖exp (w • B)‖ ≤ Real.exp (c * w.re) := by
  let D : DomainOperator X X :=
    { embedding := ContinuousLinearMap.id ℂ X
      embedding_injective := Function.injective_id
      op := w • B }
  have hw' : |w.im| ≤ w.re := hw
  have hre : 0 ≤ w.re := (abs_nonneg _).trans hw'
  have hM : ∀ x : X, (inner ℂ (D.embedding x) (D.op x)).re ≤ c * w.re * ‖D.embedding x‖ ^ 2 := by
    intro x
    have hx := hB x
    simp only [D, ContinuousLinearMap.id_apply, smul_apply, inner_smul_right,
      Complex.mul_re]
    set p := inner ℂ x (B x)
    have h1 : -(w.im * p.im) ≤ w.re * |p.im| := by
      calc -(w.im * p.im) ≤ |w.im * p.im| := neg_le_abs _
        _ = |w.im| * |p.im| := abs_mul _ _
        _ ≤ w.re * |p.im| := mul_le_mul_of_nonneg_right hw' (abs_nonneg _)
    have h2 : w.re * |p.im| ≤ w.re * (c * ‖x‖ ^ 2 - p.re) := mul_le_mul_of_nonneg_left hx hre
    nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x ↦ ?_
  have htraj : D.IsForwardStrongSolution (fun τ : ℝ ↦ exp (τ • (w • B)) x) := by
    intro t _
    have h := (hasStrictDerivAt_exp_smul_const' (𝕂 := ℝ) (w • B) t).hasDerivAt
    have h2 := ((ContinuousLinearMap.apply ℂ X x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t h
    simpa [D, Function.comp_def] using h2.hasDerivWithinAt
  have h := D.norm_embedding_le_exp_of_isForwardStrongSolution (c * w.re) hM htraj zero_le_one
  simpa [D] using h

/--
**Cauchy estimate for two commuting exponentials.**  If `B` and `C` commute and
`‖exp (u B)‖, ‖exp (u C)‖ ≤ K` for `u ∈ [0, 1]`, then
`‖exp B x - exp C x‖ ≤ K² ‖B x - C x‖`.

The interpolation `u ↦ exp ((1 - u) C) (exp (u B) x)` joins `exp C x` to `exp B x`; its
derivative (`HilleYosida.hasDerivAt_conjugate`) is `exp ((1 - u) C) (exp (u B) (B x - C x))`
once `C` has been moved across `exp (u B)`, and the mean value inequality on `[0, 1]`
gives the claim.  This is the complex-time form of `norm_approx_sub_approx_le`.
-/
theorem norm_exp_apply_sub_exp_apply_le {B C : X →L[ℂ] X} (hc : Commute B C) {K : ℝ}
    (hB : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖exp (u • B)‖ ≤ K)
    (hC : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖exp (u • C)‖ ≤ K) (x : X) :
    ‖exp B x - exp C x‖ ≤ K ^ 2 * ‖B x - C x‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖-(exp ((1 - u) • C) (C (exp (u • B) x))) + exp ((1 - u) • C) (exp (u • B) (B x))‖
        ≤ K ^ 2 * ‖B x - C x‖ := by
    rintro u ⟨hu0, hu1⟩
    have hcomm : exp (u • B) (C x) = C (exp (u • B) x) := by
      simpa [ContinuousLinearMap.mul_apply'] using
        DFunLike.congr_fun (HilleYosida.exp_commute hc u) x
    have hrw : -(exp ((1 - u) • C) (C (exp (u • B) x))) + exp ((1 - u) • C) (exp (u • B) (B x))
        = exp ((1 - u) • C) (exp (u • B) (B x - C x)) := by
      simp only [map_sub, hcomm]
      abel
    rw [hrw]
    calc ‖exp ((1 - u) • C) (exp (u • B) (B x - C x))‖
        ≤ K * ‖exp (u • B) (B x - C x)‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (hC (1 - u) ⟨by linarith, by linarith⟩) (norm_nonneg _))
      _ ≤ K * (K * ‖B x - C x‖) := mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (hB u ⟨hu0, hu1⟩) (norm_nonneg _))) hK
      _ = K ^ 2 * ‖B x - C x‖ := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ ↦ HilleYosida.expR C (1 - u) (exp (u • B) x))
    (fun u _ ↦ (HilleYosida.hasDerivAt_conjugate B C 1 x u).hasDerivWithinAt)
    hbound (convex_Icc 0 1) (Set.left_mem_Icc.mpr zero_le_one)
    (Set.right_mem_Icc.mpr zero_le_one)
  simpa [HilleYosida.expR] using h

end Exponential

section Approximant

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] {A : DomainOperator X D}

omit [CompleteSpace X] in
/--
**The sector condition passes to the Yosida approximants.**  If
`|Im ⟪ι d, A d⟫| ≤ ω ‖ι d‖² - Re ⟪ι d, A d⟫` for every domain element (with `ω ≥ 0`), then
for every parameter `s > M` with `s ≥ 2 (ω + 1) ω` the Yosida approximant `A_s` satisfies
`|Im ⟪x, A_s x⟫| ≤ (ω + 1) ‖x‖² - Re ⟪x, A_s x⟫` for every vector `x`.

Write `x = s ι d - A d` with `d` the domain-valued resolvent of `x`; then `A_s x = s A d`,
so `⟪x, A_s x⟫ = s² ⟪ι d, A d⟫ - s ‖A d‖²` and
`‖x‖² = s² ‖ι d‖² - 2 s Re ⟪ι d, A d⟫ + ‖A d‖²`.  The claim reduces to
`s ‖ι d‖² (s - 2 (ω + 1) ω) + (ω + 1 + s) ‖A d‖² ≥ 0`, using `Re ⟪ι d, A d⟫ ≤ ω ‖ι d‖²`.
-/
theorem HilleYosidaRay.sectorial_yosida {M : ℝ} (hy : HilleYosidaRay A M) {ω : ℝ}
    (hω : 0 ≤ ω)
    (hsect : ∀ d : D, |(inner ℂ (A.embedding d) (A.op d)).im| ≤
      ω * ‖A.embedding d‖ ^ 2 - (inner ℂ (A.embedding d) (A.op d)).re)
    {s : ℝ} (hs : M < s) (hs' : 2 * (ω + 1) * ω ≤ s) (x : X) :
    |(inner ℂ x (hy.yosida s x)).im| ≤
      (ω + 1) * ‖x‖ ^ 2 - (inner ℂ x (hy.yosida s x)).re := by
  have hmem := hy.mem_ofReal s hs
  have hs0 : 0 ≤ s := le_trans (by positivity) hs'
  set d := hy.resolvent.inv (s : ℂ) x with hd
  set y := A.embedding d
  set v := A.op d
  have hx : x = (s : ℂ) • y - v := by
    have h := DFunLike.congr_fun (hy.resolvent.right_inv _ hmem) x
    simpa [DomainOperator.pencil, ← hd] using h.symm
  have hR : hy.resolvent.stateResolvent (s : ℂ) x = y := rfl
  have hA : hy.yosida s x = (s : ℂ) • v := by
    simp only [HilleYosidaRay.yosida, sub_apply, smul_apply, hR, ContinuousLinearMap.id_apply]
    rw [hx]
    simp only [← Complex.coe_smul, smul_sub, smul_smul]
    push_cast
    ring_nf
    abel
  have hinner : inner ℂ x (hy.yosida s x) =
      (s : ℂ) * ((s : ℂ) * inner ℂ y v) - (s : ℂ) * inner ℂ v v := by
    rw [hA, hx, inner_sub_left, inner_smul_left, inner_smul_right, inner_smul_right,
      Complex.conj_ofReal]
  have hvv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    rw [← RCLike.re_to_complex]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hvv' : (inner ℂ v v).im = 0 := by
    rw [← RCLike.im_to_complex]
    exact inner_self_im (𝕜 := ℂ) v
  have hnorm : ‖x‖ ^ 2 = s ^ 2 * ‖y‖ ^ 2 - 2 * s * (inner ℂ y v).re + ‖v‖ ^ 2 := by
    rw [hx, @norm_sub_sq ℂ, norm_smul, inner_smul_left, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0]
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
  set p := inner ℂ y v
  have hre : (inner ℂ x (hy.yosida s x)).re = s ^ 2 * p.re - s * ‖v‖ ^ 2 := by
    rw [hinner]
    simp only [Complex.sub_re, Complex.re_ofReal_mul, hvv]
    ring
  have him : (inner ℂ x (hy.yosida s x)).im = s ^ 2 * p.im := by
    rw [hinner]
    simp only [Complex.sub_im, Complex.im_ofReal_mul, hvv']
    ring
  have hsd := hsect d
  have hpre : p.re ≤ ω * ‖y‖ ^ 2 := by linarith [abs_nonneg p.im]
  rw [hre, him, hnorm, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2)]
  have h1 : s ^ 2 * |p.im| ≤ s ^ 2 * (ω * ‖y‖ ^ 2 - p.re) :=
    mul_le_mul_of_nonneg_left hsd (by positivity)
  have h2 : 2 * s * (ω + 1) * p.re ≤ 2 * s * (ω + 1) * (ω * ‖y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hpre (by positivity)
  have h3 : 0 ≤ s * ‖y‖ ^ 2 * (s - 2 * (ω + 1) * ω) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ (ω + 1 + s) * ‖v‖ ^ 2 := by positivity
  nlinarith

open scoped Classical in
/--
The extension of the Hille–Yosida semigroup to complex times: at `z` it is the strong limit
of the approximant exponentials `exp (z A_s)` as `s → ∞` whenever that limit exists for
every vector (a bounded operator by the Banach–Steinhaus theorem,
`continuousLinearMapOfTendsto`), and `0` otherwise.  Under a sector condition the limit
exists on the closed quarter sector (`HilleYosidaRay.tendsto_sectorExtension`).
-/
noncomputable def HilleYosidaRay.sectorExtension {M : ℝ} (hy : HilleYosidaRay A M) (z : ℂ) :
    X →L[ℂ] X :=
  if h : ∀ x : X, ∃ y, Tendsto (fun s : ℝ ↦ exp (z • hy.yosida s) x) atTop (𝓝 y) then
    continuousLinearMapOfTendsto (fun s : ℝ ↦ exp (z • hy.yosida s))
      (tendsto_pi_nhds.mpr fun x ↦ (h x).choose_spec)
  else 0

/-- Where the approximant exponentials converge strongly, `sectorExtension` is their
limit. -/
theorem HilleYosidaRay.tendsto_sectorExtension_of_forall {M : ℝ}
    (hy : HilleYosidaRay A M) {z : ℂ}
    (h : ∀ x : X, ∃ y, Tendsto (fun s : ℝ ↦ exp (z • hy.yosida s) x) atTop (𝓝 y)) (x : X) :
    Tendsto (fun s : ℝ ↦ exp (z • hy.yosida s) x) atTop (𝓝 (hy.sectorExtension z x)) := by
  rw [HilleYosidaRay.sectorExtension, dite_eq_left h]
  exact (h x).choose_spec

variable {M : ℝ} (hy : HilleYosidaRay A M) {c N : ℝ}

omit [CompleteSpace X] in
/-- Under the uniform sector bound `‖exp (w A_s)‖ ≤ exp (c ‖w‖)` on the closed quarter
sector, every exponential `exp (u w A_s)`, `u ∈ [0, 1]`, is bounded by `exp (c ‖w‖)`. -/
theorem norm_exp_smul_smul_yosida_le (hc : 0 ≤ c)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖))
    {s : ℝ} (hs : N ≤ s) {w : ℂ} (hw : w ∈ closedQuarterSector) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖exp (u • (w • hy.yosida s))‖ ≤ Real.exp (c * ‖w‖) := by
  rw [← smul_assoc, Complex.real_smul]
  refine (hbd s hs _ (smul_mem_closedQuarterSector hw hu.1)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hu.2

/-- **Complex-time Cauchy estimate between two approximants**:
`‖exp (w A_r) x - exp (w A_s) x‖ ≤ exp (c ‖w‖)² ‖w‖ ‖A_r x - A_s x‖` on the closed quarter
sector, from `norm_exp_apply_sub_exp_apply_le` and the commutation of the approximants. -/
theorem norm_exp_smul_yosida_sub_le (hc : 0 ≤ c) (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖))
    {r s : ℝ} (hr : N ≤ r) (hs : N ≤ s) {w : ℂ} (hw : w ∈ closedQuarterSector) (x : X) :
    ‖exp (w • hy.yosida r) x - exp (w • hy.yosida s) x‖ ≤
      Real.exp (c * ‖w‖) ^ 2 * (‖w‖ * ‖hy.yosida r x - hy.yosida s x‖) := by
  have hcomm : Commute (w • hy.yosida r) (w • hy.yosida s) :=
    ((commute_yosida hy (hNM.trans_le hr) (hNM.trans_le hs)).smul_left w).smul_right w
  have h := norm_exp_apply_sub_exp_apply_le hcomm
    (fun u hu ↦ norm_exp_smul_smul_yosida_le hy hc hbd hr hw hu)
    (fun u hu ↦ norm_exp_smul_smul_yosida_le hy hc hbd hs hw hu) x
  rwa [smul_apply, smul_apply, ← smul_sub, norm_smul] at h

/--
**Uniform Cauchy property of the approximant exponentials.**  Under the uniform sector bound,
for every vector `x` the maps `w ↦ exp (w A_s) x` are uniformly Cauchy as `s → ∞` on each
bounded part `{|Im w| ≤ Re w, ‖w‖ ≤ R}` of the closed quarter sector.

For `x = ι d` this is the Cauchy estimate `norm_exp_smul_yosida_sub_le` together with the
convergence `A_s ι d → A d` (`tendsto_yosida_embedding`); a general `x` is approximated by
some `ι d` (density), the error being controlled by the uniform bound.
-/
theorem uniformCauchySeqOn_exp_smul_yosida (hdense : DenseRange A.embedding) (hc : 0 ≤ c)
    (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖)) (x : X) (R : ℝ) :
    UniformCauchySeqOn (fun (s : ℝ) (w : ℂ) ↦ exp (w • hy.yosida s) x) atTop
      (closedQuarterSector ∩ Metric.closedBall 0 R) := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  set K := Real.exp (c * R')
  have hK : 0 < K := Real.exp_pos _
  have hwR : ∀ w ∈ closedQuarterSector ∩ Metric.closedBall 0 R, ‖w‖ ≤ R' := fun w hw ↦
    (mem_closedBall_zero_iff.mp hw.2).trans (le_max_left _ _)
  have hKw : ∀ w ∈ closedQuarterSector ∩ Metric.closedBall 0 R, Real.exp (c * ‖w‖) ≤ K :=
    fun w hw ↦ Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hwR w hw) hc)
  obtain ⟨d, hd⟩ := hdense.exists_dist_lt x (show 0 < ε / (4 * K) by positivity)
  set η := ε / (4 * (R' * K ^ 2 + 1))
  have hη : 0 < η := by positivity
  have hηε : η * (4 * (R' * K ^ 2 + 1)) = ε := by
    simp only [η]
    field_simp
  have hKε : K * (ε / (4 * K)) = ε / 4 := by
    field_simp
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp (tendsto_yosida_embedding hy hdense d) η hη
  filter_upwards [(eventually_ge_atTop (max N N')).prod_mk (eventually_ge_atTop (max N N'))]
    with ⟨r, s⟩ ⟨hr, hs⟩ w hw
  apply hεU
  have hNr : N ≤ r := (le_max_left _ _).trans hr
  have hNs : N ≤ s := (le_max_left _ _).trans hs
  have hEr : ‖exp (w • hy.yosida r)‖ ≤ K := (hbd r hNr w hw.1).trans (hKw w hw)
  have hEs : ‖exp (w • hy.yosida s)‖ ≤ K := (hbd s hNs w hw.1).trans (hKw w hw)
  have hdr := hN' r ((le_max_right _ _).trans hr)
  have hds := hN' s ((le_max_right _ _).trans hs)
  rw [dist_eq_norm] at hdr hds hd
  have hdiff : ‖hy.yosida r (A.embedding d) - hy.yosida s (A.embedding d)‖ < 2 * η := by
    have := norm_sub_le_norm_sub_add_norm_sub (hy.yosida r (A.embedding d)) (A.op d)
      (hy.yosida s (A.embedding d))
    rw [norm_sub_rev (A.op d)] at this
    linarith
  have hmid := norm_exp_smul_yosida_sub_le hy hc hNM hbd hNr hNs hw.1 (A.embedding d)
  have hmid' : ‖exp (w • hy.yosida r) (A.embedding d) - exp (w • hy.yosida s) (A.embedding d)‖
      ≤ K ^ 2 * (R' * (2 * η)) := by
    refine hmid.trans ?_
    gcongr
    · exact hKw w hw
    · exact hwR w hw
  have h1 : ‖exp (w • hy.yosida r) (x - A.embedding d)‖ ≤ K * ‖x - A.embedding d‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hEr (norm_nonneg _))
  have h3 : ‖exp (w • hy.yosida s) (x - A.embedding d)‖ ≤ K * ‖x - A.embedding d‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hEs (norm_nonneg _))
  have hsplit : exp (w • hy.yosida r) x - exp (w • hy.yosida s) x
      = exp (w • hy.yosida r) (x - A.embedding d)
        + (exp (w • hy.yosida r) (A.embedding d) - exp (w • hy.yosida s) (A.embedding d))
        - exp (w • hy.yosida s) (x - A.embedding d) := by
    simp only [map_sub]
    abel
  rw [dist_eq_norm, hsplit]
  have hxd : K * ‖x - A.embedding d‖ < ε / 4 := by
    rw [← hKε]
    exact mul_lt_mul_of_pos_left hd hK
  have hfin : K ^ 2 * (R' * (2 * η)) ≤ ε / 2 := by
    have : K ^ 2 * (R' * (2 * η)) * 2 ≤ η * (4 * (R' * K ^ 2 + 1)) := by nlinarith
    linarith
  calc ‖exp (w • hy.yosida r) (x - A.embedding d)
        + (exp (w • hy.yosida r) (A.embedding d) - exp (w • hy.yosida s) (A.embedding d))
        - exp (w • hy.yosida s) (x - A.embedding d)‖
      ≤ ‖exp (w • hy.yosida r) (x - A.embedding d)‖
        + ‖exp (w • hy.yosida r) (A.embedding d) - exp (w • hy.yosida s) (A.embedding d)‖
        + ‖exp (w • hy.yosida s) (x - A.embedding d)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by linarith

/-- On the closed quarter sector, the approximant exponentials converge strongly to
`sectorExtension`. -/
theorem HilleYosidaRay.tendsto_sectorExtension (hdense : DenseRange A.embedding) (hc : 0 ≤ c)
    (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖))
    {w : ℂ} (hw : w ∈ closedQuarterSector) (x : X) :
    Tendsto (fun s : ℝ ↦ exp (w • hy.yosida s) x) atTop (𝓝 (hy.sectorExtension w x)) := by
  refine hy.tendsto_sectorExtension_of_forall (fun y ↦ ?_) x
  exact cauchySeq_tendsto_of_complete
    ((uniformCauchySeqOn_exp_smul_yosida hy hdense hc hNM hbd y ‖w‖).cauchySeq
      ⟨hw, mem_closedBall_zero_iff.mpr le_rfl⟩)

/-- The approximant orbits `w ↦ exp (w A_s) x` converge to `w ↦ sectorExtension w x` locally
uniformly on the closed quarter sector (uniformly on each bounded part of it). -/
theorem HilleYosidaRay.tendstoLocallyUniformlyOn_sectorExtension
    (hdense : DenseRange A.embedding) (hc : 0 ≤ c) (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖)) (x : X) :
    TendstoLocallyUniformlyOn (fun (s : ℝ) (w : ℂ) ↦ exp (w • hy.yosida s) x)
      (fun w ↦ hy.sectorExtension w x) atTop closedQuarterSector := by
  intro U hU z _
  refine ⟨closedQuarterSector ∩ Metric.closedBall 0 (‖z‖ + 1),
    inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds_of_mem (by simp)), ?_⟩
  exact UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
    (uniformCauchySeqOn_exp_smul_yosida hy hdense hc hNM hbd x (‖z‖ + 1))
    (fun w hw ↦ hy.tendsto_sectorExtension hdense hc hNM hbd hw.1 x) U hU

/-- On the closed quarter sector `‖sectorExtension w‖ ≤ exp (c ‖w‖)`. -/
theorem HilleYosidaRay.norm_sectorExtension_le (hdense : DenseRange A.embedding) (hc : 0 ≤ c)
    (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖))
    {w : ℂ} (hw : w ∈ closedQuarterSector) :
    ‖hy.sectorExtension w‖ ≤ Real.exp (c * ‖w‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x ↦ ?_
  refine le_of_tendsto (hy.tendsto_sectorExtension hdense hc hNM hbd hw x).norm ?_
  filter_upwards [eventually_ge_atTop N] with s hs
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hbd s hs w hw) (norm_nonneg _))

/-- At nonnegative real times `sectorExtension` is the Hille–Yosida semigroup: both are the
strong limit of `exp (t A_s)` (`tendsto_semigroup_apply`). -/
theorem HilleYosidaRay.sectorExtension_ofReal (hdense : DenseRange A.embedding) (hc : 0 ≤ c)
    (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖)) (t : NNReal) :
    hy.sectorExtension ((t : ℝ) : ℂ) = hy.semigroup hdense t := by
  ext x
  have hmem : ((t : ℝ) : ℂ) ∈ closedQuarterSector := by
    change |((t : ℝ) : ℂ).im| ≤ ((t : ℝ) : ℂ).re
    simp
  refine tendsto_nhds_unique (hy.tendsto_sectorExtension hdense hc hNM hbd hmem x) ?_
  have h := tendsto_semigroup_apply hy hdense t.coe_nonneg x
  rw [Real.toNNReal_coe] at h
  simpa [HilleYosidaRay.approx, Complex.coe_smul] using h

/-- The semigroup law of `sectorExtension` on the closed quarter sector, the limit of
`exp ((z + w) A_s) = exp (z A_s) exp (w A_s)`. -/
theorem HilleYosidaRay.sectorExtension_add (hdense : DenseRange A.embedding) (hc : 0 ≤ c)
    (hNM : M < N)
    (hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp (c * ‖w‖))
    {z w : ℂ} (hz : z ∈ closedQuarterSector) (hw : w ∈ closedQuarterSector) :
    hy.sectorExtension (z + w) = (hy.sectorExtension z).comp (hy.sectorExtension w) := by
  let +nondep : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ (X →L[ℂ] X)
  ext x
  refine tendsto_nhds_unique
    (hy.tendsto_sectorExtension hdense hc hNM hbd (add_mem_closedQuarterSector hz hw) x) ?_
  have hsplit : ∀ s : ℝ, exp ((z + w) • hy.yosida s) x
      = exp (z • hy.yosida s) (exp (w • hy.yosida s) x - hy.sectorExtension w x)
        + exp (z • hy.yosida s) (hy.sectorExtension w x) := by
    intro s
    rw [add_smul, exp_add_of_commute (((Commute.refl _).smul_left z).smul_right w),
      ← map_add, sub_add_cancel, mul_apply_eq_comp]
  have h1 : Tendsto (fun s : ℝ ↦
      exp (z • hy.yosida s) (exp (w • hy.yosida s) x - hy.sectorExtension w x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ ↦
      Real.exp (c * ‖z‖) * ‖exp (w • hy.yosida s) x - hy.sectorExtension w x‖) ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with s hs
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hbd s hs z hz) (norm_nonneg _))
    · have h := ((hy.tendsto_sectorExtension hdense hc hNM hbd hw x).sub_const
        (hy.sectorExtension w x)).norm
      simp only [sub_self, norm_zero] at h
      simpa using h.const_mul (Real.exp (c * ‖z‖))
  have h2 := hy.tendsto_sectorExtension hdense hc hNM hbd hz (hy.sectorExtension w x)
  have h3 := h1.add h2
  rw [zero_add] at h3
  simpa only [hsplit, ContinuousLinearMap.comp_apply] using h3

end Approximant

/--
**Sector-dissipative Hille–Yosida generators generate analytic semigroups.**  If `A` has a
Hille–Yosida ray, a dense domain, and its numerical range lies in a shifted quarter sector,
`|Im ⟪ι d, A d⟫| ≤ ω ‖ι d‖² - Re ⟪ι d, A d⟫` for every domain element `d`, then the generated
semigroup is analytic of angle `π/4`.

The sector condition passes to the Yosida approximants `A_s` with `|ω| + 1` in place of `ω`
(`HilleYosidaRay.sectorial_yosida`), which gives `‖exp (w A_s)‖ ≤ exp ((|ω| + 1) ‖w‖)` on the
closed sector `{|Im w| ≤ Re w}` (`norm_exp_smul_le_of_sectorial`).  The complex-time Cauchy
estimate makes `exp (w A_s)` converge strongly, locally uniformly in `w`, to an operator family
`sectorExtension` that agrees with the semigroup on `[0, ∞)` and obeys the semigroup law; the
locally uniform limit of the holomorphic orbits is holomorphic
(`TendstoLocallyUniformlyOn.differentiableOn`), the family is locally bounded, so it is
holomorphic in the operator norm (`differentiableOn_of_forall_apply`), and continuity of the
orbits on the closed sector gives strong continuity at `0`.
-/
theorem HilleYosidaRay.isAnalyticSemigroup_of_sectorial {X : Type u} {D : Type v}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup D] [NormedSpace ℂ D] {A : DomainOperator X D} {M : ℝ}
    (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding) (ω : ℝ)
    (hsect : ∀ d : D, |(inner ℂ (A.embedding d) (A.op d)).im| ≤
      ω * ‖A.embedding d‖ ^ 2 - (inner ℂ (A.embedding d) (A.op d)).re) :
    IsAnalyticSemigroup (hy.semigroup hdense) (Real.pi / 4) := by
  set ω₀ := |ω|
  have hω₀ : 0 ≤ ω₀ := abs_nonneg ω
  have hsect' : ∀ d : D, |(inner ℂ (A.embedding d) (A.op d)).im| ≤
      ω₀ * ‖A.embedding d‖ ^ 2 - (inner ℂ (A.embedding d) (A.op d)).re := fun d ↦
    (hsect d).trans (by nlinarith [le_abs_self ω, sq_nonneg ‖A.embedding d‖])
  set N := max (M + 1) (2 * (ω₀ + 1) * ω₀)
  have hNM : M < N := lt_of_lt_of_le (lt_add_one M) (le_max_left _ _)
  have hc : 0 ≤ ω₀ + 1 := by linarith
  have hbd : ∀ s : ℝ, N ≤ s → ∀ w ∈ closedQuarterSector,
      ‖exp (w • hy.yosida s)‖ ≤ Real.exp ((ω₀ + 1) * ‖w‖) := fun s hs w hw ↦
    (norm_exp_smul_le_of_sectorial _ _ (hy.sectorial_yosida hω₀ hsect' (hNM.trans_le hs)
      ((le_max_right _ _).trans hs)) hw).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.re_le_norm w) hc))
  have hdiffE : ∀ (s : ℝ) (x : X), Differentiable ℂ (fun w : ℂ ↦ exp (w • hy.yosida s) x) :=
    fun s x w ↦ (ContinuousLinearMap.apply ℂ X x).differentiableAt.comp w
      (hasStrictDerivAt_exp_smul_const (𝕂 := ℂ) (hy.yosida s) w).hasDerivAt.differentiableAt
  have hU : IsOpen (openSector (Real.pi / 4)) := isOpen_openSector (by linarith [Real.pi_pos])
  have hstrong : ∀ x : X,
      DifferentiableOn ℂ (fun z ↦ hy.sectorExtension z x) (openSector (Real.pi / 4)) :=
    fun x ↦ ((hy.tendstoLocallyUniformlyOn_sectorExtension hdense hc hNM hbd x).mono
      openSector_pi_div_four_subset).differentiableOn
      (Eventually.of_forall fun s ↦ (hdiffE s x).differentiableOn) hU
  have hb : ∀ z ∈ openSector (Real.pi / 4), ∃ C : ℝ,
      ∀ᶠ w in 𝓝 z, ‖hy.sectorExtension w‖ ≤ C := by
    intro z hz
    refine ⟨Real.exp ((ω₀ + 1) * (‖z‖ + 1)), ?_⟩
    filter_upwards [hU.mem_nhds hz, Metric.ball_mem_nhds z one_pos] with w hw hwz
    refine (hy.norm_sectorExtension_le hdense hc hNM hbd (openSector_pi_div_four_subset hw)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc))
    have h1 := mem_ball_iff_norm.mp hwz
    have h2 := norm_sub_norm_le w z
    linarith
  refine ⟨by positivity, by linarith [Real.pi_pos],
    ⟨⟨hy.sectorExtension, hy.sectorExtension_ofReal hdense hc hNM hbd, ?_,
      differentiableOn_of_forall_apply hU hstrong hb, ?_⟩⟩⟩
  · intro z hz w hw
    exact hy.sectorExtension_add hdense hc hNM hbd (openSector_pi_div_four_subset hz)
      (openSector_pi_div_four_subset hw)
  · intro δ' _ hδ' x
    have hcont : ContinuousOn (fun z ↦ hy.sectorExtension z x) closedQuarterSector :=
      (hy.tendstoLocallyUniformlyOn_sectorExtension hdense hc hNM hbd x).continuousOn
        (Eventually.of_forall fun s ↦ (hdiffE s x).continuous.continuousOn).frequently
    have h0 : (0 : ℂ) ∈ closedQuarterSector := by
      change |(0 : ℂ).im| ≤ (0 : ℂ).re
      simp
    have hT0 : hy.sectorExtension 0 x = x := by
      have h := hy.sectorExtension_ofReal hdense hc hNM hbd 0
      simp only [NNReal.coe_zero, Complex.ofReal_zero] at h
      rw [h]
      exact (hy.semigroup hdense).apply_zero x
    have hsub : openSector δ' ⊆ closedQuarterSector := fun z hz ↦
      openSector_pi_div_four_subset ⟨hz.1, hz.2.trans hδ'⟩
    have h := ((hcont 0 h0).mono hsub).tendsto
    rwa [hT0] at h

end FastDynamo
