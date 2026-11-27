/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.WirtingerRadial
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# One-variable calculus for Dragičević's test functions

The test functions of `HarmonicAnalysis.BeurlingAhlfors.TestFunctions`, and their smooth
approximations, are of the form `z² K (|z|²)` with a real profile `K`. This file collects what is
needed about the profiles, as functions of `t = |z|²`.

* `HarmonicAnalysis.dz_dz_sq_mul_ofReal_radial`,
  `HarmonicAnalysis.dzbar_dzbar_sq_mul_ofReal_radial`: for a real profile `k`, `C²` at
  `t = |z|²`, `∂² (z² k (|z|²)) = 2 k + 4 t k' + t² k''` and `∂_zbar² (z² k (|z|²)) = z⁴ k''`.
* `HarmonicAnalysis.deriv_deriv_mul`: the Leibniz rule `(f g)'' = f'' g + 2 f' g' + f g''`.
* `HarmonicAnalysis.DerivBoundTwo f t B`: `|f (t)|, |f' (t)|, |f'' (t)| ≤ B`, with the rules for
  products (`HarmonicAnalysis.DerivBoundTwo.mul`) and translations.
* The profiles: `t ↦ t^{−α}` (`HarmonicAnalysis.deriv_rpow_neg`,
  `HarmonicAnalysis.deriv_deriv_rpow_neg`, bounds for `t ≥ 1`); the exterior cutoff
  `E (t) = exp (−(√t − 1)²)` (`HarmonicAnalysis.BeurlingAhlfors.expCutoff`; `g₂ (|z|) = E (|z|²)`
  for `|z| ≥ 1`), with `E' = E u'`, `E'' = E (u'² + u'')`, `u (t) = −(√t − 1)²`; and the bounds on
  `Real.smoothTransition` and its first two derivatives.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ComplexConjugate ContDiff

namespace HarmonicAnalysis

/-! ### Real profiles -/

/-- `d/dt (k (t) : ℂ) = (k' (t) : ℂ)`, whether `k` is differentiable at `t` or not. -/
theorem deriv_ofReal_comp (k : ℝ → ℝ) (t : ℝ) :
    deriv (fun s => (k s : ℂ)) t = ((deriv k t : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ k t
  · exact h.hasDerivAt.ofReal_comp.deriv
  · rw [deriv_zero_of_not_differentiableAt h, Complex.ofReal_zero]
    refine deriv_zero_of_not_differentiableAt fun h' => h ?_
    have := Complex.reCLM.differentiableAt.comp t h'
    simpa [Function.comp_def] using this

/-- A function `C²` at `t` is differentiable near `t`. -/
theorem eventually_differentiableAt_of_contDiffAt {f : ℝ → ℝ} {t : ℝ}
    (h : ContDiffAt ℝ 2 f t) : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ f s :=
  (h.eventually (by simp)).mono fun _ hs => hs.differentiableAt (by norm_num)

/-- The derivative of a function `C²` at `t` is differentiable at `t`. -/
theorem differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} {t : ℝ} (h : ContDiffAt ℝ 2 f t) :
    DifferentiableAt ℝ (deriv f) t :=
  (h.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero

/-- `∂² (z² k (|z|²)) = 2 k (t) + 4 t k' (t) + t² k'' (t)`, `t = |z|²`, for a real profile `k`,
`C²` at `t`. -/
theorem dz_dz_sq_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ}
    (hk : ContDiffAt ℝ 2 k (Complex.normSq z)) :
    dz (dz (fun w => w ^ 2 * ((k (Complex.normSq w) : ℝ) : ℂ))) z =
      ((2 * k (Complex.normSq z) + 4 * Complex.normSq z * deriv k (Complex.normSq z) +
        Complex.normSq z ^ 2 * deriv (deriv k) (Complex.normSq z) : ℝ) : ℂ) := by
  have hd : deriv (fun s => (k s : ℂ)) = fun s => ((deriv k s : ℝ) : ℂ) :=
    funext (deriv_ofReal_comp k)
  have hK : ∀ᶠ t in 𝓝 (Complex.normSq z), DifferentiableAt ℝ (fun s => (k s : ℂ)) t :=
    (eventually_differentiableAt_of_contDiffAt hk).mono fun _ ht =>
      ht.hasDerivAt.ofReal_comp.differentiableAt
  have hK' : DifferentiableAt ℝ (deriv fun s => (k s : ℂ)) (Complex.normSq z) := by
    rw [hd]
    exact (differentiableAt_deriv_of_contDiffAt hk).hasDerivAt.ofReal_comp.differentiableAt
  rw [dz_dz_sq_mul_radial hK hK', hd, deriv_ofReal_comp (deriv k)]
  push_cast
  ring

/-- `∂_zbar² (z² k (|z|²)) = z⁴ k'' (|z|²)` for a real profile `k`, `C²` at `|z|²`. -/
theorem dzbar_dzbar_sq_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ}
    (hk : ContDiffAt ℝ 2 k (Complex.normSq z)) :
    dzbar (dzbar (fun w => w ^ 2 * ((k (Complex.normSq w) : ℝ) : ℂ))) z =
      z ^ 4 * ((deriv (deriv k) (Complex.normSq z) : ℝ) : ℂ) := by
  have hd : deriv (fun s => (k s : ℂ)) = fun s => ((deriv k s : ℝ) : ℂ) :=
    funext (deriv_ofReal_comp k)
  have hK : ∀ᶠ t in 𝓝 (Complex.normSq z), DifferentiableAt ℝ (fun s => (k s : ℂ)) t :=
    (eventually_differentiableAt_of_contDiffAt hk).mono fun _ ht =>
      ht.hasDerivAt.ofReal_comp.differentiableAt
  have hK' : DifferentiableAt ℝ (deriv fun s => (k s : ℂ)) (Complex.normSq z) := by
    rw [hd]
    exact (differentiableAt_deriv_of_contDiffAt hk).hasDerivAt.ofReal_comp.differentiableAt
  rw [dzbar_dzbar_sq_mul_radial hK hK', hd, deriv_ofReal_comp (deriv k)]

/-! ### The Leibniz rule and bounds on two derivatives -/

/-- The Leibniz rule for the second derivative: `(f g)'' = f'' g + 2 f' g' + f g''`. -/
theorem deriv_deriv_mul {f g : ℝ → ℝ} {t : ℝ} (hf : ContDiffAt ℝ 2 f t)
    (hg : ContDiffAt ℝ 2 g t) :
    deriv (deriv fun s => f s * g s) t =
      deriv (deriv f) t * g t + 2 * (deriv f t * deriv g t) + f t * deriv (deriv g) t := by
  have h1 : deriv (fun s => f s * g s) =ᶠ[𝓝 t] fun s => deriv f s * g s + f s * deriv g s :=
    ((eventually_differentiableAt_of_contDiffAt hf).and
      (eventually_differentiableAt_of_contDiffAt hg)).mono fun _ hs => deriv_fun_mul hs.1 hs.2
  have hf1 := differentiableAt_deriv_of_contDiffAt hf
  have hg1 := differentiableAt_deriv_of_contDiffAt hg
  have hf0 : DifferentiableAt ℝ f t := hf.differentiableAt (by norm_num)
  have hg0 : DifferentiableAt ℝ g t := hg.differentiableAt (by norm_num)
  rw [h1.deriv_eq, deriv_fun_add (hf1.fun_mul hg0) (hf0.fun_mul hg1), deriv_fun_mul hf1 hg0,
    deriv_fun_mul hf0 hg1]
  ring

/-- `|f (t)|, |f' (t)|, |f'' (t)| ≤ B`. -/
def DerivBoundTwo (f : ℝ → ℝ) (t B : ℝ) : Prop :=
  |f t| ≤ B ∧ |deriv f t| ≤ B ∧ |deriv (deriv f) t| ≤ B

namespace DerivBoundTwo

variable {f g : ℝ → ℝ} {t B F G : ℝ}

theorem nonneg (h : DerivBoundTwo f t B) : 0 ≤ B :=
  (abs_nonneg _).trans h.1

theorem mono (h : DerivBoundTwo f t B) {B' : ℝ} (hB : B ≤ B') : DerivBoundTwo f t B' :=
  ⟨h.1.trans hB, h.2.1.trans hB, h.2.2.trans hB⟩

theorem congr (h : DerivBoundTwo g t B) (hfg : f =ᶠ[𝓝 t] g) : DerivBoundTwo f t B := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hfg.self_of_nhds]; exact h.1
  · rw [hfg.deriv_eq]; exact h.2.1
  · rw [hfg.deriv.deriv_eq]; exact h.2.2

/-- The bounds for a product: `|(f g)^{(j)} (t)| ≤ 4 F G` for `j ≤ 2`. -/
theorem mul (hf : ContDiffAt ℝ 2 f t) (hg : ContDiffAt ℝ 2 g t) (hF : DerivBoundTwo f t F)
    (hG : DerivBoundTwo g t G) : DerivBoundTwo (fun s => f s * g s) t (4 * F * G) := by
  obtain ⟨hf0, hf1, hf2⟩ := hF
  obtain ⟨hg0, hg1, hg2⟩ := hG
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hf0
  have hG0 : 0 ≤ G := (abs_nonneg _).trans hg0
  have hm : ∀ {a b : ℝ}, |a| ≤ F → |b| ≤ G → |a * b| ≤ F * G := fun ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hF0
  have hFG : 0 ≤ F * G := mul_nonneg hF0 hG0
  refine ⟨?_, ?_, ?_⟩
  · exact (hm hf0 hg0).trans (by nlinarith)
  · rw [deriv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    exact (abs_add_le _ _).trans (by linarith [hm hf1 hg0, hm hf0 hg1])
  · rw [deriv_deriv_mul hf hg]
    refine (abs_add_le _ _).trans ?_
    have := (abs_add_le (deriv (deriv f) t * g t) (2 * (deriv f t * deriv g t)))
    rw [abs_mul 2, abs_two] at this
    linarith [hm hf2 hg0, hm hf1 hg1, hm hf0 hg2]

/-- Bounds for a translate: `f (· + c)` at `t` from `f` at `t + c`. -/
theorem comp_add_const {c : ℝ} (h : DerivBoundTwo f (t + c) B) :
    DerivBoundTwo (fun s => f (s + c)) t B := by
  have hd : deriv (fun s => f (s + c)) = fun s => deriv f (s + c) :=
    funext fun s => deriv_comp_add_const f c s
  refine ⟨h.1, ?_, ?_⟩
  · rw [hd]; exact h.2.1
  · rw [hd, deriv_comp_add_const (deriv f) c t]; exact h.2.2

end DerivBoundTwo

/-- The derivative of `f (c s + d)`: `c f' (c s + d)`, whether `f` is differentiable or not. -/
theorem deriv_comp_mul_add (f : ℝ → ℝ) (c d : ℝ) :
    deriv (fun s => f (c * s + d)) = fun s => c * deriv f (c * s + d) := by
  funext s
  have := deriv_comp_mul_left c (fun u => f (u + d)) s
  simp only [smul_eq_mul, deriv_comp_add_const] at this
  exact this

/-- The second derivative of `f (c s + d)`: `c² f'' (c s + d)`. -/
theorem deriv_deriv_comp_mul_add (f : ℝ → ℝ) (c d : ℝ) :
    deriv (deriv fun s => f (c * s + d)) = fun s => c ^ 2 * deriv (deriv f) (c * s + d) := by
  rw [deriv_comp_mul_add, deriv_const_mul_field', deriv_comp_mul_add]
  funext s
  ring

/-- Bounds for `f (c s + d)` with `|c| ≤ 1`, from bounds for `f` at `c t + d`. -/
theorem DerivBoundTwo.comp_mul_add {f : ℝ → ℝ} {c d t B : ℝ} (hc : |c| ≤ 1)
    (h : DerivBoundTwo f (c * t + d) B) : DerivBoundTwo (fun s => f (c * s + d)) t B := by
  have hB := h.nonneg
  have hc2 : |c ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  refine ⟨h.1, ?_, ?_⟩
  · rw [deriv_comp_mul_add, abs_mul]
    nlinarith [abs_nonneg c, abs_nonneg (deriv f (c * t + d)), h.2.1]
  · rw [deriv_deriv_comp_mul_add, abs_mul]
    nlinarith [abs_nonneg (c ^ 2), abs_nonneg (deriv (deriv f) (c * t + d)), h.2.2]

/-- Convergence of the values and the first two derivatives at `t`: `f_k^{(j)} (t) → g^{(j)} (t)`
for `j ≤ 2`. -/
def TendstoTwo (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (t : ℝ) : Prop :=
  Tendsto (fun k => f k t) atTop (𝓝 (g t)) ∧
    Tendsto (fun k => deriv (f k) t) atTop (𝓝 (deriv g t)) ∧
    Tendsto (fun k => deriv (deriv (f k)) t) atTop (𝓝 (deriv (deriv g) t))

namespace TendstoTwo

variable {f f' : ℕ → ℝ → ℝ} {g h : ℝ → ℝ} {t : ℝ}

/-- `TendstoTwo` only depends on the germs at `t` of the `f_k`, `k` large. -/
theorem congr (hf : TendstoTwo f g t) (hff' : ∀ᶠ k in atTop, f' k =ᶠ[𝓝 t] f k) :
    TendstoTwo f' g t := by
  refine ⟨hf.1.congr' ?_, hf.2.1.congr' ?_, hf.2.2.congr' ?_⟩
  · exact hff'.mono fun k hk => hk.self_of_nhds.symm
  · exact hff'.mono fun k hk => hk.deriv_eq.symm
  · exact hff'.mono fun k hk => hk.deriv.deriv_eq.symm

/-- `TendstoTwo` for the products with a fixed factor `h`, `C²` at `t`. -/
theorem mul_right (hf : TendstoTwo f g t) (hfk : ∀ k, ContDiffAt ℝ 2 (f k) t)
    (hg : ContDiffAt ℝ 2 g t) (hh : ContDiffAt ℝ 2 h t) :
    TendstoTwo (fun k s => f k s * h s) (fun s => g s * h s) t := by
  obtain ⟨h0, h1, h2⟩ := hf
  have hd : ∀ {u : ℝ → ℝ}, ContDiffAt ℝ 2 u t → DifferentiableAt ℝ u t := fun hu =>
    hu.differentiableAt (by norm_num)
  refine ⟨h0.mul_const _, ?_, ?_⟩
  · rw [deriv_fun_mul (hd hg) (hd hh)]
    exact ((h1.mul_const _).add (h0.mul_const _)).congr fun k =>
      (deriv_fun_mul (hd (hfk k)) (hd hh)).symm
  · rw [deriv_deriv_mul hg hh]
    exact (((h2.mul_const _).add ((h1.mul_const _).const_mul 2)).add (h0.mul_const _)).congr
      fun k => (deriv_deriv_mul (hfk k) hh).symm

end TendstoTwo

/-! ### Bounds and limits for `∂² (z² k (|z|²))`, `∂_zbar² (z² k (|z|²))` -/

/-- `|∂² (z² k (|z|²))|, |∂_zbar² (z² k (|z|²))| ≤ 2 (1 + |z|²)² M` if `|k^{(j)} (|z|²)| ≤ M` for
`j ≤ 2`. -/
theorem norm_dz_dz_sq_mul_ofReal_radial_le {k : ℝ → ℝ} {z : ℂ} {M : ℝ}
    (hk : ContDiffAt ℝ 2 k (Complex.normSq z)) (h : DerivBoundTwo k (Complex.normSq z) M) :
    ‖dz (dz (fun w => w ^ 2 * ((k (Complex.normSq w) : ℝ) : ℂ))) z‖ ≤
        2 * (1 + ‖z‖ ^ 2) ^ 2 * M ∧
      ‖dzbar (dzbar (fun w => w ^ 2 * ((k (Complex.normSq w) : ℝ) : ℂ))) z‖ ≤
        2 * (1 + ‖z‖ ^ 2) ^ 2 * M := by
  rw [dz_dz_sq_mul_ofReal_radial hk, dzbar_dzbar_sq_mul_ofReal_radial hk, Complex.norm_real,
    Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have ht : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hz4 : ‖z‖ ^ 4 = (Complex.normSq z) ^ 2 := by rw [ht]; ring
  rw [hz4, ← ht]
  obtain ⟨h0, h1, h2⟩ := h
  set t := Complex.normSq z
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  have ht0 : 0 ≤ t := Complex.normSq_nonneg z
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have e1 : |2 * k t + 4 * t * deriv k t + t ^ 2 * deriv (deriv k) t| ≤
      2 * |k t| + 4 * t * |deriv k t| + t ^ 2 * |deriv (deriv k) t| := by
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (le_of_eq ?_)) ?_)
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht0, abs_two,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    · rw [abs_mul, abs_of_nonneg ht2]
  have e2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * t)
  have e3 := mul_le_mul_of_nonneg_left h2 ht2
  constructor
  · nlinarith
  · nlinarith

/-- If `f_k → g` with two derivatives at `t = |z|²`, then `∂² (z² f_k (|z|²)) → ∂² (z² g (|z|²))`
and `∂_zbar² (z² f_k (|z|²)) → ∂_zbar² (z² g (|z|²))` at `z`. -/
theorem tendsto_dz_dz_sq_mul_ofReal_radial {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {z : ℂ}
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) (Complex.normSq z))
    (hg : ContDiffAt ℝ 2 g (Complex.normSq z)) (h : TendstoTwo f g (Complex.normSq z)) :
    Tendsto (fun k => dz (dz (fun w => w ^ 2 * ((f k (Complex.normSq w) : ℝ) : ℂ))) z) atTop
        (𝓝 (dz (dz (fun w => w ^ 2 * ((g (Complex.normSq w) : ℝ) : ℂ))) z)) ∧
      Tendsto (fun k => dzbar (dzbar (fun w => w ^ 2 * ((f k (Complex.normSq w) : ℝ) : ℂ))) z)
        atTop (𝓝 (dzbar (dzbar (fun w => w ^ 2 * ((g (Complex.normSq w) : ℝ) : ℂ))) z)) := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [dz_dz_sq_mul_ofReal_radial hg, dzbar_dzbar_sq_mul_ofReal_radial hg]
  constructor
  · refine ((Complex.continuous_ofReal.tendsto _).comp
      (((h0.const_mul 2).add (h1.const_mul _)).add (h2.const_mul _))).congr fun k => ?_
    rw [dz_dz_sq_mul_ofReal_radial (hf k)]
    rfl
  · refine (((Complex.continuous_ofReal.tendsto _).comp h2).const_mul _).congr fun k => ?_
    rw [dzbar_dzbar_sq_mul_ofReal_radial (hf k)]
    rfl

/-! ### The power `t^{−α}` -/

/-- `(|z|²)^{−α} = |z|^{−2α}`. -/
theorem normSq_rpow_neg (z : ℂ) (α : ℝ) : Complex.normSq z ^ (-α) = ‖z‖ ^ (-2 * α) := by
  rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast_mul (norm_nonneg z)]
  congr 1
  push_cast
  ring

/-- `d/dt t^{−α} = −α t^{−α−1}`. -/
theorem deriv_rpow_neg (α : ℝ) :
    deriv (fun s : ℝ => s ^ (-α)) = fun s => -α * s ^ (-α - 1) :=
  Real.deriv_rpow_const' (-α)

/-- `d²/dt² t^{−α} = α (α + 1) t^{−α−2}`. -/
theorem deriv_deriv_rpow_neg (α : ℝ) :
    deriv (deriv fun s : ℝ => s ^ (-α)) = fun s => α * (α + 1) * s ^ (-α - 2) := by
  rw [deriv_rpow_neg, deriv_const_mul_field', Real.deriv_rpow_const']
  funext s
  rw [show -α - 1 - 1 = -α - 2 by ring]
  ring

/-- `d/dt (t + c)^{−α} = −α (t + c)^{−α−1}`. -/
theorem deriv_rpow_add_neg (α c : ℝ) :
    deriv (fun s : ℝ => (s + c) ^ (-α)) = fun s => -α * (s + c) ^ (-α - 1) := by
  funext s
  rw [deriv_comp_add_const (fun s : ℝ => s ^ (-α)), deriv_rpow_neg]

/-- `d²/dt² (t + c)^{−α} = α (α + 1) (t + c)^{−α−2}`. -/
theorem deriv_deriv_rpow_add_neg (α c : ℝ) :
    deriv (deriv fun s : ℝ => (s + c) ^ (-α)) = fun s => α * (α + 1) * (s + c) ^ (-α - 2) := by
  funext s
  have : deriv (fun s : ℝ => (s + c) ^ (-α)) = fun s => deriv (fun s : ℝ => s ^ (-α)) (s + c) :=
    funext fun s => deriv_comp_add_const (fun s : ℝ => s ^ (-α)) c s
  rw [this, deriv_comp_add_const (deriv fun s : ℝ => s ^ (-α)), deriv_deriv_rpow_neg]

/-- `(t + ε_k)^{−α}` and its first two derivatives converge to those of `t^{−α}` at `t > 0` when
`ε_k → 0`. -/
theorem tendstoTwo_rpow_add_neg (α : ℝ) {t : ℝ} (ht : 0 < t) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    TendstoTwo (fun k s => (s + ε k) ^ (-α)) (fun s => s ^ (-α)) t := by
  have htε : Tendsto (fun k => t + ε k) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add hε
  have hlim : ∀ β : ℝ, Tendsto (fun k => (t + ε k) ^ β) atTop (𝓝 (t ^ β)) := fun β =>
    (Real.continuousAt_rpow_const t β (Or.inl ht.ne')).tendsto.comp htε
  refine ⟨hlim _, ?_, ?_⟩
  · simp only [deriv_rpow_add_neg, deriv_rpow_neg]
    exact (hlim _).const_mul _
  · simp only [deriv_deriv_rpow_add_neg, deriv_deriv_rpow_neg]
    exact (hlim _).const_mul _

/-- For `t ≥ 1` and `α ∈ [0, 1]`: `t^{−α}`, `α t^{−α−1}`, `α (α + 1) t^{−α−2} ≤ 2`. -/
theorem derivBoundTwo_rpow_neg {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ht : 1 ≤ t) :
    DerivBoundTwo (fun s : ℝ => s ^ (-α)) t 2 := by
  have h : ∀ β : ℝ, β ≤ 0 → 0 ≤ t ^ β ∧ t ^ β ≤ 1 := fun β hβ =>
    ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos ht hβ⟩
  obtain ⟨h0, h0'⟩ := h (-α) (by linarith)
  obtain ⟨h1, h1'⟩ := h (-α - 1) (by linarith)
  obtain ⟨h2, h2'⟩ := h (-α - 2) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg h0]; linarith
  · rw [deriv_rpow_neg, abs_mul, abs_neg, abs_of_nonneg hα0, abs_of_nonneg h1]
    nlinarith
  · rw [deriv_deriv_rpow_neg, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg h2]
    calc α * (α + 1) * t ^ (-α - 2) ≤ 2 * 1 := mul_le_mul (by nlinarith) h2' h2 (by norm_num)
      _ = 2 := mul_one 2

/-! ### The exterior cutoff `E (t) = exp (−(√t − 1)²)` -/

namespace BeurlingAhlfors

/-- The exterior cutoff `E (t) = exp (−(√t − 1)²)`: `g₂ (|z|) = E (|z|²)` for `|z| ≥ 1`. -/
def expCutoff (t : ℝ) : ℝ := Real.exp (-(√t - 1) ^ 2)

theorem expCutoff_pos (t : ℝ) : 0 < expCutoff t := Real.exp_pos _

/-- `E (|z|²) = exp (−(|z| − 1)²)`. -/
theorem expCutoff_normSq (z : ℂ) : expCutoff (Complex.normSq z) = Real.exp (-(‖z‖ - 1) ^ 2) := by
  rw [expCutoff, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]

theorem expCutoff_le_one (t : ℝ) : expCutoff t ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (√t - 1)])

theorem contDiffAt_expCutoff {n : WithTop ℕ∞} {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ n expCutoff t :=
  (((Real.contDiffAt_sqrt ht).sub contDiffAt_const).pow 2).neg.exp

/-- `E' (t) = E (t) u' (t)`, `u' (t) = 1/√t − 1`, for `t > 0`. -/
theorem hasDerivAt_expCutoff {t : ℝ} (ht : 0 < t) :
    HasDerivAt expCutoff (expCutoff t * ((√t)⁻¹ - 1)) t := by
  have hs : √t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h1 := (((Real.hasDerivAt_sqrt ht.ne').sub_const 1).fun_pow 2).fun_neg.exp
  refine h1.congr_deriv ?_
  simp only [expCutoff]
  field_simp
  ring

theorem deriv_expCutoff {t : ℝ} (ht : 0 < t) :
    deriv expCutoff t = expCutoff t * ((√t)⁻¹ - 1) :=
  (hasDerivAt_expCutoff ht).deriv

/-- `E'' (t) = E (t) (u' (t)² + u'' (t))`, `u'' (t) = −1/(2 √t³)`, for `t > 0`. -/
theorem deriv_deriv_expCutoff {t : ℝ} (ht : 0 < t) :
    deriv (deriv expCutoff) t = expCutoff t * (((√t)⁻¹ - 1) ^ 2 - (2 * √t ^ 3)⁻¹) := by
  have hs : √t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h1 : deriv expCutoff =ᶠ[𝓝 t] fun s => expCutoff s * ((√s)⁻¹ - 1) :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => deriv_expCutoff hs
  rw [h1.deriv_eq]
  have := (hasDerivAt_expCutoff ht).fun_mul (((Real.hasDerivAt_sqrt ht.ne').fun_inv hs).sub_const 1)
  rw [this.deriv]
  field_simp
  ring

/-- For `t ≥ 1`: `|E (t)|, |E' (t)|, |E'' (t)| ≤ 2 E (t)` (`|u'| ≤ 1`, `|u''| ≤ 1/2`). -/
theorem derivBoundTwo_expCutoff {t : ℝ} (ht : 1 ≤ t) :
    DerivBoundTwo expCutoff t (2 * expCutoff t) := by
  have ht0 : 0 < t := by linarith
  have hE := expCutoff_pos t
  have hs1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
  have hi0 : 0 < (√t)⁻¹ := inv_pos.2 (by linarith)
  have hi1 : (√t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hc0 : 0 < (2 * √t ^ 3)⁻¹ := by positivity
  have hc1 : (2 * √t ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [one_le_pow₀ (n := 3) hs1])
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos hE]; linarith
  · rw [deriv_expCutoff ht0, abs_mul, abs_of_pos hE]
    have : |(√t)⁻¹ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · rw [deriv_deriv_expCutoff ht0, abs_mul, abs_of_pos hE]
    have : |((√t)⁻¹ - 1) ^ 2 - (2 * √t ^ 3)⁻¹| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith
    nlinarith

/-- `|E (t) − 1| ≤ (t − 1)²` for `t ≥ 1` (`1 − e^{−y} ≤ y`, `√t − 1 ≤ t − 1`). -/
theorem abs_expCutoff_sub_one_le {t : ℝ} (ht : 1 ≤ t) : |expCutoff t - 1| ≤ (t - 1) ^ 2 := by
  rw [abs_of_nonpos (by linarith [expCutoff_le_one t])]
  have h := Real.add_one_le_exp (-(√t - 1) ^ 2)
  have hs1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
  have hst : √t ≤ t := by nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ t)]
  have : (√t - 1) ^ 2 ≤ (t - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  simp only [expCutoff]
  linarith

/-- `|E' (t)| ≤ t − 1` for `t ≥ 1`. -/
theorem abs_deriv_expCutoff_le {t : ℝ} (ht : 1 ≤ t) : |deriv expCutoff t| ≤ t - 1 := by
  have hs1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
  have hi1 : (√t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hsi : √t * (√t)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hst : √t ≤ t := by nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ t)]
  rw [deriv_expCutoff (by linarith), abs_mul, abs_of_pos (expCutoff_pos t),
    abs_of_nonpos (by linarith)]
  nlinarith [expCutoff_le_one t, expCutoff_pos t, mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hi1)]

/-- `E (t) ≥ e^{−1}` for `1 ≤ t ≤ 4`. -/
theorem exp_neg_one_le_expCutoff {t : ℝ} (ht : 1 ≤ t) (ht4 : t ≤ 4) :
    Real.exp (-1) ≤ expCutoff t := by
  have hs1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
  have hs2 : √t ≤ 2 := by nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ t)]
  exact Real.exp_le_exp.2 (by nlinarith)

end BeurlingAhlfors

/-! ### The smooth transition -/

/-- `Real.smoothTransition` and its first two derivatives are bounded. -/
theorem exists_derivBoundTwo_smoothTransition :
    ∃ S, 1 ≤ S ∧ ∀ x, DerivBoundTwo Real.smoothTransition x S := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs1 : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.mp hs).2
  have hs2 : ContDiff ℝ ∞ (deriv (deriv Real.smoothTransition)) :=
    (contDiff_infty_iff_deriv.mp hs1).2
  have hout : ∀ x, x ∉ Icc (0 : ℝ) 1 → x < 0 ∨ 1 < x := fun x hx => by
    simp only [mem_Icc, not_and_or, not_le] at hx; exact hx
  have hloc : ∀ x, x < 0 ∨ 1 < x →
      Real.smoothTransition =ᶠ[𝓝 x] fun _ => Real.smoothTransition x := by
    rintro x (hx | hx)
    · filter_upwards [Iio_mem_nhds hx] with y hy
      rw [Real.smoothTransition.zero_of_nonpos hy.le, Real.smoothTransition.zero_of_nonpos hx.le]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [Real.smoothTransition.one_of_one_le hy.le, Real.smoothTransition.one_of_one_le hx.le]
  have hd1 : ∀ x, x < 0 ∨ 1 < x → deriv Real.smoothTransition x = 0 := fun x hx => by
    rw [(hloc x hx).deriv_eq, deriv_const]
  have hd2 : ∀ x, x < 0 ∨ 1 < x → deriv (deriv Real.smoothTransition) x = 0 := by
    rintro x (hx | hx)
    · have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.mem_of_superset (Iio_mem_nhds hx) fun y hy => hd1 y (Or.inl hy)
      rw [this.deriv_eq, deriv_const]
    · have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.mem_of_superset (Ioi_mem_nhds hx) fun y hy => hd1 y (Or.inr hy)
      rw [this.deriv_eq, deriv_const]
  obtain ⟨C1, hC1⟩ := hs1.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc fun x hx => hd1 x (hout x hx))
  obtain ⟨C2, hC2⟩ := hs2.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc fun x hx => hd2 x (hout x hx))
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun x => ⟨?_, ?_, ?_⟩⟩
  · rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact (Real.smoothTransition.le_one x).trans (le_max_left _ _)
  · exact (hC1 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hC2 x).trans ((le_max_right _ _).trans (le_max_right _ _))

end HarmonicAnalysis
