/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
meta import Mathlib.Tactic.Abel
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Positivity
meta import Mathlib.Tactic.Ring

/-!
# Convergence of the regularised Kohn–Sham iteration (MYKSODA), abstract form

Penz, Laestadius, Tellgren and Ruggenthaler, PRL 123, 037401 (2019), with the erratum
co-authored by P. E. Lammert, PRL 125, 249902 (2020). The corrected guarantee gives bounded
quasi-density iterates. Each convergent subsequence limits to a ground-state quasi-density,
and its associated Kohn–Sham potentials converge to the reference potential for that limit.

The setting is a finite-dimensional real inner-product space `E` and two functionals `F`
(interacting, regularised) and `T` (non-interacting reference, regularised) with "gradients" `gF`,
`gT` satisfying the two inequalities characteristic of Moreau–Yosida envelopes (`IsMYSmooth`): a
supporting hyperplane below and a parabola of curvature `1/ε` above. No differentiability is used.

The iteration, for an external potential `v`:
* (a) `w i = v + gF (x i) - gT (x i)` (Kohn–Sham potential);
* (b) `x' i` is a regularised ground-state quasi-density of the reference system:
  `gT (x' i) = - w i`;
* (c) `x (i+1) = x i + s i • (x' i - x i)` with the step `s i = -ε ⟪gF (x i) + v, d⟫ / ‖d‖²`.
-/

@[expose] public section

open Filter Topology RealInnerProductSpace

namespace DFT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `g` is a gradient of `F` in the Moreau–Yosida sense: supporting hyperplanes from below,
curvature at most `1/ε` from above. -/
structure IsMYSmooth (ε : ℝ) (F : E → ℝ) (g : E → E) : Prop where
  lower : ∀ x y, F x + ⟪g x, y - x⟫ ≤ F y
  upper : ∀ x y, F y ≤ F x + ⟪g x, y - x⟫ + ‖y - x‖ ^ 2 / (2 * ε)

namespace IsMYSmooth

variable {ε : ℝ} {F : E → ℝ} {g : E → E}

/-- Adding a linear term keeps the structure. -/
lemma add_linear (h : IsMYSmooth ε F g) (v : E) :
    IsMYSmooth ε (fun y => F y + ⟪v, y⟫) (fun y => g y + v) where
  lower x y := by
    have := h.lower x y
    rw [inner_add_left, inner_sub_right v]; linarith
  upper x y := by
    have := h.upper x y
    rw [inner_add_left, inner_sub_right v]; linarith

/-- Improved lower bound. -/
lemma lower_strong (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    F x + ⟪g x, y - x⟫ + ε / 2 * ‖g y - g x‖ ^ 2 ≤ F y := by
  set a := g x; set b := g y
  set z := y - ε • (b - a)
  have h1 := h.lower x z
  have h2 := h.upper y z
  have hz1 : z - x = (y - x) - ε • (b - a) := by simp only [z]; abel
  have hz2 : z - y = -(ε • (b - a)) := by simp only [z]; abel
  rw [hz1] at h1; rw [hz2] at h2
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
  rw [inner_sub_right, inner_smul_right] at h1
  rw [inner_neg_right, inner_smul_right] at h2
  have e1 : ⟪b, b - a⟫ - ⟪a, b - a⟫ = ‖b - a‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have e2 : (ε * ‖b - a‖) ^ 2 / (2 * ε) = ε / 2 * ‖b - a‖ ^ 2 := by field_simp
  rw [e2] at h2
  nlinarith

/-- Co-coercivity of the gradient. -/
lemma cocoercive (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    ε * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫ := by
  have h1 := h.lower_strong hε x y
  have h2 := h.lower_strong hε y x
  rw [norm_sub_rev (g y) (g x)] at h1
  have e2 : ⟪g x - g y, x - y⟫ = -⟪g x, y - x⟫ - ⟪g y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub y x, inner_neg_right]
  rw [e2]
  linarith

/-- The gradient is `1/ε`-Lipschitz. -/
lemma norm_sub_le (h : IsMYSmooth ε F g) (hε : 0 < ε) (x y : E) :
    ε * ‖g x - g y‖ ≤ ‖x - y‖ := by
  have h1 := h.cocoercive hε x y
  have h2 := real_inner_le_norm (g x - g y) (x - y)
  rcases (norm_nonneg (g x - g y)).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · nlinarith

lemma continuous (h : IsMYSmooth ε F g) (hε : 0 < ε) : Continuous g := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨1 / ε, by positivity⟩) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ (1 / ε) * _
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hε, mul_comm]
  exact h.norm_sub_le hε x y

lemma norm_le (h : IsMYSmooth ε F g) (hε : 0 < ε) (x : E) : ‖g x‖ ≤ ‖g 0‖ + ‖x‖ / ε := by
  have := h.norm_sub_le hε x 0
  rw [sub_zero] at this
  have h3 : ‖g x - g 0‖ ≤ ‖x‖ / ε := by rw [le_div_iff₀ hε]; linarith
  calc ‖g x‖ = ‖(g x - g 0) + g 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖g x - g 0‖ + ‖g 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end IsMYSmooth

/-- The damped step length of MYKSODA (`0` if the direction vanishes). -/
noncomputable def ksStep (ε : ℝ) (g d : E) : ℝ := -ε * ⟪g, d⟫ / ‖d‖ ^ 2

lemma ksStep_mul (ε : ℝ) (g d : E) : ksStep ε g d * ‖d‖ ^ 2 = -ε * ⟪g, d⟫ := by
  unfold ksStep
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have : ‖d‖ ^ 2 ≠ 0 := by positivity
    field_simp

/-- One damped step: energy decrease by at least `‖step‖²/(2ε)`. -/
lemma step_descent {ε : ℝ} (hε : 0 < ε) {G : E → ℝ} {g : E → E} (hG : IsMYSmooth ε G g) (x d : E) :
    G (x + ksStep ε (g x) d • d) ≤ G x - ‖ksStep ε (g x) d • d‖ ^ 2 / (2 * ε) := by
  set s := ksStep ε (g x) d
  have h := hG.upper x (x + s • d)
  rw [add_sub_cancel_left, inner_smul_right] at h
  have hs := ksStep_mul ε (g x) d
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h ⊢
  have key : s * ⟪g x, d⟫ + s ^ 2 * ‖d‖ ^ 2 / ε = 0 := by
    have : s ^ 2 * ‖d‖ ^ 2 = s * (-ε * ⟪g x, d⟫) := by rw [← hs]; ring
    rw [this]; field_simp; ring
  have : s * ⟪g x, d⟫ + s ^ 2 * ‖d‖ ^ 2 / (2 * ε) = - (s ^ 2 * ‖d‖ ^ 2 / (2 * ε)) := by
    field_simp; field_simp at key; linarith
  linarith

/-- The step is long when the gradient is large: `ε² ‖g‖² ≤ ‖step‖ ‖d‖`, given the descent estimate
`⟪g, d⟫ ≤ -ε ‖g‖²`. -/
lemma step_lower {ε : ℝ} (hε : 0 < ε) {g d : E} (h17 : ⟪g, d⟫ ≤ -ε * ‖g‖ ^ 2) :
    ε ^ 2 * ‖g‖ ^ 2 ≤ ‖ksStep ε g d • d‖ * ‖d‖ := by
  have e : ‖ksStep ε g d • d‖ * ‖d‖ = |ksStep ε g d * ‖d‖ ^ 2| := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖d‖)]; ring
  rw [e, ksStep_mul, abs_mul, abs_neg, abs_of_pos hε]
  have : ε * ‖g‖ ^ 2 ≤ |⟪g, d⟫| := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖g‖])]; linarith
  nlinarith

namespace IsMYSmooth

variable {ε : ℝ} {F : E → ℝ} {g : E → E}

lemma continuous_fun (h : IsMYSmooth ε F g) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  have hl : Continuous fun y => F x + ⟪g x, y - x⟫ :=
    continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))
  have hu : Continuous fun y => F x + ⟪g x, y - x⟫ + ‖y - x‖ ^ 2 / (2 * ε) :=
    hl.add (((continuous_id.sub continuous_const).norm.pow 2).div_const _)
  have h1 := hl.tendsto x
  have h2 := hu.tendsto x
  simp only [sub_self, inner_zero_right, add_zero, norm_zero] at h1 h2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 (fun y => h.lower x y)
      (fun y => h.upper x y)

/-- **Existence of regularised ground-state quasi-densities.** If the sublevel sets of `F + ⟪w,·⟫`
are bounded, then `F + ⟪w,·⟫` has a minimiser `y`, and `g y + w = 0`. -/
lemma exists_stationary [ProperSpace E] (h : IsMYSmooth ε F g) (hε : 0 < ε) (w : E)
    (hsub : ∀ c, ∃ R, ∀ y, F y + ⟪w, y⟫ ≤ c → ‖y‖ ≤ R) : ∃ y, g y + w = 0 := by
  have hG := h.add_linear w
  set G : E → ℝ := fun y => F y + ⟪w, y⟫
  obtain ⟨R, hR⟩ := hsub (G 0)
  have h0 : (0 : E) ∈ Metric.closedBall (0 : E) R := by
    rw [mem_closedBall_zero_iff]; exact hR 0 le_rfl
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn ⟨0, h0⟩
    hG.continuous_fun.continuousOn
  have hglob : ∀ u, G y ≤ G u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : E) R
    · exact hmin hu
    · have : ¬ G u ≤ G 0 := fun hc => hu (mem_closedBall_zero_iff.mpr (hR u hc))
      exact le_trans (hmin h0) (le_of_lt (not_le.mp this))
  refine ⟨y, ?_⟩
  set a := g y + w
  have hup := hG.upper y (y - ε • a)
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq] at hup
  have hm := hglob (y - ε • a)
  have : ‖a‖ ^ 2 ≤ 0 := by
    have e : (ε * ‖a‖) ^ 2 / (2 * ε) = ε / 2 * ‖a‖ ^ 2 := by field_simp
    rw [e] at hup
    nlinarith [sq_nonneg ‖a‖]
  have : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
  exact norm_eq_zero.mp this

end IsMYSmooth

/-- **The MYKSODA iteration is well defined**: from any starting quasi-density, step (b) can always
be carried out, so iterates satisfying (b), (c) exist. -/
theorem myksoda_exists [ProperSpace E] {ε : ℝ} (hε : 0 < ε) {T : E → ℝ} {gF gT : E → E}
    (hT : IsMYSmooth ε T gT) (hsubT : ∀ w c, ∃ R, ∀ y, T y + ⟪w, y⟫ ≤ c → ‖y‖ ≤ R) (v x0 : E) :
    ∃ x x' : ℕ → E, x 0 = x0 ∧ (∀ i, gT (x' i) = -(v + gF (x i) - gT (x i))) ∧
      ∀ i, x (i + 1) = x i + ksStep ε (gF (x i) + v) (x' i - x i) • (x' i - x i) := by
  have hsel : ∀ y : E, ∃ y', gT y' + (v + gF y - gT y) = 0 :=
    fun y => hT.exists_stationary hε _ (hsubT _)
  choose sel hsel using hsel
  let x : ℕ → E :=
      fun i => Nat.rec x0 (fun _ y => y + ksStep ε (gF y + v) (sel y - y) • (sel y - y)) i
  refine ⟨x, fun i => sel (x i), rfl, fun i => ?_, fun i => rfl⟩
  exact eq_neg_of_add_eq_zero_left (hsel (x i))

section Iteration

variable {ε : ℝ} {F T : E → ℝ} {gF gT : E → E} {v : E} {x x' : ℕ → E}

/-- **Convergence of the regularised Kohn–Sham iteration (MYKSODA).**

Hypotheses: `F`, `T` are Moreau–Yosida-smooth with parameter `ε` (`hF`, `hT`); the reference
proximal points `y - ε gT y` are bounded (`hB`, a bounded density domain); sublevel sets of
`F + ⟪v,·⟫` are bounded (`hsub`); and `x`, `x'` follow the iteration (b), (c).

Conclusions: (1) the energies `F (x i) + ⟪v, x i⟫` are nonincreasing;
(2) the gradient `gF (x i) + v` tends
to `0`; (3) there is an accumulation point; (4) every accumulation point `z` (along `φ`) is a
ground-state quasi-density, `gF z + v = 0`, it minimises `F + ⟪v,·⟫`, the energies converge to its
energy, and the Kohn–Sham potentials `w (φ i)` converge to `-gT z`, the potential that reproduces
`z` in the reference system. -/
theorem myksoda_converges [ProperSpace E] (hε : 0 < ε) (hF : IsMYSmooth ε F gF)
    (hT : IsMYSmooth ε T gT)
    (hB : ∃ B, ∀ y, ‖y - ε • gT y‖ ≤ B)
    (hsub : ∀ c, ∃ R, ∀ y, F y + ⟪v, y⟫ ≤ c → ‖y‖ ≤ R)
    (hb : ∀ i, gT (x' i) = -(v + gF (x i) - gT (x i)))
    (hc : ∀ i, x (i + 1) = x i + ksStep ε (gF (x i) + v) (x' i - x i) • (x' i - x i)) :
    Antitone (fun i => F (x i) + ⟪v, x i⟫) ∧
    Tendsto (fun i => gF (x i) + v) atTop (𝓝 0) ∧
    (∃ z, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 z)) ∧
    ∀ z (φ : ℕ → ℕ), StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 z) →
      gF z + v = 0 ∧ (∀ y, F z + ⟪v, z⟫ ≤ F y + ⟪v, y⟫) ∧
      Tendsto (fun i => F (x i) + ⟪v, x i⟫) atTop (𝓝 (F z + ⟪v, z⟫)) ∧
      Tendsto (fun i => v + gF (x (φ i)) - gT (x (φ i))) atTop (𝓝 (-gT z)) := by
  set G : E → ℝ := fun y => F y + ⟪v, y⟫ with hGdef
  set gG : E → E := fun y => gF y + v
  have hG : IsMYSmooth ε G gG := hF.add_linear v
  set d : ℕ → E := fun i => x' i - x i
  set h : ℕ → E := fun i => ksStep ε (gG (x i)) (d i) • d i
  have hxh : ∀ i, x (i + 1) = x i + h i := hc
  -- (17): strong monotonicity estimate
  have h17 : ∀ i, ⟪gG (x i), d i⟫ ≤ -ε * ‖gG (x i)‖ ^ 2 := by
    intro i
    have hg : gG (x i) = gT (x i) - gT (x' i) := by
      simp only [gG, hb i]; abel
    have := hT.cocoercive hε (x i) (x' i)
    rw [← hg] at this
    have e : d i = -(x i - x' i) := by simp [d]
    rw [e, inner_neg_right]; linarith
  -- descent
  have hdesc : ∀ i, G (x (i + 1)) ≤ G (x i) - ‖h i‖ ^ 2 / (2 * ε) := fun i => by
    rw [hxh]; exact step_descent hε hG (x i) (d i)
  have hanti : Antitone (fun i => G (x i)) := by
    refine antitone_nat_of_succ_le fun i => ?_
    have := hdesc i; have : 0 ≤ ‖h i‖ ^ 2 / (2 * ε) := by positivity
    linarith
  -- boundedness
  obtain ⟨R, hR⟩ := hsub (G (x 0))
  have hxR : ∀ i, ‖x i‖ ≤ R := fun i => hR _ (hanti (Nat.zero_le i))
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hxR 0)
  set m := G 0 - ‖gG 0‖ * R
  have hm : ∀ i, m ≤ G (x i) := by
    intro i
    have h1 := hG.lower 0 (x i)
    rw [sub_zero] at h1
    have h2 := abs_real_inner_le_norm (gG 0) (x i)
    have h3 : ‖gG 0‖ * ‖x i‖ ≤ ‖gG 0‖ * R := mul_le_mul_of_nonneg_left (hxR i) (norm_nonneg _)
    simp only [m]; linarith [neg_abs_le ⟪gG 0, x i⟫]
  -- steps tend to zero
  have hsum : ∀ n, ∑ i ∈ Finset.range n, ‖h i‖ ^ 2 / (2 * ε) ≤ G (x 0) - m := by
    intro n
    have : ∀ n, ∑ i ∈ Finset.range n, ‖h i‖ ^ 2 / (2 * ε) ≤ G (x 0) - G (x n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ]; linarith [hdesc n]
    linarith [this n, hm n]
  have hsumm : Summable fun i => ‖h i‖ ^ 2 / (2 * ε) :=
    summable_of_sum_range_le (fun i => by positivity) hsum
  have hh2 : Tendsto (fun i => ‖h i‖ ^ 2) atTop (𝓝 0) := by
    have := hsumm.tendsto_atTop_zero.const_mul (2 * ε)
    rw [mul_zero] at this
    refine this.congr fun i => ?_
    field_simp
  have hh : Tendsto (fun i => ‖h i‖) atTop (𝓝 0) := by
    have := hh2.sqrt
    rw [Real.sqrt_zero] at this
    exact this.congr fun i => Real.sqrt_sq (norm_nonneg _)
  -- directions are bounded
  obtain ⟨B, hBB⟩ := hB
  set D := B + ε * (‖v‖ + ‖gF 0‖ + ‖gT 0‖) + 3 * R
  have hd : ∀ i, ‖d i‖ ≤ D := by
    intro i
    have h1 : ‖x' i‖ ≤ B + ε * ‖gT (x' i)‖ := by
      calc ‖x' i‖ = ‖(x' i - ε • gT (x' i)) + ε • gT (x' i)‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' i - ε • gT (x' i)‖ + ‖ε • gT (x' i)‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]; linarith [hBB (x' i)]
    have h2 : ‖gT (x' i)‖ ≤ ‖v‖ + ‖gF 0‖ + ‖gT 0‖ + 2 * R / ε := by
      rw [hb i, norm_neg]
      have a1 := hF.norm_le hε (x i)
      have a2 := hT.norm_le hε (x i)
      have a3 : ‖x i‖ / ε ≤ R / ε := div_le_div_of_nonneg_right (hxR i) hε.le
      calc ‖v + gF (x i) - gT (x i)‖ ≤ ‖v + gF (x i)‖ + ‖gT (x i)‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + ‖gF (x i)‖ + ‖gT (x i)‖ := by linarith [norm_add_le v (gF (x i))]
        _ ≤ _ := by rw [mul_div_assoc] at *; linarith
    have h3 : ε * ‖gT (x' i)‖ ≤ ε * (‖v‖ + ‖gF 0‖ + ‖gT 0‖) + 2 * R := by
      have := mul_le_mul_of_nonneg_left h2 hε.le
      rw [mul_add, mul_div_assoc', mul_comm ε (2 * R), mul_div_assoc, div_self hε.ne',
          mul_one] at this
      exact this
    calc ‖d i‖ ≤ ‖x' i‖ + ‖x i‖ := norm_sub_le _ _
      _ ≤ _ := by simp only [D]; linarith [hxR i]
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hd 0)
  -- gradient tends to zero
  have hg2 : Tendsto (fun i => ‖gG (x i)‖ ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun i => ‖h i‖ * D / ε ^ 2) atTop (𝓝 0) := by
      have := (hh.mul_const D).div_const (ε ^ 2)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun i => by positivity)
      fun i => ?_
    have := step_lower hε (h17 i)
    have h' : ‖h i‖ * ‖d i‖ ≤ ‖h i‖ * D := mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _)
    change ‖gG (x i)‖ ^ 2 ≤ ‖h i‖ * D / ε ^ 2
    rw [le_div_iff₀ (by positivity)]
    simp only [h] at h' ⊢; linarith
  have hg : Tendsto (fun i => gG (x i)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := hg2.sqrt
    rw [Real.sqrt_zero] at this
    exact this.congr fun i => Real.sqrt_sq (norm_nonneg _)
  refine ⟨hanti, hg, ?_, ?_⟩
  · -- Bolzano–Weierstrass
    obtain ⟨z, -, φ, hφ, hlim⟩ :=
      tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : E)) (r := R))
        (fun i => mem_closedBall_zero_iff.mpr (hxR i))
    exact ⟨z, φ, hφ, hlim⟩
  · intro z φ hφ hlim
    have hgz : gG z = 0 := by
      have h1 : Tendsto (fun i => gG (x (φ i))) atTop (𝓝 (gG z)) :=
        ((hF.continuous hε).add continuous_const).continuousAt.tendsto.comp hlim
      have h2 : Tendsto (fun i => gG (x (φ i))) atTop (𝓝 0) := hg.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hmin : ∀ y, G z ≤ G y := by
      intro y; have := hG.lower z y; rw [hgz, inner_zero_left] at this; linarith
    refine ⟨hgz, hmin, ?_, ?_⟩
    · exact (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).2
        (hG.continuous_fun.continuousAt.tendsto.comp hlim)
    · -- Kohn–Sham potentials converge
      have h1 : Tendsto (fun i => gG (x (φ i)) - gT (x (φ i))) atTop (𝓝 (gG z - gT z)) :=
        (((hF.continuous hε).add continuous_const).sub (hT.continuous hε)).continuousAt.tendsto.comp
            hlim
      rw [hgz, zero_sub] at h1
      refine h1.congr fun i => ?_
      simp only [gG]; abel

end Iteration

end DFT
