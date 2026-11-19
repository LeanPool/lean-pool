/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Cheeger.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel

/-!
# Smooth recovery of a globally Lipschitz test, and the reduction tools

Read `SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith` (smooth recovery) for the
main
contract, then the four reduction tools `locallyLipschitz_mul` (the local Lipschitz product rule),
`exists_lipschitzWith_of_eq_zero_outside_ball` (the bounded-support Lipschitz bound),
`AsymptoticLipschitz.apply_mul_le` (the asymptotic-Lipschitz product bound)
and `LocalSlope.apply_mul_le` (the local-slope product bound).

## What is proved

smooth recovery.  For a globally `K`-Lipschitz `g` the mollifications `g ⋆ ρ_R` of
`Energy/Euclidean/LipschitzApproximation/Kernel.lean` are `C^∞`, uniformly `K`-Lipschitz, converge
to
`g` uniformly (hence in `L²(ν)` for every probability law `ν`), and satisfy the pointwise bound
`limsup_{R → 0} ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)`: the mollification at `x` sees `g` only within
`2R`, so on the ball of radius `δ` it inherits the Lipschitz constant of `g` on the ball of
radius `δ + 2R`, and every constant strictly above `Lip_a g (x)` is such a constant for a small
enough radius.  The uniform bound `K²` makes reverse Fatou (`MeasureTheory.limsup_lintegral_le`)
applicable, so the mollifications form an approximating sequence of smooth tests whose limiting
energy is at most the asymptotic-Lipschitz energy of `g`.

The local Lipschitz product rule and the local-slope product bound are the reduction tools that
turn a general test into a globally Lipschitz one:
a locally Lipschitz function times a bounded globally Lipschitz one is locally Lipschitz; a
locally Lipschitz function vanishing outside a ball is globally Lipschitz; and the one-moving-
point Leibniz bounds for the asymptotic Lipschitz constant and for the local slope.

## What is not proved here

No density statement: the mollification radius is uniform in `x`, which is genuinely insufficient
for a general locally Lipschitz test.  The density
argument is `Energy/Euclidean/Slope/Density.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

/-! ### Secant suprema: the finite-radius data behind the two slopes -/

namespace LocalSlope

section Metric

variable {X : Type*} [MetricSpace X]

/-- The one-moving-point secant supremum on the open ball of radius `r` around `x`.  The local
slope is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x)

theorem apply_eq_iInf_secant (f : X → ℝ) (x : X) :
    apply f x = ⨅ (r : ℝ) (_ : 0 < r), secant f r x :=
  rfl

/-- Every positive radius bounds the local slope from above. -/
theorem apply_le_secant (f : X → ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    apply f x ≤ secant f r x :=
  iInf_le_of_le r (iInf_le _ hr)

/-- The secant supremum is monotone in the radius. -/
theorem secant_mono (f : X → ℝ) {r r' : ℝ} (h : r ≤ r') (x : X) :
    secant f r x ≤ secant f r' x := by
  refine iSup_le fun y ↦ iSup_le fun hy ↦ ?_
  exact le_iSup₂_of_le y (hy.trans_le h) le_rfl

/-- A uniform bound on the secant quotients bounds the secant supremum. -/
theorem secant_le_of_forall {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ≥0∞}
    (h : ∀ y, dist y x < r → ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ c) :
    secant f r x ≤ c :=
  iSup_le fun y ↦ iSup_le fun hy ↦ h y hy

/-- A real Lipschitz-type bound on a ball bounds the secant supremum. -/
theorem secant_le_ofReal {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ c * dist y x) :
    secant f r x ≤ ENNReal.ofReal c := by
  refine secant_le_of_forall fun y hy ↦ ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
  · simp [← h0, hc]
  · exact (div_le_iff₀ h0).2 (h y hy)

/-- A bound on the secant supremum is a Lipschitz-type bound on the ball. -/
theorem dist_le_of_secant_le {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : secant f r x ≤ ENNReal.ofReal c) {y : X} (hy : dist y x < r) :
    dist (f y) (f x) ≤ c * dist y x := by
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
  · have : y = x := by simpa [eq_comm] using h0.symm
    simp [this]
  · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ ENNReal.ofReal c :=
      le_trans (le_iSup₂_of_le y hy le_rfl) h
    rw [ENNReal.ofReal_le_ofReal_iff hc, div_le_iff₀ h0] at hq
    exact hq

/-- Below any strict upper bound for the local slope there is a radius whose secant supremum
already respects it. -/
theorem exists_secant_le {f : X → ℝ} {x : X} {c : ℝ≥0∞} (h : apply f x < c) :
    ∃ r : ℝ, 0 < r ∧ secant f r x ≤ c := by
  rw [apply_eq_iInf_secant, iInf_lt_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [iInf_lt_iff] at hr
  obtain ⟨hr0, hlt⟩ := hr
  exact ⟨r, hr0, hlt.le⟩

end Metric

end LocalSlope

namespace AsymptoticLipschitz

section Metric

variable {X : Type*} [MetricSpace X]

/-- The two-moving-point secant supremum on the open ball of radius `r` around `x`.  The
asymptotic Lipschitz constant is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)

theorem apply_eq_iInf_secant (f : X → ℝ) (x : X) :
    apply f x = ⨅ (r : ℝ) (_ : 0 < r), secant f r x :=
  rfl

/-- Every positive radius bounds the asymptotic Lipschitz constant from above. -/
theorem apply_le_secant (f : X → ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    apply f x ≤ secant f r x :=
  iInf_le_of_le r (iInf_le _ hr)

/-- A uniform bound on the secant quotients bounds the secant supremum. -/
theorem secant_le_of_forall {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ≥0∞}
    (h : ∀ y z, dist y x < r → dist z x < r →
      ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ c) :
    secant f r x ≤ c :=
  iSup_le fun y ↦ iSup_le fun hy ↦ iSup_le fun z ↦ iSup_le fun hz ↦ h y z hy hz

/-- A real Lipschitz-type bound on a ball bounds the secant supremum. -/
theorem secant_le_ofReal {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y z, dist y x < r → dist z x < r → dist (f y) (f z) ≤ c * dist y z) :
    secant f r x ≤ ENNReal.ofReal c := by
  refine secant_le_of_forall fun y z hy hz ↦ ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := z)) with h0 | h0
  · simp [← h0, hc]
  · exact (div_le_iff₀ h0).2 (h y z hy hz)

/-- Below any strict upper bound for the asymptotic Lipschitz constant there is a radius whose
secant supremum already respects it. -/
theorem exists_secant_le {f : X → ℝ} {x : X} {c : ℝ≥0∞} (h : apply f x < c) :
    ∃ r : ℝ, 0 < r ∧ secant f r x ≤ c := by
  rw [apply_eq_iInf_secant, iInf_lt_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [iInf_lt_iff] at hr
  obtain ⟨hr0, hlt⟩ := hr
  exact ⟨r, hr0, hlt.le⟩

/-- A bound on the secant supremum is a Lipschitz-type bound on the ball. -/
theorem dist_le_of_secant_le {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : secant f r x ≤ ENNReal.ofReal c) {y z : X} (hy : dist y x < r) (hz : dist z x < r) :
    dist (f y) (f z) ≤ c * dist y z := by
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := z)) with h0 | h0
  · have : y = z := by simpa [eq_comm] using h0.symm
    simp [this]
  · have hle : ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ secant f r x := by
      simp only [secant]
      refine le_iSup₂_of_le y hy ?_
      exact le_iSup₂_of_le z hz le_rfl
    have hq : ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ ENNReal.ofReal c := hle.trans h
    rw [ENNReal.ofReal_le_ofReal_iff hc, div_le_iff₀ h0] at hq
    exact hq

/-- A Lipschitz bound on one ball around `x` bounds the asymptotic Lipschitz constant at `x`. -/
theorem apply_le_of_lipschitzOnWith {f : X → ℝ} {x : X} {r : ℝ} (hr : 0 < r) {c : ℝ≥0}
    (h : LipschitzOnWith c f (Metric.ball x r)) :
    apply f x ≤ c := by
  refine (apply_le_secant f hr x).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine secant_le_ofReal c.coe_nonneg fun y z hy hz ↦ ?_
  exact h.dist_le_mul y (by simpa [Metric.mem_ball, dist_comm] using hy) z
    (by simpa [Metric.mem_ball, dist_comm] using hz)

end Metric

end AsymptoticLipschitz

/-!
### Local Lipschitz products and bounded-support estimates

The local Lipschitz product rule and the bounded-support Lipschitz bound are the two reduction
tools.
-/

section Reduction

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/--
the local Lipschitz product rule.  A locally Lipschitz function times a bounded globally Lipschitz
one is locally
Lipschitz. -/
theorem locallyLipschitz_mul {g h : V → ℝ} {N : ℝ≥0} (hg : LocallyLipschitz g)
    (hh : LipschitzWith N h) (hh1 : ∀ x, |h x| ≤ 1) : LocallyLipschitz (fun x ↦ g x * h x) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hg x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  set s : Set V := Metric.ball x (min r 1) with hs
  have hsub : s ⊆ t := (Metric.ball_subset_ball (min_le_left _ _)).trans hrt
  have hxs : x ∈ s := Metric.mem_ball_self (lt_min hr one_pos)
  have hKs : LipschitzOnWith K g s := hK.mono hsub
  have hbound : ∀ y ∈ s, |g y| ≤ |g x| + K := by
    intro y hy
    have : dist (g y) (g x) ≤ K * dist y x := hKs.dist_le_mul y hy x hxs
    have hd : dist y x < 1 :=
      lt_of_lt_of_le (by simpa [hs, Metric.mem_ball] using hy) (min_le_right _ _)
    have : |g y - g x| ≤ K * dist y x := by simpa [Real.dist_eq] using this
    have h2 : |g y| ≤ |g x| + K * dist y x := by
      have := abs_sub_abs_le_abs_sub (g y) (g x)
      linarith [abs_nonneg (g x)]
    refine h2.trans ?_
    have : K * dist y x ≤ K * 1 := by exact mul_le_mul_of_nonneg_left hd.le K.coe_nonneg
    linarith
  refine ⟨(K + (|g x| + K) * N).toNNReal, s, Metric.isOpen_ball.mem_nhds hxs, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have hCnn : (0 : ℝ) ≤ K + (|g x| + K) * N := by positivity
  rw [Real.coe_toNNReal _ hCnn]
  have hgyz : |g y - g z| ≤ K * dist y z := by
    simpa [Real.dist_eq] using hKs.dist_le_mul y hy z hz
  have hhyz : |h y - h z| ≤ N * dist y z := by simpa [Real.dist_eq] using hh.dist_le_mul y z
  have hkey : g y * h y - g z * h z = (g y - g z) * h y + g z * (h y - h z) := by ring
  have h1 : |(g y - g z) * h y| ≤ K * dist y z := by
    rw [abs_mul]
    calc
      |g y - g z| * |h y| ≤ (K * dist y z) * 1 := by
        apply mul_le_mul hgyz (hh1 y) (abs_nonneg _)
        positivity
      _ = K * dist y z := by ring
  have h2 : |g z * (h y - h z)| ≤ (|g x| + K) * (N * dist y z) := by
    rw [abs_mul]
    exact mul_le_mul (hbound z hz) hhyz (abs_nonneg _) (by positivity)
  calc
    dist (g y * h y) (g z * h z) = |(g y - g z) * h y + g z * (h y - h z)| := by
      rw [Real.dist_eq, hkey]
    _ ≤ |(g y - g z) * h y| + |g z * (h y - h z)| := abs_add_le _ _
    _ ≤ K * dist y z + (|g x| + K) * (N * dist y z) := add_le_add h1 h2
    _ = (K + (|g x| + K) * N) * dist y z := by ring

variable [FiniteDimensional ℝ V]

/--
the bounded-support Lipschitz bound.  A locally Lipschitz function vanishing outside a ball is
globally Lipschitz. -/
theorem exists_lipschitzWith_of_eq_zero_outside_ball {g : V → ℝ} {R : ℝ}
    (hg : LocallyLipschitz g) (hR : ∀ x, R ≤ ‖x‖ → g x = 0) : ∃ K : ℝ≥0, LipschitzWith K g := by
  rcases le_or_gt R 0 with hR0 | hR0
  · refine ⟨0, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
    rw [hR y (hR0.trans (norm_nonneg y)), hR z (hR0.trans (norm_nonneg z))]
    simp
  set S : Set V := Metric.closedBall (0 : V) (R + 1) with hS
  have hScompact : IsCompact S := isCompact_closedBall _ _
  obtain ⟨K, hK⟩ := lipschitzOnWith_of_locallyLipschitz_of_isCompact hg hScompact
  obtain ⟨M₀, hM₀⟩ := hScompact.exists_bound_of_continuousOn hg.continuous.continuousOn
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbound : ∀ x, |g x| ≤ M := by
    intro x
    rcases le_or_gt ‖x‖ (R + 1) with hx | hx
    · exact
        le_trans
          (by
            simpa [Real.norm_eq_abs] using
              hM₀ x (by simpa [hS, Metric.mem_closedBall, dist_zero_right] using hx))
          (le_max_left _ _)
    · rw [hR x (by linarith)]
      simpa using hM0
  refine ⟨(max (K : ℝ) (2 * M)).toNNReal, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  have hnn : (0 : ℝ) ≤ max (K : ℝ) (2 * M) := le_trans K.coe_nonneg (le_max_left _ _)
  rw [Real.coe_toNNReal _ hnn]
  have key : ∀ y z : V, ‖z‖ > R + 1 → dist (g y) (g z) ≤ max (K : ℝ) (2 * M) * dist y z := by
    intro y z hz
    have hgz : g z = 0 := hR z (by linarith)
    rcases le_or_gt R ‖y‖ with hy | hy
    · rw [hR y hy, hgz]
      simp only [dist_self, ge_iff_le]
      positivity
    · have hd : 1 < dist y z := by
        have : ‖z‖ - ‖y‖ ≤ dist y z := by
          rw [dist_comm, dist_eq_norm]
          exact le_trans (by linarith [norm_sub_norm_le z y]) le_rfl
        linarith
      calc
        dist (g y) (g z) = |g y| := by rw [hgz]; simp
        _ ≤ M := hMbound y
        _ ≤ 2 * M * dist y z := by nlinarith
        _ ≤ max (K : ℝ) (2 * M) * dist y z := by
          apply mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · rcases le_or_gt ‖z‖ (R + 1) with hz | hz
    · calc
        dist (g y) (g z) ≤ K * dist y z :=
          hK.dist_le_mul y (by simpa [hS, Metric.mem_closedBall, dist_zero_right] using hy) z
            (by simpa [hS, Metric.mem_closedBall, dist_zero_right] using hz)
        _ ≤ max (K : ℝ) (2 * M) * dist y z :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · exact key y z hz
  · rw [dist_comm (g y) (g z), dist_comm y z]
    exact key z y hy

end Reduction

/-!
### Asymptotic-Lipschitz and local-slope product bounds

These are the one-moving-point Leibniz bounds.
-/

namespace AsymptoticLipschitz

section Leibniz

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/--
the asymptotic-Lipschitz product bound.  Multiplying by a bounded `N`-Lipschitz factor costs at most
`|g x| · N` in the
asymptotic Lipschitz constant. -/
theorem apply_mul_le (g h : V → ℝ) {N : ℝ≥0} (hh : LipschitzWith N h) (hh1 : ∀ y, |h y| ≤ 1)
    (x : V) : apply (fun y ↦ g y * h y) x ≤ apply g x + ENNReal.ofReal |g x| * N := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hA : apply g x ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    simp at hlt
  set a : ℝ := (apply g x).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haA : apply g x = ENNReal.ofReal a := (ENNReal.ofReal_toReal hA).symm
  set η : ℝ := (ε : ℝ) / 2 with hη
  have hη0 : 0 < η := by positivity
  have hstep : apply g x < ENNReal.ofReal (a + η) := by
    rw [haA, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  obtain ⟨r₁, hr₁, hsec⟩ := exists_secant_le hstep
  set r : ℝ := min r₁ (η / ((a + η) * (N : ℝ) + 1)) with hr_def
  have hr0 : 0 < r := lt_min hr₁ (by positivity)
  have hrle : r ≤ r₁ := min_le_left _ _
  have hkey :
    ∀ y z : V,
      dist y x < r →
        dist z x < r → dist (g y * h y) (g z * h z) ≤ (a + |g x| * N + (ε : ℝ)) * dist y z := by
    intro y z hy hz
    have hgyz : dist (g y) (g z) ≤ (a + η) * dist y z :=
      dist_le_of_secant_le (by positivity) hsec (hy.trans_le hrle) (hz.trans_le hrle)
    have hgzx : dist (g z) (g x) ≤ (a + η) * dist z x := by
      refine dist_le_of_secant_le (by positivity) hsec (hz.trans_le hrle) ?_
      simpa using hr₁
    have hgzabs : |g z| ≤ |g x| + (a + η) * r := by
      have h1 : |g z| - |g x| ≤ |g z - g x| := abs_sub_abs_le_abs_sub _ _
      have h2 : |g z - g x| ≤ (a + η) * dist z x := by simpa [Real.dist_eq] using hgzx
      have h3 : (a + η) * dist z x ≤ (a + η) * r :=
        mul_le_mul_of_nonneg_left hz.le (by positivity)
      linarith
    have hhyz : |h y - h z| ≤ (N : ℝ) * dist y z := by
      simpa [Real.dist_eq] using hh.dist_le_mul y z
    have hexp : g y * h y - g z * h z = (g y - g z) * h y + g z * (h y - h z) := by ring
    have h1 : |(g y - g z) * h y| ≤ (a + η) * dist y z := by
      rw [abs_mul]
      calc
        |g y - g z| * |h y| ≤ ((a + η) * dist y z) * 1 := by
          refine mul_le_mul (by simpa [Real.dist_eq] using hgyz) (hh1 y) (abs_nonneg _) ?_
          positivity
        _ = (a + η) * dist y z := by ring
    have h2 : |g z * (h y - h z)| ≤ (|g x| + (a + η) * r) * ((N : ℝ) * dist y z) := by
      rw [abs_mul]
      refine mul_le_mul hgzabs hhyz (abs_nonneg _) ?_
      have : (0 : ℝ) ≤ (a + η) * r := by positivity
      linarith [abs_nonneg (g x)]
    have hsmall : (a + η) * r * (N : ℝ) ≤ η := by
      have hden : (0 : ℝ) < (a + η) * (N : ℝ) + 1 := by positivity
      have hrb : r ≤ η / ((a + η) * (N : ℝ) + 1) := min_le_right _ _
      have : (a + η) * (N : ℝ) * r ≤ (a + η) * (N : ℝ) * (η / ((a + η) * (N : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left hrb (by positivity)
      calc
        (a + η) * r * (N : ℝ) = (a + η) * (N : ℝ) * r := by ring
        _ ≤ (a + η) * (N : ℝ) * (η / ((a + η) * (N : ℝ) + 1)) := this
        _ ≤ η := by
          rw [mul_div_assoc'] at *
          rw [div_le_iff₀ hden]
          nlinarith [hη0.le]
    calc
      dist (g y * h y) (g z * h z) = |(g y - g z) * h y + g z * (h y - h z)| := by
        rw [Real.dist_eq, hexp]
      _ ≤ |(g y - g z) * h y| + |g z * (h y - h z)| := abs_add_le _ _
      _ ≤ (a + η) * dist y z + (|g x| + (a + η) * r) * ((N : ℝ) * dist y z) := add_le_add h1 h2
      _ = (a + η + |g x| * N + (a + η) * r * N) * dist y z := by ring
      _ ≤ (a + |g x| * N + (ε : ℝ)) * dist y z := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        have : (ε : ℝ) = η + η := by rw [hη]; ring
        linarith
  refine (apply_le_secant _ hr0 x).trans ?_
  refine (secant_le_ofReal (by positivity) hkey).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add ha0 (by positivity), ← haA, ENNReal.ofReal_mul (abs_nonneg (g x)),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

end Leibniz

end AsymptoticLipschitz

namespace LocalSlope

section Leibniz

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/--
the local-slope product bound.  Multiplying by a bounded `N`-Lipschitz factor costs at most `|g x| ·
N` in the local
slope.  Here the moving point is only `y`, so no correction in the radius is needed. -/
theorem apply_mul_le (g h : V → ℝ) {N : ℝ≥0} (hh : LipschitzWith N h) (hh1 : ∀ y, |h y| ≤ 1)
    (x : V) : apply (fun y ↦ g y * h y) x ≤ apply g x + ENNReal.ofReal |g x| * N := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hA : apply g x ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    simp at hlt
  set a : ℝ := (apply g x).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haA : apply g x = ENNReal.ofReal a := (ENNReal.ofReal_toReal hA).symm
  have hεr : (0 : ℝ) < (ε : ℝ) := hε
  have hstep : apply g x < ENNReal.ofReal (a + (ε : ℝ)) := by
    rw [haA, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  obtain ⟨r, hr0, hsec⟩ := exists_secant_le hstep
  have hkey :
    ∀ y : V,
      dist y x < r → dist (g y * h y) (g x * h x) ≤ (a + (ε : ℝ) + |g x| * N) * dist y x := by
    intro y hy
    have hgyx : dist (g y) (g x) ≤ (a + (ε : ℝ)) * dist y x :=
      dist_le_of_secant_le (by positivity) hsec hy
    have hhyx : |h y - h x| ≤ (N : ℝ) * dist y x := by
      simpa [Real.dist_eq] using hh.dist_le_mul y x
    have hexp : g y * h y - g x * h x = (g y - g x) * h y + g x * (h y - h x) := by ring
    have h1 : |(g y - g x) * h y| ≤ (a + (ε : ℝ)) * dist y x := by
      rw [abs_mul]
      calc
        |g y - g x| * |h y| ≤ ((a + (ε : ℝ)) * dist y x) * 1 := by
          refine mul_le_mul (by simpa [Real.dist_eq] using hgyx) (hh1 y) (abs_nonneg _) ?_
          positivity
        _ = (a + (ε : ℝ)) * dist y x := by ring
    have h2 : |g x * (h y - h x)| ≤ |g x| * ((N : ℝ) * dist y x) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hhyx (abs_nonneg _)
    calc
      dist (g y * h y) (g x * h x) = |(g y - g x) * h y + g x * (h y - h x)| := by
        rw [Real.dist_eq, hexp]
      _ ≤ |(g y - g x) * h y| + |g x * (h y - h x)| := abs_add_le _ _
      _ ≤ (a + (ε : ℝ)) * dist y x + |g x| * ((N : ℝ) * dist y x) := add_le_add h1 h2
      _ = (a + (ε : ℝ) + |g x| * N) * dist y x := by ring
  refine (apply_le_secant _ hr0 x).trans ?_
  refine (secant_le_ofReal (by positivity) hkey).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add ha0 (by positivity), ← haA, ENNReal.ofReal_mul (abs_nonneg (g x)),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  exact le_of_eq (by ring)

end Leibniz

end LocalSlope

/-! ### smooth recovery — smooth recovery of a globally Lipschitz test -/

section Mollification

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section MollifiedSlopes

omit [CompleteSpace V] [SecondCountableTopology V]
/-- The mollification at radius `R` inherits, on the ball of radius `δ`, every Lipschitz constant
of `g` on the ball of radius `δ + 2 * R`: the kernel of radius `2 * R` sees nothing further. -/
theorem lipschitzOnWith_mollify_ball (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    LipschitzOnWith c (mollify m R g) (Metric.ball x δ) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have hyx : ‖y - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hzx : ‖z - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [mollify_apply, mollify_apply, Real.dist_eq,
    ← integral_sub (integrable_shift_mul_kernel m hR hg y) (integrable_shift_mul_kernel m hR hg z)]
  have hKint : Integrable (fun t ↦ (c : ℝ) * dist y z * kernel m R t) m :=
    (integrable_kernel m hR).const_mul _
  calc |∫ t, (g (y - t) * kernel m R t - g (z - t) * kernel m R t) ∂m|
      ≤ ∫ t, (c : ℝ) * dist y z * kernel m R t ∂m := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hKint (ae_of_all _ fun t ↦ ?_)
        by_cases ht : kernel m R t = 0
        · simp [ht]
        · rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg m R t)]
          refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg m R t)
          have htR : ‖t‖ < 2 * R := norm_le_of_kernel_ne_zero m hR ht
          have hmem : ∀ w : V, ‖w - x‖ < δ → w - t ∈ Metric.ball x (δ + 2 * R) := by
            intro w hw
            rw [Metric.mem_ball, dist_eq_norm]
            have hrw : w - t - x = (w - x) - t := by abel
            have := norm_sub_le (w - x) t
            rw [hrw]
            linarith
          rw [← Real.dist_eq]
          calc dist (g (y - t)) (g (z - t)) ≤ (c : ℝ) * dist (y - t) (z - t) :=
                h.dist_le_mul _ (hmem y hyx) _ (hmem z hzx)
            _ = (c : ℝ) * dist y z := by rw [dist_sub_right]
    _ = (c : ℝ) * dist y z := by rw [integral_const_mul, integral_kernel m hR, mul_one]

/-- The mollification's derivative at `x` respects every Lipschitz constant of `g` on a slightly
larger ball. -/
theorem norm_fderiv_mollify_le_of_lipschitzOnWith (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    ‖fderiv ℝ (mollify m R g) x‖ ≤ c :=
  ((hasFDerivAt_mollify m hR hg x).differentiableAt.hasFDerivAt).le_of_lipschitzOn
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (lipschitzOnWith_mollify_ball m hR hg x h)

end MollifiedSlopes

omit [SecondCountableTopology V] in
/-- Pointwise reverse convergence: the gradient norms of the mollifications do not exceed the
asymptotic Lipschitz constant in the limit. -/
theorem limsup_enorm_gradient_mollify_le (m : Measure V) [m.IsAddHaarMeasure]
    {g : V → ℝ} (hg : Continuous g) (x : V) :
    limsup (fun j ↦ ‖gradient (mollify m (radius j) g) x‖ₑ) atTop ≤
      AsymptoticLipschitz.apply g x := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  set A : ℝ≥0∞ := AsymptoticLipschitz.apply g x with hA
  have hAtop : A ≠ ⊤ := hlt.ne
  have hstep : A < A + (ε : ℝ≥0∞) := ENNReal.lt_add_right hAtop (by exact_mod_cast hε.ne')
  obtain ⟨r, hr0, hsec⟩ := AsymptoticLipschitz.exists_secant_le hstep
  set c : ℝ≥0 := (A + (ε : ℝ≥0∞)).toNNReal with hc
  have hctop : A + (ε : ℝ≥0∞) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hAtop, ENNReal.coe_ne_top⟩
  have hcc : (c : ℝ≥0∞) = A + (ε : ℝ≥0∞) := ENNReal.coe_toNNReal hctop
  have hseq : AsymptoticLipschitz.secant g r x ≤ ENNReal.ofReal (c : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, hcc]
    exact hsec
  have hlipball : LipschitzOnWith c g (Metric.ball x r) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    exact AsymptoticLipschitz.dist_le_of_secant_le c.coe_nonneg hseq
      (by simpa [Metric.mem_ball, dist_comm] using hy)
      (by simpa [Metric.mem_ball, dist_comm] using hz)
  have hev : ∀ᶠ j in atTop, ‖gradient (mollify m (radius j) g) x‖ₑ ≤ (c : ℝ≥0∞) := by
    have h3 : Tendsto (fun j ↦ 3 * radius j) atTop (𝓝 0) := by
      simpa using tendsto_radius.const_mul (3 : ℝ)
    filter_upwards [(tendsto_order.1 h3).2 r hr0] with j hj
    have hsub : Metric.ball x (radius j + 2 * radius j) ⊆ Metric.ball x r := by
      refine Metric.ball_subset_ball ?_
      linarith
    have hbd : ‖fderiv ℝ (mollify m (radius j) g) x‖ ≤ (c : ℝ) :=
      norm_fderiv_mollify_le_of_lipschitzOnWith m (radius_pos j) (radius_pos j) hg x
        (hlipball.mono hsub)
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_gradient_eq_norm_fderiv]
    exact hbd
  rw [← hcc]
  exact limsup_le_of_le (by isBoundedDefault) hev

end Mollification

namespace SmoothGradient

section Recovery

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [SecondCountableTopology V] in
/-- smooth recovery.  The smooth-gradient relaxation of a globally Lipschitz test is at most its
asymptotic-Lipschitz energy.  The recovery sequence is the mollification at radius `2 / (j + 1)`;
the global Lipschitz constant dominates the integrands uniformly, so reverse Fatou converts the
pointwise bound `limsup ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)` into the energy bound. -/
theorem relaxation_le_asymptoticLipschitz_of_lipschitzWith (ν : ProbabilityMeasure V)
    {g : V → ℝ} {K : ℝ≥0} (hlip : LipschitzWith K g) (hmem : MemLp g 2 (ν : Measure V)) :
    relaxation ν (hmem.toLp g) ≤ AsymptoticLipschitz.energy ν g := by
  classical
  set m : Measure V := Measure.addHaar with hm
  set gj : ℕ → V → ℝ := fun j ↦ mollify m (radius j) g with hgj
  have hRj : ∀ j, (0 : ℝ) < radius j := radius_pos
  have hlipj : ∀ j, LipschitzWith K (gj j) := fun j ↦ lipschitzWith_mollify m (hRj j) hlip
  have hsmooth : ∀ j, ContDiff ℝ ∞ (gj j) := fun j ↦ contDiff_mollify m (hRj j) hlip.continuous
  have hbd : ∀ j, ∀ x, ‖gj j x - g x‖ ≤ (K : ℝ) * (2 * radius j) := fun j x ↦
    norm_mollify_sub_le m (hRj j) hlip x
  have hradle : ∀ j, radius j ≤ 1 := by
    intro j
    rw [radius, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hML : ∀ j, MemLp (gj j) 2 (ν : Measure V) := by
    intro j
    have hdiff : MemLp (fun x ↦ gj j x - g x) 2 (ν : Measure V) := by
      refine MemLp.of_bound ?_ ((K : ℝ) * (2 * radius j)) (ae_of_all _ fun x ↦ hbd j x)
      exact ((hlipj j).continuous.sub hlip.continuous).aestronglyMeasurable
    have hrw : gj j = fun x ↦ (gj j x - g x) + g x := by funext x; ring
    rw [hrw]
    exact hdiff.add hmem
  have hgradint : ∀ j, Integrable (fun x ↦ ‖gradient (gj j) x‖ ^ 2) (ν : Measure V) := by
    intro j
    refine Integrable.mono' (integrable_const ((K : ℝ) ^ 2))
      ((measurable_gradient (gj j)).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (gradient (gj j) x), norm_gradient_le_of_lipschitz (hlipj j) x]
  set T : ℕ → Test ν := fun j ↦
    { toFun := gj j
      contDiff := hsmooth j
      memLp_two := hML j
      gradient_sq_integrable := hgradint j } with hT
  have hconv : Tendsto (fun j ↦ (T j).toL2) atTop (𝓝 (hmem.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gj j) hML g hmem).mpr ?_
    refine tendsto_eLpNorm_zero_of_dominated (ν : Measure V) (p := 2) (by norm_num) (by norm_num)
      (F := fun j ↦ gj j - g) (bound := fun _ ↦ (K : ℝ) * 2) (fun j ↦ ?_) (memLp_const _)
      (fun j ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · exact ((hlipj j).continuous.sub hlip.continuous).aestronglyMeasurable
    · refine (hbd j x).trans ?_
      have := hradle j
      nlinarith [K.coe_nonneg, (hRj j).le]
    · refine squeeze_zero_norm (fun j ↦ hbd j x) ?_
      have : Tendsto (fun j ↦ (K : ℝ) * (2 * radius j)) atTop (𝓝 ((K : ℝ) * (2 * 0))) :=
        (tendsto_radius.const_mul (2 : ℝ)).const_mul (K : ℝ)
      simpa using this
  have henergy_eq : ∀ j, (((preEnergy ν).energy (T j) : ℝ≥0) : ℝ≥0∞) =
      ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V) := by
    intro j
    have h1 : ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)
        = ∫⁻ x, ENNReal.ofReal (‖gradient (gj j) x‖ ^ 2) ∂(ν : Measure V) := by
      refine lintegral_congr fun x ↦ ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal (hgradint j) (ae_of_all _ fun x ↦ sq_nonneg _)]
    change _ = ENNReal.ofReal ((T j).energy : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
    rfl
  refine le_trans ((preEnergy ν).sequentialRelaxation_le_sequenceEnergy
    (⟨T, hconv⟩ : (preEnergy ν).ApproximatingSequence (hmem.toLp g))) ?_
  have hliminf : (preEnergy ν).sequenceEnergy
      (⟨T, hconv⟩ : (preEnergy ν).ApproximatingSequence (hmem.toLp g)) =
      liminf (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop := by
    change liminf (fun j ↦ (((preEnergy ν).energy (T j) : ℝ≥0) : ℝ≥0∞)) atTop = _
    simp_rw [henergy_eq]
  rw [hliminf]
  have hmeas : ∀ j, Measurable (fun x ↦ ‖gradient (gj j) x‖ₑ ^ 2) := fun j ↦
    ((measurable_gradient (gj j)).enorm).pow_const 2
  have hbound : ∀ j, (fun x ↦ ‖gradient (gj j) x‖ₑ ^ 2) ≤ᵐ[(ν : Measure V)]
      fun _ ↦ ((K : ℝ≥0∞)) ^ 2 := by
    intro j
    refine ae_of_all _ fun x ↦ ?_
    refine pow_le_pow_left' ?_ 2
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (norm_gradient_le_of_lipschitz (hlipj j) x)
  have hfin : ∫⁻ _, ((K : ℝ≥0∞)) ^ 2 ∂(ν : Measure V) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  calc liminf (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop
      ≤ limsup (fun j ↦ ∫⁻ x, ‖gradient (gj j) x‖ₑ ^ 2 ∂(ν : Measure V)) atTop :=
        liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ ∫⁻ x, limsup (fun j ↦ ‖gradient (gj j) x‖ₑ ^ 2) atTop ∂(ν : Measure V) :=
        MeasureTheory.limsup_lintegral_le _ hmeas hbound hfin
    _ ≤ AsymptoticLipschitz.energy ν g := by
        refine lintegral_mono fun x ↦ ?_
        have hmono : Monotone (fun a : ℝ≥0∞ ↦ a ^ 2) := fun a b hab ↦ pow_le_pow_left' hab 2
        have hmap : (limsup (fun j ↦ ‖gradient (gj j) x‖ₑ) atTop) ^ 2
            = limsup ((fun a : ℝ≥0∞ ↦ a ^ 2) ∘ fun j ↦ ‖gradient (gj j) x‖ₑ) atTop :=
          hmono.map_limsup_of_continuousAt (F := atTop) _
            ((ENNReal.continuous_pow 2).continuousAt)
        rw [show (fun j ↦ ‖gradient (gj j) x‖ₑ ^ 2) =
          (fun a : ℝ≥0∞ ↦ a ^ 2) ∘ (fun j ↦ ‖gradient (gj j) x‖ₑ) from rfl, ← hmap]
        exact pow_le_pow_left' (limsup_enorm_gradient_mollify_le m hlip.continuous x) 2

end Recovery

end SmoothGradient

end FunctionalInequalities.Energy
