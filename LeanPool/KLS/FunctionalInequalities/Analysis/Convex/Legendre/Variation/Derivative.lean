/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Variation.Perturbation
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The first variation of the Legendre transform

Let `φ` be proper and lower semicontinuous on a finite-dimensional real inner-product space
(dimension zero included), let
`y` be interior to the finite domain of `φ*` and let `q ↦ (φ* q).toReal` be differentiable at `y`.

* Near-maximizers concentrate at the dual gradient: for every `ε > 0` there is `δ > 0` such that
  every `z` with
  `φ* y − δ ≤ ⟪z, y⟫ − φ z` satisfies `‖z − ∇(φ*)(y)‖ < ε`
  (`exists_delta_nearMaximizer_norm_sub_gradient_lt`).
* For every bounded continuous real `b`, `t ↦ (φ + t b)*(y)` is differentiable at `0` with
  derivative `−b(∇(φ*)(y))`
  (`hasDerivAt_legendre_add_smul_of_dualDifferentiable`); `φ` may take `⊤`.

No maximizing family, derivative formula, primal differentiability, global finiteness or
nonnegativity is assumed. This is
the pointwise first variation behind Cordero-Erausquin–Klartag, arXiv:1304.0630v1, (42)
(Berman–Berndtsson,
arXiv:1207.6128v1, Lemma 2.7 second point / Appendix 6); the integral first variation
(Euler–Lagrange) for a source law, the
gradient push-forward, source regularity and CEK Theorem 2 are not provided.
-/

@[expose] public section

section

namespace FunctionalInequalities.Analysis

section NearMaximizer

open Set

/-- Actual affine terms that approach the finite conjugate value concentrate
near the dual gradient. The near-maximality inequality is the quantified
antecedent, rather than a supplied stability or selected-maximizer premise. -/
theorem exists_delta_nearMaximizer_norm_sub_gradient_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E,
      (((legendre φ y).toReal - δ : ℝ) : EReal) ≤
          (inner ℝ z y : EReal) - φ z →
        ‖z - gradient (fun q : E => (legendre φ q).toReal) y‖ < ε := by
    let F : E → ℝ := fun q => (legendre φ q).toReal
    have hdF : DifferentiableAt ℝ F y := by
      simpa [F] using hd
    have hφ_bot : ∀ x : E, φ x ≠ ⊥ := by
      have hh := hφ
      simp [ProperPotential] at hh
      aesop
    have hφ_fin : ∃ x : E, φ x ≠ ⊤ := by
      have hh := hφ
      simp [ProperPotential] at hh
      aesop
    have hleg_bot : ∀ q : E, legendre φ q ≠ ⊥ := by
      rcases hφ_fin with ⟨x, hx⟩
      intro q hq
      have hf := fenchel_le φ hφ x q
      rw [hq] at hf
      have hf' : (inner ℝ x q : EReal) ≤ ⊥ := by
        simpa only [EReal.add_bot] using hf
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hf'
    have hy_top : legendre φ y ≠ ⊤ :=
      interior_subset hy
    have hLy : ((F y : ℝ) : EReal) = legendre φ y := by
      dsimp [F]
      exact EReal.coe_toReal hy_top (hleg_bot y)
    have htop_ev : ∀ᶠ q : E in nhds y, legendre φ q ≠ ⊤ := by
      exact mem_interior_iff_mem_nhds.mp hy
    have hsmall :
        (fun q => F q - F y - fderiv ℝ F y (q - y)) =o[nhds y]
          (fun q => q - y) :=
      hdF.hasFDerivAt.isLittleO
    intro ε hε
    have hrem_ev :
        ∀ᶠ q : E in nhds y,
          ‖F q - F y - fderiv ℝ F y (q - y)‖
            ≤ (ε / 4) * ‖q - y‖ := by
      exact
        (Asymptotics.isLittleO_iff.mp hsmall) (c := ε / 4) (by linarith)
    rcases (Metric.eventually_nhds_iff.mp htop_ev) with ⟨ρ, hρ, hρtop⟩
    rcases (Metric.eventually_nhds_iff.mp hrem_ev) with ⟨η, hη, hηrem⟩
    let r : ℝ := min ρ η / 2
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hrρ : r < ρ := by
      dsimp [r]
      have hmin : min ρ η ≤ ρ := min_le_left _ _
      linarith
    have hrη : r < η := by
      dsimp [r]
      have hmin : min ρ η ≤ η := min_le_right _ _
      linarith
    let δ : ℝ := r * (ε / 4)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    refine ⟨δ, hδ, ?_⟩
    intro z hp
    change ‖z - gradient F y‖ < ε
    by_cases hzg : z = gradient F y
    · subst z
      simp
      linarith
    let w : E := z - gradient F y
    have hw : w ≠ 0 := by
      dsimp [w]
      exact sub_ne_zero.mpr hzg
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : E := ‖w‖⁻¹ • w
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul]
      simp [hwpos.ne']
    let h : E := r • u
    have hh : ‖h‖ = r := by
      dsimp [h]
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
    let q : E := y + h
    have hqdist : dist q y = r := by
      rw [dist_eq_norm]
      dsimp [q]
      rw [add_sub_cancel_left, hh]
    have hqρ : dist q y < ρ := by
      rw [hqdist]
      exact hrρ
    have hqη : dist q y < η := by
      rw [hqdist]
      exact hrη
    have hqtop : legendre φ q ≠ ⊤ := hρtop hqρ
    have hLq : ((F q : ℝ) : EReal) = legendre φ q := by
      dsimp [F]
      exact EReal.coe_toReal hqtop (hleg_bot q)
    have hzbot : φ z ≠ ⊥ := hφ_bot z
    have hztop : φ z ≠ ⊤ := by
      intro hzt
      have hp' := hp
      rw [hzt, EReal.sub_top] at hp'
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hp'
    have hfen := fenchel_le φ hφ z q
    have hsum :
        (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal)
          ≤ legendre φ q + (inner ℝ z y : EReal) := by
      calc
        (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal)
            ≤ (φ z + legendre φ q) +
                ((inner ℝ z y : EReal) - φ z) :=
          add_le_add hfen hp
        _ = legendre φ q + (inner ℝ z y : EReal) := by
          have hφz : ((φ z).toReal : EReal) = φ z :=
            EReal.coe_toReal hztop hzbot
          rw [← hφz, ← hLq]
          simp only [← EReal.coe_add, ← EReal.coe_sub]
          congr 1
          ring
    have hreal :
        inner ℝ z q + (F y - δ) ≤ F q + inner ℝ z y := by
      apply EReal.coe_le_coe_iff.mp
      calc
        ((inner ℝ z q + (F y - δ) : ℝ) : EReal)
            = (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal) := by
              norm_num
        _ ≤ legendre φ q + (inner ℝ z y : EReal) := hsum
        _ = ((F q + inner ℝ z y : ℝ) : EReal) := by
          rw [← hLq]
          norm_num
    have hrel :
        inner ℝ z (q - y) ≤ F q - F y + δ := by
      calc
        inner ℝ z (q - y) = inner ℝ z q - inner ℝ z y := by
          rw [inner_sub_right]
        _ ≤ F q - F y + δ := by
          linarith
    have hgrad :
        (InnerProductSpace.toDual ℝ E) (gradient F y) = fderiv ℝ F y :=
      toDual_gradient
    have hderiv (v : E) :
        fderiv ℝ F y v = inner ℝ (gradient F y) v := by
      rw [← hgrad]
      rfl
    have hqnorm : ‖q - y‖ = r := by
      dsimp [q]
      rw [add_sub_cancel_left, hh]
    have hrem :
        F q - F y - inner ℝ (gradient F y) h ≤ (ε / 4) * r := by
      calc
        F q - F y - inner ℝ (gradient F y) h
            = F q - F y - fderiv ℝ F y h := by
              rw [hderiv]
        _ ≤ ‖F q - F y - fderiv ℝ F y (q - y)‖ := by
              rw [show q - y = h by
                dsimp [q]
                exact add_sub_cancel_left y h]
              simpa only [Real.norm_eq_abs] using (le_abs_self _)
        _ ≤ (ε / 4) * ‖q - y‖ := hηrem hqη
        _ = (ε / 4) * r := by rw [hqnorm]
    have hbound :
        inner ℝ (z - gradient F y) h ≤ (ε / 4) * r + δ := by
      calc
        inner ℝ (z - gradient F y) h
            = inner ℝ z h - inner ℝ (gradient F y) h := by
              rw [inner_sub_left]
        _ ≤ (F q - F y + δ) - inner ℝ (gradient F y) h := by
              have := hrel
              dsimp [q] at this
              rw [add_sub_cancel_left] at this
              linarith
        _ = (F q - F y - inner ℝ (gradient F y) h) + δ := by
              ring
        _ ≤ (ε / 4) * r + δ := by
              linarith
    have hleft :
        inner ℝ (z - gradient F y) h = r * ‖z - gradient F y‖ := by
      dsimp [w, h, u]
      rw [real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp [ne_of_gt hwpos]
    have hmul :
        r * ‖z - gradient F y‖ ≤ r * (ε / 2) := by
      calc
        r * ‖z - gradient F y‖ =
            inner ℝ (z - gradient F y) h := hleft.symm
        _ ≤ (ε / 4) * r + δ := hbound
        _ = r * (ε / 2) := by
          dsimp [δ]
          ring
    have hnorm : ‖z - gradient F y‖ ≤ ε / 2 := by
      nlinarith [hmul]
    linarith

end NearMaximizer

section Variation

open Set

/-- Direct first variation of the Legendre transform under a bounded continuous
perturbation. The primal potential may take `⊤`; no primal differentiability,
global finiteness, nonnegativity, or positive-dimensional assumption is made. -/
theorem hasDerivAt_legendre_add_smul_of_dualDifferentiable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q => (legendre φ q).toReal) y)
    (b : E → ℝ) (hb : Continuous b)
    (hbounded : BddAbove (Set.range fun z : E => |b z|)) :
    HasDerivAt
      (fun t : ℝ =>
        (legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y).toReal)
      (-b (gradient (fun q => (legendre φ q).toReal) y)) 0 := by
    classical
    obtain ⟨M, hMb'⟩ := bddAbove_def.mp hbounded
    have hMb (z : E) : |b z| ≤ M := hMb' _ ⟨z, rfl⟩
    have hM : 0 ≤ M := (abs_nonneg (b 0)).trans (hMb 0)
    have hy_top : legendre φ y ≠ ⊤ := interior_subset hy
    have hy_bot : legendre φ y ≠ ⊥ := legendre_ne_bot φ hφ y
    let p := gradient (fun q => (legendre φ q).toReal) y
    let A : ℝ := (legendre φ y).toReal
    let Ψ : ℝ → EReal :=
      fun t => legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
    let F : ℝ → ℝ := fun t => (Ψ t).toReal
    let a : E → ℝ := fun z => inner ℝ z y - (φ z).toReal
    have hcurve (t : ℝ) :
        Ψ t ≠ ⊤ ∧ Ψ t ≠ ⊥ ∧ |F t - A| ≤ |t| * M :=
      legendre_bounded_perturbation_finite_curve
        φ hφ y hy_top b M hM hMb t
    have hF (t : ℝ) : (F t : EReal) = Ψ t :=
      EReal.coe_toReal (hcurve t).1 (hcurve t).2.1
    have hF0 : F 0 = A := by
      simp [F, Ψ, A]
    have hterm (z : E) (hz : φ z ≠ ⊤) (t : ℝ) :
        ((a z - t * b z : ℝ) : EReal) =
          (inner ℝ z y : EReal) - (φ z + ((t * b z : ℝ) : EReal)) := by
      have hzcoe : ((φ z).toReal : EReal) = φ z :=
        EReal.coe_toReal hz (hφ.1 z)
      calc
        ((a z - t * b z : ℝ) : EReal) =
            ((inner ℝ z y - ((φ z).toReal + t * b z) : ℝ) : EReal) := by
              congr 1
              dsimp [a]
              ring
        _ = _ := by
          rw [EReal.coe_sub, EReal.coe_add, hzcoe]
    have hterm0 (z : E) (hz : φ z ≠ ⊤) :
        (a z : EReal) = (inner ℝ z y : EReal) - φ z := by
      simpa using hterm z hz 0
    obtain ⟨w, hw, hwgrad⟩ :=
      exists_legendre_maximizer_with_gradient_identity φ hφ hlsc y hy
    have hp : (inner ℝ p y : EReal) - φ p = legendre φ y := by
      simpa only [hwgrad hd] using hw
    have hpfin : φ p ≠ ⊤ := by
      intro ht
      have hh := hp
      rw [ht, EReal.sub_top] at hh
      exact hy_bot hh.symm
    have hpa : a p = A := by
      have hh := congrArg EReal.toReal ((hterm0 p hpfin).trans hp)
      simpa only [EReal.toReal_coe] using hh
    have hupper (z : E) (hz : φ z ≠ ⊤) (t : ℝ) :
        a z - t * b z ≤ F t := by
      apply EReal.coe_le_coe_iff.mp
      rw [hterm z hz t, hF t]
      exact le_iSup
        (fun w : E =>
          (inner ℝ w y : EReal) - (φ w + ((t * b w : ℝ) : EReal))) z
    have hselect (t : ℝ) :
        ∃ z : E, φ z ≠ ⊤ ∧ F t - t ^ 2 ≤ a z - t * b z := by
      by_cases ht : t = 0
      · subst t
        refine ⟨p, hpfin, ?_⟩
        simp [hF0, hpa]
      · have hlt : ((F t - t ^ 2 : ℝ) : EReal) < Ψ t := by
          calc
            ((F t - t ^ 2 : ℝ) : EReal) < (F t : EReal) :=
              EReal.coe_lt_coe_iff.mpr (by
                have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
                linarith)
            _ = Ψ t := hF t
        change ((F t - t ^ 2 : ℝ) : EReal) <
          ⨆ z : E,
            (inner ℝ z y : EReal) - (φ z + ((t * b z : ℝ) : EReal)) at hlt
        obtain ⟨z, hz⟩ := lt_iSup_iff.mp hlt
        have hzfin : φ z ≠ ⊤ := by
          intro htop
          have hh := hz
          rw [htop, EReal.top_add_coe, EReal.sub_top] at hh
          exact (not_lt_of_ge bot_le) hh
        rw [← hterm z hzfin t] at hz
        exact ⟨z, hzfin, (EReal.coe_lt_coe_iff.mp hz).le⟩
    choose z hzfin hz using hselect
    have htb (t : ℝ) : |t * b (z t)| ≤ |t| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMb (z t)) (abs_nonneg t)
    have hnearReal (t : ℝ) :
        A - (2 * M * |t| + t ^ 2) ≤ a (z t) := by
      have h₁ : -(|t| * M) ≤ F t - A :=
        (abs_le.mp (hcurve t).2.2).1
      have h₂ : -(|t| * M) ≤ t * b (z t) :=
        (abs_le.mp (htb t)).1
      have h₃ := hz t
      linarith
    have hnear (t : ℝ) :
        ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) ≤
          (inner ℝ (z t) y : EReal) - φ (z t) := by
      calc
        ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) ≤
            (a (z t) : EReal) :=
          EReal.coe_le_coe_iff.mpr (hnearReal t)
        _ = _ := hterm0 (z t) (hzfin t)
    have hsmall :
        Filter.Tendsto (fun t : ℝ => 2 * M * |t| + t ^ 2)
          (nhds 0) (nhds 0) := by
      have hc : Continuous (fun t : ℝ => 2 * M * |t| + t ^ 2) := by
        fun_prop
      simpa using hc.tendsto 0
    have hzlim : Filter.Tendsto z (nhds 0) (nhds p) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨δ, hδ, hδmax⟩ :=
        exists_delta_nearMaximizer_norm_sub_gradient_lt
          φ hφ y hy hd ε hε
      filter_upwards [hsmall.eventually (Iio_mem_nhds hδ)] with t ht
      rw [dist_eq_norm]
      apply hδmax (z t)
      calc
        ((A - δ : ℝ) : EReal) ≤
            ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
        _ ≤ _ := hnear t
    have hbz : Filter.Tendsto (fun t => b (z t))
        (nhds 0) (nhds (b p)) :=
      (hb.tendsto p).comp hzlim
    have hbconst : Filter.Tendsto (fun _ : ℝ => b p)
        (nhds 0) (nhds (b p)) :=
      continuous_const.tendsto 0
    have hbdiff : Filter.Tendsto (fun t => b (z t) - b p)
        (nhds 0) (nhds 0) := by
      simpa only [sub_self] using hbz.sub hbconst
    have hid : Filter.Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0) :=
      continuous_id.tendsto 0
    have hcontrol :
        Filter.Tendsto (fun t : ℝ => |t| + |b (z t) - b p|)
          (nhds 0) (nhds 0) := by
      simpa only [abs_zero, add_zero] using hid.abs.add hbdiff.abs
    have he_nonneg (t : ℝ) : 0 ≤ F t - A + t * b p := by
      have hh := hupper p hpfin t
      rw [hpa] at hh
      linarith
    have he_upper (t : ℝ) :
        F t - A + t * b p ≤ t ^ 2 + |t| * |b (z t) - b p| := by
      have haz : a (z t) ≤ A := by
        have hh := hupper (z t) (hzfin t) 0
        simpa only [hF0, zero_mul, sub_zero] using hh
      have hprod :
          t * (b p - b (z t)) ≤ |t| * |b (z t) - b p| := by
        calc
          t * (b p - b (z t)) ≤ |t * (b p - b (z t))| :=
            le_abs_self _
          _ = |t| * |b (z t) - b p| := by
            rw [abs_mul, abs_sub_comm (b p) (b (z t))]
      have hh := hz t
      linarith
    change HasDerivAt F (-b p) 0
    apply hasDerivAt_iff_isLittleO.mpr
    apply Asymptotics.isLittleO_iff.mpr
    intro c hc
    filter_upwards [hcontrol.eventually (Iio_mem_nhds hc)] with t ht
    simp only [sub_zero, smul_eq_mul, mul_neg, sub_neg_eq_add,
      Real.norm_eq_abs, hF0]
    rw [abs_of_nonneg (he_nonneg t)]
    calc
      F t - A + t * b p ≤ t ^ 2 + |t| * |b (z t) - b p| :=
        he_upper t
      _ = (|t| + |b (z t) - b p|) * |t| := by
        rw [← sq_abs t]
        ring
      _ ≤ c * |t| :=
        mul_le_mul_of_nonneg_right ht.le (abs_nonneg t)

end Variation

end FunctionalInequalities.Analysis
