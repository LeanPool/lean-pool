/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Pointwise multipliers on `V`

A smooth `ψ : V → ℂ` with bounded derivatives up to order `r` multiplies the Besov spaces by
differences into themselves (`Rd.modNorm_mulLp_le`): for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞` there is `C < ∞` (`Rd.multiplierTotal`) with

`‖ψ f‖_p + ‖(2^(ks) ω_r(ψ f, 2^(-k))_p)_k‖_{ℓ_q} ≤ C (‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q})`.

The ingredients:

* **bounded derivatives**: on a compact set, the derivatives of a smooth function up to order
  `r` are bounded (`ContDiffOn.exists_norm_iteratedFDerivWithin_le` for derivatives within a
  set, `Rd.exists_iteratedFDeriv_bound` with compact support);
* **differences of smooth functions**: for `G` of class `C^l`, `‖Δ_h^l G(x)‖ ≤ C ‖h‖^l` if
  `‖D^l G‖ ≤ C` on the segment from `x` to `x + l h` (`Rd.norm_higherDiff_le_of_segment`), by the
  mean value inequality, in particular if `‖D^l G‖ ≤ C` everywhere
  (`Rd.norm_higherDiff_le_of_iteratedFDeriv`);
* **Leibniz's rule for differences** (`Rd.higherDiff_mul`):
  `Δ_h^r(u v)(x) = ∑_{l ≤ r} C(r, l) Δ_h^l u(x) Δ_h^(r-l) v(x + l h)`, hence
  `ω_r(ψ f, t)_p ≤ ∑_{l ≤ r} C(r, l) C t^l ω_(r-l)(f, t)_p` (`Rd.modulus_mul_smooth_le`);
* **moduli of lower order** (`Rd.lqNorm_lpModulus_sub_le`): for `1 ≤ l ≤ s`, the quasi-norm with
  smoothness `s - l` and order `r - l` is bounded by the one with smoothness `s` and order `r`,
  through band-limited approximation, which does not depend on the order of the modulus
  (`Rd.bandModulusData`); for `l > s` the bound `ω_(r-l) ≤ 2^(r-l) ‖f‖_p` suffices.

Multiplication by a bounded continuous function is a bounded linear operator on `L_p`
(`Rd.mulLpL`). In particular, multiplication by a smooth `χ` with compact support is bounded in
the Besov quasi-norm by differences (`Rd.exists_mul_modNorm_le`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

section Smooth

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The derivative bound of one step of `Rd.norm_higherDiff_le_of_segment`: for `G` of class
`C^(l+1)`, if `‖D^(l+1) G‖ ≤ C` at the points `x + s h`, `0 ≤ s ≤ l + 1`, then
`‖D^l (Δ_h G)‖ ≤ C ‖h‖` at the points `x + t h`, `0 ≤ t ≤ l`, by the mean value inequality on the
segment from `x + t h` to `x + (t + 1) h`. -/
theorem norm_iteratedFDeriv_fwdDiff_le_of_segment {G : V → E} (l : ℕ)
    (hG : ContDiff ℝ (l + 1 : ℕ) G) (h x : V) {C : ℝ}
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) (l + 1 : ℕ), ‖iteratedFDeriv ℝ (l + 1) G (x + s • h)‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) l) :
    ‖iteratedFDeriv ℝ l (fwdDiff h G) (x + t • h)‖ ≤ C * ‖h‖ := by
  have hGh : ContDiff ℝ (l + 1 : ℕ) fun z => G (z + h) := hG.comp (contDiff_id.add contDiff_const)
  have hle : (l : WithTop ℕ∞) ≤ (l + 1 : ℕ) := by exact_mod_cast Nat.le_succ l
  have hd : Differentiable ℝ (iteratedFDeriv ℝ l G) :=
    hG.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self l)
  have hsub : iteratedFDeriv ℝ l (fwdDiff h G) (x + t • h) =
      iteratedFDeriv ℝ l G (x + t • h + h) - iteratedFDeriv ℝ l G (x + t • h) := by
    rw [show fwdDiff h G = (fun z => G (z + h)) - G from rfl,
      iteratedFDeriv_sub_apply (hGh.contDiffAt.of_le hle) (hG.contDiffAt.of_le hle),
      iteratedFDeriv_comp_add_right]
  have hder : ∀ z ∈ segment ℝ (x + t • h) (x + t • h + h),
      ‖fderiv ℝ (iteratedFDeriv ℝ l G) z‖ ≤ C := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    rw [add_sub_cancel_left, norm_fderiv_iteratedFDeriv]
    have hmem : t + θ ∈ Set.Icc (0 : ℝ) (l + 1 : ℕ) := by
      refine ⟨by linarith [ht.1, hθ.1], ?_⟩
      push_cast
      linarith [ht.2, hθ.2]
    have := hC (t + θ) hmem
    rwa [add_smul, ← add_assoc] at this
  have hmv := (convex_segment _ _).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) hder (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [add_sub_cancel_left] at hmv
  rw [hsub]
  exact hmv

/-- **Differences along a segment**: for `G` of class `C^l`, if `‖D^l G‖ ≤ C` at the points
`x + t h`, `0 ≤ t ≤ l`, then `‖Δ_h^l G(x)‖ ≤ C ‖h‖^l`. By induction on `l`: the derivatives of
order `l` of `Δ_h G` at `x + t h` are differences of those of `G`, bounded by the mean value
inequality on the segment from `x + t h` to `x + (t + 1) h`. -/
theorem norm_higherDiff_le_of_segment {G : V → E} (l : ℕ) (hG : ContDiff ℝ l G) (h x : V)
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) l, ‖iteratedFDeriv ℝ l G (x + t • h)‖ ≤ C) :
    ‖(fwdDiff h)^[l] G x‖ ≤ C * ‖h‖ ^ l := by
  induction l generalizing G C with
  | zero =>
    have := hC 0 (by simp)
    simpa [norm_iteratedFDeriv_zero] using this
  | succ l ih =>
    have hG' : ContDiff ℝ l (fwdDiff h G) :=
      ((hG.comp (contDiff_id.add contDiff_const)).sub hG).of_le
        (by exact_mod_cast Nat.le_succ l)
    rw [Function.iterate_succ_apply]
    calc ‖(fwdDiff h)^[l] (fwdDiff h G) x‖ ≤ C * ‖h‖ * ‖h‖ ^ l :=
          ih hG' fun t ht => norm_iteratedFDeriv_fwdDiff_le_of_segment l hG h x hC ht
      _ = C * ‖h‖ ^ (l + 1) := by ring

/-- **Differences of smooth functions**: if `‖D^l G‖ ≤ C` everywhere, then
`‖Δ_h^l G(x)‖ ≤ C ‖h‖^l`, the case of `Rd.norm_higherDiff_le_of_segment` with the bound on the
whole space. -/
theorem norm_higherDiff_le_of_iteratedFDeriv {G : V → E}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {l : ℕ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ l G x‖ ≤ C) (h x : V) :
    ‖(fwdDiff h)^[l] G x‖ ≤ C * ‖h‖ ^ l :=
  norm_higherDiff_le_of_segment l (hG.of_le (WithTop.coe_le_coe.2 le_top)) h x fun _ _ => hC _

/-- The bound `‖ψ‖ ≤ C` from `‖D^0 ψ‖ ≤ C`. -/
theorem norm_le_of_iteratedFDeriv_le {ψ : V → E} {r : ℕ} {C : ℝ}
    (hC : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C) (x : V) : ‖ψ x‖ ≤ C := by
  simpa [norm_iteratedFDeriv_zero] using hC 0 (Nat.zero_le r) x

/-- **Smooth functions with compact support have bounded derivatives** up to every order. -/
theorem exists_iteratedFDeriv_bound {G : V → E} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hcs : HasCompactSupport G) (r : ℕ) :
    ∃ C : ℝ, ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l G x‖ ≤ C := by
  have hb : ∀ l : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ l G x‖ ≤ C := fun l =>
    (hG.continuous_iteratedFDeriv (WithTop.coe_le_coe.2 le_top)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv l)
  choose C hC using hb
  refine ⟨∑ l ∈ Finset.range (r + 1), |C l|, fun l hl x => (hC l x).trans ((le_abs_self _).trans
    ?_)⟩
  exact Finset.single_le_sum (f := fun l => |C l|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hl))

/-- **Bounded derivatives on a compact set**: if `f` is smooth on a set `s` of unique
differentiability and `K ⊆ s` is compact, then the derivatives of `f` within `s` of the orders
`i ≤ r` are bounded on `K` by one constant (their norms are continuous on `K`). -/
theorem _root_.ContDiffOn.exists_norm_iteratedFDerivWithin_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s K : Set E} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f s)
    (hs : UniqueDiffOn ℝ s) (hK : IsCompact K) (hKs : K ⊆ s) (r : ℕ) :
    ∃ C : ℝ, ∀ i ≤ r, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ i f s x‖ ≤ C := by
  have hcont : ContinuousOn
      (fun x => ∑ i ∈ Finset.range (r + 1), ‖iteratedFDerivWithin ℝ i f s x‖) K :=
    continuousOn_finsetSum _ fun i _ =>
      ((hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.2 le_top) hs).mono hKs).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨C, fun i hi x hx => ?_⟩
  refine le_trans ?_ ((Real.le_norm_self _).trans (hC x hx))
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i f s x‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end Smooth

section Leibniz

/-- **Pascal's rule for sums**:
`∑_{l ≤ r} C(r, l) F(l + 1) + ∑_{l ≤ r} C(r, l) F(l) = ∑_{l ≤ r+1} C(r + 1, l) F(l)`. -/
theorem sum_choose_mul_succ_add (r : ℕ) (F : ℕ → ℂ) :
    ∑ l ∈ Finset.range (r + 1), (r.choose l : ℂ) * F (l + 1) +
        ∑ l ∈ Finset.range (r + 1), (r.choose l : ℂ) * F l =
      ∑ l ∈ Finset.range (r + 2), ((r + 1).choose l : ℂ) * F l := by
  rw [Finset.sum_range_succ' _ (r + 1), Finset.sum_range_succ' (fun l => (r.choose l : ℂ) * F l) r]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [Finset.sum_range_succ (fun l => (r.choose (l + 1) : ℂ) * F (l + 1)) r, Nat.choose_succ_self,
    Nat.cast_zero, zero_mul, add_zero]
  ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Leibniz's rule for differences**:
`Δ_h^r(u v)(x) = ∑_{l ≤ r} C(r, l) Δ_h^l u(x) Δ_h^(r-l) v(x + l h)`, by induction from
`Δ_h(u v)(x) = Δ_h u(x) v(x + h) + u(x) Δ_h v(x)` and Pascal's rule. -/
theorem higherDiff_mul (r : ℕ) (h : V) (u v : V → ℂ) (x : V) :
    (fwdDiff h)^[r] (fun y => u y * v y) x = ∑ l ∈ Finset.range (r + 1),
      (r.choose l : ℂ) * ((fwdDiff h)^[l] u x * (fwdDiff h)^[r - l] v (x + (l : ℝ) • h)) := by
  induction r generalizing u v x with
  | zero => simp
  | succ r ih =>
    have hstep : fwdDiff h (fun y => u y * v y) =
        (fun y => fwdDiff h u y * v (y + h)) + fun y => u y * fwdDiff h v y := by
      funext y
      simp only [fwdDiff, Pi.add_apply]
      ring
    have hT1 : (fwdDiff h)^[r] (fun y => fwdDiff h u y * v (y + h)) x =
        ∑ l ∈ Finset.range (r + 1), (r.choose l : ℂ) * ((fwdDiff h)^[l + 1] u x *
          (fwdDiff h)^[r + 1 - (l + 1)] v (x + ((l + 1 : ℕ) : ℝ) • h)) := by
      rw [ih]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Function.iterate_succ_apply, higherDiff_comp_add, Nat.add_sub_add_right]
      congr 3
      push_cast
      rw [add_smul, one_smul, add_assoc]
    have hT2 : (fwdDiff h)^[r] (fun y => u y * fwdDiff h v y) x =
        ∑ l ∈ Finset.range (r + 1), (r.choose l : ℂ) * ((fwdDiff h)^[l] u x *
          (fwdDiff h)^[r + 1 - l] v (x + (l : ℝ) • h)) := by
      rw [ih]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlr : l ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      rw [← Function.iterate_succ_apply (fwdDiff h) (r - l) v,
        show (r - l).succ = r + 1 - l by omega]
    rw [Function.iterate_succ_apply, hstep, fwdDiff_iter_add, Pi.add_apply, hT1, hT2]
    exact sum_choose_mul_succ_add r fun l =>
      (fwdDiff h)^[l] u x * (fwdDiff h)^[r + 1 - l] v (x + (l : ℝ) • h)

end Leibniz

section Lp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : Measure V} [μ.IsAddHaarMeasure]

/-- **Differences of products**: for a smooth `ψ` with `‖D^l ψ‖ ≤ C` for `l ≤ r`,
`‖Δ_h^r(ψ F)‖_p ≤ ∑_{l ≤ r} C(r, l) C ‖h‖^l ‖Δ_h^(r-l) F‖_p`. -/
theorem eLpNorm_higherDiff_mul_le {ψ F : V → ℂ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    {r : ℕ} {C : ℝ} (hC : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C)
    (hF : AEStronglyMeasurable F μ) {p : ℝ≥0∞} (hp : 1 ≤ p) (h : V) :
    eLpNorm ((fwdDiff h)^[r] (fun x => ψ x * F x)) p μ ≤
      ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ENNReal.ofReal (C * ‖h‖ ^ l) *
        eLpNorm ((fwdDiff h)^[r - l] F) p μ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le r) 0)
  set g : ℕ → V → ℝ := fun l x =>
    (r.choose l : ℝ) * (C * ‖h‖ ^ l) * ‖(fwdDiff h)^[r - l] F (x + (l : ℝ) • h)‖
  have hmeas : ∀ l, AEStronglyMeasurable (fun x => (fwdDiff h)^[r - l] F (x + (l : ℝ) • h)) μ :=
    fun l => aestronglyMeasurable_comp_add (aestronglyMeasurable_higherDiff hF _ h) _
  have hpt : ∀ x, ‖(fwdDiff h)^[r] (fun x => ψ x * F x) x‖ ≤ ∑ l ∈ Finset.range (r + 1), g l x :=
    fun x => by
      rw [higherDiff_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, ← mul_assoc]
      have hl' : l ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have := norm_higherDiff_le_of_iteratedFDeriv hψ (hC l hl') h x
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity))
        (norm_nonneg _)
  have hmeasL : AEStronglyMeasurable ((fwdDiff h)^[r] (fun x => ψ x * F x)) μ :=
    aestronglyMeasurable_higherDiff (hψ.continuous.aestronglyMeasurable.mul hF) r h
  calc eLpNorm ((fwdDiff h)^[r] (fun x => ψ x * F x)) p μ
      ≤ eLpNorm (fun x => ∑ l ∈ Finset.range (r + 1), g l x) p μ := eLpNorm_mono_real hmeasL hpt
    _ = eLpNorm (∑ l ∈ Finset.range (r + 1), g l) p μ := by
        congr 1
        funext x
        simp
    _ ≤ ∑ l ∈ Finset.range (r + 1), eLpNorm (g l) p μ :=
        eLpNorm_sum_le hp
    _ = ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ENNReal.ofReal (C * ‖h‖ ^ l) *
          eLpNorm ((fwdDiff h)^[r - l] F) p μ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have hc : 0 ≤ (r.choose l : ℝ) * (C * ‖h‖ ^ l) := by positivity
        have : g l = ((r.choose l : ℝ) * (C * ‖h‖ ^ l)) •
            fun x => ‖(fwdDiff h)^[r - l] F (x + (l : ℝ) • h)‖ := by
          funext x
          simp [g, smul_eq_mul]
        rw [this, eLpNorm_const_smul, eLpNorm_norm _ (hmeas l),
          eLpNorm_comp_add_right (aestronglyMeasurable_higherDiff hF _ h), Real.eNorm_eq_ofReal hc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-- **The modulus of a product**:
`ω_r(ψ F, t)_p ≤ ∑_{l ≤ r} C(r, l) C t^l ω_(r-l)(F, t)_p` for `t ≥ 0`. -/
theorem modulus_mul_smooth_le {ψ F : V → ℂ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {r : ℕ}
    {C : ℝ} (hC : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C) (hF : AEStronglyMeasurable F μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {t : ℝ} :
    modulus μ r p (fun x => ψ x * F x) t ≤ ∑ l ∈ Finset.range (r + 1),
      (r.choose l : ℝ≥0∞) * ENNReal.ofReal (C * t ^ l) * modulus μ (r - l) p F t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le r) 0)
  refine iSup₂_le fun h hh => (eLpNorm_higherDiff_mul_le hψ hC hF hp h).trans
    (Finset.sum_le_sum fun l _ => ?_)
  gcongr
  exact eLpNorm_higherDiff_le_modulus hh

end Lp

section Multiplier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Multiplication by a continuous function bounded by `C` keeps `L_p`. -/
theorem memLp_mul_of_bound {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F : Lp ℂ p (volume : Measure V)) : MemLp (fun x => ψ x * F x) p volume :=
  (Lp.memLp F).of_le_mul (hψ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F))
    (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hψC x) (norm_nonneg _))

/-- The product `ψ F` of a bounded continuous function and an element of `L_p`. -/
noncomputable def mulLp {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  (memLp_mul_of_bound hψ hψC F).toLp _

omit [Fact (1 ≤ p)] in
/-- The product in `L_p` is `ψ F` almost everywhere. -/
theorem mulLp_apply_ae {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F : Lp ℂ p (volume : Measure V)) : mulLp hψ hψC F =ᵐ[volume] fun x => ψ x * F x :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
/-- Multiplication by `ψ` is additive: `ψ (F - G) = ψ F - ψ G` in `L_p`. -/
theorem mulLp_sub {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F G : Lp ℂ p (volume : Measure V)) :
    mulLp hψ hψC (F - G) = mulLp hψ hψC F - mulLp hψ hψC G := by
  refine Lp.ext ?_
  filter_upwards [mulLp_apply_ae hψ hψC (F - G), mulLp_apply_ae hψ hψC F,
    mulLp_apply_ae hψ hψC G, Lp.coeFn_sub F G,
    Lp.coeFn_sub (mulLp hψ hψC F) (mulLp hψ hψC G)] with x h1 h2 h3 h4 h5
  rw [h1, h5, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, mul_sub]

omit [Fact (1 ≤ p)] in
/-- Multiplication by `ψ` is additive: `ψ (F + G) = ψ F + ψ G` in `L_p`. -/
theorem mulLp_add {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F G : Lp ℂ p (volume : Measure V)) :
    mulLp hψ hψC (F + G) = mulLp hψ hψC F + mulLp hψ hψC G := by
  refine Lp.ext ?_
  filter_upwards [mulLp_apply_ae hψ hψC (F + G), mulLp_apply_ae hψ hψC F,
    mulLp_apply_ae hψ hψC G, Lp.coeFn_add F G,
    Lp.coeFn_add (mulLp hψ hψC F) (mulLp hψ hψC G)] with x h1 h2 h3 h4 h5
  rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, mul_add]

omit [Fact (1 ≤ p)] in
/-- Multiplication by `ψ` commutes with complex scalars: `ψ (c F) = c (ψ F)` in `L_p`. -/
theorem mulLp_smul {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C) (c : ℂ)
    (F : Lp ℂ p (volume : Measure V)) : mulLp hψ hψC (c • F) = c • mulLp hψ hψC F := by
  refine Lp.ext ?_
  filter_upwards [mulLp_apply_ae hψ hψC (c • F), mulLp_apply_ae hψ hψC F, Lp.coeFn_smul c F,
    Lp.coeFn_smul c (mulLp hψ hψC F)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- `‖ψ F‖_p ≤ C ‖F‖_p`. -/
theorem enorm_mulLp_le {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F : Lp ℂ p (volume : Measure V)) : ‖mulLp hψ hψC F‖ₑ ≤ ENNReal.ofReal C * ‖F‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (mulLp_apply_ae hψ hψC F)]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (hψ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F))
    (Eventually.of_forall fun x => by
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hψC x) (norm_nonneg _)) p

/-- **Multiplication by a bounded continuous function** `ψ`, `‖ψ‖ ≤ C`, as a bounded linear
operator on `L_p` of norm at most `max C 0` (`Rd.mulLp`, `Rd.enorm_mulLp_le`). It is Mathlib's
`ContinuousLinearMap.holderL` with `q = ∞` and `B = ContinuousLinearMap.mul ℂ ℂ`, applied to the
`L_∞` class of `ψ`, packaged so that `Rd.mulLpL_apply` is `rfl` on the project's `Rd.mulLp`. -/
noncomputable def mulLpL {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  LinearMap.mkContinuous
    { toFun := mulLp hψ hψC
      map_add' := mulLp_add hψ hψC
      map_smul' := mulLp_smul hψ hψC }
    (ENNReal.ofReal C).toReal fun F => by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top)
        (enorm_mulLp_le hψ hψC F)
      rwa [ENNReal.toReal_mul, toReal_eNorm, toReal_eNorm] at h

/-- The operator `Rd.mulLpL` is `Rd.mulLp`. -/
theorem mulLpL_apply {ψ : V → ℂ} (hψ : Continuous ψ) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C)
    (F : Lp ℂ p (volume : Measure V)) : mulLpL hψ hψC F = mulLp hψ hψC F :=
  rfl

/-- **Moduli of lower order**: for `l ≤ s < r`, the quasi-norm with smoothness `s - l` and order
`r - l` is at most a constant times the one with smoothness `s` and order `r`, since both equal
band-limited approximation spaces (`Rd.bandModulusData`) and `A^s_q ⊆ A^(s-l)_q`. -/
theorem lqNorm_lpModulus_sub_le (hp : p ≠ ∞) {r l : ℕ} {s : ℝ} (hl : (l : ℝ) ≤ s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure V)) :
    lqNorm q (fun k => dyadicWeight (s - l) k * lpModulus p (r - l) F k) ≤
      (bandModulusData (V := V) hp (r - l)).inverseConst (s - l) *
        (1 - (2 : ℝ≥0∞) ^ (-(l : ℝ)))⁻¹ * (bandModulusData (V := V) hp r).directConst s *
          (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  have hlr : l ≤ r := by exact_mod_cast hl.trans hsr.le
  set M' := bandModulusData (V := V) hp (r - l)
  set M := bandModulusData (V := V) hp r
  have hθ : s - l < ((r - l : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlr]
    linarith
  calc lqNorm q (fun k => dyadicWeight (s - l) k * lpModulus p (r - l) F k)
      ≤ M'.modNorm (s - l) q F := le_add_self
    _ ≤ M'.inverseConst (s - l) * (bandScheme hp).approxNormDyadic (s - l) q F :=
        M'.modNorm_le_approxNormDyadic hq (by linarith) hθ F
    _ ≤ M'.inverseConst (s - l) * ((1 - (2 : ℝ≥0∞) ^ (-(s - (s - l))))⁻¹ *
          (bandScheme hp).approxNormDyadic s q F) :=
        mul_le_mul' le_rfl (ApproximationScheme.approxNormDyadic_le_of_lt hq hq F)
    _ ≤ M'.inverseConst (s - l) * ((1 - (2 : ℝ≥0∞) ^ (-(s - (s - l))))⁻¹ *
          (M.directConst s * M.modNorm s q F)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (M.approxNormDyadic_le_modNorm hq F))
    _ = M'.inverseConst (s - l) * (1 - (2 : ℝ≥0∞) ^ (-(l : ℝ)))⁻¹ * M.directConst s *
          M.modNorm s q F := by
        rw [sub_sub_cancel]
        ring

/-- The constant of the multiplier bound at the order `l`. -/
noncomputable def multiplierConst (hp : p ≠ ∞) (r : ℕ) (s : ℝ) (l : ℕ) : ℝ≥0∞ :=
  if l = 0 then 1 else if (l : ℝ) ≤ s then
    (bandModulusData (V := V) hp (r - l)).inverseConst (s - l) *
      (1 - (2 : ℝ≥0∞) ^ (-(l : ℝ)))⁻¹ * (bandModulusData (V := V) hp r).directConst s
  else 2 ^ (r - l) * (1 - (2 : ℝ≥0∞) ^ (-((l : ℝ) - s)))⁻¹

/-- The constants of the multiplier bound are finite for `s < r`. -/
theorem multiplierConst_ne_top (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hsr : s < r) (l : ℕ) :
    multiplierConst (V := V) hp r s l ≠ ∞ := by
  unfold multiplierConst
  split_ifs with h0 hls
  · exact ENNReal.one_ne_top
  · have hlr : l ≤ r := by exact_mod_cast hls.trans hsr.le
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ((bandModulusData (V := V) hp (r - l)).inverseConst_ne_top ?_)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top ?_))
      ((bandModulusData (V := V) hp r).directConst_ne_top s)
    · rw [Nat.cast_sub hlr]
      linarith
    · exact_mod_cast Nat.pos_of_ne_zero h0
  · replace hls := not_le.1 hls
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith))

/-- **The terms of order `l`**: `‖(2^(k(s-l)) ω_(r-l)(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K_l ‖F‖_{s,r}`. -/
theorem lqNorm_lpModulus_le_multiplierConst (hp : p ≠ ∞) {r l : ℕ} {s : ℝ}
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure V)) :
    lqNorm q (fun k => dyadicWeight (s - l) k * lpModulus p (r - l) F k) ≤
      multiplierConst (V := V) hp r s l *
        (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  unfold multiplierConst
  split_ifs with h0 hls
  · subst h0
    simp only [Nat.cast_zero, sub_zero, Nat.sub_zero, one_mul]
    exact le_add_self
  · exact lqNorm_lpModulus_sub_le hp hls hsr hq F
  · replace hls := not_le.1 hls
    calc lqNorm q (fun k => dyadicWeight (s - l) k * lpModulus p (r - l) F k)
        ≤ lqNorm q (fun k => (2 ^ (r - l) * ‖F‖ₑ) * dyadicWeight (-((l : ℝ) - s)) k) :=
          ENNReal.lqNorm_mono fun k => by
            rw [show s - (l : ℝ) = -((l : ℝ) - s) by ring, mul_comm]
            exact mul_le_mul' (lpModulus_le _ F k) le_rfl
      _ = 2 ^ (r - l) * ‖F‖ₑ * lqNorm q (dyadicWeight (-((l : ℝ) - s))) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ 2 ^ (r - l) * ‖F‖ₑ * (1 - (2 : ℝ≥0∞) ^ (-((l : ℝ) - s)))⁻¹ :=
          mul_le_mul' le_rfl (ENNReal.lqNorm_dyadicWeight_neg_le hq _)
      _ ≤ 2 ^ (r - l) * (1 - (2 : ℝ≥0∞) ^ (-((l : ℝ) - s)))⁻¹ *
            (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
          rw [mul_right_comm]
          exact mul_le_mul' le_rfl le_self_add

/-- The **constant of the multiplier bound** `K = C + ∑_{l ≤ r} C(r, l) C K_l` for a bound `C` of
the derivatives up to order `r`, with the constants `K_l` of `Rd.multiplierConst`. -/
noncomputable def multiplierTotal (hp : p ≠ ∞) (r : ℕ) (s : ℝ) (C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal C + ∑ l ∈ Finset.range (r + 1),
    (r.choose l : ℝ≥0∞) * ENNReal.ofReal C * multiplierConst (V := V) hp r s l

/-- **Pointwise multipliers**: for a smooth `ψ` with `‖D^l ψ‖ ≤ C` for `l ≤ r`, `1 ≤ p < ∞`,
`s < r` and `1 ≤ q ≤ ∞`,
`‖ψ F‖_p + ‖(2^(ks) ω_r(ψ F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`
with `K = C + ∑_{l ≤ r} C(r, l) C K_l` (`Rd.multiplierTotal`, `Rd.multiplierConst`). -/
theorem modNorm_mulLp_le (hp : p ≠ ∞) {ψ : V → ℂ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    {r : ℕ} {C : ℝ} (hC : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C) {s : ℝ} (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure V)) :
    ‖mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k *
          lpModulus p r (mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F) k) ≤
      multiplierTotal (V := V) hp r s C *
        (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  set G := mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F
  set N := ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le r) 0)
  have hmod : ∀ k, lpModulus p r G k ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) *
      ENNReal.ofReal C * (dyadicWeight (-(l : ℝ)) k * lpModulus p (r - l) F k) := fun k => by
    rw [lpModulus, modulus_congr_ae (mulLp_apply_ae _ _ F)]
    refine (modulus_mul_smooth_le hψ hC (Lp.aestronglyMeasurable F) Fact.out).trans_eq ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_one_div_two_pow_pow, lpModulus]
    ring
  have hseq : lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k) ≤
      ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ENNReal.ofReal C *
        (multiplierConst (V := V) hp r s l * N) := by
    calc lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k)
        ≤ lqNorm q (fun k => ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) *
            ENNReal.ofReal C * (dyadicWeight (s - l) k * lpModulus p (r - l) F k)) :=
          ENNReal.lqNorm_mono fun k => by
            refine (mul_le_mul' le_rfl (hmod k)).trans_eq ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [sub_eq_add_neg, ENNReal.dyadicWeight_add]
            ring
      _ ≤ ∑ l ∈ Finset.range (r + 1), lqNorm q (fun k => (r.choose l : ℝ≥0∞) *
            ENNReal.ofReal C * (dyadicWeight (s - l) k * lpModulus p (r - l) F k)) :=
          ENNReal.lqNorm_sum_le hq _ _
      _ = ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ENNReal.ofReal C *
            lqNorm q (fun k => dyadicWeight (s - l) k * lpModulus p (r - l) F k) :=
          Finset.sum_congr rfl fun l _ => ENNReal.lqNorm_const_mul _ _
      _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ENNReal.ofReal C *
            (multiplierConst (V := V) hp r s l * N) :=
          Finset.sum_le_sum fun l _ => mul_le_mul' le_rfl
            (lqNorm_lpModulus_le_multiplierConst hp hsr hq F)
  calc ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k)
      ≤ ENNReal.ofReal C * N + ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) *
          ENNReal.ofReal C * (multiplierConst (V := V) hp r s l * N) :=
        add_le_add ((enorm_mulLp_le _ _ F).trans (mul_le_mul' le_rfl le_self_add)) hseq
    _ = multiplierTotal (V := V) hp r s C * N := by
        rw [multiplierTotal, add_mul, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun l _ => by ring

/-- The constant of `Rd.modNorm_mulLp_le` is finite for `s < r`. -/
theorem multiplierTotal_ne_top (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hsr : s < r) (C : ℝ) :
    multiplierTotal (V := V) hp r s C ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.2 fun l _ =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (multiplierConst_ne_top hp hsr l)⟩

/-- **Multipliers keep the Besov spaces by differences**: if `ψ` is smooth with bounded
derivatives up to order `r`, `s < r` and `F` has a finite `(s, r)`-quasi-norm, so has `ψ F`. -/
theorem modNorm_mulLp_lt_top (hp : p ≠ ∞) {ψ : V → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {r : ℕ} {C : ℝ}
    (hC : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C) {s : ℝ} (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞) :
    ‖mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k *
          lpModulus p r (mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F) k) < ∞ :=
  (modNorm_mulLp_le hp hψ hC hsr hq F).trans_lt
    (ENNReal.mul_lt_top (multiplierTotal_ne_top hp hsr C).lt_top hF)

/-- **Smooth cutoffs are Besov multipliers**: for a smooth `χ : V → ℂ` with compact support,
`1 ≤ p < ∞`, `s < r` and `1 ≤ q ≤ ∞` there is `C < ∞` such that for every `F ∈ L_p(V)` the class
`G` of `χ F` satisfies
`‖G‖_p + ‖(2^(ks) ω_r(G, 2^(-k))_p)_k‖_{ℓ_q} ≤ C (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`.
The derivatives of `χ` up to order `r` are bounded (`Rd.exists_iteratedFDeriv_bound`), so the
pointwise multiplier theorem applies (`Rd.modNorm_mulLp_le`, with the constant
`Rd.multiplierTotal`). -/
theorem exists_mul_modNorm_le (hp : p ≠ ∞) {χ : V → ℂ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) {r : ℕ} {s : ℝ}
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V), ∃ G : Lp ℂ p (volume : Measure V),
      (G : V → ℂ) =ᵐ[volume] (fun x => χ x * F x) ∧
      ‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r G k) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  obtain ⟨C, hC⟩ := exists_iteratedFDeriv_bound hχ hχc r
  exact ⟨multiplierTotal (V := V) hp r s C, multiplierTotal_ne_top hp hsr C, fun F =>
    ⟨_, mulLp_apply_ae _ _ F, modNorm_mulLp_le hp hχ hC hsr hq F⟩⟩

end Multiplier

end Rd
