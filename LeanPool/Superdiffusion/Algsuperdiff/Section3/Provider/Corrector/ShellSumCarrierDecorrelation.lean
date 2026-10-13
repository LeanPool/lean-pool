/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Probability.Independence.Integration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.ShellIndependence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.ShellRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.FreshShellDecorrelation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellSecondMoment

/-!
# ShellSumCarrierDecorrelation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shell-sum forcing has compactly supported covariance, at range `√d · 3^m`

ABK26, `e.perturb.assumption` and its forcing `shom_{m-h}^{-1} (k_m - k_{m-h})
e` of `e.def.w`.

`Algsuperdiff/Section3/Provider/Corrector/FreshShellDecorrelation.lean` proves
the covariance kill for the **fresh shell alone**, at the range `√d` hard-wired
in `ShellLawJ1.range_dependence`.  The recurrence consumer
`Provider/Diffusivity/ApproximateRecurrence/LocalizationRecurrenceMesh.lean`
does not force with one shell but with the *finite shell increment*
`k_m - k_n = Σ_{k ∈ (n,m]} j_k`, whose range of dependence is `√d · 3^m`, not
`√d`.  This file supplies the covariance kill at that range.

Nothing in `FreshShellDecorrelation.lean` is edited: its `√d` statements keep
their consumers, and the statements below are the strictly more general forms,
proved from the same two halves of (J1) plus the cross-shell independence of
ABK26.

## The two mechanisms

Write `f_Σ(ω)(x) = (Σ_{k ∈ (n,m]} j_k(x)) e` for the shell-sum forcing.  Its
covariance expands into the double sum `Σ_{k,k'} E[ (j_k(w) e) · (j_{k'}(0) e) ]`
and **every** term vanishes, for two different reasons:

* the diagonal terms `k = k'` by the *spatial* range of dependence of shell `k`
  at range `√d · 3^k ≤ √d · 3^m` -- this is `e.diff.law.shift`
  (`ShellLawPrefix.marginal_scaling`) applied to (J1), already packaged as
  `Cutoff.indep_shellLocal_of_cutoff_separation`;
* the off-diagonal terms `k ≠ k'` by the *cross-shell* independence of ABK26,
  `ShellLawPrefix.independent`, packaged as
  `Cutoff.indepFun_of_measurable_shellIndexSigma_of_disjoint`.

In both cases the two factors are independent, so the product is integrable and
its expectation factors; the frozen mean-zero field then kills each factor
(`Stream.integral_shell_entry_at_point_eq_zero`, itself a `marginal_scaling`
transport of `ShellLawJ1.mean_zero`).

## The reachable constant

Exactly as at the fresh shell, `‖w‖ = √d · 3^m` is **not** reachable and every
`‖w‖ > √d · 3^m` is: the frozen (J1) local `σ`-algebras are *integral*
generated, so a point value is local only on a set containing a ball of strictly
positive radius, and the two read sets must be thickened before (J1) applies.
The exported forms are therefore stated with a strict inequality
(`..._of_lt_norm`).

## Main results

* `indepFun_shellRowForcing` -- any two shell-row observables of the increment,
  one read at `w` and one at the origin, are independent once
  `√d · 3^m < ‖w‖`.
* `memLp_two_hilbertForcing_finiteShellIncrement` -- the shell-sum forcing lies
  in `L²`; the Minkowski step over the block of the frozen (J2) tail.
* `integral_vecDot_matVecMul_finiteShellIncrement_eq_zero_of_lt_norm` -- the
  covariance of the shell-sum forcing against its `w`-translate vanishes.
-/

open MeasureTheory ProbabilityTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### Separation of two thickened read sets, at an arbitrary range -/

/-- Two closed balls of radius `r`, centred at `w` and at the origin, are
`rho`-separated in the Euclidean norm as soon as `rho + 2 r ≤ ‖w‖`.  This is the
range-`rho` form of the fresh-shell separation lemma; the supremum norm carried
by `Vec d` is dominated by the Euclidean norm (`norm_le_vecNorm`), so a
supremum-norm separation is stronger than the Euclidean one (J1) asks for. -/
private theorem le_vecNorm_sub_of_mem_closedBall {w : Vec d} {r rho : ℝ}
    (hw : rho + 2 * r ≤ ‖w‖) ⦃x y : Vec d⦄
    (hx : x ∈ Metric.closedBall w r) (hy : y ∈ Metric.closedBall (0 : Vec d) r) :
    rho ≤ Book.Ch02.vecNorm (x - y) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx hy
  rw [sub_zero] at hy
  have hdecomp : w = x - y - (x - w) + y := by abel
  have htri : ‖w‖ ≤ ‖x - y‖ + ‖x - w‖ + ‖y‖ := by
    calc ‖w‖ = ‖x - y - (x - w) + y‖ := by rw [← hdecomp]
      _ ≤ ‖x - y - (x - w)‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ + ‖x - w‖ + ‖y‖ := by
          linarith [norm_sub_le (x - y) (x - w)]
  have hnorm : rho ≤ ‖x - y‖ := by linarith
  exact hnorm.trans (norm_le_vecNorm (x - y))

/-! ### The shell-row observables of the increment forcing -/

/-- The `i`-th component of `j_k(x) e`, as a real observable of the shell
sequence.  The shell-sum forcing pairs into the double sum over shell indices of
products of two such observables, one read at `w` and one read at `0`. -/
def shellRowForcing (e x : Vec d) (i : Fin d) (k : ℤ) (omega : ShellSeq d) : ℝ :=
  ∑ l : Fin d, (omega k) x i l * e l

theorem measurable_shellRowForcing (e x : Vec d) (i : Fin d) (k : ℤ) :
    Measurable (shellRowForcing (d := d) e x i k) :=
  Finset.univ.measurable_sum fun l _ =>
    (((ShellField.measurable_eval_entry x i l).comp
      (measurable_pi_apply k)).mul_const (e l))

/-- A shell-row observable of shell `k` read at `x` is measurable for the
`k`-th coordinate comap of the integral-generated local `σ`-algebra of any set
containing a closed ball of positive radius around `x`. -/
private theorem measurable_shellRowForcing_comap {U : Set (Vec d)} {x : Vec d}
    {r : ℝ} (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) (e : Vec d) (i : Fin d)
    (k : ℤ) :
    @Measurable (ShellSeq d) ℝ
      ((ShellField.lihLocalSigma U).comap (fun omega : ShellSeq d => omega k))
      inferInstance (shellRowForcing e x i k) := by
  let : MeasurableSpace (ShellField d) := ShellField.lihLocalSigma U
  have hrow : @Measurable (ShellField d) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j : ShellField d => ∑ l : Fin d, j x i l * e l) :=
    Finset.univ.measurable_sum fun l _ =>
      (BadEvents.measurable_entry_eval_lihLocalSigma hr hrU i l).mul_const (e l)
  exact hrow.comp (Measurable.of_comap_le le_rfl)

/-- A shell-row observable of shell `k` is measurable for the `σ`-field
generated by the shells indexed by any set containing `k`. -/
private theorem measurable_shellRowForcing_shellIndexSigma {I : Set ℤ} {k : ℤ}
    (hk : k ∈ I) (e x : Vec d) (i : Fin d) :
    @Measurable (ShellSeq d) ℝ (shellIndexSigma I) inferInstance
      (shellRowForcing e x i k) := by
  have hrow : Measurable (fun j : ShellField d => ∑ l : Fin d, j x i l * e l) :=
    Finset.univ.measurable_sum fun l _ =>
      (ShellField.measurable_eval_entry x i l).mul_const (e l)
  exact hrow.comp (measurable_shellCoordinate_shellIndexSigma (d := d) hk)

/-! ### Integrability and mean zero of a shell-row observable -/

/-- **The shell-row observables are square integrable.**  This is the frozen (J2)
tail transported to shell `k` by `e.diff.law.shift`, through
`Stream.memLp_two_shell_entry`. -/
theorem memLp_two_shellRowForcing (M : ABKModel d) (e x : Vec d) (i : Fin d)
    (k : ℤ) :
    MemLp (shellRowForcing e x i k) 2 M.P.toMeasure := by
  show MemLp (fun omega : ShellSeq d => ∑ l : Fin d, (omega k) x i l * e l) 2
    M.P.toMeasure
  refine memLp_finsetSum (μ := M.P.toMeasure) Finset.univ fun l _ => ?_
  exact (Stream.memLp_two_shell_entry M k x i l).mul_const (e l)

theorem integrable_shellRowForcing (M : ABKModel d) (e x : Vec d) (i : Fin d)
    (k : ℤ) :
    Integrable (shellRowForcing e x i k) M.P.toMeasure :=
  (memLp_two_shellRowForcing M e x i k).integrable (by norm_num)

/-- **The shell-row observables are centred.**  This is the frozen (J1)
mean-zero field transported to shell `k` by `e.diff.law.shift`, through
`Stream.integral_shell_entry_at_point_eq_zero`. -/
theorem integral_shellRowForcing_eq_zero (M : ABKModel d) (e x : Vec d) (i : Fin d)
    (k : ℤ) :
    ∫ omega : ShellSeq d, shellRowForcing e x i k omega ∂M.P.toMeasure = 0 := by
  rw [show shellRowForcing (d := d) e x i k
      = fun omega : ShellSeq d => ∑ l : Fin d, (omega k) x i l * e l from rfl,
    integral_finsetSum _ fun l _ =>
      Integrable.mul_const
        ((Stream.memLp_two_shell_entry M k x i l).integrable (by norm_num)) (e l)]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_mul_const, Stream.integral_shell_entry_at_point_eq_zero M k x i l,
    zero_mul]

/-! ### Independence of the two read points -/

/-- **Any two shell-row observables of the increment decouple.**

`k` and `k'` are two shell indices at or below `m`, the first observable is read
at `w` and the second at the origin, and `√d · 3^m < ‖w‖`.  Then the two are
independent.  Two disjoint mechanisms cover the two cases: for `k = k'` the
*spatial* range of dependence of shell `k` at range `√d · 3^k ≤ √d · 3^m`, for
`k ≠ k'` the cross-shell independence of ABK26. -/
theorem indepFun_shellRowForcing (M : ABKModel d) (e : Vec d) {w : Vec d} {m : ℤ}
    (hw : Real.sqrt (d : ℝ) * (3 : ℝ) ^ m < ‖w‖) {k k' : ℤ}
    (hk : k ≤ m) (hk' : k' ≤ m) (i i' : Fin d) :
    IndepFun (shellRowForcing e w i k) (shellRowForcing e 0 i' k') M.P.toMeasure := by
  rcases eq_or_ne k k' with rfl | hne
  · -- Same shell: the spatial range of dependence at range `√d · 3^m`.
    obtain ⟨r, hr, hrsum⟩ : ∃ r : ℝ, 0 < r ∧
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ m + 2 * r ≤ ‖w‖ :=
      ⟨(‖w‖ - Real.sqrt (d : ℝ) * (3 : ℝ) ^ m) / 2, by linarith, by linarith⟩
    have hindep := indep_shellLocal_of_cutoff_separation M m k hk
      (Metric.closedBall w r) (Metric.closedBall (0 : Vec d) r)
      measurableSet_closedBall measurableSet_closedBall
      (fun _ _ hx hy => le_vecNorm_sub_of_mem_closedBall hrsum hx hy)
    refine (IndepFun_iff_Indep _ _ _).mpr ?_
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hindep
        (measurable_shellRowForcing_comap hr subset_rfl e i k).comap_le)
      (measurable_shellRowForcing_comap hr subset_rfl e i' k).comap_le
  · -- Different shells: cross-shell independence.
    have hX : @Measurable (ShellSeq d) ℝ (shellIndexSigma ({k} : Set ℤ))
        inferInstance (shellRowForcing e w i k) :=
      measurable_shellRowForcing_shellIndexSigma (Set.mem_singleton_iff.mpr rfl) e w i
    have hY : @Measurable (ShellSeq d) ℝ (shellIndexSigma ({k'} : Set ℤ))
        inferInstance (shellRowForcing e 0 i' k') :=
      measurable_shellRowForcing_shellIndexSigma (Set.mem_singleton_iff.mpr rfl) e 0 i'
    exact indepFun_of_measurable_shellIndexSigma_of_disjoint M
      (Set.disjoint_singleton.mpr hne) hX hY

/-- The expectation of a product of two shell-row observables of the increment,
one read at `w` and one at the origin, vanishes: they are independent and each
is centred. -/
theorem integral_shellRowForcing_mul_eq_zero (M : ABKModel d) (e : Vec d)
    {w : Vec d} {m : ℤ} (hw : Real.sqrt (d : ℝ) * (3 : ℝ) ^ m < ‖w‖) {k k' : ℤ}
    (hk : k ≤ m) (hk' : k' ≤ m) (i i' : Fin d) :
    ∫ omega : ShellSeq d,
        shellRowForcing e w i k omega * shellRowForcing e 0 i' k' omega
      ∂M.P.toMeasure = 0 := by
  rw [(indepFun_shellRowForcing M e hw hk hk' i i').integral_fun_mul_eq_mul_integral
      (measurable_shellRowForcing e w i k).aestronglyMeasurable
      (measurable_shellRowForcing e 0 i' k').aestronglyMeasurable,
    integral_shellRowForcing_eq_zero M e w i k, zero_mul]

/-! ### The covariance of the shell-sum forcing -/

/-- The forcing coordinate of the finite shell increment is the sum over the
shell block of the shell-row observables. -/
theorem matVecMul_finiteShellIncrement_apply (e x : Vec d) (n m : ℤ)
    (i : Fin d) (omega : ShellSeq d) :
    matVecMul (finiteShellIncrement omega n m x) e i
      = ∑ k ∈ Finset.Ioc n m, shellRowForcing e x i k omega := by
  simp only [matVecMul, shellRowForcing]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [finiteShellIncrement_apply_entry, Finset.sum_mul]

/-- The shell-sum forcing splits over the block into the single-shell forcings.
Both `matVecMul (· ) e` and `HilbertVec.ofVec` are linear. -/
theorem hilbertForcing_finiteShellIncrement_eq_sum (e x : Vec d) (n m : ℤ)
    (omega : ShellSeq d) :
    HilbertVec.ofVec (matVecMul (finiteShellIncrement omega n m x) e)
      = ∑ k ∈ Finset.Ioc n m, HilbertVec.ofVec (matVecMul ((omega k) x) e) := by
  have hvec : matVecMul (finiteShellIncrement omega n m x) e
      = ∑ k ∈ Finset.Ioc n m, matVecMul ((omega k) x) e := by
    funext i
    rw [Finset.sum_apply, matVecMul_finiteShellIncrement_apply e x n m i omega]
    rfl
  rw [hvec, ← HilbertVec.ofVecL_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => HilbertVec.ofVecL_apply _

/-- The single-shell forcing is dominated by the sum of the absolute values of
its row observables. -/
private theorem norm_hilbertForcing_shell_le (e x : Vec d) (k : ℤ)
    (omega : ShellSeq d) :
    ‖HilbertVec.ofVec (matVecMul ((omega k) x) e)‖
      ≤ (d : ℝ) * ∑ i : Fin d, ‖shellRowForcing e x i k omega‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ‖shellRowForcing e x i k omega‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hsup : ‖matVecMul ((omega k) x) e‖
      ≤ ∑ i : Fin d, ‖shellRowForcing e x i k omega‖ := by
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
    exact Finset.single_le_sum
      (f := fun j : Fin d => ‖shellRowForcing e x j k omega‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  refine le_trans (HilbertVec.norm_ofVec_le_mul_norm _) ?_
  exact mul_le_mul_of_nonneg_left hsup (Nat.cast_nonneg d)

/-- The single-shell forcing lies in `L²`: the frozen (J2) tail read through
`Stream.memLp_two_shell_entry`. -/
theorem memLp_two_hilbertForcing_shell (M : ABKModel d) (e x : Vec d) (k : ℤ) :
    MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (matVecMul ((omega k) x) e)) 2
      M.P.toMeasure := by
  have hmeasV : Measurable (fun omega : ShellSeq d => matVecMul ((omega k) x) e) :=
    Measurable.of_eval fun i => measurable_shellRowForcing e x i k
  have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      HilbertVec.ofVec (matVecMul ((omega k) x) e)) M.P.toMeasure :=
    ((HilbertVec.ofVecL d).continuous.comp_stronglyMeasurable
      hmeasV.stronglyMeasurable).aestronglyMeasurable
  have hsum : MemLp (fun omega : ShellSeq d =>
      ∑ i : Fin d, ‖shellRowForcing e x i k omega‖) 2 M.P.toMeasure :=
    memLp_finsetSum (μ := M.P.toMeasure) Finset.univ
      fun i _ => (memLp_two_shellRowForcing M e x i k).norm
  have hg : MemLp (fun omega : ShellSeq d =>
      (d : ℝ) * ∑ i : Fin d, ‖shellRowForcing e x i k omega‖) 2 M.P.toMeasure :=
    hsum.const_mul (d : ℝ)
  refine hg.of_le hmeas (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : (0 : ℝ) ≤ (d : ℝ) * ∑ i : Fin d, ‖shellRowForcing e x i k omega‖ :=
    mul_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun i _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact norm_hilbertForcing_shell_le e x k omega

/-- **The shell-sum forcing lies in `L²`.**

The Minkowski step of the manuscript's `L²` bookkeeping: the block forcing is
the sum over the block of the single-shell forcings, and every shell entry is
square integrable by the frozen (J2) tail through
`Stream.memLp_two_shell_entry`.  No normalization of `e` is assumed. -/
theorem memLp_two_hilbertForcing_finiteShellIncrement (M : ABKModel d) (e x : Vec d)
    (n m : ℤ) :
    MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (matVecMul (finiteShellIncrement omega n m x) e)) 2
      M.P.toMeasure := by
  have hsplit : (fun omega : ShellSeq d =>
        HilbertVec.ofVec (matVecMul (finiteShellIncrement omega n m x) e))
      = fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
          HilbertVec.ofVec (matVecMul ((omega k) x) e) :=
    funext fun omega => hilbertForcing_finiteShellIncrement_eq_sum e x n m omega
  rw [hsplit]
  exact memLp_finsetSum (μ := M.P.toMeasure) (Finset.Ioc n m)
    fun k _ => memLp_two_hilbertForcing_shell M e x k

/-- **The shell-sum forcing has compactly supported covariance, at the range
`√d · 3^m`.**

For every translation `w` with `√d · 3^m < ‖w‖`, the covariance of the finite
shell-increment forcing `(k_m - k_n) e` against its `w`-translate vanishes under
the shell-sequence law.  The two halves of (J1), `e.diff.law.shift` and the
cross-shell independence of are the only inputs; no lower bound on `n` is needed
and the degenerate block `m ≤ n` is covered (the increment is then zero). -/
theorem integral_vecDot_matVecMul_finiteShellIncrement_eq_zero_of_lt_norm
    (M : ABKModel d) (e : Vec d) (n m : ℤ) {w : Vec d}
    (hw : Real.sqrt (d : ℝ) * (3 : ℝ) ^ m < ‖w‖) :
    ∫ omega : ShellSeq d,
        vecDot (matVecMul (finiteShellIncrement omega n m w) e)
          (matVecMul (finiteShellIncrement omega n m 0) e)
      ∂M.P.toMeasure = 0 := by
  have hmemIoc : ∀ k ∈ Finset.Ioc n m, k ≤ m := fun k hk =>
    (Finset.mem_Ioc.mp hk).2
  -- Expand the pairing into the triple sum of shell-row products.
  have hpt : ∀ omega : ShellSeq d,
      vecDot (matVecMul (finiteShellIncrement omega n m w) e)
          (matVecMul (finiteShellIncrement omega n m 0) e)
        = ∑ i : Fin d, ∑ k ∈ Finset.Ioc n m, ∑ k' ∈ Finset.Ioc n m,
            shellRowForcing e w i k omega * shellRowForcing e 0 i k' omega := by
    intro omega
    simp only [vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [matVecMul_finiteShellIncrement_apply e w n m i omega,
      matVecMul_finiteShellIncrement_apply e 0 n m i omega, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  -- Each product is integrable, by independence of the two factors.
  have hprodint : ∀ (i : Fin d) (k : ℤ), k ≤ m → ∀ (k' : ℤ), k' ≤ m →
      Integrable (fun omega : ShellSeq d =>
        shellRowForcing e w i k omega * shellRowForcing e 0 i k' omega)
        M.P.toMeasure := by
    intro i k hk k' hk'
    exact (indepFun_shellRowForcing M e hw hk hk' i i).integrable_mul
      (integrable_shellRowForcing M e w i k) (integrable_shellRowForcing M e 0 i k')
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum _ fun k hk =>
      integrable_finsetSum _ fun k' hk' =>
        hprodint i k (hmemIoc k hk) k' (hmemIoc k' hk')]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun k hk =>
    integrable_finsetSum _ fun k' hk' =>
      hprodint i k (hmemIoc k hk) k' (hmemIoc k' hk')]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_finsetSum _ fun k' hk' =>
    hprodint i k (hmemIoc k hk) k' (hmemIoc k' hk')]
  refine Finset.sum_eq_zero fun k' hk' => ?_
  exact integral_shellRowForcing_mul_eq_zero M e hw (hmemIoc k hk) (hmemIoc k' hk') i i

end

end Algsuperdiff.Section3.Provider.Corrector
