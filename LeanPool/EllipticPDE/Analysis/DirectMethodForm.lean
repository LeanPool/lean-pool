/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Analysis.WeakCompactness
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.LocallyConvex.SeparatingDual


/-!
# Direct method for a coercive symmetric form

A symmetric coercive form `B` on a real Hilbert space `H` attains its minimum on the set
`{U : ‖T U‖ = 1}`, for any compact `T : H →L[ℝ] E` into a normed space whose unit sphere the
image meets. This is the abstract direct method of the calculus of variations, where
compactness of the constraint map is what takes the constraint to a weak limit.

Three ingredients. Coercivity bounds a minimising sequence in `H`, so
`EllipticPdes.Analysis.exists_weakLimit` supplies a weak limit `w`. Compactness of `T` takes a
further subsequence to a strong limit `z` in `E`, and duality identifies `z` with `T w`, whence
`‖T w‖ = 1`. Weak lower semicontinuity of `B`, which is the expansion of `0 ≤ B[uₖ - w, uₖ - w]`
against `B[uₖ, w] → B[w, w]`, gives `B[w, w] ≤ inf`.

The identification of `z` needs no adjoint, and so asks nothing of `E` beyond a norm: for a
functional `g` on `E` the composite `g ∘ T` is a functional on `H`, Riesz names the vector it
pairs against, and the weak convergence in `H` gives `g (T uₖ) → g (T w)`. Two elements of `E` on
which every functional agrees are equal.

Taking `E = L²(Ω)` and `T` the Rellich embedding recovers the Rayleigh problem of
`EllipticPdes.Sobolev.exists_rayleigh_minimiser`, where the constraint is quadratic and the
minimiser satisfies a linear equation. Taking `E = L^q(Ω)` for a subcritical `q` gives the
semilinear problem, where the constraint is not quadratic and the equation is
`-Δu = λ|u|^{q-2}u`.

## Main declarations

* `EllipticPdes.Analysis.bilin_self_nonneg`: a coercive form is positive semidefinite.
* `EllipticPdes.Analysis.bilin_le_of_weakLimit`: weak lower semicontinuity.
* `EllipticPdes.Analysis.exists_bilin_minimiser`: the minimum is attained.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.2.
-/

@[expose] public section

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {B : H →L[ℝ] H →L[ℝ] ℝ}

omit [CompleteSpace H] in
/-- A coercive form is positive semidefinite. -/
lemma bilin_self_nonneg (hco : IsCoercive B) (U : H) : 0 ≤ B U U := by
  obtain ⟨C, hC, hcoer⟩ := hco
  nlinarith [hcoer U, mul_nonneg (mul_nonneg hC.le (norm_nonneg U)) (norm_nonneg U)]

omit [CompleteSpace H] in
/-- The form on a difference, expanded by symmetry. -/
lemma bilin_sub_self (hsymm : ∀ U V : H, B U V = B V U) (U V : H) :
    B (U - V) (U - V) = B U U - 2 * B U V + B V V := by
  have h1 : B (U - V) = B U - B V := by rw [map_sub]
  simp only [h1, _root_.sub_apply, map_sub]
  rw [hsymm V U]
  ring

/-- **Weak lower semicontinuity of a symmetric coercive form.** If `uₖ` converges weakly to `w`
and `B[uₖ, uₖ]` converges to `L`, then `B[w, w] ≤ L`. Positive semidefiniteness applied to
`uₖ - w` is the whole argument; no Cauchy-Schwarz for `B` is needed. -/
theorem bilin_le_of_weakLimit (hco : IsCoercive B) (hsymm : ∀ U V : H, B U V = B V U)
    {u : ℕ → H} {w : H} {L : ℝ}
    (hweak : ∀ v : H, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫))
    (hlim : Tendsto (fun k => B (u k) (u k)) atTop (𝓝 L)) :
    B w w ≤ L := by
  have hBconv : Tendsto (fun k => B (u k) w) atTop (𝓝 (B w w)) := by
    have hrw : ∀ x : H, ⟪x, hco.continuousLinearEquivOfBilin w⟫ = B x w := by
      intro x
      rw [real_inner_comm, hco.continuousLinearEquivOfBilin_apply]
      exact hsymm w x
    simpa only [hrw] using hweak (hco.continuousLinearEquivOfBilin w)
  have hlim2 : Tendsto (fun k => 2 * B (u k) w - B w w) atTop (𝓝 (B w w)) := by
    have h := (hBconv.const_mul 2).sub_const (B w w)
    rwa [show 2 * B w w - B w w = B w w by ring] at h
  refine le_of_tendsto_of_tendsto' hlim2 hlim (fun k => ?_)
  have h0 : 0 ≤ B (u k - w) (u k - w) := bilin_self_nonneg hco _
  rw [bilin_sub_self hsymm] at h0
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Direct method for a coercive symmetric form.** With `T` compact and its image meeting
the unit sphere of `E`, the form attains its minimum on `{U : ‖T U‖ = 1}`. -/
theorem exists_bilin_minimiser (hco : IsCoercive B) (hsymm : ∀ U V : H, B U V = B V U)
    (T : H →L[ℝ] E) (hT : IsCompactOperator T.toLinearMap) (hne : ∃ V : H, ‖T V‖ = 1) :
    ∃ U : H, ‖T U‖ = 1 ∧ ∀ V : H, ‖T V‖ = 1 → B U U ≤ B V V := by
  obtain ⟨C, hC, hcoer⟩ := id hco
  set S : Set ℝ := (fun U : H => B U U) '' {U : H | ‖T U‖ = 1} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨V, hV⟩ := hne
    exact ⟨B V V, V, hV, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨U, -, rfl⟩; exact bilin_self_nonneg hco U⟩
  set m : ℝ := sInf S with hmdef
  have hmle : ∀ V : H, ‖T V‖ = 1 → m ≤ B V V := fun V hV => csInf_le hSbdd ⟨V, hV, rfl⟩
  -- A minimising sequence.
  have hchoice : ∀ n : ℕ, ∃ U : H, ‖T U‖ = 1 ∧ B U U < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt hSne hlt
    obtain ⟨U, hU, rfl⟩ := hr
    exact ⟨U, hU, hrlt⟩
  choose U hUC hUlt using hchoice
  have hUB : ∀ n, B (U n) (U n) < m + 1 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hUlt n]
  set M : ℝ := Real.sqrt ((m + 1) / C) with hMdef
  have hMbound : ∀ n, ‖U n‖ ≤ M := by
    intro n
    have h2 : ‖U n‖ ^ 2 ≤ (m + 1) / C := by
      rw [le_div_iff₀ hC]
      nlinarith [hcoer (U n), hUB n]
    calc ‖U n‖ = Real.sqrt (‖U n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ M := Real.sqrt_le_sqrt h2
  -- Weak compactness in `H`.
  obtain ⟨w, φ, hφ, hweak⟩ := exists_weakLimit (u := U) hMbound
  -- Compactness of `T` in `E`.
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hcl := (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap hM1).mp hT
  have hmemcl : ∀ k, T (U (φ k))
      ∈ closure (⇑T.toLinearMap '' Metric.closedBall (0 : H) (M + 1)) :=
    fun k => subset_closure ⟨U (φ k), by
      simpa [Metric.mem_closedBall, dist_zero_right] using (hMbound (φ k)).trans (by linarith),
      rfl⟩
  obtain ⟨z, -, ψ, hψ, hψtend⟩ := hcl.tendsto_subseq hmemcl
  -- Duality identifies the strong limit with the image of the weak limit.
  have hzw : z = T w := by
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr (fun g => ?_)
    have hstrong : Tendsto (fun j => g (T (U (φ (ψ j))))) atTop (𝓝 (g z)) := by
      simpa [Function.comp_def] using (g.continuous.tendsto z).comp hψtend
    have hweakg : Tendsto (fun k => g (T (U (φ k)))) atTop (𝓝 (g (T w))) := by
      set v₀ : H := (InnerProductSpace.toDual ℝ H).symm (g.comp T) with hv₀
      have hrepr : ∀ x : H, ⟪x, v₀⟫ = g (T x) := by
        intro x
        rw [real_inner_comm, hv₀, InnerProductSpace.toDual_symm_apply]
        rfl
      simpa only [hrepr] using hweak v₀
    exact tendsto_nhds_unique hstrong (hweakg.comp hψ.tendsto_atTop)
  have hznorm : ‖z‖ = 1 := by
    have h1 : Tendsto (fun j => ‖T (U (φ (ψ j)))‖) atTop (𝓝 ‖z‖) := by
      simpa [Function.comp_def] using (continuous_norm.tendsto z).comp hψtend
    have h2 : Tendsto (fun j => ‖T (U (φ (ψ j)))‖) atTop (𝓝 1) := by
      simp only [hUC]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- Weak lower semicontinuity of the form.
  have hBUU : Tendsto (fun n => B (U n) (U n)) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => m)
      (h := fun n => m + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_
      (fun n => hmle (U n) (hUC n)) (fun n => (hUlt n).le)
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 (m + 0)) :=
      tendsto_const_nhds.add hzero
    rwa [add_zero] at hsum
  have hlsc : B w w ≤ m := by
    refine bilin_le_of_weakLimit hco hsymm hweak ?_
    simpa [Function.comp_def] using hBUU.comp hφ.tendsto_atTop
  exact ⟨w, by rw [← hzw]; exact hznorm, fun V hV => hlsc.trans (hmle V hV)⟩

end EllipticPdes.Analysis
